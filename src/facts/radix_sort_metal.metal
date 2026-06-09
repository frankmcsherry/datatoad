// LSB radix sort kernels, 8 bits per pass.
//
// Sorts u64 keys (treat the 8-byte big-endian source row as `u64::from_be_bytes`),
// carrying a u32 payload in lockstep. Stable.
//
// Each threadgroup of TG=256 threads processes ITEMS_PER_TG = K*TG items, with
// each thread handling K items. Increasing K reduces num_tgs (and thus the size
// of `tg_hist`) at the cost of more per-thread state.
//
// Buffers:
//   keys_in / keys_out — u64, length n
//   vals_in / vals_out — u32, length n (ignored if has_payload == 0)
//   tg_hist            — u32, length num_tgs * 256, [tg][bin] layout.
//                        After `hist`: counts. After `scan_columns`: exclusive
//                        prefix sums down each column (the per-bin partials).
//   totals             — u32, length 256
//   bin_base           — u32, length 256

#include <metal_stdlib>
using namespace metal;

constant uint TG = 256;
constant uint K = 32;
constant uint ITEMS_PER_TG = TG * K;

// Detect which of the 8 key bytes have more than one distinct value.
// Multiple threadgroups, stride loop, per-byte bitwise AND/OR reduction.
// Each tg reduces its slice locally, then atomically merges into `glob_and_or`.
// Layout of glob_and_or: 16 uints, interleaved [AND_b0, OR_b0, AND_b1, OR_b1, ...].
// Host initializes AND slots to 0xFFFFFFFF and OR slots to 0 before dispatch,
// then computes live[b] = ((AND_b & 0xff) != (OR_b & 0xff)).
kernel void detect_live_bytes(
    device const ulong*  keys_in       [[buffer(0)]],
    device atomic_uint*  glob_and_or   [[buffer(1)]],  // 16 entries, init by host
    constant uint&       n             [[buffer(2)]],
    uint  tid       [[thread_position_in_threadgroup]],
    uint  tgid      [[threadgroup_position_in_grid]],
    uint  grid_tgs  [[threadgroups_per_grid]])
{
    threadgroup uchar t_and[TG * 8];
    threadgroup uchar t_or [TG * 8];

    uchar la[8] = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };
    uchar lo[8] = { 0,    0,    0,    0,    0,    0,    0,    0    };
    bool  saw_any = false;

    // Stride loop: this tg's threads visit positions tgid*TG + tid, +grid_tgs*TG, ...
    uint stride = grid_tgs * TG;
    for (uint i = tgid * TG + tid; i < n; i += stride) {
        ulong key = keys_in[i];
        for (uint b = 0; b < 8; ++b) {
            uchar byte = (uchar)((key >> (b * 8)) & 0xFFul);
            la[b] &= byte;
            lo[b] |= byte;
        }
        saw_any = true;
    }

    for (uint b = 0; b < 8; ++b) {
        t_and[b * TG + tid] = saw_any ? la[b] : 0xff;
        t_or [b * TG + tid] = saw_any ? lo[b] : 0x00;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Threads 0..7 each reduce one byte column then atomically merge into global.
    if (tid < 8) {
        uchar a = 0xff;
        uchar o = 0x00;
        for (uint i = 0; i < TG; ++i) {
            a &= t_and[tid * TG + i];
            o |= t_or [tid * TG + i];
        }
        atomic_fetch_and_explicit(&glob_and_or[tid * 2 + 0], (uint)a, memory_order_relaxed);
        atomic_fetch_or_explicit (&glob_and_or[tid * 2 + 1], (uint)o, memory_order_relaxed);
    }
}

// Per-threadgroup histogram of the current digit. Each thread bins K items.
kernel void hist(
    device const ulong* keys_in   [[buffer(0)]],
    device atomic_uint* tg_hist   [[buffer(1)]],
    constant uint&      n         [[buffer(2)]],
    constant uint&      shift     [[buffer(3)]],
    uint  tid  [[thread_position_in_threadgroup]],
    uint  tgid [[threadgroup_position_in_grid]])
{
    threadgroup atomic_uint local_hist[256];
    atomic_store_explicit(&local_hist[tid], 0u, memory_order_relaxed);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint tg_base = tgid * ITEMS_PER_TG;
    for (uint k = 0; k < K; ++k) {
        uint gid = tg_base + k * TG + tid;
        if (gid < n) {
            uint b = (uint)((keys_in[gid] >> shift) & 0xFFul);
            atomic_fetch_add_explicit(&local_hist[b], 1u, memory_order_relaxed);
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint v = atomic_load_explicit(&local_hist[tid], memory_order_relaxed);
    atomic_store_explicit(&tg_hist[tgid * 256 + tid], v, memory_order_relaxed);
}

// Column-wise exclusive prefix scan. Launch 256 tgs of 256 threads, one tg per bin.
// In place: tg_hist[*][b] becomes the per-tg partial offset for bin b.
// Also writes the total count of bin b to totals[b].
kernel void scan_columns(
    device uint*       tg_hist  [[buffer(0)]],
    device uint*       totals   [[buffer(1)]],
    constant uint&     num_tgs  [[buffer(2)]],
    uint  tid [[thread_position_in_threadgroup]],
    uint  b   [[threadgroup_position_in_grid]])
{
    threadgroup uint t_sums[TG];

    uint chunk = (num_tgs + TG - 1) / TG;
    uint start = tid * chunk;
    uint end   = min(start + chunk, num_tgs);

    uint s = 0;
    for (uint i = start; i < end; ++i) {
        s += tg_hist[i * 256 + b];
    }
    t_sums[tid] = s;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    if (tid == 0) {
        uint acc = 0;
        for (uint i = 0; i < TG; ++i) {
            uint v = t_sums[i];
            t_sums[i] = acc;
            acc += v;
        }
        totals[b] = acc;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint acc = t_sums[tid];
    for (uint i = start; i < end; ++i) {
        uint v = tg_hist[i * 256 + b];
        tg_hist[i * 256 + b] = acc;
        acc += v;
    }
}

// Exclusive prefix scan over the 256 per-bin totals → bin_base. One tg, single thread.
kernel void scan_totals(
    device const uint* totals    [[buffer(0)]],
    device uint*       bin_base  [[buffer(1)]],
    uint  tid [[thread_position_in_threadgroup]])
{
    if (tid == 0) {
        uint acc = 0;
        for (uint i = 0; i < 256; ++i) {
            bin_base[i] = acc;
            acc += totals[i];
        }
    }
}

// Stable scatter. Each thread processes K items across K iterations.
// Rank-within-tg is split into:
//   * iter_acc[b]: items of bin b processed in prior iterations of this tg
//   * within-iter rank: items of bin b in this iteration, before this thread
//     in stable lane order (earlier warps + lower lanes in my warp)
kernel void scatter(
    device const ulong* keys_in     [[buffer(0)]],
    device const uint*  vals_in     [[buffer(1)]],
    device ulong*       keys_out    [[buffer(2)]],
    device uint*        vals_out    [[buffer(3)]],
    device const uint*  tg_hist     [[buffer(4)]],
    device const uint*  bin_base    [[buffer(5)]],
    constant uint&      n           [[buffer(6)]],
    constant uint&      shift       [[buffer(7)]],
    constant uint&      has_payload [[buffer(8)]],
    uint  tid       [[thread_position_in_threadgroup]],
    uint  tgid      [[threadgroup_position_in_grid]],
    uint  simd_lane [[thread_index_in_simdgroup]],
    uint  simd_grp  [[simdgroup_index_in_threadgroup]])
{
    threadgroup atomic_uint warp_hist[8 * 256];  // 8 KiB
    threadgroup uint iter_acc[256];              // 1 KiB — per-bin count from prior iters
    threadgroup uint tg_partial[256];            // 1 KiB — cached row of tg_hist

    // One-time init: zero iter_acc and stage this tg's tg_hist row.
    iter_acc[tid] = 0;
    tg_partial[tid] = tg_hist[tgid * 256 + tid];
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint tg_base = tgid * ITEMS_PER_TG;

    for (uint k = 0; k < K; ++k) {
        // Reset warp_hist for this iteration: each thread zeros 8 entries.
        for (uint w = 0; w < 8; ++w) {
            atomic_store_explicit(&warp_hist[w * 256 + tid], 0u, memory_order_relaxed);
        }

        uint gid = tg_base + k * TG + tid;
        bool active = gid < n;

        ulong my_key = 0;
        uint  my_val = 0;
        uint  my_bin = 256u;
        if (active) {
            my_key = keys_in[gid];
            my_bin = (uint)((my_key >> shift) & 0xFFul);
            if (has_payload != 0u) my_val = vals_in[gid];
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (active) {
            atomic_fetch_add_explicit(&warp_hist[simd_grp * 256 + my_bin], 1u,
                                      memory_order_relaxed);
        }

        // Within-warp rank — all 32 lanes execute all 32 shuffles uniformly.
        uint rank_in_warp = 0;
        for (uint i = 0; i < 32u; ++i) {
            uint other = simd_shuffle(my_bin, (ushort)i);
            if (i < simd_lane && other == my_bin) rank_in_warp++;
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);

        if (active) {
            // Cross-warp prefix within this iteration.
            uint warp_acc = 0;
            for (uint w = 0; w < simd_grp; ++w) {
                warp_acc += atomic_load_explicit(&warp_hist[w * 256 + my_bin],
                                                 memory_order_relaxed);
            }
            uint rank_within_tg = iter_acc[my_bin] + warp_acc + rank_in_warp;
            uint dst = bin_base[my_bin] + tg_partial[my_bin] + rank_within_tg;
            keys_out[dst] = my_key;
            if (has_payload != 0u) vals_out[dst] = my_val;
        }

        // Update iter_acc with this iteration's per-bin totals.
        // Each thread sums warp_hist[*][tid] and adds to iter_acc[tid].
        threadgroup_barrier(mem_flags::mem_threadgroup);
        uint this_iter = 0;
        for (uint w = 0; w < 8; ++w) {
            this_iter += atomic_load_explicit(&warp_hist[w * 256 + tid],
                                              memory_order_relaxed);
        }
        iter_acc[tid] += this_iter;
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }
}
