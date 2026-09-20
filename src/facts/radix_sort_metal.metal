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
// `base` is the element offset of the sub-range being sorted (0 for the whole
// array); the histogram covers `base .. base+n`. This lets MSD recursion run the
// same kernel over a bucket without rebinding buffers (no offset-alignment gamble).
kernel void hist(
    device const ulong* keys_in   [[buffer(0)]],
    device atomic_uint* tg_hist   [[buffer(1)]],
    constant uint&      n         [[buffer(2)]],
    constant uint&      shift     [[buffer(3)]],
    constant uint&      base      [[buffer(4)]],
    uint  tid  [[thread_position_in_threadgroup]],
    uint  tgid [[threadgroup_position_in_grid]])
{
    threadgroup atomic_uint local_hist[256];
    atomic_store_explicit(&local_hist[tid], 0u, memory_order_relaxed);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint tg_base = tgid * ITEMS_PER_TG;
    for (uint k = 0; k < K; ++k) {
        uint local = tg_base + k * TG + tid;
        if (local < n) {
            uint b = (uint)((keys_in[base + local] >> shift) & 0xFFul);
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
    constant uint&      base        [[buffer(9)]],
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
            my_key = keys_in[base + gid];
            my_bin = (uint)((my_key >> shift) & 0xFFul);
            if (has_payload != 0u) my_val = vals_in[base + gid];
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
            keys_out[base + dst] = my_key;
            if (has_payload != 0u) vals_out[base + dst] = my_val;
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

// ── Fused inner sort: one threadgroup per bucket, all lower bytes in one dispatch ──
//
// After the MSD partition (by the top live byte) the array is 256 contiguous,
// key-ordered buckets sitting in `keys_b/vals_b`. This kernel assigns one TG to
// each bucket and finishes it by the remaining lower live bytes (LSD order),
// ping-ponging the bucket between the B and A buffers *in place* over its own
// sub-range. Because a bucket is revisited across all its lower passes, it stays
// resident in the System Level Cache rather than streaming to DRAM each pass — the
// bandwidth win MSD is supposed to buy. The whole inner phase is a single dispatch,
// so v1's per-(bucket×byte) command-encoder storm collapses to one launch.
//
// Each bucket's result is left in the A buffer (`keys_a/vals_a`) regardless of how
// many passes it took, so the host reads a single canonical buffer.
//
// One stable counting-sort pass over the bucket, single-TG: bin base is the bucket's
// own exclusive-prefix (no cross-TG term); rank-within-TG is iter_acc + cross-warp
// prefix + within-warp rank, exactly as in `scatter`.
kernel void inner_fused(
    device ulong*       keys_a       [[buffer(0)]],  // result buffer
    device ulong*       keys_b       [[buffer(1)]],  // partitioned input
    device uint*        vals_a       [[buffer(2)]],
    device uint*        vals_b       [[buffer(3)]],
    device const uint*  bucket_off   [[buffer(4)]],  // 256 bucket start offsets
    device const uint*  bucket_cnt   [[buffer(5)]],  // 256 bucket counts
    device const uint*  lower_shifts [[buffer(6)]],  // n_lower shifts, LSD order
    constant uint&      n_lower      [[buffer(7)]],
    constant uint&      has_payload  [[buffer(8)]],
    constant uint&      max_cnt      [[buffer(9)]],  // skip buckets bigger than this
    uint  tid       [[thread_position_in_threadgroup]],
    uint  bin       [[threadgroup_position_in_grid]],
    uint  simd_lane [[thread_index_in_simdgroup]],
    uint  simd_grp  [[simdgroup_index_in_threadgroup]])
{
    uint base = bucket_off[bin];
    uint cnt  = bucket_cnt[bin];
    // Buckets larger than `max_cnt` are finished by the full-width global kernels
    // instead (one TG per bucket would starve the GPU when there are few of them).
    if (cnt > max_cnt) return;

    threadgroup uint        prefix[256];          // bucket's exclusive-prefix bin base
    threadgroup atomic_uint warp_hist[8 * 256];   // 8 KiB
    threadgroup uint        iter_acc[256];

    // Ping-pong device pointers for this bucket; input lives in B.
    device ulong* sk = keys_b; device ulong* dk = keys_a;
    device uint*  sv = vals_b; device uint*  dv = vals_a;

    for (uint p = 0; p < n_lower; ++p) {
        uint shift = lower_shifts[p];

        // ---- histogram of this byte over the bucket (into prefix[], reused) ----
        prefix[tid] = 0;
        iter_acc[tid] = 0;
        threadgroup_barrier(mem_flags::mem_threadgroup);
        // count via atomics in warp_hist row 0 to keep prefix[] non-atomic afterwards.
        atomic_store_explicit(&warp_hist[tid], 0u, memory_order_relaxed);
        threadgroup_barrier(mem_flags::mem_threadgroup);
        for (uint i = tid; i < cnt; i += TG) {
            uint b = (uint)((sk[base + i] >> shift) & 0xFFul);
            atomic_fetch_add_explicit(&warp_hist[b], 1u, memory_order_relaxed);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        // exclusive prefix sum over the 256 counts (single thread; 256 is small).
        if (tid == 0) {
            uint acc = 0;
            for (uint b = 0; b < 256; ++b) {
                uint v = atomic_load_explicit(&warp_hist[b], memory_order_relaxed);
                prefix[b] = acc;
                acc += v;
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);

        // ---- stable scatter over the bucket in iterations of TG elements ----
        uint iters = (cnt + TG - 1) / TG;
        for (uint it = 0; it < iters; ++it) {
            for (uint w = 0; w < 8; ++w) {
                atomic_store_explicit(&warp_hist[w * 256 + tid], 0u, memory_order_relaxed);
            }
            uint i = it * TG + tid;
            bool active = i < cnt;

            ulong my_key = 0; uint my_val = 0; uint my_bin = 256u;
            if (active) {
                my_key = sk[base + i];
                my_bin = (uint)((my_key >> shift) & 0xFFul);
                if (has_payload != 0u) my_val = sv[base + i];
            }
            threadgroup_barrier(mem_flags::mem_threadgroup);
            if (active) {
                atomic_fetch_add_explicit(&warp_hist[simd_grp * 256 + my_bin], 1u,
                                          memory_order_relaxed);
            }
            uint rank_in_warp = 0;
            for (uint j = 0; j < 32u; ++j) {
                uint other = simd_shuffle(my_bin, (ushort)j);
                if (j < simd_lane && other == my_bin) rank_in_warp++;
            }
            threadgroup_barrier(mem_flags::mem_threadgroup);
            if (active) {
                uint warp_acc = 0;
                for (uint w = 0; w < simd_grp; ++w) {
                    warp_acc += atomic_load_explicit(&warp_hist[w * 256 + my_bin],
                                                     memory_order_relaxed);
                }
                uint rank = iter_acc[my_bin] + warp_acc + rank_in_warp;
                uint dst = prefix[my_bin] + rank;
                dk[base + dst] = my_key;
                if (has_payload != 0u) dv[base + dst] = my_val;
            }
            threadgroup_barrier(mem_flags::mem_threadgroup);
            uint this_iter = 0;
            for (uint w = 0; w < 8; ++w) {
                this_iter += atomic_load_explicit(&warp_hist[w * 256 + tid],
                                                  memory_order_relaxed);
            }
            iter_acc[tid] += this_iter;
            threadgroup_barrier(mem_flags::mem_threadgroup);
        }

        // swap src/dst for the next byte.
        device ulong* tk = sk; sk = dk; dk = tk;
        device uint*  tv = sv; sv = dv; dv = tv;
    }

    // Ensure the bucket's final data is in the A buffer for a single-buffer readout.
    if (sk != keys_a) {
        for (uint i = tid; i < cnt; i += TG) {
            keys_a[base + i] = sk[base + i];
            if (has_payload != 0u) vals_a[base + i] = sv[base + i];
        }
    }
}

// ── Software write-combining (SWWC) scatter for the MSD partition byte ──
//
// The plain `scatter` writes 32 lanes of a warp to 32 different bins → 32 scattered,
// uncoalesced DRAM writes. This kernel instead buckets a threadgroup's slice *in
// threadgroup memory* (grouped by bin), reserves one contiguous output run per bin
// via a single global atomic, then streams the staging buffer to DRAM so consecutive
// threads hit consecutive addresses — coalesced full-line writes.
//
// It is UNSTABLE within a bin, which is fine for the MSD partition: inner_fused
// re-sorts every bucket by the lower bytes afterward, so partition order is moot.
//
// `cursor[256]` must be host-initialized to the exclusive-prefix bin offsets
// (`bin_base`); each threadgroup atomically advances it to claim its run.
constant uint K_S    = 6;
constant uint ITEMS_S = TG * K_S;   // 1536 staged elements per threadgroup

kernel void scatter_swwc(
    device const ulong* keys_in     [[buffer(0)]],
    device const uint*  vals_in     [[buffer(1)]],
    device ulong*       keys_out    [[buffer(2)]],
    device uint*        vals_out     [[buffer(3)]],
    device atomic_uint* cursor      [[buffer(4)]],  // 256, init to bin_base
    constant uint&      n           [[buffer(5)]],
    constant uint&      shift       [[buffer(6)]],
    constant uint&      has_payload [[buffer(7)]],
    constant uint&      base        [[buffer(8)]],
    uint  tid  [[thread_position_in_threadgroup]],
    uint  tgid [[threadgroup_position_in_grid]])
{
    threadgroup ulong s_keys[ITEMS_S];
    threadgroup uint  s_vals[ITEMS_S];
    threadgroup uchar s_bin [ITEMS_S];
    threadgroup atomic_uint lcount[256];   // this TG's per-bin counts
    threadgroup uint        lbase [256];   // exclusive prefix of lcount (staging layout)
    threadgroup atomic_uint lfill [256];   // placement cursor within each bin's run
    threadgroup uint        run_start[256];// reserved global offset per bin

    atomic_store_explicit(&lcount[tid], 0u, memory_order_relaxed);
    atomic_store_explicit(&lfill[tid], 0u, memory_order_relaxed);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint tg_base = tgid * ITEMS_S;
    ulong mk[K_S]; uint mv[K_S]; uchar mb[K_S]; bool act[K_S];
    for (uint k = 0; k < K_S; ++k) {
        uint local = k * TG + tid;          // strided → coalesced input reads
        uint gid = tg_base + local;
        act[k] = gid < n;
        if (act[k]) {
            mk[k] = keys_in[base + gid];
            mb[k] = (uchar)((mk[k] >> shift) & 0xFFul);
            if (has_payload != 0u) mv[k] = vals_in[base + gid];
            atomic_fetch_add_explicit(&lcount[mb[k]], 1u, memory_order_relaxed);
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Exclusive prefix of this TG's per-bin counts → staging layout.
    if (tid == 0) {
        uint acc = 0;
        for (uint b = 0; b < 256; ++b) {
            uint c = atomic_load_explicit(&lcount[b], memory_order_relaxed);
            lbase[b] = acc;
            acc += c;
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Reserve one contiguous global run per bin (thread tid owns bin tid).
    uint my_cnt = atomic_load_explicit(&lcount[tid], memory_order_relaxed);
    run_start[tid] = (my_cnt > 0)
        ? atomic_fetch_add_explicit(&cursor[tid], my_cnt, memory_order_relaxed)
        : 0u;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Group this TG's elements by bin into the staging buffer.
    for (uint k = 0; k < K_S; ++k) {
        if (act[k]) {
            uint slot = lbase[mb[k]] +
                atomic_fetch_add_explicit(&lfill[mb[k]], 1u, memory_order_relaxed);
            s_keys[slot] = mk[k];
            if (has_payload != 0u) s_vals[slot] = mv[k];
            s_bin[slot] = mb[k];
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Stream staging → DRAM: consecutive `i` share a bin run ⇒ consecutive dst.
    uint total = lbase[255] + atomic_load_explicit(&lcount[255], memory_order_relaxed);
    for (uint i = tid; i < total; i += TG) {
        uint b = s_bin[i];
        uint dst = run_start[b] + (i - lbase[b]);
        keys_out[base + dst] = s_keys[i];
        if (has_payload != 0u) vals_out[base + dst] = s_vals[i];
    }
}
