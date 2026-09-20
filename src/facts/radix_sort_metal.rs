//! GPU LSB radix sort via Metal, matching the semantics of
//! `crate::facts::radix_sort::lsb_range` for the 8-byte and 12-byte row layouts
//! produced by `u32_sort` / `u32_sort_last` in `trie.rs`.
//!
//! The row is treated as `key = u64::from_be_bytes(row[0..8])` plus an optional
//! 4-byte payload `row[8..12]`. Sorting is stable and ascending by `key`.

use metal::{
    Buffer, CommandQueue, CompileOptions, ComputePipelineState, Device, Library,
    MTLResourceOptions, MTLSize,
};
use std::cell::RefCell;
use std::ffi::c_void;

const TG: u64 = 256;
const K: u64 = 32;
const ITEMS_PER_TG: u64 = TG * K;

const METAL_SRC: &str = include_str!("radix_sort_metal.metal");

thread_local! {
    static SORTER: RefCell<Option<MetalRadixSorter>> = RefCell::new(MetalRadixSorter::new());
}

/// Sort with the thread-local Metal sorter. Returns true if the GPU sort ran,
/// false if Metal initialization failed and the caller should fall back.
pub fn try_sort_u64_be<const W: usize>(rows: &mut [[u8; W]]) -> bool {
    SORTER.with(|cell| {
        let s = cell.borrow();
        if let Some(sorter) = s.as_ref() {
            if std::env::var_os("DT_METAL_TRACE").is_some() {
                eprintln!("metal sort: n={} W={}", rows.len(), W);
            }
            sorter.sort_u64_be(rows);
            true
        } else {
            false
        }
    })
}

pub struct MetalRadixSorter {
    device: Device,
    queue: CommandQueue,
    detect_pipe: ComputePipelineState,
    hist_pipe: ComputePipelineState,
    scan_cols_pipe: ComputePipelineState,
    scan_totals_pipe: ComputePipelineState,
    scatter_pipe: ComputePipelineState,
    inner_fused_pipe: ComputePipelineState,
    scatter_swwc_pipe: ComputePipelineState,
    scratch: RefCell<Scratch>,
}

#[derive(Default)]
struct Scratch {
    keys_a: Option<Buffer>,
    keys_b: Option<Buffer>,
    vals_a: Option<Buffer>,
    vals_b: Option<Buffer>,
    tg_hist: Option<Buffer>,
    totals: Option<Buffer>,
    bin_base: Option<Buffer>,
    live_bytes: Option<Buffer>,  // 8 uchars
    swwc_cursor: Option<Buffer>, // 256 u32, per-bin output cursor for scatter_swwc
    capacity: usize,   // num items the (a/b) buffers can hold
    hist_caps: usize,  // num tgs the tg_hist buffer can hold
}

impl MetalRadixSorter {
    pub fn new() -> Option<Self> {
        let device = Device::system_default()?;
        let queue = device.new_command_queue();
        let library: Library = device
            .new_library_with_source(METAL_SRC, &CompileOptions::new())
            .ok()?;
        let f = |name: &str| -> Option<ComputePipelineState> {
            let func = library.get_function(name, None).ok()?;
            device.new_compute_pipeline_state_with_function(&func).ok()
        };
        Some(Self {
            detect_pipe: f("detect_live_bytes")?,
            hist_pipe: f("hist")?,
            scan_cols_pipe: f("scan_columns")?,
            scan_totals_pipe: f("scan_totals")?,
            scatter_pipe: f("scatter")?,
            inner_fused_pipe: f("inner_fused")?,
            scatter_swwc_pipe: f("scatter_swwc")?,
            device,
            queue,
            scratch: RefCell::new(Scratch::default()),
        })
    }

    fn ensure_scratch(&self, n: usize, num_tgs: usize) {
        let opts = MTLResourceOptions::StorageModeShared;
        let mut s = self.scratch.borrow_mut();
        if s.capacity < n {
            let key_bytes = (n.max(1) * 8) as u64;
            let val_bytes = (n.max(1) * 4) as u64;
            s.keys_a = Some(self.device.new_buffer(key_bytes, opts));
            s.keys_b = Some(self.device.new_buffer(key_bytes, opts));
            s.vals_a = Some(self.device.new_buffer(val_bytes, opts));
            s.vals_b = Some(self.device.new_buffer(val_bytes, opts));
            s.capacity = n;
        }
        if s.hist_caps < num_tgs {
            let hist_bytes = (num_tgs.max(1) * 256 * 4) as u64;
            s.tg_hist = Some(self.device.new_buffer(hist_bytes, opts));
            s.hist_caps = num_tgs;
        }
        if s.totals.is_none() {
            s.totals = Some(self.device.new_buffer(256 * 4, opts));
            s.bin_base = Some(self.device.new_buffer(256 * 4, opts));
            s.live_bytes = Some(self.device.new_buffer(16 * 4, opts));
            s.swwc_cursor = Some(self.device.new_buffer(256 * 4, opts));
        }
    }

    /// Sort `rows` ascending by `u64::from_be_bytes(row[0..8])`. Stable.
    /// `W` must be 8 (key only) or 12 (key + 4-byte payload).
    pub fn sort_u64_be<const W: usize>(&self, rows: &mut [[u8; W]]) {
        assert!(W == 8 || W == 12, "only [u8;8] and [u8;12] supported");
        let n = rows.len();
        if n < 2 {
            return;
        }

        let num_tgs = ((n as u64) + ITEMS_PER_TG - 1) / ITEMS_PER_TG;
        self.ensure_scratch(n, num_tgs as usize);
        let s = self.scratch.borrow();
        let keys_a = s.keys_a.as_ref().unwrap();
        let keys_b = s.keys_b.as_ref().unwrap();
        let vals_a = s.vals_a.as_ref().unwrap();
        let vals_b = s.vals_b.as_ref().unwrap();
        let tg_hist = s.tg_hist.as_ref().unwrap();
        let totals = s.totals.as_ref().unwrap();
        let bin_base = s.bin_base.as_ref().unwrap();
        let live_bytes = s.live_bytes.as_ref().unwrap();

        let has_payload: u32 = if W == 12 { 1 } else { 0 };

        // Pack rows into the (a) buffers as BE u64 keys + u32 payloads.
        unsafe {
            let keys_ptr = keys_a.contents() as *mut u64;
            let vals_ptr = vals_a.contents() as *mut u32;
            for (i, row) in rows.iter().enumerate() {
                let mut k = [0u8; 8];
                k.copy_from_slice(&row[..8]);
                *keys_ptr.add(i) = u64::from_be_bytes(k);
                if W == 12 {
                    let mut p = [0u8; 4];
                    p.copy_from_slice(&row[8..12]);
                    *vals_ptr.add(i) = u32::from_be_bytes(p);
                }
            }
        }

        let n_u32 = n as u32;
        let num_tgs_u32 = num_tgs as u32;

        // ---- Detection pass: which of the 8 key bytes have >1 distinct value? ----
        // Skipping a constant-byte pass saves ~12% of total bandwidth per byte skipped.
        const DETECT_TGS: u64 = 64;
        unsafe {
            // Initialize 16 interleaved uints: [AND_b0=0xFF.., OR_b0=0, AND_b1=..., OR_b1=0, ...].
            let p = live_bytes.contents() as *mut u32;
            for b in 0..8 {
                *p.add(b * 2 + 0) = 0xFFFFFFFF;
                *p.add(b * 2 + 1) = 0;
            }
        }
        {
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.detect_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(live_bytes), 0);
            enc.set_bytes(2, 4, &n_u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: DETECT_TGS, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 },
            );
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }

        // Read AND/OR pairs and compute live mask: byte b is live iff AND_b != OR_b (low 8 bits).
        let live_indices: Vec<u32> = unsafe {
            let p = live_bytes.contents() as *const u32;
            (0u32..8)
                .filter(|b| {
                    let a = (*p.add(*b as usize * 2 + 0)) & 0xff;
                    let o = (*p.add(*b as usize * 2 + 1)) & 0xff;
                    a != o
                })
                .collect()
        };

        // If no bytes are live, the input is already sorted (all keys identical) — nothing to do.
        if live_indices.is_empty() {
            return;
        }

        // ---- Main command buffer: only the live passes, chained. ----
        let cb = self.queue.new_command_buffer();
        for (pass, &byte_idx) in live_indices.iter().enumerate() {
            // LSD order: process LSB (byte index 7 in BE = lowest in u64) first.
            // live_indices is in ascending byte-index order (0..8), which IS LSD order
            // for our u64 encoding (byte 0 = LSB).
            let shift = (byte_idx * 8) as u32;
            // Source / dest swap each (live) pass. Pass 0 reads `a` writes `b`.
            let (k_src, k_dst, v_src, v_dst) = if pass % 2 == 0 {
                (keys_a, keys_b, vals_a, vals_b)
            } else {
                (keys_b, keys_a, vals_b, vals_a)
            };

            // ---- hist ----
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.hist_pipe);
            enc.set_buffer(0, Some(k_src), 0);
            enc.set_buffer(1, Some(tg_hist), 0);
            enc.set_bytes(2, 4, &n_u32 as *const u32 as *const c_void);
            enc.set_bytes(3, 4, &shift as *const u32 as *const c_void);
            enc.set_bytes(4, 4, &0u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: num_tgs, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 },
            );
            enc.end_encoding();

            // ---- scan_columns ----
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.scan_cols_pipe);
            enc.set_buffer(0, Some(tg_hist), 0);
            enc.set_buffer(1, Some(totals), 0);
            enc.set_bytes(2, 4, &num_tgs_u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: 256, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 },
            );
            enc.end_encoding();

            // ---- scan_totals ----
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.scan_totals_pipe);
            enc.set_buffer(0, Some(totals), 0);
            enc.set_buffer(1, Some(bin_base), 0);
            enc.dispatch_thread_groups(
                MTLSize { width: 1, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 },
            );
            enc.end_encoding();

            // ---- scatter ----
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.scatter_pipe);
            enc.set_buffer(0, Some(k_src), 0);
            enc.set_buffer(1, Some(v_src), 0);
            enc.set_buffer(2, Some(k_dst), 0);
            enc.set_buffer(3, Some(v_dst), 0);
            enc.set_buffer(4, Some(tg_hist), 0);
            enc.set_buffer(5, Some(bin_base), 0);
            enc.set_bytes(6, 4, &n_u32 as *const u32 as *const c_void);
            enc.set_bytes(7, 4, &shift as *const u32 as *const c_void);
            enc.set_bytes(8, 4, &has_payload as *const u32 as *const c_void);
            enc.set_bytes(9, 4, &0u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: num_tgs, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 },
            );
            enc.end_encoding();
        }
        cb.commit();
        cb.wait_until_completed();

        // After N passes starting in `a`, even N ends in `a` and odd N ends in `b`.
        let (final_keys, final_vals) = if live_indices.len() % 2 == 0 {
            (keys_a, vals_a)
        } else {
            (keys_b, vals_b)
        };
        unsafe {
            let k_ptr = final_keys.contents() as *const u64;
            let v_ptr = final_vals.contents() as *const u32;
            for (i, row) in rows.iter_mut().enumerate() {
                let key_be = (*k_ptr.add(i)).to_be_bytes();
                row[..8].copy_from_slice(&key_be);
                if W == 12 {
                    let val_be = (*v_ptr.add(i)).to_be_bytes();
                    row[8..12].copy_from_slice(&val_be);
                }
            }
        }
    }

    /// Emit one radix pass (hist → scan_columns → scan_totals → scatter) over the
    /// sub-range `[base, base+count)` at `shift`, reading `k_src/v_src` and writing
    /// `k_dst/v_dst`, into the given command buffer. `tg_hist/totals/bin_base` are
    /// shared scratch; because compute encoders serialize within a command buffer,
    /// passes that reuse this scratch run correctly back-to-back.
    #[allow(clippy::too_many_arguments)]
    fn emit_pass(
        &self,
        cb: &metal::CommandBufferRef,
        k_src: &Buffer, v_src: &Buffer, k_dst: &Buffer, v_dst: &Buffer,
        tg_hist: &Buffer, totals: &Buffer, bin_base: &Buffer,
        base: u32, count: u32, num_tgs: u32, shift: u32, has_payload: u32,
    ) {
        let tgs = MTLSize { width: num_tgs as u64, height: 1, depth: 1 };
        let threads = MTLSize { width: TG, height: 1, depth: 1 };

        let enc = cb.new_compute_command_encoder();
        enc.set_compute_pipeline_state(&self.hist_pipe);
        enc.set_buffer(0, Some(k_src), 0);
        enc.set_buffer(1, Some(tg_hist), 0);
        enc.set_bytes(2, 4, &count as *const u32 as *const c_void);
        enc.set_bytes(3, 4, &shift as *const u32 as *const c_void);
        enc.set_bytes(4, 4, &base as *const u32 as *const c_void);
        enc.dispatch_thread_groups(tgs, threads);
        enc.end_encoding();

        let enc = cb.new_compute_command_encoder();
        enc.set_compute_pipeline_state(&self.scan_cols_pipe);
        enc.set_buffer(0, Some(tg_hist), 0);
        enc.set_buffer(1, Some(totals), 0);
        enc.set_bytes(2, 4, &num_tgs as *const u32 as *const c_void);
        enc.dispatch_thread_groups(
            MTLSize { width: 256, height: 1, depth: 1 }, threads);
        enc.end_encoding();

        let enc = cb.new_compute_command_encoder();
        enc.set_compute_pipeline_state(&self.scan_totals_pipe);
        enc.set_buffer(0, Some(totals), 0);
        enc.set_buffer(1, Some(bin_base), 0);
        enc.dispatch_thread_groups(
            MTLSize { width: 1, height: 1, depth: 1 }, threads);
        enc.end_encoding();

        let enc = cb.new_compute_command_encoder();
        enc.set_compute_pipeline_state(&self.scatter_pipe);
        enc.set_buffer(0, Some(k_src), 0);
        enc.set_buffer(1, Some(v_src), 0);
        enc.set_buffer(2, Some(k_dst), 0);
        enc.set_buffer(3, Some(v_dst), 0);
        enc.set_buffer(4, Some(tg_hist), 0);
        enc.set_buffer(5, Some(bin_base), 0);
        enc.set_bytes(6, 4, &count as *const u32 as *const c_void);
        enc.set_bytes(7, 4, &shift as *const u32 as *const c_void);
        enc.set_bytes(8, 4, &has_payload as *const u32 as *const c_void);
        enc.set_bytes(9, 4, &base as *const u32 as *const c_void);
        enc.dispatch_thread_groups(tgs, threads);
        enc.end_encoding();
    }

    /// MSD variant: one GPU pass partitions by the most-significant *live* byte into
    /// 256 contiguous, key-ordered buckets; then each bucket is finished by its
    /// remaining lower live bytes (LSD order), addressed to the bucket's sub-range —
    /// "narrow once, then finish each bucket where it is cache-resident." Produces
    /// the same key order as `sort_u64_be`.
    ///
    /// v1: the inner finish reuses the global parallel kernels per bucket via the
    /// `base` offset, so the bulk runs on the optimized scatter; the cost is one
    /// command-encoder set per (bucket × lower byte). Single-dispatch segmented
    /// inner passes are the next step.
    pub fn sort_u64_be_msd<const W: usize>(&self, rows: &mut [[u8; W]]) {
        assert!(W == 8 || W == 12, "only [u8;8] and [u8;12] supported");
        let n = rows.len();
        if n < 2 { return; }

        let num_tgs = ((n as u64) + ITEMS_PER_TG - 1) / ITEMS_PER_TG;
        self.ensure_scratch(n, num_tgs as usize);
        let s = self.scratch.borrow();
        let keys_a = s.keys_a.as_ref().unwrap();
        let keys_b = s.keys_b.as_ref().unwrap();
        let vals_a = s.vals_a.as_ref().unwrap();
        let vals_b = s.vals_b.as_ref().unwrap();
        let tg_hist = s.tg_hist.as_ref().unwrap();
        let totals = s.totals.as_ref().unwrap();
        let bin_base = s.bin_base.as_ref().unwrap();
        let live_bytes = s.live_bytes.as_ref().unwrap();

        let has_payload: u32 = if W == 12 { 1 } else { 0 };

        // Pack rows into the (a) buffers as BE u64 keys + u32 payloads.
        unsafe {
            let keys_ptr = keys_a.contents() as *mut u64;
            let vals_ptr = vals_a.contents() as *mut u32;
            for (i, row) in rows.iter().enumerate() {
                let mut k = [0u8; 8];
                k.copy_from_slice(&row[..8]);
                *keys_ptr.add(i) = u64::from_be_bytes(k);
                if W == 12 {
                    let mut p = [0u8; 4];
                    p.copy_from_slice(&row[8..12]);
                    *vals_ptr.add(i) = u32::from_be_bytes(p);
                }
            }
        }

        let n_u32 = n as u32;

        // ---- Detect which key bytes are live (same as the LSB path). ----
        const DETECT_TGS: u64 = 64;
        unsafe {
            let p = live_bytes.contents() as *mut u32;
            for b in 0..8 { *p.add(b * 2) = 0xFFFFFFFF; *p.add(b * 2 + 1) = 0; }
        }
        {
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.detect_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(live_bytes), 0);
            enc.set_bytes(2, 4, &n_u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: DETECT_TGS, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 });
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }
        let live_indices: Vec<u32> = unsafe {
            let p = live_bytes.contents() as *const u32;
            (0u32..8).filter(|b| {
                let a = (*p.add(*b as usize * 2)) & 0xff;
                let o = (*p.add(*b as usize * 2 + 1)) & 0xff;
                a != o
            }).collect()
        };
        if live_indices.is_empty() { return; }

        // Most-significant live byte partitions first; the rest finish each bucket.
        let top = *live_indices.last().unwrap();
        let lower: Vec<u32> = live_indices[..live_indices.len() - 1].to_vec(); // ascending = LSD order

        // ---- Partition pass by the top byte: a -> b. ----
        {
            let cb = self.queue.new_command_buffer();
            self.emit_pass(cb, keys_a, vals_a, keys_b, vals_b, tg_hist, totals, bin_base,
                0, n_u32, num_tgs as u32, top * 8, has_payload);
            cb.commit();
            cb.wait_until_completed();
        }
        // Bucket offsets/counts for the top byte (data now lives in `b`).
        let (offsets, counts): ([u32; 256], [u32; 256]) = unsafe {
            let bb = bin_base.contents() as *const u32;
            let tt = totals.contents() as *const u32;
            let mut offs = [0u32; 256];
            let mut cnts = [0u32; 256];
            for i in 0..256 { offs[i] = *bb.add(i); cnts[i] = *tt.add(i); }
            (offs, cnts)
        };

        // ---- Inner: finish every bucket by the lower live bytes (LSD order). ----
        // All non-empty buckets take the same number of passes, so the whole array
        // ping-pongs uniformly; pass index continues from the partition (pass 0).
        if !lower.is_empty() {
            let cb = self.queue.new_command_buffer();
            for (j, &byte) in lower.iter().enumerate() {
                let pass = 1 + j;
                let (k_src, v_src, k_dst, v_dst) = if pass % 2 == 0 {
                    (keys_a, vals_a, keys_b, vals_b)
                } else {
                    (keys_b, vals_b, keys_a, vals_a)
                };
                for bin in 0..256 {
                    let cnt = counts[bin];
                    if cnt == 0 { continue; }
                    let btgs = ((cnt as u64) + ITEMS_PER_TG - 1) / ITEMS_PER_TG;
                    self.emit_pass(cb, k_src, v_src, k_dst, v_dst, tg_hist, totals, bin_base,
                        offsets[bin], cnt, btgs as u32, byte * 8, has_payload);
                }
            }
            cb.commit();
            cb.wait_until_completed();
        }

        // total passes = partition (1) + one per lower live byte. Even → ends in `a`.
        let total_passes = 1 + lower.len();
        let (final_keys, final_vals) = if total_passes % 2 == 0 {
            (keys_a, vals_a)
        } else {
            (keys_b, vals_b)
        };
        unsafe {
            let k_ptr = final_keys.contents() as *const u64;
            let v_ptr = final_vals.contents() as *const u32;
            for (i, row) in rows.iter_mut().enumerate() {
                let key_be = (*k_ptr.add(i)).to_be_bytes();
                row[..8].copy_from_slice(&key_be);
                if W == 12 {
                    let val_be = (*v_ptr.add(i)).to_be_bytes();
                    row[8..12].copy_from_slice(&val_be);
                }
            }
        }
    }

    /// MSD with a fused inner finish (v2): one GPU pass partitions by the top live
    /// byte, then a *single* `inner_fused` dispatch assigns one threadgroup per
    /// bucket and sorts each bucket by all its lower live bytes while it stays
    /// resident in the SLC — one launch instead of v1's per-(bucket×byte) storm.
    /// Same key order as `sort_u64_be`.
    pub fn sort_u64_be_msd_fused<const W: usize>(&self, rows: &mut [[u8; W]]) {
        assert!(W == 8 || W == 12, "only [u8;8] and [u8;12] supported");
        let n = rows.len();
        if n < 2 { return; }

        let num_tgs = ((n as u64) + ITEMS_PER_TG - 1) / ITEMS_PER_TG;
        self.ensure_scratch(n, num_tgs as usize);
        let s = self.scratch.borrow();
        let keys_a = s.keys_a.as_ref().unwrap();
        let keys_b = s.keys_b.as_ref().unwrap();
        let vals_a = s.vals_a.as_ref().unwrap();
        let vals_b = s.vals_b.as_ref().unwrap();
        let tg_hist = s.tg_hist.as_ref().unwrap();
        let totals = s.totals.as_ref().unwrap();
        let bin_base = s.bin_base.as_ref().unwrap();
        let live_bytes = s.live_bytes.as_ref().unwrap();

        let has_payload: u32 = if W == 12 { 1 } else { 0 };

        unsafe {
            let keys_ptr = keys_a.contents() as *mut u64;
            let vals_ptr = vals_a.contents() as *mut u32;
            for (i, row) in rows.iter().enumerate() {
                let mut k = [0u8; 8];
                k.copy_from_slice(&row[..8]);
                *keys_ptr.add(i) = u64::from_be_bytes(k);
                if W == 12 {
                    let mut p = [0u8; 4];
                    p.copy_from_slice(&row[8..12]);
                    *vals_ptr.add(i) = u32::from_be_bytes(p);
                }
            }
        }

        let n_u32 = n as u32;

        // ---- Detect live bytes. ----
        const DETECT_TGS: u64 = 64;
        unsafe {
            let p = live_bytes.contents() as *mut u32;
            for b in 0..8 { *p.add(b * 2) = 0xFFFFFFFF; *p.add(b * 2 + 1) = 0; }
        }
        {
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.detect_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(live_bytes), 0);
            enc.set_bytes(2, 4, &n_u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: DETECT_TGS, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 });
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }
        let live_indices: Vec<u32> = unsafe {
            let p = live_bytes.contents() as *const u32;
            (0u32..8).filter(|b| {
                let a = (*p.add(*b as usize * 2)) & 0xff;
                let o = (*p.add(*b as usize * 2 + 1)) & 0xff;
                a != o
            }).collect()
        };
        if live_indices.is_empty() { return; }

        let top = *live_indices.last().unwrap();
        let lower: Vec<u32> = live_indices[..live_indices.len() - 1].to_vec();
        let n_lower = lower.len() as u32;

        // ---- Partition by the top byte: a -> b (offsets in bin_base, counts in totals). ----
        {
            let cb = self.queue.new_command_buffer();
            self.emit_pass(cb, keys_a, vals_a, keys_b, vals_b, tg_hist, totals, bin_base,
                0, n_u32, num_tgs as u32, top * 8, has_payload);
            cb.commit();
            cb.wait_until_completed();
        }

        // Lower-byte shifts (LSD order) into a small device buffer (reuse live_bytes).
        unsafe {
            let p = live_bytes.contents() as *mut u32;
            for (j, &byte) in lower.iter().enumerate() { *p.add(j) = byte * 8; }
        }

        // ---- Fused inner: one dispatch, one TG per bucket, finishes lower bytes. ----
        {
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.inner_fused_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(keys_b), 0);
            enc.set_buffer(2, Some(vals_a), 0);
            enc.set_buffer(3, Some(vals_b), 0);
            enc.set_buffer(4, Some(bin_base), 0);  // bucket offsets
            enc.set_buffer(5, Some(totals), 0);    // bucket counts
            enc.set_buffer(6, Some(live_bytes), 0); // lower shifts
            enc.set_bytes(7, 4, &n_lower as *const u32 as *const c_void);
            enc.set_bytes(8, 4, &has_payload as *const u32 as *const c_void);
            enc.set_bytes(9, 4, &u32::MAX as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: 256, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 });
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }

        // inner_fused always leaves each bucket's result in the A buffer.
        unsafe {
            let k_ptr = keys_a.contents() as *const u64;
            let v_ptr = vals_a.contents() as *const u32;
            for (i, row) in rows.iter_mut().enumerate() {
                let key_be = (*k_ptr.add(i)).to_be_bytes();
                row[..8].copy_from_slice(&key_be);
                if W == 12 {
                    let val_be = (*v_ptr.add(i)).to_be_bytes();
                    row[8..12].copy_from_slice(&val_be);
                }
            }
        }
    }

    /// MSD v3: size-adaptive inner finish. After the top-byte partition, *small*
    /// buckets are finished by the one-TG fused kernel, while the few *big* buckets
    /// (which would starve the GPU at one TG each — e.g. low-entropy keys whose top
    /// byte yields only a handful of buckets) are finished by the full-width global
    /// kernels over their sub-range. Same key order as `sort_u64_be`.
    pub fn sort_u64_be_msd_v3<const W: usize>(&self, rows: &mut [[u8; W]]) {
        assert!(W == 8 || W == 12, "only [u8;8] and [u8;12] supported");
        let n = rows.len();
        if n < 2 { return; }
        // Buckets above this go to the full-width path; below, to the fused path.
        const BIG: u32 = 1 << 17;

        let num_tgs = ((n as u64) + ITEMS_PER_TG - 1) / ITEMS_PER_TG;
        self.ensure_scratch(n, num_tgs as usize);
        let s = self.scratch.borrow();
        let keys_a = s.keys_a.as_ref().unwrap();
        let keys_b = s.keys_b.as_ref().unwrap();
        let vals_a = s.vals_a.as_ref().unwrap();
        let vals_b = s.vals_b.as_ref().unwrap();
        let tg_hist = s.tg_hist.as_ref().unwrap();
        let totals = s.totals.as_ref().unwrap();
        let bin_base = s.bin_base.as_ref().unwrap();
        let live_bytes = s.live_bytes.as_ref().unwrap();

        let has_payload: u32 = if W == 12 { 1 } else { 0 };

        unsafe {
            let keys_ptr = keys_a.contents() as *mut u64;
            let vals_ptr = vals_a.contents() as *mut u32;
            for (i, row) in rows.iter().enumerate() {
                let mut k = [0u8; 8];
                k.copy_from_slice(&row[..8]);
                *keys_ptr.add(i) = u64::from_be_bytes(k);
                if W == 12 {
                    let mut p = [0u8; 4];
                    p.copy_from_slice(&row[8..12]);
                    *vals_ptr.add(i) = u32::from_be_bytes(p);
                }
            }
        }

        let n_u32 = n as u32;
        const DETECT_TGS: u64 = 64;
        unsafe {
            let p = live_bytes.contents() as *mut u32;
            for b in 0..8 { *p.add(b * 2) = 0xFFFFFFFF; *p.add(b * 2 + 1) = 0; }
        }
        {
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.detect_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(live_bytes), 0);
            enc.set_bytes(2, 4, &n_u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: DETECT_TGS, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 });
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }
        let live_indices: Vec<u32> = unsafe {
            let p = live_bytes.contents() as *const u32;
            (0u32..8).filter(|b| {
                let a = (*p.add(*b as usize * 2)) & 0xff;
                let o = (*p.add(*b as usize * 2 + 1)) & 0xff;
                a != o
            }).collect()
        };
        if live_indices.is_empty() { return; }

        let top = *live_indices.last().unwrap();
        let lower: Vec<u32> = live_indices[..live_indices.len() - 1].to_vec();
        let n_lower = lower.len() as u32;

        // Partition by the top byte: a -> b.
        {
            let cb = self.queue.new_command_buffer();
            self.emit_pass(cb, keys_a, vals_a, keys_b, vals_b, tg_hist, totals, bin_base,
                0, n_u32, num_tgs as u32, top * 8, has_payload);
            cb.commit();
            cb.wait_until_completed();
        }
        let (offsets, counts): ([u32; 256], [u32; 256]) = unsafe {
            let bb = bin_base.contents() as *const u32;
            let tt = totals.contents() as *const u32;
            let mut offs = [0u32; 256];
            let mut cnts = [0u32; 256];
            for i in 0..256 { offs[i] = *bb.add(i); cnts[i] = *tt.add(i); }
            (offs, cnts)
        };

        // Fused finish of the *small* buckets (reads bin_base/totals; must run before
        // the big-bucket path clobbers that scratch).
        unsafe {
            let p = live_bytes.contents() as *mut u32;
            for (j, &byte) in lower.iter().enumerate() { *p.add(j) = byte * 8; }
        }
        {
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.inner_fused_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(keys_b), 0);
            enc.set_buffer(2, Some(vals_a), 0);
            enc.set_buffer(3, Some(vals_b), 0);
            enc.set_buffer(4, Some(bin_base), 0);
            enc.set_buffer(5, Some(totals), 0);
            enc.set_buffer(6, Some(live_bytes), 0);
            enc.set_bytes(7, 4, &n_lower as *const u32 as *const c_void);
            enc.set_bytes(8, 4, &has_payload as *const u32 as *const c_void);
            enc.set_bytes(9, 4, &BIG as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: 256, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 });
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }

        // Full-width finish of the *big* buckets over their lower bytes (LSD order).
        let bigs: Vec<usize> = (0..256).filter(|&b| counts[b] > BIG).collect();
        if !bigs.is_empty() {
            if n_lower > 0 {
                let cb = self.queue.new_command_buffer();
                for (p, &byte) in lower.iter().enumerate() {
                    // pass 0 reads B (partition output) -> A, then alternate.
                    let (k_src, v_src, k_dst, v_dst) = if p % 2 == 0 {
                        (keys_b, vals_b, keys_a, vals_a)
                    } else {
                        (keys_a, vals_a, keys_b, vals_b)
                    };
                    for &bin in &bigs {
                        let cnt = counts[bin];
                        let btgs = ((cnt as u64) + ITEMS_PER_TG - 1) / ITEMS_PER_TG;
                        self.emit_pass(cb, k_src, v_src, k_dst, v_dst, tg_hist, totals, bin_base,
                            offsets[bin], cnt, btgs as u32, byte * 8, has_payload);
                    }
                }
                cb.commit();
                cb.wait_until_completed();
            }
            // After n_lower passes from B, big buckets are in A iff n_lower is odd.
            // Otherwise (including n_lower == 0) copy the big ranges B -> A.
            if n_lower % 2 == 0 {
                unsafe {
                    let ka = keys_a.contents() as *mut u64;
                    let kb = keys_b.contents() as *const u64;
                    let va = vals_a.contents() as *mut u32;
                    let vb = vals_b.contents() as *const u32;
                    for &bin in &bigs {
                        let base = offsets[bin] as usize;
                        let cnt = counts[bin] as usize;
                        for i in base..base + cnt {
                            *ka.add(i) = *kb.add(i);
                            if W == 12 { *va.add(i) = *vb.add(i); }
                        }
                    }
                }
            }
        }

        // Everything is now in the A buffer.
        unsafe {
            let k_ptr = keys_a.contents() as *const u64;
            let v_ptr = vals_a.contents() as *const u32;
            for (i, row) in rows.iter_mut().enumerate() {
                let key_be = (*k_ptr.add(i)).to_be_bytes();
                row[..8].copy_from_slice(&key_be);
                if W == 12 {
                    let val_be = (*v_ptr.add(i)).to_be_bytes();
                    row[8..12].copy_from_slice(&val_be);
                }
            }
        }
    }

    /// Like `sort_u64_be_msd_v3`, but the partition scatter uses the software
    /// write-combining kernel (`scatter_swwc`) to coalesce the one full-array DRAM
    /// scatter. Unstable in the partition (inner_fused re-sorts each bucket), so the
    /// key order still matches `sort_u64_be`.
    pub fn sort_u64_be_msd_swwc<const W: usize>(&self, rows: &mut [[u8; W]]) {
        assert!(W == 8 || W == 12, "only [u8;8] and [u8;12] supported");
        let n = rows.len();
        if n < 2 { return; }
        const BIG: u32 = 1 << 17;
        const ITEMS_S: u64 = 256 * 6; // must match K_S * TG in the shader

        let num_tgs = ((n as u64) + ITEMS_PER_TG - 1) / ITEMS_PER_TG;
        self.ensure_scratch(n, num_tgs as usize);
        let s = self.scratch.borrow();
        let keys_a = s.keys_a.as_ref().unwrap();
        let keys_b = s.keys_b.as_ref().unwrap();
        let vals_a = s.vals_a.as_ref().unwrap();
        let vals_b = s.vals_b.as_ref().unwrap();
        let tg_hist = s.tg_hist.as_ref().unwrap();
        let totals = s.totals.as_ref().unwrap();
        let bin_base = s.bin_base.as_ref().unwrap();
        let live_bytes = s.live_bytes.as_ref().unwrap();
        let cursor = s.swwc_cursor.as_ref().unwrap();

        let has_payload: u32 = if W == 12 { 1 } else { 0 };

        unsafe {
            let keys_ptr = keys_a.contents() as *mut u64;
            let vals_ptr = vals_a.contents() as *mut u32;
            for (i, row) in rows.iter().enumerate() {
                let mut k = [0u8; 8];
                k.copy_from_slice(&row[..8]);
                *keys_ptr.add(i) = u64::from_be_bytes(k);
                if W == 12 {
                    let mut p = [0u8; 4];
                    p.copy_from_slice(&row[8..12]);
                    *vals_ptr.add(i) = u32::from_be_bytes(p);
                }
            }
        }

        let n_u32 = n as u32;
        const DETECT_TGS: u64 = 64;
        unsafe {
            let p = live_bytes.contents() as *mut u32;
            for b in 0..8 { *p.add(b * 2) = 0xFFFFFFFF; *p.add(b * 2 + 1) = 0; }
        }
        {
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.detect_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(live_bytes), 0);
            enc.set_bytes(2, 4, &n_u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: DETECT_TGS, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 });
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }
        let live_indices: Vec<u32> = unsafe {
            let p = live_bytes.contents() as *const u32;
            (0u32..8).filter(|b| {
                let a = (*p.add(*b as usize * 2)) & 0xff;
                let o = (*p.add(*b as usize * 2 + 1)) & 0xff;
                a != o
            }).collect()
        };
        if live_indices.is_empty() { return; }

        let top = *live_indices.last().unwrap();
        let lower: Vec<u32> = live_indices[..live_indices.len() - 1].to_vec();
        let n_lower = lower.len() as u32;

        // ---- Partition by the top byte via SWWC. ----
        // (1) hist + scan_columns + scan_totals → totals, bin_base (no scatter yet).
        let shift = top * 8;
        {
            let cb = self.queue.new_command_buffer();
            let threads = MTLSize { width: TG, height: 1, depth: 1 };
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.hist_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(tg_hist), 0);
            enc.set_bytes(2, 4, &n_u32 as *const u32 as *const c_void);
            enc.set_bytes(3, 4, &shift as *const u32 as *const c_void);
            enc.set_bytes(4, 4, &0u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(MTLSize { width: num_tgs, height: 1, depth: 1 }, threads);
            enc.end_encoding();

            let nt = num_tgs as u32;
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.scan_cols_pipe);
            enc.set_buffer(0, Some(tg_hist), 0);
            enc.set_buffer(1, Some(totals), 0);
            enc.set_bytes(2, 4, &nt as *const u32 as *const c_void);
            enc.dispatch_thread_groups(MTLSize { width: 256, height: 1, depth: 1 }, threads);
            enc.end_encoding();

            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.scan_totals_pipe);
            enc.set_buffer(0, Some(totals), 0);
            enc.set_buffer(1, Some(bin_base), 0);
            enc.dispatch_thread_groups(MTLSize { width: 1, height: 1, depth: 1 }, threads);
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }
        let (offsets, counts): ([u32; 256], [u32; 256]) = unsafe {
            let bb = bin_base.contents() as *const u32;
            let tt = totals.contents() as *const u32;
            let mut offs = [0u32; 256];
            let mut cnts = [0u32; 256];
            for i in 0..256 { offs[i] = *bb.add(i); cnts[i] = *tt.add(i); }
            (offs, cnts)
        };
        // (2) init cursor = bin_base, then SWWC scatter A -> B.
        unsafe {
            std::ptr::copy_nonoverlapping(
                bin_base.contents() as *const u32, cursor.contents() as *mut u32, 256);
        }
        {
            let num_tgs_s = ((n as u64) + ITEMS_S - 1) / ITEMS_S;
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.scatter_swwc_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(vals_a), 0);
            enc.set_buffer(2, Some(keys_b), 0);
            enc.set_buffer(3, Some(vals_b), 0);
            enc.set_buffer(4, Some(cursor), 0);
            enc.set_bytes(5, 4, &n_u32 as *const u32 as *const c_void);
            enc.set_bytes(6, 4, &shift as *const u32 as *const c_void);
            enc.set_bytes(7, 4, &has_payload as *const u32 as *const c_void);
            enc.set_bytes(8, 4, &0u32 as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: num_tgs_s, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 });
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }

        // ---- Inner finish: identical to v3 (fused small + full-width big). ----
        unsafe {
            let p = live_bytes.contents() as *mut u32;
            for (j, &byte) in lower.iter().enumerate() { *p.add(j) = byte * 8; }
        }
        {
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_compute_pipeline_state(&self.inner_fused_pipe);
            enc.set_buffer(0, Some(keys_a), 0);
            enc.set_buffer(1, Some(keys_b), 0);
            enc.set_buffer(2, Some(vals_a), 0);
            enc.set_buffer(3, Some(vals_b), 0);
            enc.set_buffer(4, Some(bin_base), 0);
            enc.set_buffer(5, Some(totals), 0);
            enc.set_buffer(6, Some(live_bytes), 0);
            enc.set_bytes(7, 4, &n_lower as *const u32 as *const c_void);
            enc.set_bytes(8, 4, &has_payload as *const u32 as *const c_void);
            enc.set_bytes(9, 4, &BIG as *const u32 as *const c_void);
            enc.dispatch_thread_groups(
                MTLSize { width: 256, height: 1, depth: 1 },
                MTLSize { width: TG, height: 1, depth: 1 });
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
        }

        let bigs: Vec<usize> = (0..256).filter(|&b| counts[b] > BIG).collect();
        if !bigs.is_empty() {
            if n_lower > 0 {
                let cb = self.queue.new_command_buffer();
                for (p, &byte) in lower.iter().enumerate() {
                    let (k_src, v_src, k_dst, v_dst) = if p % 2 == 0 {
                        (keys_b, vals_b, keys_a, vals_a)
                    } else {
                        (keys_a, vals_a, keys_b, vals_b)
                    };
                    for &bin in &bigs {
                        let cnt = counts[bin];
                        let btgs = ((cnt as u64) + ITEMS_PER_TG - 1) / ITEMS_PER_TG;
                        self.emit_pass(cb, k_src, v_src, k_dst, v_dst, tg_hist, totals, bin_base,
                            offsets[bin], cnt, btgs as u32, byte * 8, has_payload);
                    }
                }
                cb.commit();
                cb.wait_until_completed();
            }
            if n_lower % 2 == 0 {
                unsafe {
                    let ka = keys_a.contents() as *mut u64;
                    let kb = keys_b.contents() as *const u64;
                    let va = vals_a.contents() as *mut u32;
                    let vb = vals_b.contents() as *const u32;
                    for &bin in &bigs {
                        let base = offsets[bin] as usize;
                        let cnt = counts[bin] as usize;
                        for i in base..base + cnt {
                            *ka.add(i) = *kb.add(i);
                            if W == 12 { *va.add(i) = *vb.add(i); }
                        }
                    }
                }
            }
        }

        unsafe {
            let k_ptr = keys_a.contents() as *const u64;
            let v_ptr = vals_a.contents() as *const u32;
            for (i, row) in rows.iter_mut().enumerate() {
                let key_be = (*k_ptr.add(i)).to_be_bytes();
                row[..8].copy_from_slice(&key_be);
                if W == 12 {
                    let val_be = (*v_ptr.add(i)).to_be_bytes();
                    row[8..12].copy_from_slice(&val_be);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cpu_sort_ref<const W: usize>(rows: &mut [[u8; W]]) {
        crate::facts::radix_sort::lsb_range(rows, 0, 8);
    }

    fn xorshift(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    fn random_rows<const W: usize>(n: usize, seed: u64) -> Vec<[u8; W]> {
        let mut s = seed | 1;
        (0..n)
            .map(|_| {
                let mut row = [0u8; W];
                for i in 0..W {
                    row[i] = (xorshift(&mut s) & 0xFF) as u8;
                }
                row
            })
            .collect()
    }

    #[test]
    fn matches_cpu_8byte() {
        let Some(sorter) = MetalRadixSorter::new() else {
            eprintln!("skipped: no Metal device");
            return;
        };
        for &n in &[1usize, 2, 255, 256, 257, 1023, 1024, 1025, 100_000] {
            let mut a = random_rows::<8>(n, 0xC0FFEE ^ (n as u64));
            let mut b = a.clone();
            sorter.sort_u64_be(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(a, b, "mismatch at n={n} (8-byte)");
        }
    }

    #[test]
    fn matches_cpu_12byte() {
        let Some(sorter) = MetalRadixSorter::new() else {
            eprintln!("skipped: no Metal device");
            return;
        };
        for &n in &[1usize, 2, 255, 256, 257, 1023, 1024, 1025, 100_000] {
            let mut a = random_rows::<12>(n, 0xBADC0DE ^ (n as u64));
            let mut b = a.clone();
            sorter.sort_u64_be(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(
                a.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                b.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                "key mismatch at n={n}"
            );
            let mut a_payloads: Vec<_> = a.iter().map(|r| (&r[..8], &r[8..])).collect();
            let mut b_payloads: Vec<_> = b.iter().map(|r| (&r[..8], &r[8..])).collect();
            a_payloads.sort();
            b_payloads.sort();
            assert_eq!(a_payloads, b_payloads, "payload mismatch at n={n}");
        }
    }

    /// Low-entropy, datatoad-like rows (small group/value domains → leading dead
    /// bytes, short distinguishing prefixes) — the case MSD is meant to exploit.
    fn grouped_rows<const W: usize>(n: usize, groups: u64, seed: u64) -> Vec<[u8; W]> {
        let mut s = seed | 1;
        (0..n).map(|_| {
            let mut row = [0u8; W];
            let g = (xorshift(&mut s) % groups) as u32;
            let v = (xorshift(&mut s) % groups) as u32;
            row[0..4].copy_from_slice(&g.to_be_bytes());
            row[4..8].copy_from_slice(&v.to_be_bytes());
            for i in 8..W { row[i] = (xorshift(&mut s) & 0xFF) as u8; }
            row
        }).collect()
    }

    #[test]
    fn msd_matches_cpu() {
        let Some(sorter) = MetalRadixSorter::new() else {
            eprintln!("skipped: no Metal device");
            return;
        };
        for &n in &[1usize, 2, 255, 256, 257, 1023, 1024, 1025, 9999, 100_000] {
            // 8-byte, fully random (all bytes live).
            let mut a = random_rows::<8>(n, 0x5EED ^ (n as u64));
            let mut b = a.clone();
            sorter.sort_u64_be_msd(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(a, b, "msd 8-byte random mismatch at n={n}");

            // 8-byte, low-entropy (leading dead bytes, short prefixes).
            let mut a = grouped_rows::<8>(n, (n as u64 / 8).max(2), 0x1234 ^ n as u64);
            let mut b = a.clone();
            sorter.sort_u64_be_msd(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(a, b, "msd 8-byte grouped mismatch at n={n}");

            // 12-byte: compare key order only (payload tie order is unconstrained).
            let mut a = grouped_rows::<12>(n, (n as u64 / 8).max(2), 0xABCD ^ n as u64);
            let mut b = a.clone();
            sorter.sort_u64_be_msd(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(
                a.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                b.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                "msd 12-byte key mismatch at n={n}"
            );
        }
    }

    #[test]
    fn msd_fused_matches_cpu() {
        let Some(sorter) = MetalRadixSorter::new() else {
            eprintln!("skipped: no Metal device");
            return;
        };
        for &n in &[1usize, 2, 255, 256, 257, 1023, 1024, 1025, 9999, 100_000] {
            // 8-byte random (all bytes live → exercises the full lower-byte chain).
            let mut a = random_rows::<8>(n, 0xF00D ^ (n as u64));
            let mut b = a.clone();
            sorter.sort_u64_be_msd_fused(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(a, b, "fused 8-byte random mismatch at n={n}");

            // 8-byte low-entropy.
            let mut a = grouped_rows::<8>(n, (n as u64 / 8).max(2), 0xBEEF ^ n as u64);
            let mut b = a.clone();
            sorter.sort_u64_be_msd_fused(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(a, b, "fused 8-byte grouped mismatch at n={n}");

            // 12-byte: key order only.
            let mut a = grouped_rows::<12>(n, (n as u64 / 8).max(2), 0x99AA ^ n as u64);
            let mut b = a.clone();
            sorter.sort_u64_be_msd_fused(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(
                a.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                b.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                "fused 12-byte key mismatch at n={n}"
            );
        }
    }

    #[test]
    fn msd_v3_matches_cpu() {
        let Some(sorter) = MetalRadixSorter::new() else {
            eprintln!("skipped: no Metal device");
            return;
        };
        // Sizes that straddle the BIG=131072 big-bucket threshold; the very low group
        // counts force a few huge buckets (the big-bucket path), higher ones exercise
        // the small/fused path — and the mix exercises both at once.
        for &n in &[1usize, 257, 1025, 200_000, 500_000] {
            for &groups in &[2u64, 4, 64, (n as u64 / 8).max(2)] {
                let mut a = grouped_rows::<12>(n, groups, 0x3333 ^ n as u64 ^ groups);
                let mut b = a.clone();
                sorter.sort_u64_be_msd_v3(&mut a);
                cpu_sort_ref(&mut b);
                assert_eq!(
                    a.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                    b.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                    "v3 key mismatch at n={n} groups={groups}"
                );
            }
            // also a fully-random 8-byte case.
            let mut a = random_rows::<8>(n, 0x7777 ^ n as u64);
            let mut b = a.clone();
            sorter.sort_u64_be_msd_v3(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(a, b, "v3 8-byte random mismatch at n={n}");
        }
    }

    #[test]
    fn msd_swwc_matches_cpu() {
        let Some(sorter) = MetalRadixSorter::new() else {
            eprintln!("skipped: no Metal device");
            return;
        };
        for &n in &[1usize, 257, 1025, 1537, 3072, 200_000, 500_000] {
            for &groups in &[2u64, 4, 64, (n as u64 / 8).max(2)] {
                let mut a = grouped_rows::<12>(n, groups, 0x55AA ^ n as u64 ^ groups);
                let mut b = a.clone();
                sorter.sort_u64_be_msd_swwc(&mut a);
                cpu_sort_ref(&mut b);
                assert_eq!(
                    a.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                    b.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                    "swwc key mismatch at n={n} groups={groups}"
                );
            }
            let mut a = random_rows::<8>(n, 0xAA55 ^ n as u64);
            let mut b = a.clone();
            sorter.sort_u64_be_msd_swwc(&mut a);
            cpu_sort_ref(&mut b);
            assert_eq!(a, b, "swwc 8-byte random mismatch at n={n}");
        }
    }
}
