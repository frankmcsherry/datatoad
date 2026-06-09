//! Microbenchmark: Metal radix sort vs CPU `lsb_range` over (u64 BE key + optional u32 payload).
//!
//! Run with: cargo run --release --features metal --example bench_sort

use datatoad::facts::radix_sort::lsb_range;
#[cfg(all(feature = "metal", target_os = "macos"))]
use datatoad::facts::radix_sort_metal::MetalRadixSorter;
use std::time::Instant;

fn xorshift(s: &mut u64) -> u64 {
    let mut x = *s;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *s = x;
    x
}

fn random_rows<const W: usize>(n: usize, seed: u64) -> Vec<[u8; W]> {
    let mut s = seed | 1;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let mut r = [0u8; W];
        for i in 0..W {
            r[i] = (xorshift(&mut s) & 0xFF) as u8;
        }
        v.push(r);
    }
    v
}

/// Mimics datatoad u32_sort input: key is `(group_be(4), value_be(4))`.
/// `group` is bounded by `max_group` (small group counts leave high bytes constant).
/// `value` bytes are random. Payload bytes (8..W) are random.
fn datatoadish_rows<const W: usize>(n: usize, max_group: u32, seed: u64) -> Vec<[u8; W]> {
    let mut s = seed | 1;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let mut r = [0u8; W];
        let g = (xorshift(&mut s) as u32) % max_group.max(1);
        r[0..4].copy_from_slice(&g.to_be_bytes());
        for i in 4..W {
            r[i] = (xorshift(&mut s) & 0xFF) as u8;
        }
        v.push(r);
    }
    v
}

fn bench_cpu<const W: usize>(rows: &[[u8; W]], iters: usize) -> f64 {
    let mut best = f64::INFINITY;
    for _ in 0..iters {
        let mut data = rows.to_vec();
        let t = Instant::now();
        lsb_range(&mut data, 0, 8);
        let dt = t.elapsed().as_secs_f64();
        if dt < best {
            best = dt;
        }
        std::hint::black_box(&data);
    }
    best
}

#[cfg(all(feature = "metal", target_os = "macos"))]
fn bench_gpu<const W: usize>(
    sorter: &MetalRadixSorter,
    rows: &[[u8; W]],
    iters: usize,
) -> f64 {
    let mut best = f64::INFINITY;
    for _ in 0..iters {
        let mut data = rows.to_vec();
        let t = Instant::now();
        sorter.sort_u64_be(&mut data);
        let dt = t.elapsed().as_secs_f64();
        if dt < best {
            best = dt;
        }
        std::hint::black_box(&data);
    }
    best
}

fn main() {
    #[cfg(all(feature = "metal", target_os = "macos"))]
    let sorter = MetalRadixSorter::new().expect("no Metal device");

    let sizes = [1_000_000usize, 5_000_000, 10_000_000];

    for (label, max_group) in &[("random (all 8 bytes live)", 0u32), ("max_group=2^16 (1 byte dead)", 1u32 << 16), ("max_group=2^8 (2 bytes dead)", 1u32 << 8)] {
        for &w in &[8usize, 12] {
            println!("\n=== {label}, row width {w} bytes ===");
            println!("{:>12}  {:>10}  {:>10}  {:>8}", "n", "cpu(ms)", "gpu(ms)", "speedup");
            for &n in &sizes {
                let iters = 3;
                let (cpu_ms, gpu_ms) = if w == 8 {
                    let rows = if *max_group == 0 {
                        random_rows::<8>(n, 0xC0FFEE ^ n as u64)
                    } else {
                        datatoadish_rows::<8>(n, *max_group, 0xC0FFEE ^ n as u64)
                    };
                    let cpu = bench_cpu::<8>(&rows, iters);
                    #[cfg(all(feature = "metal", target_os = "macos"))]
                    let gpu = {
                        let _ = bench_gpu::<8>(&sorter, &rows[..n.min(1024)], 1);
                        bench_gpu::<8>(&sorter, &rows, iters)
                    };
                    #[cfg(not(all(feature = "metal", target_os = "macos")))]
                    let gpu = f64::NAN;
                    (cpu, gpu)
                } else {
                    let rows = if *max_group == 0 {
                        random_rows::<12>(n, 0xBADC0DE ^ n as u64)
                    } else {
                        datatoadish_rows::<12>(n, *max_group, 0xBADC0DE ^ n as u64)
                    };
                    let cpu = bench_cpu::<12>(&rows, iters);
                    #[cfg(all(feature = "metal", target_os = "macos"))]
                    let gpu = {
                        let _ = bench_gpu::<12>(&sorter, &rows[..n.min(1024)], 1);
                        bench_gpu::<12>(&sorter, &rows, iters)
                    };
                    #[cfg(not(all(feature = "metal", target_os = "macos")))]
                    let gpu = f64::NAN;
                    (cpu, gpu)
                };
                println!(
                    "{:>12}  {:>10.3}  {:>10.3}  {:>7.2}x",
                    n, cpu_ms * 1e3, gpu_ms * 1e3, cpu_ms / gpu_ms
                );
            }
        }
    }
}
