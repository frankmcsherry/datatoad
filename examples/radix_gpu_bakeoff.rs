//! GPU bake-off: CPU contig-LSB vs our runtime-compiled Metal GPU-LSB vs the new
//! GPU-MSD (one partition pass by the top live byte, then per-bucket inner finish).
//! All three sort the 12-byte `u32_sort` shape by the 8-byte key prefix.
//!
//! Run: cargo run --release --features metal --example radix_gpu_bakeoff

use datatoad::facts::radix_sort::lsb_range;
use datatoad::facts::radix_sort_metal::MetalRadixSorter;
use std::time::Instant;

fn lcg(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed.wrapping_mul(2) + 1;
    move || { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); s >> 33 }
}

/// Low-entropy datatoad-like keys: small group/value domains → leading dead bytes,
/// short distinguishing prefixes (the case MSD is meant to win).
fn rows(n: usize, groups: u64, seed: u64) -> Vec<[u8; 12]> {
    let mut next = lcg(seed);
    (0..n).map(|i| {
        let mut r = [0u8; 12];
        r[0..4].copy_from_slice(&((next() % groups) as u32).to_be_bytes());
        r[4..8].copy_from_slice(&((next() % groups) as u32).to_be_bytes());
        r[8..12].copy_from_slice(&(i as u32).to_be_bytes());
        r
    }).collect()
}

fn min_ns(reps: usize, mut f: impl FnMut()) -> u128 {
    let mut best = u128::MAX;
    for _ in 0..reps { let t = Instant::now(); f(); best = best.min(t.elapsed().as_nanos()); }
    best
}

fn main() {
    let sorter = MetalRadixSorter::new().expect("no Metal device");
    let reps = 5;
    let sizes = [16_000usize, 256_000, 1_000_000, 4_000_000, 16_000_000];

    for (label, fanout) in [("dense (groups=n/8)", 8u64), ("sparse (groups=n)", 1)] {
        println!("\n#### {label} ####");
        println!("{:>10} {:>8} {:>8} {:>8} {:>9}  {:>8} {:>8}",
            "n", "cpu", "gpu-lsb", "msd-v3", "msd-swwc", "v3_sp", "swwc_sp");
        for &n in &sizes {
            let groups = (n as u64 / fanout).max(2);
            let base = rows(n, groups, 0xC0FFEE ^ n as u64 ^ fanout);

            let cpu = min_ns(reps, || { let mut d = base.clone(); lsb_range(&mut d[..], 0, 8); std::hint::black_box(&d); });

            // warm up each GPU path once (shader/pipeline + buffer alloc), then time.
            { let mut d = base.clone(); sorter.sort_u64_be(&mut d); }
            let glsb = min_ns(reps, || { let mut d = base.clone(); sorter.sort_u64_be(&mut d); std::hint::black_box(&d); });
            { let mut d = base.clone(); sorter.sort_u64_be_msd_v3(&mut d); }
            let gv3 = min_ns(reps, || { let mut d = base.clone(); sorter.sort_u64_be_msd_v3(&mut d); std::hint::black_box(&d); });
            { let mut d = base.clone(); sorter.sort_u64_be_msd_swwc(&mut d); }
            let gsw = min_ns(reps, || { let mut d = base.clone(); sorter.sort_u64_be_msd_swwc(&mut d); std::hint::black_box(&d); });

            // correctness cross-check at this size (swwc vs CPU).
            let mut a = base.clone(); sorter.sort_u64_be_msd_swwc(&mut a);
            let mut b = base.clone(); lsb_range(&mut b[..], 0, 8);
            assert_eq!(a.iter().map(|r| &r[..8]).collect::<Vec<_>>(),
                       b.iter().map(|r| &r[..8]).collect::<Vec<_>>(), "swwc key mismatch n={n}");

            let (c, l, v, w) = (cpu as f64 / n as f64, glsb as f64 / n as f64, gv3 as f64 / n as f64, gsw as f64 / n as f64);
            println!("{:>10} {:>8.2} {:>8.2} {:>8.2} {:>9.2}  {:>7.2}x {:>7.2}x", n, c, l, v, w, c / v, c / w);
        }
    }
    println!("\n(ns/elem, min of {reps} reps, incl. host pack/unpack. spdup = cpu / gpu. mini-01 / Apple M4.)");
}
