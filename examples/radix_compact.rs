//! Dead-byte *compaction* vs dead-byte *skipping* on the CPU (the engine that wins
//! the bandwidth race). `lsb_range` skips constant key-byte planes but still moves the
//! full 12-byte row each pass; `lsb_compact` removes them, sorting a narrower
//! (live+4)-byte element, then expanding back. The win should scale with how many key
//! bytes are dead.
//!
//! Run: cargo run --release --example radix_compact

use datatoad::facts::radix_sort::{lsb_range, lsb_compact};
use std::time::Instant;

fn lcg(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed.wrapping_mul(2) + 1;
    move || { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); s >> 33 }
}

/// (group, value) over `groups` distinct keys; index = position. Smaller `groups`
/// ⇒ more leading constant (dead) bytes ⇒ a narrower compacted element.
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

fn live_key_bytes(rows: &[[u8; 12]]) -> usize {
    (0..8).filter(|&p| { let f = rows[0][p]; rows.iter().any(|r| r[p] != f) }).count()
}

fn main() {
    let reps = 7;
    let sizes = [256_000usize, 1_000_000, 4_000_000, 16_000_000];

    // groups controls dead-byte count: tiny→few live bytes, n→all 8 live.
    for &(label, fanout) in &[("dense  (groups=n/64)", 64u64), ("medium (groups=n/8)", 8), ("sparse (groups=n)", 1)] {
        println!("\n#### {label} ####");
        println!("{:>10} {:>6} {:>8} {:>8} {:>10} {:>8}", "n", "live", "skip", "compact", "stride", "speedup");
        for &n in &sizes {
            let groups = (n as u64 / fanout).max(2);
            let base = rows(n, groups, 0xC0FFEE ^ n as u64 ^ fanout);
            let live = live_key_bytes(&base);

            let skip = min_ns(reps, || { let mut d = base.clone(); lsb_range(&mut d[..], 0, 8); std::hint::black_box(&d); });
            let comp = min_ns(reps, || { let mut d = base.clone(); lsb_compact(&mut d); std::hint::black_box(&d); });

            // correctness: compact must match the stable skip sort exactly.
            let mut a = base.clone(); lsb_compact(&mut a);
            let mut b = base.clone(); lsb_range(&mut b[..], 0, 8);
            assert_eq!(a, b, "compact != lsb_range at n={n} groups={groups}");

            let (s, c) = (skip as f64 / n as f64, comp as f64 / n as f64);
            println!("{:>10} {:>6} {:>8.2} {:>8.2} {:>10} {:>7.2}x", n, live, s, c, live + 4, s / c);
        }
    }
    println!("\n(ns/elem, min of {reps} reps. skip = lsb_range; compact = lsb_compact.");
    println!(" stride = bytes moved per pass by compact (vs 12 for skip). mini-01 / Apple M4.)");
}
