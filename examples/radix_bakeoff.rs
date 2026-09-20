//! Radix sort bake-off for the datatoad `u32_sort` shape: 12-byte rows of
//! (group:u32_be, value:u32_be, index:u32_be), sorted by the 8-byte key prefix
//! (group, value); the index is an opaque payload that rides along.
//!
//! Contenders (CPU, all in-tree):
//!   * contig LSB  — `lsb_range(rows, 0, 8)`, the current incumbent
//!   * paged  LSB  — `lsb_paged`, bounded-peak-memory variant
//!   * prefix MSB  — `msb_range(rows, 0, 8)`, in-place American-flag, no 2x temp
//! Contender (GPU, Apple Silicon only, external crate):
//!   * forge-sort  — `GpuSorter::sort_pairs_u64`, measured two ways:
//!       - "forge+marshal": BE bytes -> (u64 key, u32 val) extraction + sort
//!         (apples-to-apples: what it would cost to actually use it here)
//!       - "forge kernel": sort of pre-marshalled arrays (its best case)
//!
//! The `from_be_bytes` extraction is exactly the marshalling tax our PR #64
//! concluded was the wall: BE storage means forge's zero-copy path is unreachable
//! without changing datatoad's native key layout.
//!
//! Run: cargo run --release --example radix_bakeoff

use datatoad::facts::radix_sort::{lsb_range, lsb_paged, msb_range, PageBuilder};
use std::time::Instant;

fn lcg(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed.wrapping_mul(2) + 1;
    move || { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); s >> 33 }
}

/// (group, value) pairs over `groups` distinct keys; index = position. Uniform.
fn rows_uniform(n: usize, groups: u64, seed: u64) -> Vec<[u8; 12]> {
    let mut next = lcg(seed);
    (0..n).map(|i| {
        let mut r = [0u8; 12];
        r[0..4].copy_from_slice(&((next() % groups) as u32).to_be_bytes());
        r[4..8].copy_from_slice(&((next() % groups) as u32).to_be_bytes());
        r[8..12].copy_from_slice(&(i as u32).to_be_bytes());
        r
    }).collect()
}

/// Skewed keys to stress MSB load imbalance: ~80% of rows collapse the group into
/// just 4 values (so the top partition byte produces a few huge buckets that blow
/// the cache), the rest spread over `groups`. LSB is distribution-insensitive; MSB
/// is not, so this input is where the two should diverge most.
fn rows_skewed(n: usize, groups: u64, seed: u64) -> Vec<[u8; 12]> {
    let mut next = lcg(seed);
    (0..n).map(|i| {
        let mut r = [0u8; 12];
        let g = if next() % 5 != 0 { next() % 4 } else { next() % groups };
        let v = if next() % 5 != 0 { next() % 4 } else { next() % groups };
        r[0..4].copy_from_slice(&(g as u32).to_be_bytes());
        r[4..8].copy_from_slice(&(v as u32).to_be_bytes());
        r[8..12].copy_from_slice(&(i as u32).to_be_bytes());
        r
    }).collect()
}

/// The 8-byte key prefix, for verification (the order the kernels must agree on).
fn key(r: &[u8; 12]) -> [u8; 8] { r[0..8].try_into().unwrap() }

fn min_ns(reps: usize, mut f: impl FnMut()) -> u128 {
    let mut best = u128::MAX;
    for _ in 0..reps {
        let t = Instant::now();
        f();
        best = best.min(t.elapsed().as_nanos());
    }
    best
}

fn bench_contig(base: &[[u8; 12]], reps: usize) -> (f64, Vec<[u8; 8]>) {
    let mut out = Vec::new();
    let ns = min_ns(reps, || {
        let mut d = base.to_vec();
        lsb_range(&mut d[..], 0, 8);
        out = d.iter().map(key).collect();
        std::hint::black_box(&d);
    });
    (ns as f64 / base.len() as f64, out)
}

fn bench_paged(base: &[[u8; 12]], reps: usize) -> (f64, Vec<[u8; 8]>) {
    let mut out = Vec::new();
    let ns = min_ns(reps, || {
        let mut b = PageBuilder::<[u8; 12], 12, 1024>::default();
        let mut it = base.iter().copied();
        loop {
            let p: Vec<[u8; 12]> = it.by_ref().take(1024).collect();
            if p.is_empty() { break; }
            b.push_page(p);
        }
        let (mut pages, mut filter) = b.done();
        for f in &mut filter[8..12] { *f = false; }
        lsb_paged::<_, 1024>(&mut pages, &filter[..]);
        out = pages.concat().iter().map(key).collect();
    });
    (ns as f64 / base.len() as f64, out)
}

fn bench_msb(base: &[[u8; 12]], reps: usize) -> (f64, Vec<[u8; 8]>) {
    let mut out = Vec::new();
    let ns = min_ns(reps, || {
        let mut d = base.to_vec();
        msb_range(&mut d[..], 0, 8);
        out = d.iter().map(key).collect();
        std::hint::black_box(&d);
    });
    (ns as f64 / base.len() as f64, out)
}

#[cfg(all(target_os = "macos", feature = "forge"))]
mod gpu {
    use super::*;
    use forge_sort::GpuSorter;

    /// forge-sort including the BE->native marshalling (the real cost of using it here).
    pub fn bench_forge_marshal(sorter: &mut GpuSorter, base: &[[u8; 12]], reps: usize) -> (f64, Vec<[u8; 8]>) {
        let n = base.len();
        let mut out = Vec::new();
        let ns = min_ns(reps, || {
            let mut keys: Vec<u64> = base.iter().map(|r| u64::from_be_bytes(r[0..8].try_into().unwrap())).collect();
            let mut vals: Vec<u32> = base.iter().map(|r| u32::from_be_bytes(r[8..12].try_into().unwrap())).collect();
            sorter.sort_pairs_u64(&mut keys, &mut vals).expect("forge sort_pairs_u64");
            out = keys.iter().map(|k| k.to_be_bytes()).collect();
            std::hint::black_box((&keys, &vals));
        });
        let _ = n;
        (ns as f64 / base.len() as f64, out)
    }

    /// forge-sort kernel only: arrays pre-marshalled, time just the sort (its best case).
    pub fn bench_forge_kernel(sorter: &mut GpuSorter, base: &[[u8; 12]], reps: usize) -> (f64, Vec<[u8; 8]>) {
        let keys0: Vec<u64> = base.iter().map(|r| u64::from_be_bytes(r[0..8].try_into().unwrap())).collect();
        let vals0: Vec<u32> = base.iter().map(|r| u32::from_be_bytes(r[8..12].try_into().unwrap())).collect();
        let mut out = Vec::new();
        let ns = min_ns(reps, || {
            let mut keys = keys0.clone();
            let mut vals = vals0.clone();
            sorter.sort_pairs_u64(&mut keys, &mut vals).expect("forge sort_pairs_u64");
            out = keys.iter().map(|k| k.to_be_bytes()).collect();
            std::hint::black_box((&keys, &vals));
        });
        (ns as f64 / base.len() as f64, out)
    }
}

fn main() {
    let reps = 7;
    #[cfg(all(target_os = "macos", feature = "forge"))]
    let mut sorter = forge_sort::GpuSorter::new().expect("no Metal device for forge-sort");

    let sizes = [1_000usize, 16_000, 256_000, 1_000_000, 4_000_000, 16_000_000];

    for (dist_name, skewed) in [("uniform", false), ("skewed (MSB-imbalanced)", true)] {
        println!("\n############ distribution: {dist_name} ############");
        println!(
            "{:>10} {:>8} {:>9} {:>9} {:>9} {:>11} {:>11}  winner",
            "n", "groups", "contig", "paged", "msb", "forge+mar", "forge-ker"
        );
        for &n in &sizes {
            let groups = (n as u64 / 8).max(2);
            let base = if skewed {
                rows_skewed(n, groups, 0xC0FFEE ^ n as u64)
            } else {
                rows_uniform(n, groups, 0xC0FFEE ^ n as u64)
            };

            let (c_ns, c_key) = bench_contig(&base, reps);
            let (p_ns, p_key) = bench_paged(&base, reps);
            let (m_ns, m_key) = bench_msb(&base, reps);

            // Correctness: every CPU method must produce the identical key sequence.
            assert!(c_key.windows(2).all(|w| w[0] <= w[1]), "contig not sorted n={n}");
            assert_eq!(c_key, p_key, "paged disagrees with contig n={n}");
            assert_eq!(c_key, m_key, "msb_range disagrees with contig n={n}");

            #[cfg(all(target_os = "macos", feature = "forge"))]
            let (fm_ns, fk_ns) = {
                let (fm, fm_key) = gpu::bench_forge_marshal(&mut sorter, &base, reps);
                let (fk, _fk_key) = gpu::bench_forge_kernel(&mut sorter, &base, reps);
                // forge is unstable on equal keys; check the KEY sequence only.
                assert_eq!(c_key, fm_key, "forge disagrees with contig (keys) n={n}");
                (fm, fk)
            };
            #[cfg(not(all(target_os = "macos", feature = "forge")))]
            let (fm_ns, fk_ns) = (f64::NAN, f64::NAN);

            let best = [c_ns, p_ns, m_ns, fm_ns].iter().cloned().filter(|x| x.is_finite()).fold(f64::INFINITY, f64::min);
            let win = if c_ns == best { "contig" }
                else if p_ns == best { "paged" }
                else if m_ns == best { "msb" }
                else { "forge+mar" };

            println!(
                "{:>10} {:>8} {:>9.2} {:>9.2} {:>9.2} {:>11.2} {:>11.2}  {}",
                n, groups, c_ns, p_ns, m_ns, fm_ns, fk_ns, win
            );
        }
    }
    println!("\n(ns/elem, min of {reps} reps. forge+mar includes BE->native extraction;");
    println!(" forge-ker times the kernel on pre-marshalled arrays. mini-01 / Apple M4.)");
}
