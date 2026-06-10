//! Kernel-level spike: contiguous LSB vs paged LSB (vs MSB where it applies),
//! to locate the size crossover behind the M2/M4 split on #54.
//!
//! The workload mirrors `u32_sort`: rows of (group:u32, value:u32, index:u32) as
//! big-endian bytes, sorted on the first 8 bytes (group then value), index as an
//! ignored payload. IDs are small integers, so high bytes are often constant —
//! exactly the leading-zero pattern both kernels skip, as in real galen data.
//!
//! Each variant is timed end-to-end (buffer construction + sort), because #54
//! changed both the layout and the sort. Run: `cargo run --release --example radix_spike`.

use datatoad::facts::radix_sort::{lsb_range, lsb_paged, PageBuilder};

fn lcg(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed.wrapping_mul(2) + 1;
    move || { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); s >> 33 }
}

/// (group, value) pairs: `groups` distinct keys, average fan-out `n / groups`.
fn rows12(n: usize, groups: u64, seed: u64) -> Vec<[u8; 12]> {
    let mut next = lcg(seed);
    (0..n).map(|i| {
        let mut r = [0u8; 12];
        r[0..4].copy_from_slice(&((next() % groups) as u32).to_be_bytes());
        r[4..8].copy_from_slice(&((next() % groups) as u32).to_be_bytes());
        r[8..12].copy_from_slice(&(i as u32).to_be_bytes());
        r
    }).collect()
}

fn now() -> std::time::Instant { std::time::Instant::now() }

/// Sort key for verification: first 8 bytes only (the prefix the kernels sort by).
fn key(r: &[u8; 12]) -> [u8; 8] { r[0..8].try_into().unwrap() }

fn main() {
    let reps = 7;
    println!("{:>10} {:>8} {:>12} {:>12} {:>10}", "n", "groups", "contig_ns/e", "paged_ns/e", "ratio");
    for &n in &[1_000usize, 4_000, 16_000, 64_000, 256_000, 1_000_000, 4_000_000, 16_000_000] {
        // A spread of fan-outs: dense keys (few groups, long lists) and sparse (many groups).
        for &groups in &[(n as u64 / 8).max(1), (n as u64).max(1)] {
            let base = rows12(n, groups, 0xC0FFEE ^ n as u64 ^ groups);

            // Contiguous: clone, lsb_range over bytes 0..8.
            let mut c_ns = u128::MAX;
            let mut c_ref = None;
            for _ in 0..reps {
                let mut data = base.clone();
                let t = now();
                lsb_range(&mut data[..], 0, 8);
                c_ns = c_ns.min(t.elapsed().as_nanos());
                c_ref = Some(data);
            }

            // Paged: build pages with bulk push_page (as u32_sort does), mask payload, lsb_paged.
            let mut p_ns = u128::MAX;
            let mut p_ref = None;
            for _ in 0..reps {
                let mut builder = PageBuilder::<[u8; 12], 12, 1024>::default();
                let t = now();
                let mut it = base.iter().copied();
                loop {
                    let page: Vec<[u8; 12]> = it.by_ref().take(1024).collect();
                    if page.is_empty() { break; }
                    builder.push_page(page);
                }
                let (mut pages, mut filter) = builder.done();
                for f in &mut filter[8..12] { *f = false; }
                lsb_paged::<_, 1024>(&mut pages, &filter[..]);
                p_ns = p_ns.min(t.elapsed().as_nanos());
                p_ref = Some(pages.concat());
            }

            // Cross-check both orderings agree on the 8-byte key.
            let c = c_ref.unwrap(); let p = p_ref.unwrap();
            let ck: Vec<_> = c.iter().map(key).collect();
            let pk: Vec<_> = p.iter().map(key).collect();
            assert_eq!(ck, pk, "orderings disagree at n={} groups={}", n, groups);
            assert!(ck.windows(2).all(|w| w[0] <= w[1]), "not sorted n={}", n);

            let cpe = c_ns as f64 / n as f64;
            let ppe = p_ns as f64 / n as f64;
            let tag = if cpe < ppe { "contig" } else { "paged" };
            println!("{:>10} {:>8} {:>12.2} {:>12.2} {:>9.2}x {}", n, groups, cpe, ppe, ppe / cpe, tag);
        }
    }
}
