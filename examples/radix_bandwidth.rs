//! Is datatoad's sort bandwidth-bound, and how many CPU cores saturate the shared
//! memory pool? Run N independent CPU sorts concurrently and watch whether aggregate
//! throughput scales linearly (compute-bound) or plateaus (bandwidth-bound). The
//! plateau is the *system* sort ceiling that the GPU also has to share.
//!
//! Run: cargo run --release --example radix_bandwidth

use datatoad::facts::radix_sort::lsb_range;
use std::sync::{Arc, Barrier};
use std::time::Instant;

fn lcg(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed.wrapping_mul(2) + 1;
    move || { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); s >> 33 }
}

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

fn main() {
    let n_per = 2_000_000usize; // per-thread array
    let reps = 12;              // sorts per thread (in place; redoes all passes each time)
    let groups = (n_per as u64 / 8).max(2);

    println!("Per-thread n={n_per}, {reps} sorts/thread, 12-byte rows sorted on 8-byte key.");
    println!("Barrier-synchronized concurrent start; aggregate over slowest thread.\n");
    println!("{:>8} {:>16} {:>14} {:>10} {:>11}", "threads", "per-stream ns/e", "agg Melem/s", "speedup", "efficiency");

    let mut base_agg = 0.0f64;
    for &threads in &[1usize, 2, 3, 4, 6, 8, 10] {
        let mut datas: Vec<Vec<[u8; 12]>> =
            (0..threads).map(|t| rows(n_per, groups, 0xC0FFEE ^ (t as u64).wrapping_mul(0x9E37))).collect();

        let barrier = Arc::new(Barrier::new(threads));
        let max_secs = std::thread::scope(|s| {
            let handles: Vec<_> = datas.iter_mut().map(|d| {
                let b = Arc::clone(&barrier);
                s.spawn(move || {
                    b.wait(); // all streams start together
                    let t = Instant::now();
                    for _ in 0..reps { lsb_range(&mut d[..], 0, 8); }
                    t.elapsed().as_secs_f64()
                })
            }).collect();
            handles.into_iter().map(|h| h.join().unwrap()).fold(0.0f64, f64::max)
        });

        let total_elems = (threads * reps * n_per) as f64;
        let per_stream_ns = max_secs / (reps * n_per) as f64 * 1e9;
        let agg_melem = total_elems / max_secs / 1e6;
        if threads == 1 { base_agg = agg_melem; }
        let speedup = agg_melem / base_agg;
        let eff = speedup / threads as f64;
        println!("{:>8} {:>16.2} {:>14.0} {:>9.2}x {:>10.0}%", threads, per_stream_ns, agg_melem, speedup, eff * 100.0);
    }

    println!("\nIf agg Melem/s stops rising (efficiency falls toward 0), the sort is");
    println!("bandwidth-bound and that plateau is the ceiling the GPU also draws from.");
    println!("Single GPU-fused stream measured ~4.2 ns/e ~= ~240 Melem/s. mini-01 / Apple M4.");
}
