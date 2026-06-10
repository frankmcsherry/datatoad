//! MSB option map: on the 8-byte full-key sort (the u32_sort_last shape), compare
//! contiguous LSB, paged LSB, and in-place MSB. MSB sorts full-width by Ord, so it
//! is drop-in only here (not the 12-byte sort-by-prefix path) and uses no 2x temp.
use datatoad::facts::radix_sort::{lsb_range, lsb_paged, PageBuilder, msb};
fn lcg(s0: u64) -> impl FnMut() -> u64 { let mut s=s0.wrapping_mul(2)+1; move|| { s=s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); s>>33 } }
fn rows8(n: usize, groups: u64, seed: u64) -> Vec<[u8;8]> {
    let mut next = lcg(seed);
    (0..n).map(|_| { let mut r=[0u8;8]; r[0..4].copy_from_slice(&((next()%groups) as u32).to_be_bytes()); r[4..8].copy_from_slice(&((next()%groups) as u32).to_be_bytes()); r }).collect()
}
fn main() {
    let reps = 7;
    println!("{:>10} {:>12} {:>12} {:>12}  winner", "n", "contig_ns/e", "paged_ns/e", "msb_ns/e");
    for &n in &[1_000usize, 16_000, 256_000, 1_000_000, 4_000_000, 16_000_000] {
        let groups = (n as u64/8).max(1);
        let base = rows8(n, groups, 0xABCD ^ n as u64);
        let mut cn=u128::MAX; for _ in 0..reps { let mut d=base.clone(); let t=std::time::Instant::now(); lsb_range(&mut d[..],0,8); cn=cn.min(t.elapsed().as_nanos()); }
        let mut pn=u128::MAX; for _ in 0..reps { let mut b=PageBuilder::<[u8;8],8,1024>::default(); let t=std::time::Instant::now(); let mut it=base.iter().copied(); loop { let p:Vec<[u8;8]>=it.by_ref().take(1024).collect(); if p.is_empty(){break;} b.push_page(p);} let (mut pg,f)=b.done(); lsb_paged::<_,1024>(&mut pg,&f[..]); pn=pn.min(t.elapsed().as_nanos()); }
        let mut mn=u128::MAX; let mut mref=None; for _ in 0..reps { let mut d=base.clone(); let t=std::time::Instant::now(); msb(&mut d[..]); mn=mn.min(t.elapsed().as_nanos()); mref=Some(d); }
        // correctness: msb output sorted
        assert!(mref.unwrap().windows(2).all(|w| w[0]<=w[1]), "msb not sorted n={}", n);
        let (c,p,m)=(cn as f64/n as f64, pn as f64/n as f64, mn as f64/n as f64);
        let win = if c<=p && c<=m {"contig"} else if m<=p {"msb"} else {"paged"};
        println!("{:>10} {:>12.2} {:>12.2} {:>12.2}  {}", n, c, p, m, win);
    }
}
