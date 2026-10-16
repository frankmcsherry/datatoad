//! Layer kernels specialized to fixed-width byte string items, `[u8; K]` with `K <= 4`.
//!
//! The generic kernels in `trie::layers` are written against `Container` and work item
//! by item through `Index::get` and `extend_from_self`, which for fixed-width items means
//! a `memmove` call per copied run, however short, and galloping searches launched on
//! every switch between inputs. These kernels instead read items as big-endian integers,
//! merge interleaved runs without branches, and reserve galloping and bulk copies for
//! the long runs where they pay off.

use std::collections::VecDeque;
use columnar::{Borrow, Container, Len};

use crate::facts::Lists;
use crate::facts::trie::layers::Report;

/// Borrowed lists of fixed-width items.
type Fixed<'a, const K: usize> = <Lists<Vec<[u8; K]>> as Borrow>::Borrowed<'a>;

/// The item as a big-endian integer, whose order matches that of the byte strings.
#[inline(always)]
fn key<const K: usize>(item: &[u8; K]) -> u32 {
    let mut result = 0u32;
    for byte in item.iter() { result = (result << 8) | (*byte as u32); }
    result
}

/// Runs at least this long are found by galloping and copied in bulk.
const RUN: usize = 8;

/// Advances `lower` past the elements of `items[.. upper]` strictly less than `bound`.
///
/// The search starts at `lower`, and costs time logarithmic in the distance advanced.
/// It first doubles a step until it overshoots, and then binary searches the last step
/// without branching on the comparisons, whose outcomes are unpredictable.
#[inline(always)]
fn gallop<const K: usize>(items: &[[u8; K]], lower: &mut usize, upper: usize, bound: u32) {
    if *lower < upper && key(&items[*lower]) < bound {
        let mut step = 1;
        while *lower + step < upper && key(&items[*lower + step]) < bound {
            *lower += step;
            step <<= 1;
        }
        // The first element at least `bound` is in `lo .. hi`, or is `hi` itself.
        let lo = *lower + 1;
        let hi = std::cmp::min(*lower + step, upper);
        if lo >= hi { *lower = hi; return; }
        let mut base = lo;
        let mut len = hi - lo;
        while len > 1 {
            let half = len / 2;
            base += ((key(&items[base + half]) < bound) as usize) * half;
            len -= half;
        }
        *lower = base + (key(&items[base]) < bound) as usize;
    }
}

/// Appends the sorted, deduplicated union of sorted `a` and `b` to `output`.
#[inline(always)]
fn merge<const K: usize>(a: &[[u8; K]], b: &[[u8; K]], output: &mut Vec<[u8; K]>) {
    output.reserve(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        let (x, y) = (key(&a[i]), key(&b[j]));
        // Long runs from one input are found by galloping and copied in bulk.
        if i + RUN <= a.len() && key(&a[i + RUN - 1]) < y {
            let start = i;
            i += RUN;
            gallop(a, &mut i, a.len(), y);
            output.extend_from_slice(&a[start .. i]);
        }
        else if j + RUN <= b.len() && key(&b[j + RUN - 1]) < x {
            let start = j;
            j += RUN;
            gallop(b, &mut j, b.len(), x);
            output.extend_from_slice(&b[start .. j]);
        }
        else {
            // Interleaved inputs: merge without branches. Each step consumes at least
            // one element from either input, and at most one from each, so `steps`
            // steps cannot overrun either input.
            let steps = std::cmp::min(RUN, std::cmp::min(a.len() - i, b.len() - j));
            let mut len = output.len();
            let ptr = output.as_mut_ptr();
            for _ in 0 .. steps {
                if i >= a.len() || j >= b.len() { break; }
                let (x, y) = (a[i], b[j]);
                let (kx, ky) = (key(&x), key(&y));
                // SAFETY: we reserved space for all of `a` and `b`, and write each element at most once.
                unsafe { ptr.add(len).write(if kx <= ky { x } else { y }); }
                len += 1;
                i += (kx <= ky) as usize;
                j += (ky <= kx) as usize;
            }
            // SAFETY: elements `.. len` are initialized.
            unsafe { output.set_len(len); }
        }
    }
    output.extend_from_slice(&a[i ..]);
    output.extend_from_slice(&b[j ..]);
}

/// Merges two sequences of lists using alignment information in `reports`.
///
/// Equivalent to `trie::layers::union` for fixed-width items.
#[inline(never)]
pub fn union<'a, const K: usize>(
    lists0: Fixed<'a, K>,
    lists1: Fixed<'a, K>,
    reports: &mut VecDeque<Report>,
    next: bool,
) -> Lists<Vec<[u8; K]>> {

    let mut list = <Lists::<Vec<[u8; K]>> as Container>::with_capacity_for([lists0, lists1].into_iter());

    let report_count = reports.len();
    for _ in 0 .. report_count {
        match reports.pop_front().unwrap() {
            Report::This(lower0, upper0) => {
                list.extend_from_self(lists0, lower0 .. upper0);
                let (new_lower, _) = lists0.bounds.bounds(lower0);
                let (_, new_upper) = lists0.bounds.bounds(upper0-1);
                if next { reports.push_back(Report::This(new_lower, new_upper)); }
            },
            Report::Both(index0, index1) => {
                let (lower0, upper0) = lists0.bounds.bounds(index0);
                let (lower1, upper1) = lists1.bounds.bounds(index1);
                if next { merge_reporting(lists0.values, lower0, upper0, lists1.values, lower1, upper1, &mut list.values, reports); }
                else { merge(&lists0.values[lower0 .. upper0], &lists1.values[lower1 .. upper1], &mut list.values); }
                list.bounds.push(list.values.len() as u64);
            },
            Report::That(lower1, upper1) => {
                list.extend_from_self(lists1, lower1 .. upper1);
                let (new_lower, _) = lists1.bounds.bounds(lower1);
                let (_, new_upper) = lists1.bounds.bounds(upper1-1);
                if next { reports.push_back(Report::That(new_lower, new_upper)); }
            },
        }
    }

    list
}

/// Merges `values0[lower0 .. upper0]` and `values1[lower1 .. upper1]` into `output`, reporting the alignment.
#[inline(always)]
fn merge_reporting<const K: usize>(
    values0: &[[u8; K]], mut lower0: usize, upper0: usize,
    values1: &[[u8; K]], mut lower1: usize, upper1: usize,
    output: &mut Vec<[u8; K]>,
    reports: &mut VecDeque<Report>,
) {
    while lower0 < upper0 && lower1 < upper1 {
        let (val0, val1) = (values0[lower0], values1[lower1]);
        let (key0, key1) = (key(&val0), key(&val1));
        if key0 < key1 {
            let start = lower0;
            lower0 += 1;
            gallop(values0, &mut lower0, upper0, key1);
            reports.push_back(Report::This(start, lower0));
            if lower0 == start + 1 { output.push(val0); } else { output.extend_from_slice(&values0[start .. lower0]); }
        }
        else if key0 == key1 {
            reports.push_back(Report::Both(lower0, lower1));
            output.push(val0);
            lower0 += 1;
            lower1 += 1;
        }
        else {
            let start = lower1;
            lower1 += 1;
            gallop(values1, &mut lower1, upper1, key0);
            reports.push_back(Report::That(start, lower1));
            if lower1 == start + 1 { output.push(val1); } else { output.extend_from_slice(&values1[start .. lower1]); }
        }
    }
    if lower0 < upper0 {
        output.extend_from_slice(&values0[lower0 .. upper0]);
        reports.push_back(Report::This(lower0, upper0));
    }
    if lower1 < upper1 {
        output.extend_from_slice(&values1[lower1 .. upper1]);
        reports.push_back(Report::That(lower1, upper1));
    }
}

/// Intersects pairs of lists aligned by `both0` and `both1`, producing aligned item indexes.
///
/// Equivalent to `trie::layers::intersection` for fixed-width items.
#[inline(never)]
pub fn intersection<'a, const K: usize>(
    list0: Fixed<'a, K>,
    list1: Fixed<'a, K>,
    both0: &[usize],
    both1: &[usize],
) -> (Vec<usize>, Vec<usize>) {

    assert_eq!(both0.len(), both1.len());

    let mut match0 = Vec::new();
    let mut match1 = Vec::new();

    let values0 = list0.values;
    let values1 = list1.values;

    for (index0, index1) in both0.iter().copied().zip(both1.iter().copied()) {

        let (lower0, upper0) = list0.bounds.bounds(index0);
        let (lower1, upper1) = list1.bounds.bounds(index1);
        let (len0, len1) = (upper0 - lower0, upper1 - lower1);

        if len0 == 0 || len1 == 0 { continue; }
        // Quickly dismiss lists with disjoint ranges.
        if key(&values0[upper0-1]) < key(&values1[lower1]) || key(&values1[upper1-1]) < key(&values0[lower0]) { continue; }

        if len0 * RUN < len1 {
            // Few items in `list0`; search for each in `list1`.
            let mut lower1 = lower1;
            for index in lower0 .. upper0 {
                let target = key(&values0[index]);
                gallop(values1, &mut lower1, upper1, target);
                if lower1 >= upper1 { break; }
                if key(&values1[lower1]) == target { match0.push(index); match1.push(lower1); lower1 += 1; }
            }
        }
        else if len1 * RUN < len0 {
            // Few items in `list1`; search for each in `list0`.
            let mut lower0 = lower0;
            for index in lower1 .. upper1 {
                let target = key(&values1[index]);
                gallop(values0, &mut lower0, upper0, target);
                if lower0 >= upper0 { break; }
                if key(&values0[lower0]) == target { match0.push(lower0); match1.push(index); lower0 += 1; }
            }
        }
        else {
            // Comparable sizes: a branch-free merge, which writes candidate matches unconditionally
            // and advances the output only on equality.
            let (mut lower0, mut lower1) = (lower0, lower1);
            let capacity = std::cmp::min(len0, len1);
            match0.reserve(capacity);
            match1.reserve(capacity);
            let mut len = match0.len();
            let (ptr0, ptr1) = (match0.as_mut_ptr(), match1.as_mut_ptr());
            while lower0 < upper0 && lower1 < upper1 {
                let (key0, key1) = (key(&values0[lower0]), key(&values1[lower1]));
                // SAFETY: at most `capacity` matches, and we reserved that much space.
                unsafe { ptr0.add(len).write(lower0); ptr1.add(len).write(lower1); }
                len += (key0 == key1) as usize;
                lower0 += (key0 <= key1) as usize;
                lower1 += (key1 <= key0) as usize;
            }
            // SAFETY: elements `.. len` are initialized.
            unsafe { match0.set_len(len); match1.set_len(len); }
        }
    }

    (match0, match1)
}

#[cfg(test)]
mod tests {

    use std::collections::VecDeque;
    use columnar::{Borrow, Index, Len, Push};
    use crate::facts::Lists;
    use crate::facts::trie::layers::{self, Report};

    fn lcg(seed: u64) -> impl FnMut() -> u64 {
        let mut state = seed.wrapping_mul(2) + 1;
        move || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); state >> 33 }
    }

    /// Random lists of sorted distinct items, with list lengths and densities that vary widely.
    fn lists(seed: u64, count: usize) -> Lists<Vec<[u8; 4]>> {
        let mut next = lcg(seed);
        let mut result = Lists::<Vec<[u8; 4]>>::default();
        for _ in 0 .. count {
            let len = match next() % 4 { 0 => 0, 1 => next() % 4, 2 => next() % 64, _ => next() % 1024 } as usize;
            let range = 1 + match next() % 3 { 0 => len as u64, 1 => 4 * len as u64, _ => 1 << 20 };
            let mut items: Vec<u32> = (0 .. len).map(|_| (next() % range) as u32).collect();
            items.sort();
            items.dedup();
            let items: Vec<[u8; 4]> = items.into_iter().map(|x| x.to_be_bytes()).collect();
            result.push(&items[..]);
        }
        result
    }

    fn equal(a: &Lists<Vec<[u8; 4]>>, b: &Lists<Vec<[u8; 4]>>) -> bool {
        a.borrow().len() == b.borrow().len() && (0 .. a.borrow().len()).all(|i| a.borrow().get(i) == b.borrow().get(i))
    }

    #[test]
    fn union_matches_generic() {
        for seed in 0 .. 20 {
            let a = lists(seed, 50);
            let b = lists(seed + 1000, 50);
            for next in [false, true] {
                let mut reports0: VecDeque<Report> = (0 .. 50).map(|i| match i % 3 { 0 => Report::Both(i, i), 1 => Report::This(i, i+1), _ => Report::That(i, i+1) }).collect();
                let mut reports1 = reports0.clone();
                let x = super::union::<4>(a.borrow(), b.borrow(), &mut reports0, next);
                let y = layers::union::<Vec<[u8; 4]>>(a.borrow(), b.borrow(), &mut reports1, next);
                assert!(equal(&x, &y));
                assert_eq!(format!("{:?}", reports0), format!("{:?}", reports1));
            }
        }
    }

    #[test]
    fn intersection_matches_generic() {
        for seed in 0 .. 20 {
            let a = lists(seed, 200);
            let b = lists(seed + 1000, 200);
            let mut next = lcg(seed + 7);
            let both0: Vec<usize> = (0 .. 300).map(|_| (next() % 200) as usize).collect();
            let both1: Vec<usize> = (0 .. 300).map(|_| (next() % 200) as usize).collect();
            let x = super::intersection::<4>(a.borrow(), b.borrow(), &both0, &both1);
            let y = layers::intersection::<Vec<[u8; 4]>>(a.borrow(), b.borrow(), &both0, &both1);
            assert_eq!(x, y);
        }
    }
}
