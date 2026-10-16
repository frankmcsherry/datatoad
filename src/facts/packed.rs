//! Radix sorting of `(group, value)` pairs packed into integer keys.
//!
//! Column sorts order rows of `(group, value)` pairs, where `group` names the list
//! the row belongs to and `value` is a four-byte item. A byte-oriented radix sort
//! skips byte positions that are constant across rows, but nearly constant bytes
//! still cost a full pass: groups less than 2^17 have one live bit in their third
//! byte. We instead pack each row into an integer key with exactly as many bits as
//! the ranges of its groups and values require, append the row's index below the
//! key when the sort must report where rows went, and then sort by the key bits in
//! as few (wide) digits as they require.

use std::mem::MaybeUninit;

use columnar::Len;
use crate::facts::Lists;

/// An integer key that can be radix sorted by bit ranges.
pub trait RadixKey: Copy + Ord {
    /// The bits of `self` at `shift .. shift + bits(mask)`, as a bucket index.
    fn digit(&self, shift: u32, mask: usize) -> usize;
}
impl RadixKey for u32 { #[inline(always)] fn digit(&self, shift: u32, mask: usize) -> usize { ((*self >> shift) as usize) & mask } }
impl RadixKey for u64 { #[inline(always)] fn digit(&self, shift: u32, mask: usize) -> usize { ((*self >> shift) as usize) & mask } }
impl RadixKey for u128 { #[inline(always)] fn digit(&self, shift: u32, mask: usize) -> usize { ((*self >> shift) as usize) & mask } }

/// The maximum number of bits per radix digit.
///
/// Wider digits mean fewer passes, but larger histograms and more scatter streams.
/// On Apple M4, replaying the sorts of the galen workload, fewer passes won up to
/// about fourteen bits, at all sizes from thousands to millions of rows.
pub const DIGIT_BITS: u32 = 13;

/// Number of bits needed to represent `x`.
#[inline(always)]
pub fn bits(x: u64) -> u32 { 64 - x.leading_zeros() }

/// A plan to LSB radix sort by bits `lower .. lower + passes * digit`.
#[derive(Copy, Clone, Debug)]
pub struct Plan { pub lower: u32, pub passes: u32, pub digit: u32 }

impl Plan {
    /// Splits the bits `lower .. upper` into as few digits as possible, evenly.
    pub fn new(lower: u32, upper: u32) -> Self {
        let width = upper.saturating_sub(lower);
        let passes = width.div_ceil(DIGIT_BITS);
        let digit = if passes == 0 { 0 } else { width.div_ceil(passes) };
        Self { lower, passes, digit }
    }
    #[inline(always)] pub fn buckets(&self) -> usize { 1 << self.digit }
    #[inline(always)] pub fn mask(&self) -> usize { self.buckets() - 1 }
    #[inline(always)] pub fn shift(&self, pass: u32) -> u32 { self.lower + pass * self.digit }
}

/// Collects `keys` into a vector, and histograms each digit of `plan`.
///
/// Fusing the histogram with the formation of keys avoids a separate pass over them.
#[inline(always)]
fn collect_counted<K: RadixKey>(n: usize, keys: impl Iterator<Item = K>, plan: Plan) -> (Vec<K>, Vec<u32>) {
    match plan.passes {
        0 => (keys.collect(), Vec::new()),
        1 => collect_counted_inner::<K, 1>(n, keys, plan),
        2 => collect_counted_inner::<K, 2>(n, keys, plan),
        3 => collect_counted_inner::<K, 3>(n, keys, plan),
        4 => collect_counted_inner::<K, 4>(n, keys, plan),
        5 => collect_counted_inner::<K, 5>(n, keys, plan),
        6 => collect_counted_inner::<K, 6>(n, keys, plan),
        7 => collect_counted_inner::<K, 7>(n, keys, plan),
        8 => collect_counted_inner::<K, 8>(n, keys, plan),
        9 => collect_counted_inner::<K, 9>(n, keys, plan),
        10 => collect_counted_inner::<K, 10>(n, keys, plan),
        p => panic!("too many radix passes: {}", p),
    }
}

/// Collects `n` keys and histograms each of the `P` digits of `plan`.
///
/// Consecutive keys often share digits (rows of a group arrive together), and incrementing
/// the same count back to back stalls on store-to-load forwarding. We alternate between two
/// sets of counts, and sum them at the end.
#[inline(always)]
fn collect_counted_inner<K: RadixKey, const P: usize>(n: usize, keys: impl Iterator<Item = K>, plan: Plan) -> (Vec<K>, Vec<u32>) {
    assert_eq!(P, plan.passes as usize);
    let buckets = plan.buckets();
    let mask = plan.mask();
    let stride = buckets * P;
    let mut counts = vec![0u32; 2 * stride];
    let mut shifts = [0u32; P];
    for (pass, shift) in shifts.iter_mut().enumerate() { *shift = plan.shift(pass as u32); }
    let mut result: Vec<K> = Vec::with_capacity(n);
    let mut count = 0;
    for (key, slot) in keys.zip(result.spare_capacity_mut().iter_mut()) {
        slot.write(key);
        let base = (count & 1) * stride;
        count += 1;
        for pass in 0 .. P {
            // SAFETY: `digit <= mask < buckets`, and `pass < P`, so the index is less than `2 * stride`.
            unsafe { *counts.get_unchecked_mut(base + pass * buckets + key.digit(shifts[pass], mask)) += 1; }
        }
    }
    assert_eq!(count, n);
    // SAFETY: we wrote the first `n` elements.
    unsafe { result.set_len(n); }
    let (even, odd) = counts.split_at_mut(stride);
    for (x, y) in even.iter_mut().zip(odd.iter()) { *x += *y; }
    counts.truncate(stride);
    (result, counts)
}

/// Stable LSB radix sort of `data` by the digits of `plan`, using `temp` as scratch.
///
/// The `counts` histograms must be those of `data` for each digit of `plan`.
/// The sorted result ends up in one of `data` or `temp`; the method returns `true` if it
/// is in `temp`. Bits outside the plan are payload, and do not affect the order.
/// Digits whose value is the same for all elements are skipped. The `temp` vector is
/// cleared and resized as needed, and its prior contents are irrelevant.
pub fn lsb_planned<K: RadixKey>(data: &mut Vec<K>, temp: &mut Vec<K>, plan: Plan, counts: &[u32]) -> bool {

    let n = data.len();
    if n <= 1 { return false; }

    let buckets = plan.buckets();
    temp.clear();
    temp.reserve(n);

    let mut in_temp = false;
    let mut offsets = vec![0usize; buckets];
    for pass in 0 .. plan.passes {
        let count = &counts[pass as usize * buckets .. (pass as usize + 1) * buckets];
        // Skip digits shared by all elements.
        if count.iter().any(|c| *c as usize == n) { continue; }
        let mut total = 0;
        for (offset, count) in offsets.iter_mut().zip(count.iter()) { *offset = total; total += *count as usize; }
        let (src, dst) = if in_temp { (&temp[..], spare_all(data)) } else { (&data[..], spare_all(temp)) };
        scatter(src, dst, &mut offsets, plan.shift(pass), plan.mask());
        // SAFETY: `scatter` wrote all `n` elements of `dst`, as `offsets` partition `0 .. n`.
        unsafe { if in_temp { data.set_len(n) } else { temp.set_len(n) } }
        in_temp = !in_temp;
    }
    in_temp
}

/// Writes each element of `src` to `dst` at the position named by its digit's offset.
#[inline(never)]
fn scatter<K: RadixKey>(src: &[K], dst: &mut [MaybeUninit<K>], offsets: &mut [usize], shift: u32, mask: usize) {
    assert!(dst.len() >= src.len());
    assert!(offsets.len() > mask);
    let dst = dst.as_mut_ptr();
    for item in src.iter() {
        let digit = item.digit(shift, mask);
        // SAFETY: `digit <= mask < offsets.len()`, and offsets partition `0 .. src.len()`.
        unsafe {
            let offset = offsets.get_unchecked_mut(digit);
            (*dst.add(*offset)).write(*item);
            *offset += 1;
        }
    }
}

/// The full capacity of `vec` as uninitialized memory, forgetting its (`Copy`) contents.
fn spare_all<K: Copy>(vec: &mut Vec<K>) -> &mut [MaybeUninit<K>] {
    // SAFETY: zero is at most the capacity, and `K: Copy` has no drop obligations.
    unsafe { vec.set_len(0); }
    vec.spare_capacity_mut()
}

/// Sort the items of `lists` subject to the grouping/ordering of `group` of the lists.
///
/// Mints a new item for each distinct `(group, item)` pair and a new list for each distinct
/// group, rewriting `groups` with output item indexes unless `last` is set.
#[inline(never)]
pub fn u32_sort(items: &[[u8;4]], groups: &mut [usize], indexs: &[usize], last: bool) -> Lists<Vec<[u8;4]>> {

    assert_eq!(groups.len(), indexs.len());
    let n = groups.len();
    let mut output = Lists::<Vec<[u8;4]>>::default();
    if n == 0 { return output; }

    // Gather values, and learn the ranges of groups and values.
    let mut values: Vec<u32> = Vec::with_capacity(n);
    let (mut vmin, mut vmax) = (u32::MAX, 0u32);
    let (mut gmin, mut gmax) = (usize::MAX, 0usize);
    let mut v_sorted = true;
    let mut prev = 0u32;
    for (group, index) in groups.iter().zip(indexs.iter()) {
        let value = u32::from_be_bytes(items[*index]);
        values.push(value);
        vmin = vmin.min(value);
        vmax = vmax.max(value);
        gmin = gmin.min(*group);
        gmax = gmax.max(*group);
        v_sorted &= prev <= value;
        prev = value;
    }

    let vbits = bits((vmax - vmin) as u64);
    let gbits = bits((gmax - gmin) as u64);
    let kbits = vbits + gbits;
    // Groups index rows and fit in 32 bits in practice, but should keys not fit, fall back to comparison sorting.
    if kbits > 64 || (!last && kbits + bits(n as u64 - 1) > 128) {
        return crate::facts::trie::layers::col_sort::<Vec<[u8;4]>>(items, groups, indexs, last);
    }
    // When values are already ordered, a stable sort by group suffices.
    let sort_lower = if v_sorted { vbits } else { 0 };
    let packing = Packing { vmin, vbits, groups: gmax - gmin + 1 };

    if last {
        let plan = Plan::new(sort_lower, kbits);
        if kbits <= 32 {
            let keys = values.iter().zip(groups.iter()).map(|(v, g)| ((*g - gmin) as u32).wrapping_shl(vbits) | (v - vmin));
            let (keys, counts) = collect_counted(n, keys, plan);
            drop(values);
            emit_last::<u32>(keys, plan, &counts, packing, &mut output);
        }
        else {
            let keys = values.iter().zip(groups.iter()).map(|(v, g)| (((*g - gmin) as u64) << vbits) | (v - vmin) as u64);
            let (keys, counts) = collect_counted(n, keys, plan);
            drop(values);
            emit_last::<u64>(keys, plan, &counts, packing, &mut output);
        }
    }
    else {
        let ibits = bits(n as u64 - 1);
        let plan = Plan::new(sort_lower + ibits, kbits + ibits);
        if kbits + ibits <= 64 {
            let keys = values.iter().zip(groups.iter()).enumerate().map(|(i, (v, g))| (((((*g - gmin) as u64) << vbits) | (v - vmin) as u64) << ibits) | i as u64);
            let (keys, counts) = collect_counted(n, keys, plan);
            drop(values);
            emit_next::<u64>(keys, plan, &counts, packing, ibits, groups, &mut output);
        }
        else {
            let keys = values.iter().zip(groups.iter()).enumerate().map(|(i, (v, g))| (((((*g - gmin) as u128) << vbits) | (v - vmin) as u128) << ibits) | i as u128);
            let (keys, counts) = collect_counted(n, keys, plan);
            drop(values);
            emit_next::<u128>(keys, plan, &counts, packing, ibits, groups, &mut output);
        }
    }

    output
}

/// How `(group, value)` pairs were packed into keys: `((group - gmin) << vbits) | (value - vmin)`.
#[derive(Copy, Clone)]
struct Packing {
    vmin: u32,
    vbits: u32,
    /// An upper bound on the number of distinct groups.
    groups: usize,
}

/// Unpacking of keys into the low bits (`low`) and the bits from a shift onward (`high`).
trait Unpack: RadixKey { fn low(self, bits: u32) -> u64; fn high(self, shift: u32) -> u64; }
impl Unpack for u32 {
    #[inline(always)] fn low(self, bits: u32) -> u64 { (self as u64) & ((1u64 << bits) - 1) }
    #[inline(always)] fn high(self, shift: u32) -> u64 { (self as u64) >> shift }
}
impl Unpack for u64 {
    #[inline(always)] fn low(self, bits: u32) -> u64 { if bits >= 64 { self } else { self & ((1u64 << bits) - 1) } }
    #[inline(always)] fn high(self, shift: u32) -> u64 { if shift >= 64 { 0 } else { self >> shift } }
}
impl Unpack for u128 {
    #[inline(always)] fn low(self, bits: u32) -> u64 { (self & ((1u128 << bits) - 1)) as u64 }
    #[inline(always)] fn high(self, shift: u32) -> u64 { (self >> shift) as u64 }
}

/// Sorts keys of `(group, value)` and forms deduplicated lists of values for each group.
#[inline(never)]
fn emit_last<K: Unpack>(mut keys: Vec<K>, plan: Plan, counts: &[u32], packing: Packing, output: &mut Lists<Vec<[u8;4]>>) {
    let Packing { vmin, vbits, groups } = packing;
    let mut temp = Vec::new();
    let keys = if lsb_planned(&mut keys, &mut temp, plan, counts) { drop(keys); temp } else { drop(temp); keys };
    if keys.is_empty() { return; }
    // Write values and list bounds unconditionally, and advance past them only when they are new.
    // Duplicates are common and unpredictable, and branching on them is expensive.
    let mut values: Vec<[u8; 4]> = Vec::with_capacity(keys.len());
    let mut bounds: Vec<u64> = Vec::with_capacity(std::cmp::min(groups, keys.len()) + 1);
    let (values_ptr, bounds_ptr) = (values.as_mut_ptr(), bounds.as_mut_ptr());
    let mut prev = keys[0];
    // SAFETY: there is at most one value per key, and at most one bound per distinct group,
    // of which there are at most `groups` and at most `keys.len()`.
    unsafe { values_ptr.write((prev.low(vbits) as u32 + vmin).to_be_bytes()); }
    let (mut values_len, mut bounds_len) = (1, 0);
    for key in keys[1..].iter() {
        let new_value = *key != prev;
        let new_group = key.high(vbits) != prev.high(vbits);
        unsafe {
            bounds_ptr.add(bounds_len).write(values_len as u64);
            values_ptr.add(values_len).write((key.low(vbits) as u32 + vmin).to_be_bytes());
        }
        bounds_len += new_group as usize;
        values_len += new_value as usize;
        prev = *key;
    }
    unsafe {
        bounds_ptr.add(bounds_len).write(values_len as u64);
        values.set_len(values_len);
        bounds.set_len(bounds_len + 1);
    }
    output.values = values;
    for bound in bounds { output.bounds.push(bound); }
}

/// Sorts keys of `(group, value, index)` and forms deduplicated lists of values for each group,
/// writing in `groups[index]` the position of the row's `(group, value)` in the output.
#[inline(never)]
fn emit_next<K: Unpack>(mut keys: Vec<K>, plan: Plan, counts: &[u32], packing: Packing, ibits: u32, groups: &mut [usize], output: &mut Lists<Vec<[u8;4]>>) {
    let Packing { vmin, vbits, groups: group_count } = packing;
    let mut temp = Vec::new();
    let keys = if lsb_planned(&mut keys, &mut temp, plan, counts) { drop(keys); temp } else { drop(temp); keys };
    if keys.is_empty() { return; }
    // As in `emit_last`, write unconditionally and advance only past new values and bounds.
    let mut values: Vec<[u8; 4]> = Vec::with_capacity(keys.len());
    let mut bounds: Vec<u64> = Vec::with_capacity(std::cmp::min(group_count, keys.len()) + 1);
    let (values_ptr, bounds_ptr) = (values.as_mut_ptr(), bounds.as_mut_ptr());
    let mut prev = keys[0].high(ibits);
    groups[keys[0].low(ibits) as usize] = 0;
    // SAFETY: there is at most one value per key, and at most one bound per distinct group,
    // of which there are at most `group_count` and at most `keys.len()`.
    unsafe { values_ptr.write((prev.low(vbits) as u32 + vmin).to_be_bytes()); }
    let (mut values_len, mut bounds_len) = (1, 0);
    for key in keys[1..].iter() {
        let row = key.high(ibits);
        let new_value = row != prev;
        let new_group = (row >> vbits) != (prev >> vbits);
        unsafe {
            bounds_ptr.add(bounds_len).write(values_len as u64);
            values_ptr.add(values_len).write((row.low(vbits) as u32 + vmin).to_be_bytes());
        }
        bounds_len += new_group as usize;
        values_len += new_value as usize;
        groups[key.low(ibits) as usize] = values_len - 1;
        prev = row;
    }
    unsafe {
        bounds_ptr.add(bounds_len).write(values_len as u64);
        values.set_len(values_len);
        bounds.set_len(bounds_len + 1);
    }
    output.values = values;
    for bound in bounds { output.bounds.push(bound); }
}

#[cfg(test)]
mod tests {

    use columnar::{Borrow, Index, Len};
    use crate::facts::trie::layers::col_sort;

    fn lcg(seed: u64) -> impl FnMut() -> u64 {
        let mut state = seed.wrapping_mul(2) + 1;
        move || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); state >> 33 }
    }

    /// Compares against the comparison-sort kernel, across group and value ranges that exercise
    /// 32, 64, and 128 bit keys, presorted values, and repeated rows.
    #[test]
    fn u32_sort_matches_col_sort() {
        for seed in 0 .. 204u64 {
            let mut next = lcg(seed);
            // The final seeds are large enough to need 128 bit keys.
            let n = if seed >= 200 { 100_000 } else { match seed % 5 { 0 => 1, 1 => 2 + (next() % 10) as usize, _ => 1 + (next() % 5000) as usize } };
            let vrange = if seed >= 200 { u32::MAX as u64 } else { match seed % 4 { 0 => 1, 1 => 16, 2 => 1 << 20, _ => u32::MAX as u64 } };
            let grange = if seed >= 200 { n as u64 } else { match seed % 3 { 0 => 1, 1 => 1 + n as u64 / 3, _ => 1 + n as u64 } };
            let items: Vec<[u8; 4]> = (0 .. 1 + n).map(|_| ((next() << 1 ^ next()) % vrange.max(1)) as u32).map(|x| x.to_be_bytes()).collect();
            let mut groups: Vec<usize> = (0 .. n).map(|_| (next() % grange) as usize).collect();
            if seed % 7 == 0 { groups.sort(); }
            let mut indexs: Vec<usize> = (0 .. n).map(|_| (next() as usize) % items.len()).collect();
            if seed % 11 == 0 { indexs.sort(); }
            for last in [false, true] {
                let mut g0 = groups.clone();
                let mut g1 = groups.clone();
                let x = super::u32_sort(&items, &mut g0, &indexs, last);
                let y = col_sort::<Vec<[u8; 4]>>(&items[..], &mut g1, &indexs, last);
                assert_eq!(x.values, y.values);
                assert_eq!(x.bounds.borrow().len(), y.bounds.borrow().len());
                for i in 0 .. x.bounds.borrow().len() { assert_eq!(x.bounds.borrow().get(i), y.bounds.borrow().get(i)); }
                if !last { assert_eq!(g0, g1); }
            }
        }
    }
}
