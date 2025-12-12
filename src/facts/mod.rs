//! Methods and types to support building and maintaining ordered sets of facts.

use std::collections::BTreeMap;
use columnar::{Borrow, Index};
use columnar::Vecs;
use columnar::primitive::offsets::Strides;

use crate::types::Action;

pub mod trie;

/// A `Vecs` using strided offsets.
pub type Lists<C> = Vecs<C, Strides>;
/// Use the `List` type to access an alternate columnar container.
pub type Terms = Lists<Vec<u8>>;

/// A map from text name to collection of facts.
///
/// In addition to their default representation (columns in order as defined),
/// we also maintain collections that result from the application of various
/// `Action`s to the fact collection. They are meant to be read not written,
/// and their `stable` and `recent` members track those of the base collection,
/// with the caveat that the `recent` will be deduplicated against `stable`,
/// as any projection in the action may cause distinct input facts to result
/// in duplicate output facts.
///
/// Although some names may be equivalent to actions on other names, this store
/// is oblivious to this information, and leaves it up to the planner to decide
/// whether it should use atoms as named or substitute other atoms and actions.
#[derive(Default)]
pub struct Relations {
    /// Map from name to raw data, and various linear transforms thereof.
    relations: BTreeMap<String, (FactSet<FactCollection>, Forms)>,
}

/// An alias for a map from actions to fact sets, one for each relation.
pub type Forms = BTreeMap<Action<String>, FactSet<FactCollection>>;

impl Relations {
    pub fn get(&self, name: &str) -> Option<&FactSet<FactCollection>> {
        self.relations.get(name).map(|(base, _)| base)
    }
    pub fn get_mut(&mut self, name: &str) -> Option<&mut FactSet<FactCollection>> {
        self.relations.get_mut (name).map(|(base, _)| base)
    }
    pub fn entry(&mut self, name: String) -> &mut FactSet<FactCollection> {
        &mut self.relations.entry(name).or_default().0
    }
    pub fn advance(&mut self) {
        for (facts, transforms) in self.relations.values_mut() {
            facts.advance();
            for (action, transform) in transforms.iter_mut() {
                if !transform.recent.is_empty() {
                    transform.stable.push(std::mem::take(&mut transform.recent));
                }
                if let Some(mut recent) = facts.recent.act_on(action).flatten() {
                    // Non-permutations need to be deduplicated against existing facts.
                    if !action.is_permutation() { recent = recent.antijoin(transform.stable.contents()); }
                    transform.recent = recent;
                }
            }
        }
    }
    pub fn active(&self) -> bool {
        self.relations.values().any(|x| x.0.active())
    }
    pub fn list(&self) {
        for (name, facts) in self.relations.iter() {
            println!("\t{}:\t{:?}\tIdentity", name, facts.0.len());
            for (_action, facts) in facts.1.iter() {
                println!("\t\t{:?}\t{:?}", facts.len(), _action);
            }
        }
    }

    /// Ensures that we have an entry for this name and the associated action.
    pub fn ensure_action(&mut self, name: &str, action: &Action<String>){
        let (base, transforms) = self.relations.entry(name.to_string()).or_default();
        if !action.is_identity() && !transforms.contains_key(action) {
            let mut fact_set = FactSet::default();
            // TODO: Can be more elegant if we see all columns retained, as it means no duplication.
            for layer in base.stable.contents() {
                fact_set.stable.extend(&mut layer.act_on(action));
            }
            // Flattening deduplicates, which may be necessary as `action` may introduce collisions
            // across LSM layers.
            if let Some(stable) = fact_set.stable.flatten() {
                fact_set.stable.push(stable);
            }
            if let Some(recent) = base.recent.act_on(action).flatten() {
                fact_set.recent = recent.antijoin(fact_set.stable.contents());
            }
            transforms.insert(action.clone(), fact_set);
        }
    }

    /// Gets a fact set by name, and by an action that is applied to them.
    ///
    /// This will only be non-`None` once `ensure_action` has been called with this name and action.
    pub fn get_action(&self, name: &str, action: &Action<String>) -> Option<&FactSet<FactCollection>> {
        if action.is_identity() { self.relations.get(name).map(|(base,_)| base) }
        else { self.relations.get(name).and_then(|(_base, transforms)| transforms.get(action)) }
    }
}

// pub use list::FactList as FactCollection;
pub use trie::Forest;
pub type FactCollection = Forest<Terms>;

/// A constant integer to which the facts could be upgraded.
///
/// The upgraded form is a distinct type, and this method cannot produce it alone.
/// It requires help to observe the possibility, and invoke the specialized code.
pub fn upgrade_hint(terms: <Lists<Terms> as Borrow>::Borrowed<'_>) -> Option<u64> { terms.values.bounds.strided() }

/// Attempts to recast a general term list as one of fixed width byte slices.
pub fn upgrade<'a, const K: usize>(terms: <Lists<Terms> as Borrow>::Borrowed<'a>) -> Option<<Lists<Vec<[u8; K]>> as Borrow>::Borrowed<'a>> {
    if upgrade_hint(terms)? as usize == K {
        let (most, rest) = terms.values.values.as_chunks::<K>();
        assert!(rest.is_empty());
        Some(Vecs {
            bounds: terms.bounds,
            values: most,
        })
    }
    else { None }
}

/// Converts a term list of fixed width byte slices to a general term list.
pub fn downgrade<const K: usize>(terms: Lists<Vec<[u8; K]>>) -> Lists<Terms> {
    let strides: Strides = Strides {
        stride: (K as u64),
        length: terms.values.len() as u64,
        bounds: Vec::default(),
    };
    Vecs {
        bounds: terms.bounds,
        values: Vecs {
            bounds: strides,
            values: terms.values.into_flattened(),
        }
    }
}

pub trait Length {
    /// Number of facts in the container.
    fn len(&self) -> usize;
    /// True when the number of facts is zero.
    fn is_empty(&self) -> bool { self.len() == 0 }
}

pub trait Merge {
    /// Builds a container of facts present in `self` or `other`.
    fn merge(self, other: Self) -> Self;
}

/// A type that can contain and work with facts.
pub trait FactContainer : Length + Merge + Default + Sized + Clone {

    /// Applies an action to the facts, building the corresponding output.
    fn act_on(&self, action: &Action<String>) -> FactLSM<Self>;
    /// Joins `self` and `other` on the first `arity` columns, putting projected results in `builders`.
    fn join<'a>(&'a self, other: &'a Self, arity: usize, projection: &[usize]) -> FactLSM<Self> { self.join_many([other].into_iter(), arity, projection) }
    /// The subset of `self` whose facts do not start with any prefix in `others`.
    fn antijoin<'a>(self, _others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { unimplemented!() }
    /// The subset of `self` whose facts start with some prefix in `others`.
    fn semijoin<'a>(self, _others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a;

    /// Joins `self` and `others` on the first `arity` columns, putting projected results in `builders`.
    ///
    /// The default implementation processes `others` in order, but more thoughtful implementations exist.
    fn join_many<'a>(&'a self, others: impl Iterator<Item = &'a Self>, arity: usize, projection: &[usize]) -> FactLSM<Self> {
        let mut result = FactLSM::default();
        for other in others { result.extend(&mut self.join(other, arity, projection)); }
        result
    }
}

/// An evolving set of facts.
#[derive(Default)]
pub struct FactSet<F: FactContainer = FactCollection> {
    pub stable: FactLSM<F>,
    pub recent: F,
    pub to_add: FactLSM<F>,
}

impl<F: FactContainer> FactSet<F> {

    pub fn len(&self) -> usize { self.stable.layers.iter().map(|x| x.len()).sum::<usize>() + self.recent.len() }

    pub fn active(&self) -> bool {
        !self.recent.is_empty() || !self.to_add.layers.is_empty()
    }
    /// Moves `facts` into `self.to_add`, with no assumptions on `facts`.
    pub fn extend(&mut self, facts: impl IntoIterator<Item = F>) {
        for facts in facts.into_iter() {
            if !facts.is_empty() { self.to_add.push(facts); }
        }
    }

    pub fn advance(&mut self) {
        // Move recent into stable
        if !self.recent.is_empty() {
            self.stable.push(std::mem::take(&mut self.recent));
        }

        if let Some(to_add) = self.to_add.flatten() {
            // Tidy stable by an amount proportional to the work we are about to do.
            self.stable.tidy_through(2 * to_add.len());
            // Remove from to_add any facts already in stable.
            self.recent = to_add.antijoin(self.stable.contents());
        }
    }
}

/// A list of fact lists that double in length, each sorted and distinct.
#[derive(Clone, Default)]
pub struct FactLSM<F> {
    pub layers: Vec<F>,
}

impl<F: Merge + Length> FactLSM<F> {
    pub fn is_empty(&self) -> bool { self.layers.iter().all(|l| l.is_empty()) }
    pub fn push(&mut self, layer: F) {
        if !layer.is_empty() {
            self.layers.push(layer);
            self.tidy();
        }
    }

    pub fn extend(&mut self, other: &mut FactLSM<F>) {
        Extend::extend(&mut self.layers, other.layers.drain(..).filter(|f| !f.is_empty()));
        self.tidy();
    }

    pub fn contents(&self) -> impl Iterator<Item = &F> {
        self.layers.iter()
    }

    /// Flattens the layers into one layer, and takes it.
    pub fn flatten(&mut self) -> Option<F> {
        self.layers.sort_by_key(|x| x.len());
        self.layers.reverse();
        while self.layers.len() > 1 {
            let x = self.layers.pop().unwrap();
            let y = self.layers.pop().unwrap();
            self.layers.push(x.merge(y));
            self.layers.sort_by_key(|x| x.len());
            self.layers.reverse();
        }
        self.layers.pop()
    }

    /// Ensures layers double in size.
    fn tidy(&mut self) {
        self.layers.sort_by_key(|x| x.len());
        self.layers.reverse();
        while let Some(pos) = (1..self.layers.len()).position(|i| self.layers[i-1].len() < 2 * self.layers[i].len()) {
            while self.layers.len() > pos + 1 {
                let x = self.layers.pop().unwrap();
                let y = self.layers.pop().unwrap();
                self.layers.push(x.merge(y));
                self.layers.sort_by_key(|x| x.len());
                self.layers.reverse();
            }
        }
    }

    /// Ensures layers double in size and at most one is less than `size`.
    pub fn tidy_through(&mut self, size: usize) {
        self.layers.sort_by_key(|x| x.len());
        self.layers.reverse();
        while self.layers.len() > 1 && self.layers[self.layers.len()-2].len() < size {
            let x = self.layers.pop().unwrap();
            let y = self.layers.pop().unwrap();
            self.layers.push(x.merge(y));
            self.layers.sort_by_key(|x| x.len());
            self.layers.reverse();
        }
        self.tidy();
    }
}

impl<F> IntoIterator for FactLSM<F> {
    type Item = F;
    type IntoIter = std::vec::IntoIter<F>;
    fn into_iter(self) -> Self::IntoIter { self.layers.into_iter() }
}

impl<F: Length> From<F> for FactLSM<F> {
    fn from(item: F) -> Self {
        Self { layers: if item.is_empty() { Vec::default() } else { vec![item] } }
    }
}

pub mod radix_sort {

    /// Counts the number of bytes present for each
    #[inline(never)]
    pub fn count_bytes<R: Radixable>(data: &mut [R], filter: &[bool]) -> Vec<[usize;256]> {
        assert_eq!(filter.len(), R::WIDTH);
        let mut counts = vec![[0usize; 256]; R::WIDTH];
        for item in data.iter() {
            for index in 0 .. R::WIDTH {
                if filter[index] { counts[index][item.byte(index) as usize] += 1; }
            }
        }
        counts
    }

    /// Least-significant-byte radix sort, skipping identical bytes.
    #[inline(never)]
    pub fn lsb<R: Radixable>(data: &mut [R]) { lsb_range(data, 0, R::WIDTH) }

    pub fn lsb_range<R: Radixable>(data: &mut [R], lower: usize, upper: usize) {

        let mut filter = vec![false; R::WIDTH];
        for i in lower .. upper { filter[i] = true; }
        let mut counts = count_bytes(data, &filter);

        let mut temp = data.to_vec();
        let mut temp = &mut temp[..];
        let mut data = &mut data[..];

        for index in 0 .. R::WIDTH { if filter[index] { filter[index] = counts[index].iter().filter(|c| **c > 0).count() > 1; } }
        for index in (0 .. R::WIDTH).rev() {
            if filter[index] {
                let count = &mut counts[index];
                let mut total = 0;
                for i in 0 .. 256 {
                    std::mem::swap(&mut count[i], &mut total);
                    total += count[i];
                }
                for item in data.iter() {
                    let byte = item.byte(index) as usize;
                    temp[count[byte]] = *item;
                    count[byte] += 1;
                }
                std::mem::swap(&mut data, &mut temp);
            }
        }
        // We should perform an even number of copies to return to the input `data`.
        // TODO: if we don't need in-place sorting, we could swap or return `temp`.
        if filter.iter().filter(|b| **b).count() % 2 == 1 { temp.copy_from_slice(data); }
    }

    pub trait Radixable : Copy + std::fmt::Debug {
        const WIDTH: usize;
        fn byte(&self, index: usize) -> u8;
    }

    impl Radixable for u8 {
        const WIDTH: usize = 1;
        #[inline(always)] fn byte(&self, _index: usize) -> u8 { *self }
    }

    impl<const K: usize, R: Radixable> Radixable for [R; K] {
        const WIDTH: usize = K * R::WIDTH;
        #[inline(always)] fn byte(&self, index: usize) -> u8 {
            self[index/R::WIDTH].byte(index % R::WIDTH)
        }
    }

    pub fn msb2<R: Radixable + Ord>(data: &mut [R]) {
        msb_inner(data, 0);
    }

    /// MSB radix sort counts leading bytes, establishes offsets, and then repeatedly
    /// swaps elements from their current range to their target range. The swap moves
    /// elements to where they want to be, and collects elements that likely need the
    /// process repeated on their behalf.
    ///
    /// We can go one element at a time, or perform batches of swaps from one range.
    /// Batches of swaps out of multiple ranges has the potential to be confusing.
    pub fn msb_inner<R: Radixable + Ord>(data: &mut [R], digit: usize) {
        // Divert and return if the data are not long enough.
        // TODO: Don't accidentally sort by an associated payload.
        if data.len() <= 512 { data.sort_unstable() }
        // Only continue if bytes remain (TODO: non-constant widths).
        else if digit < R::WIDTH {
            let mut counts = vec![0usize; 256];
            for item in data.iter() { counts[item.byte(digit) as usize] += 1; }
            // If we have a byte common to everyone, just continue recursively.
            if counts.iter().filter(|c| **c > 0).count() == 1 { msb_inner(data, digit + 1); return; }
            let mut offsets = vec![0usize; 256];
            for index in 1 .. 256 { offsets[index] = offsets[index-1] + counts[index-1]; }
            // move forward through `data`, swapping elements to intended ranges.
            let mut cursors = offsets.clone();
            for byte in 0 .. 255 {      // Skip the last byte, as it ends up fine.
                while cursors[byte] < offsets[byte + 1] {
                    let bound = std::cmp::min(offsets[byte + 1], cursors[byte] + 32);
                    for index in cursors[byte] .. bound {
                        let data_byte = data[index].byte(digit) as usize;
                        data.swap(index, cursors[data_byte]);
                        cursors[data_byte] += 1;
                    }
                }
            }
            for byte in 0 .. 256 {
                let lower = offsets[byte];
                let upper = offsets.get(byte + 1).copied().unwrap_or(data.len());
                if upper - lower > 512 { msb_inner(&mut data[lower .. upper], digit + 1); }
                else { data[lower .. upper].sort_unstable(); }
            }
        }
    }


    pub fn msb<R: Radixable + Ord>(data: &mut [R]) {

        let size_thresh = 512;

        if data.len() <= size_thresh { data.sort_unstable(); return; }

        // Pre-allocate the buffers we'll want to use.
        let mut counts = vec![0usize; 256];
        let mut bounds = vec![0usize; 256];

        // Prepare our "stack" of recursive calls.
        let mut todo = vec![((0, data.len()), 0)];

        while let Some(((lower, upper), digit)) = todo.pop() {
            counts.fill(0);
            for item in data[lower .. upper].iter() { counts[item.byte(digit) as usize] += 1; }
            if counts.iter().filter(|c| **c > 0).count() == 1 {
                if digit + 1 < R::WIDTH { todo.push(((lower, upper), digit + 1)); }
            }
            else {
                bounds[0] = lower;
                for index in 0 .. 255 {
                    bounds[index + 1] = bounds[index] + counts[index];
                    counts[index] = bounds[index];
                }
                counts[255] = bounds[255];
                let mut writes = counts;

                for byte in 0 .. 255 {      // Skip the last byte, as it ends up fine.
                    while writes[byte] < bounds[byte + 1] {
                        for index in writes[byte] .. bounds[byte + 1] {
                            let data_byte = data[index].byte(digit) as usize;
                            data.swap(index, writes[data_byte]);
                            writes[data_byte] += 1;
                        }
                    }
                }
                if digit + 1 < R::WIDTH {
                    for byte in (0 .. 256).rev() {  // enqueue in reverse order.
                        let lower = bounds[byte];
                        let upper = bounds.get(byte + 1).copied().unwrap_or(upper);
                        if upper - lower < size_thresh { data[lower .. upper].sort_unstable() }
                        else { todo.push(((lower, upper), digit+1)); }
                    }
                }

                counts = writes;
            }
        }
    }
}

/// Increments `index` until just after the last element of `input` to satisfy `cmp`.
///
/// The method assumes that `cmp` is monotonic, never becoming true once it is false.
/// If an `upper` is supplied, it acts as a constraint on the interval of `input` explored.
#[inline(always)]
pub(crate) fn gallop<C: Index>(input: C, lower: &mut usize, upper: usize, mut cmp: impl FnMut(<C as Index>::Ref) -> bool) {
    // if empty input, or already >= element, return
    if *lower < upper && cmp(input.get(*lower)) {
        let mut step = 1;
        while *lower + step < upper && cmp(input.get(*lower + step)) {
            *lower += step;
            step <<= 1;
        }

        step >>= 1;
        while step > 0 {
            if *lower + step < upper && cmp(input.get(*lower + step)) {
                *lower += step;
            }
            step >>= 1;
        }

        *lower += 1;
    }
}
