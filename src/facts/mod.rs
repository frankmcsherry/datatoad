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
pub type Forms = BTreeMap<Action<Vec<u8>>, FactSet<FactCollection>>;

impl Relations {
    pub fn get(&self, name: &str) -> Option<&FactSet<FactCollection>> {
        self.relations.get(name).map(|(base, _)| base)
    }
    pub fn get_mut(&mut self, name: &str) -> Option<&mut FactSet<FactCollection>> {
        self.relations.get_mut (name).map(|(base, _)| base)
    }
    pub fn entry(&mut self, atom: &crate::types::Atom) -> &mut FactSet<FactCollection> {
        &mut self.relations.entry(atom.name.clone()).or_default().0
    }
    pub fn advance(&mut self, comms: &mut crate::comms::Comms) {
        for (facts, transforms) in self.relations.values_mut() {
            facts.advance();
            for (action, transform) in transforms.iter_mut() {
                transform.stable.extend(transform.recent.take());
                let mut acted_on = if let Some(recent) = facts.recent.as_ref() { recent.act_on(action) } else { FactLSM::default() };
                comms.exchange(&mut acted_on);
                if let Some(recent) = acted_on.flatten() {
                    // Non-permutations need to be deduplicated against existing facts.
                    transform.recent = if !action.is_permutation() { recent.antijoin(transform.stable.contents()).flatten() } else { Some(recent) };
                }
            }
        }
    }
    pub fn active(&self) -> bool {
        self.relations.values().any(|x| x.0.active())
    }
    pub fn list(&self) {
        let max_name_len = self.relations.keys().map(|name| name.len()).max().unwrap_or(0);
        for (name, facts) in self.relations.iter() {
            print!("{:>10} {:<2$} [forms: Identity", facts.0.len(), name, max_name_len);
            for (action, _facts) in facts.1.iter() { print!(", {:?}", action); }
            println!("]");
            for forest in facts.0.stable.contents() {
                print!("\t");
                for column in forest.layers.iter() {
                    use columnar::AsBytes;
                    print!("[ ");
                    for (_, bytes) in column.list.borrow().as_bytes() { print!("{:?} ", bytes.len()); }
                    print!("]\t");
                }
                println!();
            }
        }
    }

    /// Ensures that we have an entry for this name and the associated action.
    pub fn ensure_action(&mut self, comms: &mut crate::comms::Comms, name: &str, action: &Action<Vec<u8>>){
        let (base, transforms) = self.relations.entry(name.to_string()).or_default();
        if !action.is_identity() && !transforms.contains_key(action) {
            let mut fact_set = FactSet::default();
            // TODO: Can be more elegant if we see all columns retained, as it means no duplication.
            for layer in base.stable.contents() {
                fact_set.stable.extend(layer.act_on(action));
            }
            comms.exchange(&mut fact_set.stable);
            // Flattening deduplicates, which may be necessary as `action` may introduce collisions
            // across LSM layers.
            if let Some(stable) = fact_set.stable.flatten() { fact_set.stable.push(stable); }
            let mut acted_on = if let Some(recent) = base.recent.as_ref() { recent.act_on(action) } else { FactLSM::default() };
            comms.exchange(&mut acted_on);
            if let Some(recent) = acted_on.flatten() {
                fact_set.recent = recent.antijoin(fact_set.stable.contents()).flatten();
            }
            transforms.insert(action.clone(), fact_set);
        }
    }

    /// Gets a fact set by name, and by an action that is applied to them.
    ///
    /// This will only be non-`None` once `ensure_action` has been called with this name and action.
    pub fn get_action(&self, name: &str, action: &Action<Vec<u8>>) -> Option<&FactSet<FactCollection>> {
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

/// A type with a specific number of columns.
pub trait Arity {
    /// The number of columns.
    fn arity(&self) -> usize;
}

/// A type that can contain and work with facts.
pub trait FactContainer : Length + Merge + Arity + Sized + Clone {

    /// Applies an action to the facts, building the corresponding output.
    fn act_on(&self, action: &Action<Vec<u8>>) -> FactLSM<Self>;
    /// The subset of `self` whose facts do not start with any prefix in `others`.
    fn antijoin<'a>(self, _others: impl Iterator<Item = &'a Self>) -> FactLSM<Self> where Self: 'a;
    /// The subset of `self` whose facts start with some prefix in `others`.
    fn semijoin<'a>(self, _others: impl Iterator<Item = &'a Self>) -> FactLSM<Self> where Self: 'a;

    /// Joins `self` and `others` on the first `arity` columns, putting projected results in `builders`.
    ///
    /// The default implementation processes `others` in order, but more thoughtful implementations exist.
    fn join_many<'a>(&'a self, others: impl Iterator<Item = &'a Self>, arity: usize, projection: &[usize], conduit: crate::comms::Conduit) -> FactLSM<Self>;
}

/// An evolving set of facts.
pub struct FactSet<F: FactContainer = FactCollection> {
    pub stable: FactLSM<F>,
    pub recent: Option<F>,
    pub to_add: FactLSM<F>,
}

impl<F: FactContainer> Default for FactSet<F> { fn default() -> Self { Self { stable: Default::default(), recent: None, to_add: Default::default() } } }

impl<F: FactContainer> FactSet<F> {

    pub fn len(&self) -> usize { self.stable.layers.iter().chain(self.recent.as_ref()).map(|x| x.len()).sum::<usize>() }

    pub fn active(&self) -> bool {
        self.recent.is_some() || !self.to_add.layers.is_empty()
    }
    /// Moves `facts` into `self.to_add`, with no assumptions on `facts`.
    pub fn extend(&mut self, facts: impl IntoIterator<Item = F>) { self.to_add.extend(facts); }

    pub fn advance(&mut self) {
        // Move recent into stable
        self.stable.extend(self.recent.take());

        if let Some(to_add) = self.to_add.flatten() {
            // Tidy stable by an amount proportional to the work we are about to do.
            self.stable.tidy_through(2 * to_add.len());
            // Remove from to_add any facts already in stable.
            self.recent = to_add.antijoin(self.stable.contents()).flatten();
        }
    }
}

/// A potentially empty list of non-empty fact containers, each sorted and distinct.
///
/// The LSM (log-structured merge) structure merges any containers whose counts are within a factor of two.
/// This ensures that there are at most a logarithmic number of containers, and that the number of contained
/// facts is at most twice the number of distinct facts (the largest layer is all distinct facts, and the
/// other layers telescope to sum to at most this).
///
/// The `FactLSM` does not have a specific arity or type itself, but it will check that introduced containers
/// match other present containers, and panic if this occurs.
#[derive(Clone)]
pub struct FactLSM<F> { layers: Vec<F> }

impl<F> Default for FactLSM<F> { fn default() -> Self { Self { layers: Default::default() } } }

impl<F: Merge + Length + Arity> FactLSM<F> {
    pub fn is_empty(&self) -> bool {
        // Each container is meant to be non-empty, making the LSM non-empty when `self.layers` is.
        for layer in self.layers.iter() { assert!(!layer.is_empty()); }
        self.layers.is_empty()
    }
    pub fn push(&mut self, layer: F) {
        if !layer.is_empty() {
            self.layers.push(layer);
            self.tidy();
        }
    }

    pub fn contents(&self) -> impl Iterator<Item = &F> { self.layers.iter() }

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
        if !self.layers.is_empty() { self.layers.iter().for_each(|l| assert_eq!(l.arity(), self.layers[0].arity())) }
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

impl<F: Merge+Length+Arity> Extend<F> for FactLSM<F> {
    fn extend<T: IntoIterator<Item=F>>(&mut self, iter: T) {
        self.layers.extend(iter.into_iter().filter(|f| !f.is_empty()));
        self.tidy();
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

    /// LSB radix sorting using "pages" rather than contiguous memory.
    ///
    /// Rather than expect the input in a large contiguous `[R]` we instead accept a sequence of smaller arrays (pages).
    /// We are able to fully drain pages as we process them, repurpose empty pages, and also to populate 256 independent
    /// pages for each byte without knowing their absolute offset in the larger array.
    ///
    /// This allows us to incrementally allocate data to sort, maintain a fixed working set as we sort, and to drain the
    /// results incrementally on the way out. This avoids ever requiring twice as much memory as needs to be sorted.
    ///
    /// This approach also allows us to skip counting each byte pattern at each position, and we only really benefit from
    /// knowing each position where there are at least two distinct byte patterns, which is easier to determine (maybe SIMD).
    pub use lsb_pages::{PageBuilder, lsb_paged};
    mod lsb_pages {

        use super::Radixable;

        /// A builder for the paged representation of a sequence of `R` values.
        ///
        /// The intended lifecycle is to create a new `PageBuilder` with a page size (try 1024), then repeatedly call `push`
        /// with items, and finally call `done` to extract the list of pages and the bits that identify avoidable indexes.
        /// One should likely call `lsb_paged` with a reference to the list of pages and the bits, perhaps after any further
        /// masking of the bits that may be important (e.g. masking away "payload" bytes).
        pub struct PageBuilder<R: Radixable, const W: usize> {
            size: usize,        // page size.
            diff: [bool; W],    // for each position, have we seen two distinct bytes.
            byte: [u8; W],      // for each position, the most recently seen byte.
            data: Vec<Vec<R>>,  // sequence of full pages.
            page: Vec<R>,       // partial page we are assembling; at most `self.size` in length.
        }
        impl<R: Radixable, const W: usize> PageBuilder<R, W> {
            /// Create a new `Self` with a specific page size.
            pub fn new(size: usize) -> Self { Self { size, diff: [false; W], byte: [0u8; W], data: Default::default(), page: Vec::with_capacity(size) }}
            pub fn push(&mut self, item: R) {
                for index in 0 .. W { self.diff[index] |= self.byte[index] != item.byte(index); self.byte[index] = item.byte(index); }
                self.page.push(item);
                if self.page.len() >= self.size { self.data.push(std::mem::replace(&mut self.page, Vec::with_capacity(self.size))); }
            }
            pub fn done(mut self) -> (Vec<Vec<R>>, [bool;W]) { if !self.page.is_empty() { self.data.push(std::mem::take(&mut self.page)); } (self.data, self.diff) }
        }

        /// A page-oriented LSB radix sort, which consumes pages of `data` and shuffles into 256 streams of pages that we reassemble.
        ///
        /// The `data` pages should each be the same capacity, though they need not all be equally full.
        /// The `filter` argument should be as large as `R::WIDTH`, and each position should indicate whether we should sort by this index.
        /// The sorting happens in the reverse direction, from largest index to smallest, as this is a LSB (bottom-up) radix sort.
        ///
        /// The capacity of the first page in `data` will be used as the capacity for all pages; it is best if these capacities are consistent.
        /// The drained pages from `data` will be re-used, and if their capacities vary there may be either reallocations or unused capacity.
        pub fn lsb_paged<R: Radixable>(data: &mut Vec<Vec<R>>, filter: &[bool]) {

            if data.is_empty() { return; }

            let page_len = data[0].capacity();

            let mut free: Vec<Vec<R>> = Vec::default();
            let mut full: [Vec<Vec<R>>; 256] = (0 .. 256).map(|_| Default::default()).collect::<Vec<_>>().try_into().unwrap();
            let mut part: [Vec<R>; 256] = (0 .. 256).map(|_| Vec::with_capacity(page_len)).collect::<Vec<_>>().try_into().unwrap();

            for index in (0 .. R::WIDTH).rev() {
                if filter[index] {
                    for mut page in data.drain(..) {
                        for item in page.drain(..) {
                            let byte = item.byte(index) as usize;
                            part[byte].push(item);
                            if part[byte].len() >= page_len {
                                full[byte].push(std::mem::replace(&mut part[byte], free.pop().unwrap_or_else(|| Vec::with_capacity(page_len))));
                            }
                        }
                        free.push(page);
                    }

                    // Drain each `part` into `full`, and drain `full` into `data`.
                    for byte in 0 .. 256 {
                        // We want to append `full[byte]` then `part[byte]`.
                        data.append(&mut full[byte]);
                        // We may be able to copy part of `part[byte]` in rather than append the whole page.
                        if let Some(last) = data.last_mut() {
                            // Not helpful if there is another full page immediately afterwards.
                            if last.len() < page_len && (byte == 255 || full[byte].is_empty()) {
                                let to_drain = std::cmp::min(page_len - last.len(), part[byte].len());
                                last.extend(part[byte].drain(0.. to_drain));
                            }
                        }
                        if !part[byte].is_empty() {
                            data.push(std::mem::replace(&mut part[byte], free.pop().unwrap_or_else(|| Vec::with_capacity(page_len))));
                        }
                    }
                }
            }
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
