//! Methods and types to support building and maintaining ordered sets of facts.

use std::collections::BTreeMap;
use columnar::{Container, Index, Len, Push};
use columnar::Vecs;

/// A `Vecs` using strided offsets.
pub type Lists<C> = Vecs<C, Strides>;

/// Use the `List` type to access an alternate columnar container.
pub type Fact = Vec<Vec<u8>>;
pub type Terms = Lists<Vec<u8>>;
pub type Facts = Lists<Terms>;
pub type Relations = BTreeMap<String, FactSet>;

#[derive(Default)]
pub struct FactSet {
    pub stable: FactLSM,
    pub recent: FactContainer,
    pub to_add: FactLSM,
}

impl FactSet {

    pub fn len(&self) -> usize { self.stable.layers.iter().map(|x| x.len()).sum::<usize>() + self.recent.len() }

    pub fn active(&self) -> bool {
        !self.recent.is_empty() || !self.to_add.layers.is_empty()
    }

    pub fn add_set(&mut self, facts: FactBuilder) {
        let mut facts = facts.finish();
        if !facts.layers.is_empty() {
            self.to_add.extend(&mut facts);
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
            let mut starts = vec![0; self.stable.layers.len()];
            let stable = &self.stable;
            self.recent = to_add.filter(move |x| {
                starts.iter_mut().zip(&stable.layers).all(|(start, layer)| {
                    crate::join::gallop::<Facts>(layer.borrow(), start, |y| y < x);
                    *start >= layer.len() || layer.borrow().get(*start) != x
                })
            });
        }
    }
}

pub use stride::Strides;
/// An internal container implementation that optimizes offsets when strided.
///
/// This module exists mostly because of limitations in `columnar`, and how
/// containers require an owned type that they are a container of. In this
/// case there is no good type that isn't already taken, or that seems to be.
mod stride {

    use std::ops::Deref;
    use columnar::{Container, Index, Len, Push, Clear, AsBytes, FromBytes};

    /// The first two integers describe a stride pattern, [stride, length].
    ///
    /// If the length is zero the collection is empty. The first `item` pushed
    /// always becomes the first list element. The next element is the number of
    /// items at position `i` whose value is `item * (i+1)`. After this comes
    /// the remaining entries in the bounds container.
    #[derive(Copy, Clone, Default)]
    pub struct Strides<BC = Vec<u64>> { pub bounds: BC }

    impl<BC: Deref<Target=[u64]>> Strides<BC> {
        #[inline(always)]
        pub fn bounds(&self, index: usize) -> (usize, usize) {
            let stride = self.bounds[0];
            let length = self.bounds[1];
            let index = index as u64;
            let lower = if index == 0 { 0 } else {
                let index = index - 1;
                if index < length { (index+1) * stride } else { self.bounds[(index - length + 2) as usize] }
            } as usize;
            let upper = if index < length { (index+1) * stride } else { self.bounds[(index - length + 2) as usize] } as usize;
            (lower, upper)
        }
        pub fn strided(&self) -> Option<usize> {
            if self.bounds.len() == 2 {
                Some(self.bounds[0] as usize)
            }
            else { None }
        }
    }

    impl Container for Strides {
        type Ref<'a> = u64;
        type Borrowed<'a> = Strides<&'a [u64]>;

        fn borrow<'a>(&'a self) -> Self::Borrowed<'a> { Strides { bounds: &self.bounds[..] } }
        /// Reborrows the borrowed type to a shorter lifetime. See [`Columnar::reborrow`] for details.
        fn reborrow<'b, 'a: 'b>(item: Self::Borrowed<'a>) -> Self::Borrowed<'b> where Self: 'a {
            Strides { bounds: item.bounds }
        }
        /// Reborrows the borrowed type to a shorter lifetime. See [`Columnar::reborrow`] for details.
        fn reborrow_ref<'b, 'a: 'b>(item: Self::Ref<'a>) -> Self::Ref<'b> where Self: 'a { item }
    }

    impl<'a> Push<&'a u64> for Strides { fn push(&mut self, item: &'a u64) { self.push(*item) } }
    impl Push<u64> for Strides { fn push(&mut self, item: u64) { self.push(item) } }
    impl Clear for Strides { fn clear(&mut self) { self.clear() } }

    impl<C: Len + Deref<Target=[u64]>> Len for Strides<C> { fn len(&self) -> usize { if self.bounds.len() < 2 { 0 } else { self.bounds[1] as usize + self.bounds.len() - 2 } } }
    impl<'a> Index for Strides<&'a [u64]> {
        type Ref = u64;
        fn get(&self, index: usize) -> Self::Ref {
            let stride = self.bounds[0];
            let length = self.bounds[1];
            let index = index as u64;
            if index < length { (index+1) * stride } else { self.bounds[(index - length + 2) as usize] }
        }
    }

    impl<'a, C: AsBytes<'a>> AsBytes<'a> for Strides<C> {
        #[inline(always)]
        fn as_bytes(&self) -> impl Iterator<Item=(u64, &'a [u8])> {
            self.bounds.as_bytes()
        }
    }
    impl<'a, C: FromBytes<'a>> FromBytes<'a> for Strides<C> {
        #[inline(always)]
        fn from_bytes(bytes: &mut impl Iterator<Item=&'a [u8]>) -> Self {
            Self { bounds: C::from_bytes(bytes) }
        }
    }

    impl Strides {
        #[inline(always)]
        pub fn push(&mut self, item: u64) {
            if self.bounds.len() < 2 { self.clear() }
            if self.bounds[..2] == [0,0] {
                self.bounds[0] = item;
                self.bounds[1] = 1;
            }
            else if self.bounds.len() > 2 {
                self.bounds.push(item);
            }
            else if item == self.bounds[0] * (self.bounds[1] + 1) {
                self.bounds[1] += 1;
            }
            else {
                self.bounds.push(item);
            }
        }
        #[inline(always)]
        pub fn clear(&mut self) {
            self.bounds.clear();
            self.bounds.push(0);
            self.bounds.push(0);
        }
    }
}

/// A sorted list of distinct facts.
#[derive(Clone, Default)]
pub struct FactContainer {
    pub ordered: Facts,
}

impl FactContainer {

    pub fn borrow(&self) -> <Facts as Container>::Borrowed<'_> { self.ordered.borrow() }

    pub fn len(&self) -> usize { self.borrow().len() }
    pub fn is_empty(&self) -> bool { self.borrow().is_empty() }

    fn filter(mut self, mut p: impl FnMut(<Facts as Container>::Ref<'_>) -> bool) -> FactContainer {
        let mut ordered = Facts::default();
        ordered.extend(self.borrow().into_index_iter().filter(|x| p(*x)));
        use columnar::Clear;
        self.ordered.clear();
        Self { ordered }
    }

    /// Merges two sorted deduplicated lists into one sorted deduplicated list.
    fn merge(mut self, mut other: Self) -> Self {
    
        if self.is_empty() { return other; }
        if other.is_empty() { return self; }
    
        // TODO: Test for appendability.
        // if self.borrow().last() < Some(other.borrow().get(0)) { println!("prepend"); }
        // if other.borrow().last() < Some(self.borrow().get(0)) { println!("postpend"); }

        // Attempt to sniff out a known pattern of fact and term sizes.
        // Clearly needs to be generalized, or something.
        if let (Some(2), Some(4)) = (self.ordered.bounds.strided(), self.ordered.values.bounds.strided()) {
            if let (Some(2), Some(4)) = (other.ordered.bounds.strided(), other.ordered.values.bounds.strided()) {

                if self.len() < other.len() { std::mem::swap(&mut self, &mut other); }

                self.ordered.bounds.bounds[1] += other.ordered.bounds.bounds[1];
                self.ordered.values.bounds.bounds[1] += other.ordered.values.bounds.bounds[1];
                Extend::extend(&mut self.ordered.values.values, other.ordered.values.values);

                let (more, less) = self.ordered.values.values.as_chunks_mut::<8>();
                assert!(less.is_empty());
                more.sort();
                let mut finger = 0;
                for i in 1 .. more.len() {
                    if more[i] != more[finger] {
                        finger += 1;
                        more[finger] = more[i];
                    }
                }
                finger += 1;
                self.ordered.values.values.truncate(8 * finger);

                self.ordered.bounds.clear();
                self.ordered.bounds.bounds[0] = 2;
                self.ordered.bounds.bounds[1] = finger as u64;
                self.ordered.values.bounds.clear();
                self.ordered.values.bounds.bounds[0] = 4;
                self.ordered.values.bounds.bounds[1] = 2 * finger as u64;

                return self;
            }
        }

        let ordered = Facts::merge::<true>(self.borrow(), other.borrow());
        Self { ordered }
    }

    fn from(facts: &mut Facts) -> Self {

        // Attempt to sniff out a known pattern of fact and term sizes.
        // Clearly needs to be generalized, or something.
        if let (Some(2), Some(4)) = (facts.bounds.strided(), facts.values.bounds.strided()) {
            let (more, less) = facts.values.values.as_chunks_mut::<8>();
            assert!(less.is_empty());
            more.sort_unstable();
            let mut finger = 0;
            for i in 1 .. more.len() {
                if more[i] != more[finger] {
                    finger += 1;
                    more[finger] = more[i];
                }
            }
            finger += 1;
            facts.values.values.truncate(8 * finger);
            facts.bounds.bounds[1] = finger as u64;
            facts.values.bounds.bounds[1] = 2 * finger as u64;

            return Self { ordered: std::mem::take(facts) }
        }

        facts.sort::<true>();
        Self { ordered: std::mem::take(facts) }
    }
}

#[derive(Clone, Default)]
pub struct FactBuilder {
    active: Facts,
    layers: FactLSM,
}

impl FactBuilder {
    pub fn push<I>(&mut self, item: I) where Facts: Push<I> {
        self.active.push(item);
        if self.active.len() > 1_000_000 {
            use columnar::Clear;
            self.layers.push(FactContainer::from(&mut self.active));
            self.active.clear();
        }
    }
    fn finish(mut self) -> FactLSM {
        self.layers.push(FactContainer::from(&mut self.active));
        self.layers
    }
}

/// A list of fact lists that double in length, each sorted and distinct.
#[derive(Clone, Default)]
pub struct FactLSM {
    layers: Vec<FactContainer>,
}

impl FactLSM {
    fn push(&mut self, layer: FactContainer) {
        if !layer.is_empty() {
            self.layers.push(layer);
            self.tidy();
        }
    }
    
    fn extend(&mut self, other: &mut FactLSM) {
        Extend::extend(&mut self.layers, other.layers.drain(..));
        self.tidy();
    }

    pub fn contents(&self) -> impl Iterator<Item = &FactContainer> {
        self.layers.iter()
    }

    /// Flattens the layers into one layer, and takes it.
    fn flatten(&mut self) -> Option<FactContainer> {
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
    fn tidy_through(&mut self, size: usize) {
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

/// A layered trie representation in columns.
pub mod forests {

    use columnar::{Container, Index};
    use crate::facts::Lists;

    /// A sequence of `[T]` ordered lists, each acting as a map.
    ///
    /// For each integer input, corresponding to a path to a tree node,
    /// the node forks by way of the associated list of `T`, where each
    /// child has an index that can be used in a next layer (or not!).
    pub struct Layer<C: Container> { pub list: Lists<C> }

    /// A sequence of layers, where the outputs in one match the inputs in the next.
    ///
    /// Represents a layered trie, where each layer introduces a new "symbol".
    pub struct Forest<C: Container> { pub layers: Vec<Layer<C>> }

    /// A report we would expect to see in a sequence about two layers.
    ///
    /// A sequence of these reports reveal an ordered traversal of the keys
    /// of two layers, with ranges exclusive to one, ranges exclusive to the
    /// other, and individual elements (not ranges) common to both.
    #[derive(Copy, Clone)]
    pub enum Report {
        /// Range of indices in this input.
        This(usize, usize),
        /// Range of indices in that input.
        That(usize, usize),
        /// Matching indices in both inputs.
        Both(usize, usize),
    }

    impl<C: for<'a> Container<Ref<'a>: Ord>> Forest<C> {

        /// Create a forest from an ordered list of `[C::Ref]` of a common length.
        pub fn form<'a>(sorted: impl Iterator<Item = <Lists<C> as Container>::Ref<'a>>) -> Self {
            let mut sorted = sorted.peekable();
            if let Some(prev) = sorted.next() {
                let arity = prev.len();
                let mut layers = (0 .. arity).map(|_| Layer { list: Lists::<C>::default() }).collect::<Vec<_>>();

                for (index, layer) in layers.iter_mut().enumerate() { layer.list.values.push(prev.get(index)); }

                // For each new item, we assess the first coordinate it diverges from the prior,
                // then seal subsequent lists and push all values from this coordinate onward.
                for item in sorted {
                    let mut differs = false;
                    for (index, layer) in layers.iter_mut().enumerate().take(arity) {
                        let len = layer.list.values.len();
                        if differs {  layer.list.bounds.push(len as u64); }
                        differs |= C::reborrow_ref(item.get(index)) != layer.list.values.borrow().get(len-1);
                        if differs { layer.list.values.push(C::reborrow_ref(item.get(index))); }
                    }
                }
                // Seal the last lists with their bounds.
                for layer in layers.iter_mut() { layer.list.bounds.push(layer.list.values.len() as u64); }

                Self { layers }
            }
            else {
                println!("Formed an empty forest");
                Self { layers: Vec::default() }
            }
        }

        /// For each layer a map of its key dispositions for each output.
        ///
        /// Each element in the result spells out the key ordering in that layer.
        /// The intent is that this map allows one to navigate directly to matching
        /// records, and conduct further investigation without much more thinking.
        pub fn survey(&self, other: &Self) -> Vec<Vec<Report>> {
            let mut results = Vec::with_capacity(self.layers.len());
            if let (Some(l0), Some(l1)) = (self.layers.first(), other.layers.first()) {
                results.push(l0.survey(l1, &[Report::Both(0, 0)]));
                for (layer0, layer1) in self.layers.iter().zip(other.layers.iter()).skip(1) {
                    let last = results.last().unwrap();
                    results.push(layer0.survey(layer1, last));
                }
            }
            results
        }

    }

    impl<C: for<'a> Container<Ref<'a>: Ord>> Layer<C> {
        /// Given an input map, enrich the contended areas with further detail.
        ///
        /// Produces an output map fit for consumption by a next layer.
        pub fn survey(&self, other: &Self, inbound: &[Report]) -> Vec<Report> {

            use columnar::Container;
            let list0 = self.list.borrow();
            let list1 = other.list.borrow();

            let mut result = Vec::default();
            for report in inbound.iter() {

                // We are only interested in contended areas.
                if let Report::Both(index0, index1) = report {

                    // Fetch the bounds from the layers.
                    let (mut lower0, upper0) = list0.bounds.bounds(*index0);
                    let (mut lower1, upper1) = list1.bounds.bounds(*index1);

                    // Scour the intersecting range for matches.
                    while lower0 < upper0 && lower1 < upper1 {
                        let val0 = list0.values.get(lower0);
                        let val1 = list1.values.get(lower1);
                        match val0.cmp(&val1) {
                            std::cmp::Ordering::Less => {
                                let start = lower0;
                                crate::join::gallop::<C>(list0.values, &mut lower0, |x| x < val1);
                                result.push(Report::This(start, lower0));
                            },
                            std::cmp::Ordering::Equal => {
                                result.push(Report::Both(lower0, lower1));
                                lower0 += 1;
                                lower1 += 1;
                            },
                            std::cmp::Ordering::Greater => {
                                let start = lower1;
                                crate::join::gallop::<C>(list1.values, &mut lower1, |x| x < val0);
                                result.push(Report::That(start, lower1));
                            },
                        }
                    }
                    if lower0 < upper0 { result.push(Report::This(lower0, upper0))}
                    if lower1 < upper1 { result.push(Report::This(lower1, upper1))}
                }
            }
            result
        }
    }
}

/// Least-significant-digit radix sort, skipping identical bytes.
fn _radix_sort<const K: usize>(slices: &mut [[u8; K]]) {

    let mut histogram = [[0usize; 256]; K];
    for slice in slices.iter() {
        for (index, byte) in slice.iter().enumerate() {
            histogram[index][*byte as usize] += 1;
        }
    }
    let mut buffer = vec![[0u8; K]; slices.len()];
    let mut borrow = &mut buffer[..];
    let mut slices = &mut slices[..];

    let indexes = histogram.iter_mut().enumerate().filter(|(_,h)| h.iter().filter(|c| **c > 0).count() > 1).collect::<Vec<_>>();
    for (round, hist) in indexes.iter().rev() {
        let mut counts = [0usize; 256];
        for i in 1 .. 256 { counts[i] = counts[i-1] + hist[i-1]; }
        for slice in slices.iter() {
            let byte = slice[*round] as usize;
            borrow[counts[byte]] = *slice;
            counts[byte] += 1;
        }
        std::mem::swap(&mut slices, &mut borrow);
    }
    // TODO: we could dedup as part of this scan.
    if indexes.len() % 2 == 1 { slices.copy_from_slice(borrow); }
}

impl <C: for<'a> Container<Ref<'a>: Ord>> Sorted for C { }

/// Methods on containers with orderable items.
///
/// When specified, the `const DEDUP: usize` argument indicates that the inputs
/// should be considered deduplicated, and the result should be deduplicated as
/// well. Essentially, that repeats across collections should be suppressed.
pub trait Sorted : for<'a> Container<Ref<'a>: Ord> {

    /// Sort the container in place; optionally deduplicate.
    fn sort<const DEDUP: bool>(&mut self) {
        let mut result = Self::default();
        let borrowed = self.borrow();
        let mut items = borrowed.into_index_iter().collect::<Vec<_>>();
        items.sort();
        if DEDUP { items.dedup(); }
        result.extend(items);
        *self = result;
    }

    /// Merge two borrowed variants into an owned container.
    fn merge<'a, const DEDUP: bool>(this: Self::Borrowed<'a>, that: Self::Borrowed<'a>) -> Self {

        use crate::join::gallop;

        let mut merged = Self::default();

        let mut index0 = 0;
        let mut index1 = 0;

        while index0 < this.len() && index1 < that.len() {
            let val0 = this.get(index0);
            let val1 = that.get(index1);
            match val0.cmp(&val1) {
                std::cmp::Ordering::Less => {
                    let lower = index0;
                    // advance `index1` while strictly less than `pos2`.
                    gallop::<Self>(this, &mut index0, |x| x < val1);
                    merged.extend_from_self(this, lower .. index0);
                }
                std::cmp::Ordering::Equal => {
                    merged.extend_from_self(this, index0 .. index0 + 1);
                    if !DEDUP {
                        // Use `that`, in case of some weird `Ord` impl.
                        merged.extend_from_self(that, index1 .. index1 + 1);
                    }
                    index0 += 1;
                    index1 += 1;
                }
                std::cmp::Ordering::Greater => {
                    let lower = index1;
                    // advance `index1` while strictly less than `pos2`.
                    gallop::<Self>(that, &mut index1, |x| x < val0);
                    merged.extend_from_self(that, lower .. index1);
                }
            }
        }

        merged.extend_from_self(this, index0 .. this.len());
        merged.extend_from_self(that, index1 .. that.len());

        merged
    }

    /// Merges many sorted deduplicated lists into one sorted deduplicated list.
    fn multiway_merge<const K: usize, const DEDUP: bool>(many: &[Self; K]) -> Self {

        let mut merged = Self::default();

        let mut iters: [_; K] =
        many.iter()
            .map(|x| x.borrow().into_index_iter().peekable())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap_or_else(|_| panic!());

        // TODO: Gallop a bit and see if there is an interval to `extend_from_self`.
        while let Some((_min, idx)) = iters.iter_mut().enumerate().filter_map(|(i,x)| x.peek().map(|x| (x,i))).min() {
            let min = iters[idx].next().unwrap();
            if DEDUP { merged.push(min); }
            for iter in iters.iter_mut() {
                if iter.peek() == Some(&min) {
                    if !DEDUP { merged.push(min); }
                    iter.next();
                }
            }
        }

        merged
    }
}
