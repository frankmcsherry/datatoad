//! Methods and types to support building and maintaining ordered sets of facts.

use std::collections::BTreeMap;
use columnar::{Container, Index, Len, Push};
use columnar::Vecs;
use columnar::primitive::offsets::Strides;

pub mod list;
pub mod trie;

/// A `Vecs` using strided offsets.
pub type Lists<C> = Vecs<C, Strides>;

/// Use the `List` type to access an alternate columnar container.
pub type Fact = Vec<Vec<u8>>;
pub type Terms = Lists<Vec<u8>>;
pub type Facts = Lists<Terms>;
pub type Relations = BTreeMap<String, FactSet<FactCollection>>;

// pub use list::FactList as FactCollection;
pub use trie::Forest;
pub type FactCollection = Forest<Terms>;

/// A type that can contain and work with facts.
pub trait FactContainer : Default + Sized {
    /// Forms a container from a list of facts.
    ///
    /// The mutable reference allows us to efficiently sort `facts` if it has the right shape.
    /// The method is not expected to consume or remove `facts`, and the caller should expect
    /// to be able to reuse the resources after the call, without needing to reallocate.
    fn form(facts: &mut Facts) -> Self;
    /// Number of facts in the container.
    fn len(&self) -> usize;
    /// True when the number of facts is zero.
    fn is_empty(&self) -> bool { self.len() == 0 }
    /// Applies an action to each contained fact.
    fn apply<'a>(&'a self, action: impl FnMut(&[<Terms as Container>::Ref<'a>]));
    /// Joins `self` and `other` on the first `arity` columns, putting projected results in `builders`.
    fn join<'a>(&'a self, other: &'a Self, arity: usize, projections: &[&[Result<usize, String>]]) -> Vec<FactLSM<Self>> ;
    /// Builds a container of facts present in `self` but not in any of `others`.
    fn except<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a;
    /// Builds a container of facts present in `self` or `other`.
    fn merge(self, other: Self) -> Self;
}

/// An evolving set of facts.
#[derive(Default)]
pub struct FactSet<F: FactContainer> {
    pub stable: FactLSM<F>,
    pub recent: F,
    pub to_add: FactLSM<F>,
}

impl<F: FactContainer> FactSet<F> {

    pub fn len(&self) -> usize { self.stable.layers.iter().map(|x| x.len()).sum::<usize>() + self.recent.len() }

    pub fn active(&self) -> bool {
        !self.recent.is_empty() || !self.to_add.layers.is_empty()
    }

    pub fn add_set(&mut self, mut facts: FactLSM<F>) {
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
            self.recent = to_add.except(self.stable.contents());
        }
    }
}

/// A staging ground for developing facts.
#[derive(Clone, Default)]
pub struct FactBuilder<F: FactContainer> {
    active: Facts,
    layers: FactLSM<F>,
}

impl<F: FactContainer> FactBuilder<F> {
    pub fn push<I>(&mut self, item: I) where Facts: Push<I> {
        self.active.push(item);
        if self.active.len() > 1_000_000 {
            use columnar::Clear;
            self.layers.push(FactContainer::form(&mut self.active));
            self.active.clear();
        }
    }
    pub fn finish(mut self) -> FactLSM<F> {
        self.layers.push(FactContainer::form(&mut self.active));
        self.layers
    }
}

/// A list of fact lists that double in length, each sorted and distinct.
#[derive(Clone, Default)]
pub struct FactLSM<F: FactContainer> {
    layers: Vec<F>,
}

impl<F: FactContainer> FactLSM<F> {
    fn push(&mut self, layer: F) {
        if !layer.is_empty() {
            self.layers.push(layer);
            self.tidy();
        }
    }

    pub fn extend(&mut self, other: &mut FactLSM<F>) {
        Extend::extend(&mut self.layers, other.layers.drain(..));
        self.tidy();
    }

    pub fn contents(&self) -> impl Iterator<Item = &F> {
        self.layers.iter()
    }

    /// Flattens the layers into one layer, and takes it.
    fn flatten(&mut self) -> Option<F> {
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
                    gallop(this, &mut index0, this.len(), |x| x < val1);
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
                    gallop(that, &mut index1, that.len(), |x| x < val0);
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
