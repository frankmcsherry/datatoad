//! Methods and types to support building and maintaining ordered sets of facts.

use std::collections::BTreeMap;
use columnar::{Container, Index, Len, Push};
use columnar::Vecs;
use columnar::primitive::offsets::Strides;

use crate::types::Action;

pub mod list;
pub mod trie;

/// A `Vecs` using strided offsets.
pub type Lists<C> = Vecs<C, Strides>;

/// Use the `List` type to access an alternate columnar container.
pub type Fact = Vec<Vec<u8>>;
pub type Terms = Lists<Vec<u8>>;
pub type Facts = Lists<Terms>;

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
    relations: BTreeMap<String, (FactSet<FactCollection>, BTreeMap<Action<String>, FactSet<FactCollection>>)>,
}

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
                if let Some(recent) = facts.recent.act_on(action).flatten() {
                    transform.recent = recent.except(transform.stable.contents());
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
                fact_set.recent = recent.except(fact_set.stable.contents());
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
pub fn upgrade_hint(terms: <Lists<Terms> as Container>::Borrowed<'_>) -> Option<u64> {
    terms.values.bounds.strided()
}

/// Attempts to recast a general term list as one of fixed width byte slices.
pub fn upgrade<'a, const K: usize>(terms: <Lists<Terms> as Container>::Borrowed<'a>) -> Option<<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>> {
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

/// Sorts and potentially deduplicates
pub fn sort<const DEDUP: bool>(facts: &mut Facts) {
    // Attempt to sniff out a known pattern of fact and term sizes.
    // Clearly needs to be generalized, or something.

    let terms = facts.bounds.strided();
    let bytes = facts.values.bounds.strided();

    let width = terms.and_then(|w0| bytes.map(|w1| w0 * w1));
    match width {
        Some(8)  => sort_help::<DEDUP,  8>(facts, terms.unwrap()),
        Some(12) => sort_help::<DEDUP, 12>(facts, terms.unwrap()),
        Some(16) => sort_help::<DEDUP, 16>(facts, terms.unwrap()),
        _ => {
            use crate::facts::Sorted;
            facts.sort::<DEDUP>();
        }
    }
}

#[inline(never)]
fn sort_help<const DEDUP: bool, const W: usize>(facts: &mut Facts, terms: u64) {
    let (more, less) = facts.values.values.as_chunks_mut::<W>();
    assert!(less.is_empty());
    // more.sort();
    // more.sort_unstable();
    radix_sort::lsb(more);
    // radix_sort::msb(more);
    if DEDUP {
        let mut finger = 0;
        for i in 1 .. more.len() {
            if more[i] != more[finger] {
                finger += 1;
                more[finger] = more[i];
            }
        }
        finger += 1;
        // Popping back out to referencing bytes.
        facts.values.values.truncate(W * finger);
        facts.bounds.length = finger as u64;
        facts.values.bounds.length = terms * finger as u64;
    }
}

pub trait Form {
    /// Forms a container from a list of facts.
    ///
    /// The mutable reference allows us to efficiently sort `facts` if it has the right shape.
    /// The method is not expected to consume or remove `facts`, and the caller should expect
    /// to be able to reuse the resources after the call, without needing to reallocate.
    fn form(facts: &mut Facts) -> Self;
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
pub trait FactContainer : Form + Length + Merge + Default + Sized {
    /// Applies an action to each contained fact.
    fn apply<'a>(&'a self, action: impl FnMut(&[<Terms as Container>::Ref<'a>]));
    /// Joins `self` and `other` on the first `arity` columns, putting projected results in `builders`.
    fn join<'a>(&'a self, other: &'a Self, arity: usize, projections: &[&[Result<usize, String>]]) -> Vec<FactLSM<Self>> ;
    /// Builds a container of facts present in `self` but not in any of `others`.
    fn except<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a;

    /// The subset of `self` whose facts do not start with any prefix in `others`.
    fn antijoin<'a>(self, _others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { unimplemented!() }
    /// The subset of `self` whose facts start with some prefix in `others`.
    fn semijoin<'a>(self, _others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { unimplemented!() }
    /// Applies an action to the set of facts, building the corresponding output.
    fn act_on(&self, action: &Action<String>) -> FactLSM<Self> {
        // This has the potential to be efficiently implemented, by capturing and unfolding the corresponding columns,
        // filtering and sorting as appropriate, and then rebuilding. Much more structured than `apply`, who is only
        // provided a closure.
        let mut builder = FactBuilder::default();
        self.apply(|row| {
            let lit_filtered = action.lit_filter.iter().all(|(index, value)| row[*index].as_slice() == value.as_bytes());
            let var_filtered = action.var_filter.iter().all(|columns| columns[1..].iter().all(|c| row[*c] == row[columns[0]]));
            if lit_filtered && var_filtered {
                builder.push(action.projection.iter().map(|c| {
                    match c {
                        Ok(col) => row[*col].as_slice(),
                        Err(lit) => lit.as_bytes(),
                    }
                }))
            }
        });
        builder.finish()
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
pub struct FactBuilder<F: Merge> {
    active: Facts,
    layers: FactLSM<F>,
}

impl<F: Form + Merge + Length> FactBuilder<F> {
    pub fn push<I>(&mut self, item: I) where Facts: Push<I> {
        self.active.push(item);
        if self.active.len() > 1_000_000 {
            use columnar::Clear;
            self.layers.push(Form::form(&mut self.active));
            self.active.clear();
        }
    }
    pub fn finish(mut self) -> FactLSM<F> {
        self.layers.push(Form::form(&mut self.active));
        self.layers
    }
}

/// A list of fact lists that double in length, each sorted and distinct.
#[derive(Clone, Default)]
pub struct FactLSM<F> {
    pub layers: Vec<F>,
}

impl<F: Merge + Length> FactLSM<F> {
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

pub mod radix_sort {

    /// Least-significant-byte radix sort, skipping identical bytes.
    #[inline(never)]
    pub fn lsb<R: Radixable>(data: &mut [R]) {

        let mut histogram = vec![[0usize; 256]; R::WIDTH];
        for item in data.iter() {
            for index in 0 .. R::WIDTH {
                histogram[index][item.byte(index) as usize] += 1;
            }
        }
        let mut temp = data.to_vec();
        let mut temp = &mut temp[..];
        let mut data = &mut data[..];

        let indexes = histogram.iter_mut().enumerate().filter(|(_,h)| h.iter().filter(|c| **c > 0).count() > 1).collect::<Vec<_>>();
        for (round, hist) in indexes.iter().rev() {
            let mut counts = [0usize; 256];
            for i in 1 .. 256 { counts[i] = counts[i-1] + hist[i-1]; }
            for item in data.iter() {
                let byte = item.byte(*round) as usize;
                temp[counts[byte]] = *item;
                counts[byte] += 1;
            }
            std::mem::swap(&mut data, &mut temp);
        }
        // TODO: we could dedup as part of this scan.
        if indexes.len() % 2 == 1 { temp.copy_from_slice(data); }
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
