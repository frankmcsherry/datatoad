//! A layered trie representation in columns.

use columnar::{Container, Index, Len, Vecs};
use crate::facts::{Facts, FactBuilder, FactContainer, FactLSM, Lists, Terms};

/// A sequence of `[T]` ordered lists, each acting as a map.
///
/// For each integer input, corresponding to a path to a tree node,
/// the node forks by way of the associated list of `T`, where each
/// child has an index that can be used in a next layer (or not!).
#[derive(Clone, Debug, Default)]
pub struct Layer<C> { pub list: Lists<C> }

impl<C: Container> Layer<C> {
    fn borrow(&self) -> <Lists<C> as Container>::Borrowed<'_> { self.list.borrow() }
}

/// A sequence of layers, where the outputs in one match the inputs in the next.
///
/// Represents a layered trie, where each layer introduces a new "symbol".
#[derive(Clone, Debug, Default)]
pub struct Forest<C> { pub layers: Vec<Layer<C>> }

impl<C: Container> Forest<C> {
    fn borrow<'a>(&'a self) -> Vec<<Lists<C> as Container>::Borrowed<'a>> {
        self.layers.iter().map(|x| x.list.borrow()).collect::<Vec<_>>()
    }
}

use columnar::primitive::offsets::Strides;
impl Forest<Terms> {
    /// Attempts to borrow `self` and convert to a list of fixed-size arrays.
    fn upgrade<'a, const K: usize>(&'a self) -> Option<Vec<<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>>> {
        self.layers.iter().map(|l| crate::facts::upgrade(l.list.borrow())).collect()
    }
    /// Converts a list of fixed-sized arrays to a list of byte slices.
    fn downgrade<const K: usize>(arrays: Forest<Vec<[u8; K]>>) -> Self {
        Self { layers: arrays.layers.into_iter().map(|l| { Layer { list: crate::facts::downgrade(l.list) } }).collect() }
    }
}

impl<C: Container> Forest<C> {
    pub fn len(&self) -> usize { self.layers.last().map(|l| l.list.values.len()).unwrap_or(0) }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
}

impl<C: for<'a> Container<Ref<'a>: PartialEq>> Forest<C> {

    /// Create a forest from an ordered list of `[C::Ref]` of a common length.
    pub fn form_inner<'a>(mut sorted: impl Iterator<Item = <Lists<C> as Container>::Ref<'a>>) -> Self {
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
                    if differs { layer.list.bounds.push(len as u64); }
                    differs |= C::reborrow_ref(item.get(index)) != layer.list.values.borrow().get(len-1);
                    if differs { layer.list.values.push(C::reborrow_ref(item.get(index))); }
                }
            }
            // Seal the last lists with their bounds.
            for layer in layers.iter_mut() { layer.list.bounds.push(layer.list.values.len() as u64); }

            Self { layers }
        }
        else {
            Self { layers: Vec::default() }
        }
    }
}

/// From `index`, build all extensions and invoke `action` on each.
fn apply<'a, F, TC>(
    layers: &[Vecs<TC, Strides<&'a [u64], &'a u64>>],
    index: usize,
    mut action: F,
)
where
    F: FnMut(&[TC::Ref]),
    TC: Index<Ref: Ord> + Len + Copy,
{
    // An empty forest is empty.
    if layers.is_empty() { return; }

    // A call stack of ranges for each layer.
    //
    // A range `start .. end` in position `i` indicates that we have yet to complete
    // the work for the *values* in layer i from start to end. Each value may prompt
    // further work for later layers, or can be retired by action if the last layer.
    let mut ranges = Vec::with_capacity(layers.len());
    // Values for each layer. As above, pushed onto and popped from.
    //
    // Generally, we expect this to have one fewer element than `ranges`, as ranges
    // includes at its top the next range of values to enqueue and retire.
    let mut values = Vec::with_capacity(layers.len());

    // Peer into the void and decide to process all initial values.
    // TODO: generalize to lists of lists in the outer layer.
    ranges.push(layers[0].bounds.bounds(index));

    // We repeatedly progress the work atop `ranges`.
    while let Some((lower, upper)) = ranges.last_mut() {
        if lower < upper {
            // If we have all but the last elements, we should blast through them.
            if values.len() == layers.len() - 1 {
                // We are essentially inlining the innermost loop.
                let borrow = layers.last().unwrap();
                for index in *lower .. *upper {
                    values.push(borrow.values.get(index));
                    action(&values[..]);
                    values.pop();
                }
                ranges.pop();
                values.pop();
            }
            // Otherwise, discover and enqueue the next layer of work.
            else {
                let depth = values.len();
                let bounds = layers[depth+1].bounds.bounds(*lower);
                values.push(layers[depth].values.get(*lower));
                *lower += 1;
                ranges.push(bounds);
            }
        }
        else {
            ranges.pop();
            values.pop();
        }
    }
}

/// Zips up the matching prefixes of `self` and `other`, through layer `arity`.
///
/// Each consequential moment is provided to `action`, including ranges in layers
/// where matches do not happen. The action is allowed to react as appropriate in
/// each case.
// fn align<'a, F>(&'a self, other: &'a Self, arity: usize, mut action: F)
// TC: Copy, BC: Len+IndexAs<u64>
fn align<'a, F, TC> (
    this: &[Vecs<TC, Strides<&'a [u64], &'a u64>>],
    that: &[Vecs<TC, Strides<&'a [u64], &'a u64>>],
    mut action: F,
)
where
    F: FnMut(&[<TC as Index>::Ref], std::cmp::Ordering, (usize, usize)),
    TC: Index<Ref: Ord> + Len + Copy,
{
    // An empty forest is empty.
    if this.is_empty() || that.is_empty() { return; }

    assert_eq!(this.len(), that.len());

    // A call stack of ranges for each layer.
    let mut ranges = Vec::with_capacity(this.len());
    // Values for each layer. As above, pushed onto and popped from.
    let mut values = Vec::with_capacity(this.len());

    // Peer into the void and decide to process all initial values.
    // TODO: generalize to lists of lists in the outer layer.
    ranges.push(((0, this[0].values.len()),
                 (0, that[0].values.len())));

    // We repeatedly progress the work atop `ranges`.
    while let Some(((l0, u0), (l1, u1))) = ranges.last_mut() {
        if l0 < u0 && l1 < u1 {
            // Gallop around to find the next intersection, then enqueue.
            let depth = values.len();
            let borrow0 = this[depth].values;
            let borrow1 = that[depth].values;
            let item0 = borrow0.get(*l0);
            let item1 = borrow1.get(*l1);
            match item0.cmp(&item1) {
                std::cmp::Ordering::Less => {
                    let lower = *l0;
                    crate::join::gallop(borrow0, l0, *u0, |x| x < item1);
                    action(&values[..], std::cmp::Ordering::Less, (lower, *l0));
                },
                std::cmp::Ordering::Equal => {
                    let depth = values.len();
                    values.push(this[depth].values.get(*l0));
                    if values.len() == this.len() {
                        action(&values[..], std::cmp::Ordering::Equal, (*l0, *l1));
                        values.pop();
                        *l0 += 1;
                        *l1 += 1;
                    }
                    else {
                        let bounds0 = this[depth+1].bounds.bounds(*l0);
                        let bounds1 = that[depth+1].bounds.bounds(*l1);
                        *l0 += 1;
                        *l1 += 1;
                        ranges.push((bounds0, bounds1));
                    }
                },
                std::cmp::Ordering::Greater => {
                    let lower = *l1;
                    crate::join::gallop(borrow1, l1, *u1, |x| x < item0);
                    action(&values[..], std::cmp::Ordering::Greater, (lower, *l1));
                },
            }
        }
        else {

            if l0 < u0 { action(&values[..], std::cmp::Ordering::Less, (*l0, *u0)); }
            if l1 < u1 { action(&values[..], std::cmp::Ordering::Greater, (*l1, *u1)); }

            ranges.pop();
            values.pop();
        }
    }
}

#[inline(never)]
fn join_help<'a, const K: usize>(
    this: Vec<<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>>,
    that: Vec<<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>>,
    arity: usize,
    projections: &[&[Result<usize, String>]],
) -> Vec<FactLSM<Forest<Terms>>> {

    if projections.is_empty() { return Vec::default(); }
    let mut builders: Vec<FactBuilder<Forest<Vec<[u8;K]>>>> = vec![FactBuilder::default(); projections.len()];

    if this.len() < arity || that.len() < arity { return Vec::default(); }

    let width0 = this.len() - arity;
    let width1 = that.len() - arity;

    // Allocations to stash the post-`arity` extensions for each of `this` and `that`.
    let mut extensions0: Vec<&'a [u8; K]> = Vec::with_capacity(width0);
    let mut extensions1: Vec<&'a [u8; K]> = Vec::with_capacity(width1);

    align(&this[..arity], &that[..arity], |prefix, order, (index0, index1)| {
        if let std::cmp::Ordering::Equal = order {

            // TODO: Project away columns not referenced by any projection.
            apply(&this[arity..], index0, |list| Extend::extend(&mut extensions0, list.into_iter().cloned()));
            apply(&that[arity..], index1, |list| Extend::extend(&mut extensions1, list.into_iter().cloned()));

            // Width 0 moments still have a unit `[]` to engage with.
            let count0 = if width0 > 0 { extensions0.len() / width0 } else { 1 };
            let count1 = if width1 > 0 { extensions1.len() / width1 } else { 1 };

            // TODO: Pivot the logic to be builders first, then columns, then rows.
            for idx0 in 0 .. count0 {
                let ext0 = &extensions0[idx0 * width0 ..][.. width0];
                for idx1 in 0 .. count1 {
                    let ext1 = &extensions1[idx1 * width1 ..][.. width1];
                    for (projection, builder) in projections.iter().zip(builders.iter_mut()) {
                        builder.push(projection.iter().map(|i| match i {
                            Ok(col) => {
                                if *col < arity { prefix[*col] }
                                else if *col < arity + width0 { ext0[col - arity] }
                                else if *col < arity + width0 + arity { prefix[*col - arity - width0] }
                                else { ext1[col - width0 - arity - arity] }
                            }
                            Err(lit) => lit.as_bytes()
                        }));
                    }
                }
            }

            // Tidy up after ourselves.
            extensions0.clear();
            extensions1.clear();
        }
    });

    builders.into_iter().map(|b| { FactLSM { layers: b.finish().layers.into_iter().map(|l| Forest::downgrade(l)).collect() } }).collect()
}

impl crate::facts::Merge for Forest<Terms> {
    fn merge(self, other: Self) -> Self {
        if self.is_empty() { return other; }
        if other.is_empty() { return self; }

        assert_eq!(self.layers.len(), other.layers.len());

        // // It's possible we can upgrade to `[u8; 4]` terms, and speed along faster.
        // if let (Some(this), Some(that)) = (self.upgrade::<4>(), other.upgrade::<4>()) {
        //     let mut builder = ForestBuilder::<Vec<[u8; 4]>>::with_layers(self.layers.len());
        //     align(&this[..], &that[..], |prefix, order, (lower, upper)| {
        //         match order {
        //             std::cmp::Ordering::Less => { builder.graft(prefix, lower, upper, &this[prefix.len()..]); }
        //             std::cmp::Ordering::Equal => { builder.graft(prefix, lower, lower+1, &this[prefix.len()..]); }
        //             std::cmp::Ordering::Greater => { builder.graft(prefix, lower, upper, &that[prefix.len()..]); }
        //         }
        //     });
        //     Self::downgrade(builder.done())
        // }
        // else
        // {
        //     let this = self.borrow();
        //     let that = other.borrow();

        //     let mut builder: ForestBuilder<Terms> = ForestBuilder::with_layers(self.layers.len());
        //     align(&this[..], &that[..], |prefix, order, (lower, upper)| {
        //         match order {
        //             std::cmp::Ordering::Less => { builder.graft(prefix, lower, upper, &this[prefix.len()..]); }
        //             std::cmp::Ordering::Equal => { builder.graft(prefix, lower, lower+1, &this[prefix.len()..]); }
        //             std::cmp::Ordering::Greater => { builder.graft(prefix, lower, upper, &that[prefix.len()..]); }
        //         }
        //     });

        //     builder.done()
        // }

        self.union(&other)
    }
}

impl<const K: usize> crate::facts::Merge for Forest<Vec<[u8; K]>> {
    fn merge(self, other: Self) -> Self {
        if self.is_empty() { return other; }
        if other.is_empty() { return self; }

        assert_eq!(self.layers.len(), other.layers.len());

        let this = self.borrow();
        let that = other.borrow();

        let mut builder = ForestBuilder::with_layers(self.layers.len());
        align(&this[..], &that[..], |prefix, order, (lower, upper)| {
            match order {
                std::cmp::Ordering::Less => { builder.graft(prefix, lower, upper, &this[prefix.len()..]); }
                std::cmp::Ordering::Equal => { builder.graft(prefix, lower, lower+1, &this[prefix.len()..]); }
                std::cmp::Ordering::Greater => { builder.graft(prefix, lower, upper, &that[prefix.len()..]); }
            }
        });
        builder.done()
    }
}

impl crate::facts::Length for Forest<Terms> {
    fn len(&self) -> usize { self.layers.last().map(|x| x.list.values.len()).unwrap_or(0) }
}

impl<const K: usize> crate::facts::Length for Forest<Vec<[u8; K]>> {
    fn len(&self) -> usize { self.layers.last().map(|x| x.list.values.len()).unwrap_or(0) }
}

impl FactContainer for Forest<Terms> {

    fn apply<'a>(&'a self, action: impl FnMut(&[<Terms as Container>::Ref<'a>])) {
        if self.len() > 0 { apply(&self.borrow()[..], 0, action); }
    }

    fn join<'a>(&'a self, other: &'a Self, arity: usize, projections: &[&[Result<usize, String>]]) -> Vec<FactLSM<Self>> {

        if self.layers.len() < arity || other.layers.len() < arity { return Vec::default(); }

        if let (Some(this), Some(that)) = (self.upgrade::<4>(), other.upgrade::<4>()) {
            return join_help(this, that, arity, projections);
        }

        let mut builders = vec![FactBuilder::default(); projections.len()];

        let shared0 = self.layers.iter().take(arity).map(|x| x.list.borrow()).collect::<Vec<_>>();
        let shared1 = other.layers.iter().take(arity).map(|x| x.list.borrow()).collect::<Vec<_>>();

        let unique0 = self.layers.iter().skip(arity).map(|x| x.list.borrow()).collect::<Vec<_>>();
        let unique1 = other.layers.iter().skip(arity).map(|x| x.list.borrow()).collect::<Vec<_>>();

        // Allocations to stash the post-`arity` extensions for each of `self` and `other`.
        let mut extensions0: Vec<<Terms as Container>::Ref<'a>> = Vec::with_capacity(unique0.len());
        let mut extensions1: Vec<<Terms as Container>::Ref<'a>> = Vec::with_capacity(unique1.len());

        align(&shared0[..], &shared1[..], |prefix, order, (index0, index1)| {
            if let std::cmp::Ordering::Equal = order {

                // TODO: Project away columns not referenced by any projection.
                apply(&unique0[..], index0, |list| Extend::extend(&mut extensions0, list.into_iter().cloned()));
                apply(&unique1[..], index1, |list| Extend::extend(&mut extensions1, list.into_iter().cloned()));

                let width0 = unique0.len();
                let width1 = unique1.len();

                // Width 0 moments still have a unit `[]` to engage with.
                let count0 = if width0 > 0 { extensions0.len() / width0 } else { 1 };
                let count1 = if width1 > 0 { extensions1.len() / width1 } else { 1 };

                // TODO: Pivot the logic to be builders first, then columns, then rows.
                for idx0 in 0 .. count0 {
                    let ext0 = &extensions0[idx0 * width0 ..][.. width0];
                    for idx1 in 0 .. count1 {
                        let ext1 = &extensions1[idx1 * width1 ..][.. width1];
                        for (projection, builder) in projections.iter().zip(builders.iter_mut()) {
                            builder.push(projection.iter().map(|i| match i {
                                Ok(col) => {
                                    if *col < arity { prefix[*col].as_slice() }
                                    else if *col < arity + width0 { ext0[col - arity].as_slice() }
                                    else if *col < arity + width0 + arity { prefix[*col - arity - width0].as_slice() }
                                    else { ext1[col - width0 - arity - arity].as_slice() }
                                }
                                Err(lit) => lit.as_bytes()
                            }));
                        }
                    }
                }

                // Tidy up after ourselves.
                extensions0.clear();
                extensions1.clear();
            }
        });

        builders.into_iter().map(|b| b.finish()).collect::<Vec<_>>()
    }

    fn except<'a>(mut self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a {
        for other in others {
            let old_len = self.len();
            assert_eq!(self.layers.len(), other.layers.len());

            // It's possible we can upgrade to `[u8; 4]` terms, and speed along faster.
            if let (Some(this), Some(that)) = (self.upgrade::<4>(), other.upgrade::<4>()) {
                let mut builder = ForestBuilder::with_layers(this.len());
                align(&this[..], &that[..], |prefix, order, (lower, upper)| {
                    if let std::cmp::Ordering::Less = order {
                        builder.graft(prefix, lower, upper, &this[prefix.len()..]);
                    }
                });
                self = Self::downgrade(builder.done());
            }
            else {
                let this = self.borrow();
                let that = other.borrow();

                let mut builder = ForestBuilder::with_layers(this.len());
                align(&this[..], &that[..], |prefix, order, (lower, upper)| {
                    if let std::cmp::Ordering::Less = order {
                        builder.graft(prefix, lower, upper, &this[prefix.len()..]);
                    }
                });
                self = builder.done();
            }
            assert!(old_len >= self.len());
        }
        self
    }
}

impl crate::facts::Form for Forest<Terms> {
    fn form(facts: &mut Facts) -> Self {

        if facts.len() == 0 {
            return Self::form_inner(None.into_iter());
        }

        crate::facts::sort::<true>(facts);

        // Clearly needs to be generalized, or something.
        if let Some(4) = facts.values.bounds.strided() {
            let borrow = facts.borrow();
            let arrays: Vecs<&[[u8;4]],_> = Vecs {
                bounds: borrow.bounds,
                values: borrow.values.values.as_chunks::<4>().0,
            };
            let formed: Forest<Vec<[u8; 4]>> = Forest::form_inner(arrays.into_index_iter());
            Self::downgrade(formed)
        }
        else {
            use crate::facts::Sorted;
            facts.sort::<true>();
            Self::form_inner(facts.borrow().into_index_iter())
        }
    }
}

impl<const K: usize> crate::facts::Form for Forest<Vec<[u8; K]>> {
    fn form(facts: &mut Facts) -> Self {

        if facts.len() == 0 {
            return Self::form_inner(None.into_iter());
        }

        if facts.values.bounds.strided() == Some(K as u64) {
            crate::facts::sort::<true>(facts);
            let borrow = facts.borrow();
            let arrays: Vecs<&[[u8; K]],_> = Vecs {
                bounds: borrow.bounds,
                values: borrow.values.values.as_chunks::<K>().0,
            };
            Forest::form_inner(arrays.into_index_iter())
        }
        else {
            panic!("Cannot form fixed width terms from variable width terms");
        }
    }
}


pub use forest_builder::ForestBuilder;
mod forest_builder {

    use columnar::{Container, Index};
    use crate::facts::{Lists, trie::{Forest, Layer}};

    pub struct ForestBuilder<C> { pub layers: Vec<Layer<C>> }

    impl<C: for<'a> Container<Ref<'a>: PartialEq>> ForestBuilder<C> {

        pub fn with_layers(layers: usize) -> Self {
            let layers = (0 .. layers).map(|_| Layer { list: Lists::<C>::default() }).collect::<Vec<_>>();
            Self { layers }
        }

        /// Grafts a branch that is `prefix` followed by the remaining branch.
        pub fn graft(&mut self, prefix: &[C::Ref<'_>], mut lower: usize, mut upper: usize, splice: &[<Lists<C> as Container>::Borrowed<'_>]) {

            assert_eq!(self.layers.len(), prefix.len() + splice.len());

            // Handle the prefix
            let mut differs = false;
            for (value, layer) in prefix.iter().zip(self.layers.iter_mut()) {
                let len = layer.list.values.len();
                if len > 0 {
                    if differs && len as u64 > layer.list.bounds.borrow().last().unwrap_or(0) {
                        // assert!(len as u64 > layer.list.bounds.borrow().last().unwrap_or(0));
                        layer.list.bounds.push(len as u64);
                    }
                    differs |= C::reborrow_ref(*value) != layer.list.values.borrow().get(len-1);
                    if differs { layer.list.values.push(C::reborrow_ref(*value)); }
                }
                else {
                    layer.list.values.push(C::reborrow_ref(*value));
                }
            }

            // The `lower .. upper` range of *values* in the first splice correspond to the prefix,
            // but they aren't necessarily mutually exclusive with prior calls. We could be called
            // with
            //          prefix, [a, b, c]
            //          prefix, [f, g]
            //          prefix, [z]
            //
            // We should copy in the range of values, and then completely copy all subsequent layers.

            if !splice.is_empty() {

                let len = self.layers[prefix.len()].list.values.len() as u64;
                if differs {
                    if len as u64 > self.layers[prefix.len()].list.bounds.borrow().last().unwrap_or(0) {
                        self.layers[prefix.len()].list.bounds.push(len);
                    }
                }

                self.layers[prefix.len()].list.values.extend_from_self(splice[0].values, lower .. upper);

                // Seal and copy all subsequent layers.
                for (layer, splice) in self.layers.iter_mut().skip(prefix.len()).zip(splice.iter()).skip(1) {

                    let len = layer.list.values.len() as u64;
                    if len > layer.list.bounds.borrow().last().unwrap_or(0) {
                        layer.list.bounds.push(len);
                    }

                    layer.list.extend_from_self(*splice, lower .. upper);
                    let (next_lower, _) = splice.bounds.bounds(lower);
                    let (_, next_upper) = splice.bounds.bounds(upper-1);
                    lower = next_lower;
                    upper = next_upper;
                }
            }
        }

        pub fn done(mut self) -> Forest<C> {
            for layer in self.layers.iter_mut() {
                let len = layer.list.values.len() as u64;
                if len > layer.list.bounds.borrow().last().unwrap_or(0) {
                    layer.list.bounds.push(len);
                }
            }

            Forest { layers: self.layers }
        }
    }
}

/// Types and logic for exploring and constructing forests layer-at-a-time.
pub mod survey {

    //!
    //! A forest layer can be "surveyed", which results in a list of bits which indicate the presence
    //! or absence of a layer value in a larger ambient space, often the union of the values of the
    //! layer with the values of other layers. The lists should be as long as the size of the union
    //! of the values, and have as many set bits as there are values in the layer. Put alongside the
    //! survey results from the other layers, the lists of bits tell us which keys are exclusive to
    //! any of the layers, or are in common to multiple layers.
    //!
    //! We'll want to be careful how we represent these lists of bits, as the number of keys may be
    //! much larger than the size of some of the inputs, and we would like to use as few resources as
    //! possible. One candidate is to record a sequence of integers, which indicate the next offset
    //! at which the bit value flips. This encodes ranges of set and unset bits, at the expense of
    //! more integers for alternating bit patterns. Generally, we can think about further optimization,
    //! but we should ack that we need to keep things as tight as the computation we perform to find
    //! these ranges.

    use columnar::{Columnar, Container, Index, Len, Push, Vecs};

    use crate::facts::{Lists, Terms, upgrade_hint, upgrade, downgrade};
    use super::{Forest, Layer};

    /// A report we would expect to see in a sequence about two layers.
    ///
    /// A sequence of these reports reveal an ordered traversal of the keys
    /// of two layers, with ranges exclusive to one, ranges exclusive to the
    /// other, and individual elements (not ranges) common to both.
    #[derive(Copy, Clone, Columnar, Debug)]
    pub enum Report {
        /// Range of indices in this input.
        This(usize, usize),
        /// Range of indices in that input.
        That(usize, usize),
        /// Matching indices in both inputs.
        Both(usize, usize),
    }

    type Reports = ::columnar::ContainerOf<Report>;

    impl Forest<Terms> {

        /// For each layer a map of its key dispositions for each output.
        ///
        /// Each element in the result spells out the key ordering in that layer.
        /// The intent is that this map allows one to navigate directly to matching
        /// records, and conduct further investigation without much more thinking.
        pub fn survey<const FULL: bool>(&self, other: &Self) -> Vec<Vecs<Reports>> {

            let mut results = Vec::with_capacity(self.layers.len() + 1);

            let mut init = Vecs::<Reports>::default();
            init.values.push(Report::Both(0,0));
            init.bounds.push(init.values.len() as u64);
            results.push(init);

            for (layer0, layer1) in self.layers.iter().zip(other.layers.iter()) {
                let prior_map = results.last().unwrap().values.borrow();
                let lists0: <Lists<Terms> as Container>::Borrowed<'_> = layer0.list.borrow();
                let lists1: <Lists<Terms> as Container>::Borrowed<'_> = layer1.list.borrow();
                let map = match (upgrade_hint(lists0), upgrade_hint(lists1)) {
                    // TODO: Add other recognized sizes
                    (Some(4), Some(4)) => { survey::<FULL,Vec<[u8;4]>>(upgrade::<4>(lists0).unwrap(), upgrade::<4>(lists1).unwrap(), prior_map) },
                    _                  => { survey::<FULL,Terms>(lists0, lists1, prior_map) },
                };
                results.push(map)
            }

            results
        }

        /// Produces a forest describing the union of the input forests.
        ///
        /// At each layer, for each inbound path, the lists will be the union of the lists
        /// in each input. These may be exactly the lists from one of the inputs, or the
        /// union of the two lists if the path exists in both inputs.
        #[inline(never)]
        pub fn union(&self, other: &Self) -> Self {

            assert_eq!(self.layers.len(), other.layers.len());
            let mut layers = Vec::with_capacity(self.layers.len());

            let mut reports = std::collections::VecDeque::default();
            reports.push_back(Report::Both(0, 0));
            for (layer0, layer1) in self.layers.iter().zip(other.layers.iter()) {
                let lists0: <Lists<Terms> as Container>::Borrowed<'_> = layer0.list.borrow();
                let lists1: <Lists<Terms> as Container>::Borrowed<'_> = layer1.list.borrow();
                let list = match (upgrade_hint(lists0), upgrade_hint(lists1)) {
                    (Some(4), Some(4)) => {
                        if layers.len() + 1 < self.layers.len() { downgrade(union::<true,_>(upgrade::<4>(lists0).unwrap(), upgrade::<4>(lists1).unwrap(), &mut reports)) }
                        else { downgrade(union::<false,_>(upgrade::<4>(lists0).unwrap(), upgrade::<4>(lists1).unwrap(), &mut reports)) }
                    }
                    _ => {
                        if layers.len() + 1 < self.layers.len() { union::<true,_>(lists0, lists1, &mut reports) }
                        else { union::<false,_>(lists0, lists1, &mut reports) }
                    }
                };
                layers.push(Layer { list });
            }

            Self { layers }
        }

        /// Produces a forest of elements in `self` but not in `other`.
        pub fn minus(&self, other: &Self) -> Self {

            assert_eq!(self.layers.len(), other.layers.len());
            let mut layers = Vec::with_capacity(self.layers.len());

            // We'll proceed through layers "bottom-up", from the lowest layers to the highest,
            // once we've constructed a map of the intesection of the layers. This is not helpful
            // for merging facts, but will be useful for consolidation, and other merge rules in
            // which cancelation may occur, and the presence of paths at higher levels depends on
            // the outcome of the merges at the lower levels.

            let map = self.survey::<true>(other);

            // Except wants to track across each layer whether a write happened, specifically for
            // `Both` variants that are unclear about whether they will or will not produce items
            // in the next layer. If we have positive evidence that they did so, then the `Both`
            // should push its items and indicate that it did so for the benefit of the next layer.
            //
            // If we populate a `Bools` at each level, we are most of the way towards a `Options`
            // container, which more clearly spells out whether a collection exists or not. If we
            // instead have folks build a layer of `Option<Vec<T>>` rather than of `Vec<T>`, it
            // would be rather clear what it means to `filter_map` the result through, retaining
            // only the non-`None` instances. Should we do so explicitly, though? We could start
            // by building `Options<Empties>` and see where that leads us.

            // We may only need to populate these for `Both` variants, which we'll check in order.
            use columnar::primitive::Bools;
            let mut roots:Bools  = Bools::default();
            let mut leaves:Bools = Bools::default();

            // Go from last layer to first; not for Datalog merges, but to prep for consolidation.
            for (index, layer0) in self.layers.iter().enumerate().rev() {

                // What happens in each layer is determined by a combination of the map in
                // this layer and the map in the higher layer. The map of the higher layer
                // speaks about the *lists* of this layer, and the map of this layer speaks
                // about the *elements* of this layer.

                let mut list = Lists::<Terms>::default();

                let layer0 = layer0.borrow();
                let mut both_counter = 0;

                // We'll need access to the map of the incoming (higher) layer, to inform us about ranges
                // of lists we may want to simply copy in. We'll also need the map of the current layer to
                // reveal how to resolve incoming paths present in both layers.
                let prev_map = &map[index].values;
                let next_map = &map[index+1];

                // TODO: We can consolidate the extensions we perform, both within inbound `Both` variants,
                // and across them when they turn out to amount to `This` or `That` (or even both). This is
                // specific to merging, and different logic would be needed for e.g. `EXCEPT`.
                for (prev_report, next_reports) in prev_map.into_index_iter().zip(next_map.into_index_iter()) {
                    match prev_report {
                        ReportReference::This((lower0, upper0)) => { list.extend_from_self(layer0, lower0 .. upper0); },
                        ReportReference::Both((_idx0, _idx1)) => {
                            // We have report of a contended element, and must proceed with care.
                            // Any `Both` element may be empty in the next layer, and we'll want
                            // to check this before extending any values into `list`. All `This`
                            // values should be good to go, and all `That` values should be ignored.
                            let prev_len = list.values.len();
                            for next_report in next_reports.into_index_iter() {
                                match next_report {
                                    ReportReference::This((lower0, upper0)) => { list.values.extend_from_self(layer0.values, lower0 .. upper0); },
                                    ReportReference::Both((index0, _index1)) => {
                                        if both_counter < leaves.len() && leaves.get(both_counter) {
                                            list.values.extend_from_self(layer0.values, index0 .. index0+1);
                                        }
                                        both_counter += 1;
                                    },
                                    ReportReference::That(_) => { /* nothing to do here */ },
                                }
                            }
                            roots.push(prev_len < list.values.len());
                            list.bounds.push(list.values.len() as u64);
                        }
                        ReportReference::That(_) => { /* nothing to do here */ },
                    }
                }

                use columnar::Clear;
                leaves.clear();
                std::mem::swap(&mut roots, &mut leaves);

                layers.push(Layer { list });
            }

            layers.reverse();
            Self { layers }
        }
    }

    /// Given the values of an input map, enrich the contended areas with further detail.
    ///
    /// Provided a sequence of reports, produce a sequence of report lists, which mirror
    /// the input reports for disjoint regions, or provide additional detail for regions
    /// that are contended.
    ///
    /// The `FULL` parameter controls whether reports are produced for uncontended regions
    /// (true) or only for contended regions (false). In the latter case, the output has
    /// as many elements as there are `Report::Both` variants in the input.
    #[inline(never)]
    pub fn survey<'a, const FULL: bool, C: Container<Ref<'a>: Ord>>(
        list0: <Lists<C> as Container>::Borrowed<'a>,
        list1: <Lists<C> as Container>::Borrowed<'a>,
        inbound: <Reports as Container>::Borrowed<'_>,
    ) -> Vecs<Reports> {

        let mut result: Vecs<Reports> = Vecs::default();
        for report in inbound.into_index_iter() {
            match report {
                // Exclusive ranges are communicated onward.
                ReportReference::This((lower, upper)) => {
                    if FULL {
                        let (new_lower, _) = list0.bounds.bounds(lower);
                        let (_, new_upper) = list0.bounds.bounds(upper-1);
                        result.push(Some(Report::This(new_lower, new_upper)));
                    }
                }
                // We are primarily interested in contended areas.
                ReportReference::Both((index0, index1)) => {

                    // Fetch the bounds from the layers.
                    let (mut lower0, upper0) = list0.bounds.bounds(index0);
                    let (mut lower1, upper1) = list1.bounds.bounds(index1);

                    // Scour the intersecting range for matches.
                    while lower0 < upper0 && lower1 < upper1 {
                        let val0 = list0.values.get(lower0);
                        let val1 = list1.values.get(lower1);
                        match val0.cmp(&val1) {
                            std::cmp::Ordering::Less => {
                                let start = lower0;
                                crate::join::gallop(list0.values, &mut lower0, upper0, |x| x < val1);
                                if FULL { result.values.push(Report::This(start, lower0)); }
                            },
                            std::cmp::Ordering::Equal => {
                                result.values.push(Report::Both(lower0, lower1));
                                lower0 += 1;
                                lower1 += 1;
                            },
                            std::cmp::Ordering::Greater => {
                                let start = lower1;
                                crate::join::gallop(list1.values, &mut lower1, upper1, |x| x < val0);
                                if FULL { result.values.push(Report::That(start, lower1)); }
                            },
                        }
                    }
                    if FULL {
                        if lower0 < upper0 { result.values.push(Report::This(lower0, upper0))}
                        if lower1 < upper1 { result.values.push(Report::That(lower1, upper1))}
                    }
                    result.bounds.push(result.values.len() as u64);
                }
                // Exclusive ranges are communicated onward.
                ReportReference::That((lower, upper)) => {
                    if FULL {
                        let (new_lower, _) = list1.bounds.bounds(lower);
                        let (_, new_upper) = list1.bounds.bounds(upper-1);
                        result.push(Some(Report::That(new_lower, new_upper)));
                    }
                }
            }
        }

        result
    }

    /// Merges two sequences of lists using alignment information in outer and inner maps.
    pub fn union<'a, const NEXT: bool, C: Container<Ref<'a>: Ord>>(
        lists0: <Lists<C> as Container>::Borrowed<'a>,
        lists1: <Lists<C> as Container>::Borrowed<'a>,
        reports: &mut std::collections::VecDeque<Report>,
    ) -> Lists<C> {

        let mut list = <Lists::<C> as Container>::with_capacity_for([lists0, lists1].into_iter());

        let report_count = reports.len();

        for _ in 0 .. report_count {
            match reports.pop_front().unwrap() {
                Report::This(lower0, upper0) => {
                    list.extend_from_self(lists0, lower0 .. upper0);
                    let (new_lower, _) = lists0.bounds.bounds(lower0);
                    let (_, new_upper) = lists0.bounds.bounds(upper0-1);
                    if NEXT { reports.push_back(Report::This(new_lower, new_upper)); }
                },
                Report::Both(index0, index1) => {

                    // Fetch the bounds from the layers.
                    let (mut lower0, upper0) = lists0.bounds.bounds(index0);
                    let (mut lower1, upper1) = lists1.bounds.bounds(index1);

                    // Scour the intersecting range for matches.
                    while lower0 < upper0 && lower1 < upper1 {
                        let val0 = lists0.values.get(lower0);
                        let val1 = lists1.values.get(lower1);
                        match val0.cmp(&val1) {
                            std::cmp::Ordering::Less => {
                                let start = lower0;
                                crate::join::gallop(lists0.values, &mut lower0, upper0, |x| x < val1);
                                if NEXT { reports.push_back(Report::This(start, lower0)); }
                                list.values.extend_from_self(lists0.values, start .. lower0);
                            },
                            std::cmp::Ordering::Equal => {
                                if NEXT { reports.push_back(Report::Both(lower0, lower1)); }
                                list.values.extend_from_self(lists0.values, lower0 .. lower0+1);
                                lower0 += 1;
                                lower1 += 1;
                            },
                            std::cmp::Ordering::Greater => {
                                let start = lower1;
                                crate::join::gallop(lists1.values, &mut lower1, upper1, |x| x < val0);
                                if NEXT { reports.push_back(Report::That(start, lower1)); }
                                list.values.extend_from_self(lists1.values, start .. lower1);
                            },
                        }
                    }
                    if lower0 < upper0 {
                        list.values.extend_from_self(lists0.values, lower0 .. upper0);
                        if NEXT { reports.push_back(Report::This(lower0, upper0)); }
                    }
                    if lower1 < upper1 {
                        list.values.extend_from_self(lists1.values, lower1 .. upper1);
                        if NEXT { reports.push_back(Report::That(lower1, upper1)); }
                    }
                    list.bounds.push(list.values.len() as u64);
                },
                Report::That(lower1, upper1) => {
                    list.extend_from_self(lists1, lower1 .. upper1);
                    let (new_lower, _) = lists1.bounds.bounds(lower1);
                    let (_, new_upper) = lists1.bounds.bounds(upper1-1);
                    if NEXT { reports.push_back(Report::That(new_lower, new_upper)); }
                },
            }
        }

        list
    }

}