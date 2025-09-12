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
                    *l0 += 1;
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
                    *l1 += 1;
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

/// Support method for binary joins on arrays of bytes.
///
/// Matches are found by comparing the first `arity` columns of `this` and `that`, and for each match,
/// enumerating the cross join of all remaining columns, and subjecting it to various projections.
/// The projections are column references, where
///     columns in `[0, arity)` are from the matched columns,
///     columns in `[arity, this_arity)` are from the additional columns of `this`,
///     columns in `[this_arity, this_arity + arity)` are again the matched columns,
///     columns in `[this_arity + arity, this_arity + that_arity + arity)` are from the additional columns of `that`.
#[inline(never)]
fn join_help<'a, const K: usize>(
    this: Vec<<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>>,
    that: Vec<<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>>,
    arity: usize,
    projections: &[&[usize]],
) -> Vec<FactLSM<Forest<Terms>>> {

    if projections.is_empty() { return Vec::default(); }

    // We'll build into buffers of the specific type, without knowing the projection width.
    // To commit the values, we'll need to reshape using `as_chunks()`.
    // The intent is that we buffer up ~1M rows and form a `Forest<Vec<[u8;K]>>` from them,
    // and commit each of these to an ongoing `FactLSM` for each projection.
    let mut buffered = 0;
    let mut buffers: Vec<Vec<[u8; K]>> = projections.iter().map(|p| Vec::with_capacity(1_000_000 * p.len())).collect();
    let mut builders: Vec<FactLSM<Forest<Vec<[u8;K]>>>> = vec![FactLSM::default(); projections.len()];

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

            if buffered + count0 * count1 > 1_000_000 {
                for index in 0 .. projections.len() {
                    builders[index].push(Forest::from_bytes(&mut buffers[index], projections[index].len()));
                    buffers[index].clear();
                }
                buffered = 0;
            }

            // TODO: Pivot the logic to be builders first, then columns, then rows.
            for idx0 in 0 .. count0 {
                let ext0 = &extensions0[idx0 * width0 ..][.. width0];
                for idx1 in 0 .. count1 {
                    let ext1 = &extensions1[idx1 * width1 ..][.. width1];
                    for (projection, buffer) in projections.iter().zip(buffers.iter_mut()) {
                        buffer.extend(projection.iter().map(|col|
                            if *col < arity { prefix[*col] }
                            else if *col < arity + width0 { ext0[col - arity] }
                            else if *col < arity + width0 + arity { prefix[*col - arity - width0] }
                            else { ext1[col - width0 - arity - arity] }
                        ));
                    }
                }
            }
            buffered += count0 * count1;

            // Tidy up after ourselves.
            extensions0.clear();
            extensions1.clear();
        }
    });

    for index in 0 .. projections.len() {
        builders[index].push(Forest::from_bytes(&mut buffers[index], projections[index].len()));
    }

    builders.into_iter().map(|b| { FactLSM { layers: b.layers.into_iter().map(|l| Forest::downgrade(l)).collect() } }).collect()
}

impl crate::facts::Merge for Forest<Terms> {
    fn merge(self, other: Self) -> Self {
        if self.is_empty() { return other; }
        if other.is_empty() { return self; }

        assert_eq!(self.layers.len(), other.layers.len());

        self.union(&other)
    }
}

impl<const K: usize> crate::facts::Merge for Forest<Vec<[u8; K]>> {
    fn merge(self, other: Self) -> Self {

        if self.is_empty() { return other; }
        if other.is_empty() { return self; }

        assert_eq!(self.layers.len(), other.layers.len());

        use crate::facts::trie::survey::{Report, union};

        let mut layers = Vec::with_capacity(self.layers.len());
        let mut reports = std::collections::VecDeque::default();
        reports.push_back(Report::Both(0, 0));
        for (layer0, layer1) in self.layers.iter().zip(other.layers.iter()) {
            let lists0 = layer0.list.borrow();
            let lists1 = layer1.list.borrow();
            let list = if layers.len() + 1 < self.layers.len() {
                union::<true,_>(lists0, lists1, &mut reports)
            }
            else { union::<false,_>(lists0, lists1, &mut reports) };

            layers.push(Layer { list });
        }

        Self { layers }
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

    fn join<'a>(&'a self, other: &'a Self, arity: usize, projections: &[&[usize]]) -> Vec<FactLSM<Self>> {

        if self.layers.len() < arity || other.layers.len() < arity {
            assert!(self.len() == 0 || other.len() == 0);
            return vec![FactLSM::default(); projections.len()];
        }

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
                            builder.push(projection.iter().map(|col|
                                if *col < arity { prefix[*col].as_slice() }
                                else if *col < arity + width0 { ext0[col - arity].as_slice() }
                                else if *col < arity + width0 + arity { prefix[*col - arity - width0].as_slice() }
                                else { ext1[col - width0 - arity - arity].as_slice() }
                            ));
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

    #[inline(never)]
    fn except<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a {
        self.antijoin(others)
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

impl<const K: usize> Forest<Vec<[u8; K]>> {
    /// Produce a forest of `width` layers from byte arrays.
    fn from_bytes(bytes: &mut [[u8; K]], width: usize) -> Self {
        match width {
            1 => Self::from_bytes_array::<1>(bytes),
            2 => Self::from_bytes_array::<2>(bytes),
            3 => Self::from_bytes_array::<3>(bytes),
            4 => Self::from_bytes_array::<4>(bytes),
            5 => Self::from_bytes_array::<5>(bytes),
            x => unimplemented!("Bytes width {x} not yet implemented"),
        }
    }
    /// Produce a forest of `W` layers from byte arrays.
    fn from_bytes_array<const W: usize>(bytes: &mut [[u8; K]]) -> Self {
        if bytes.is_empty() { return Self::default() }

        let (facts, rest) = bytes.as_chunks_mut::<W>();
        assert!(rest.is_empty());
        crate::facts::radix_sort::lsb(facts);

        let mut layers: [Layer<Vec<[u8; K]>>; W] = (0 .. W).map(|_| Default::default()).collect::<Vec<_>>().try_into().unwrap();
        for i in 0 .. W { layers[i].list.values.push(facts[0][i]); }
        for i in 1 .. facts.len() {
            if facts[i] != facts[i-1] {
                let pos = facts[i].iter().zip(facts[i-1].iter()).position(|(i0, i1)| i0 != i1).unwrap();
                for to_seal in pos+1 .. W { layers[to_seal].list.bounds.push(layers[to_seal].list.values.len() as u64); }
                for to_push in pos   .. W { layers[to_push].list.values.push(facts[i][to_push]); }
            }
        }

        for to_seal in 0 .. W { layers[to_seal].list.bounds.push(layers[to_seal].list.values.len() as u64); }

        Self { layers: layers.into_iter().collect() }
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

    use columnar::{Columnar, Container, Index, Len};

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

    impl Forest<Terms> {

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

        /// Produces elements in `self` that have an element of `others` as a prefix.
        ///
        /// All of `others` should have the same number of layers, at most the number of `self`.
        pub fn semijoin<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self { self.retain_join::<'a, true>(others) }
        /// Produces elements in `self` that do not have an element of `others` as a prefix.
        ///
        /// All of `others` should have the same number of layers, at most the number of `self`.
        pub fn antijoin<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self { self.retain_join::<'a, false>(others) }

        /// Produces elements in `self` based on their presence in any of `others`.
        ///
        /// The `SEMI` argument controls whether this performs a semijoin or an antijoin,
        /// where a semijoin retains elements that are in common with `others`, whereas
        /// an antijoin retains elements not in common with `others`.
        ///
       /// All of `others` should have the same number of layers, at most the number of `self`.
         #[inline(never)]
        pub fn retain_join<'a, const SEMI: bool>(mut self, others: impl Iterator<Item = &'a Self>) -> Self {

            use std::collections::VecDeque;

            let others = others.collect::<Vec<_>>();
            if others.is_empty() { return self; }
            let other_arity = others[0].layers.len();
            others.iter().for_each(|other| {
                assert!(self.layers.len() >= other.layers.len());
                assert_eq!(other.layers.len(), other_arity);
            });

            // First, collect reports to determine paths to retain to `self`.
            let mut include = std::iter::repeat(!SEMI).take(self.layers[other_arity-1].list.values.len()).collect::<VecDeque<_>>();
            let mut reports = VecDeque::default();
            for other in others.iter() {
                reports.push_back((0, 0));
                for (layer0, layer1) in self.layers.iter().zip(other.layers.iter()) {
                    // Borrow the layers for read-only access.
                    let lists0 = layer0.borrow();
                    let lists1 = layer1.borrow();
                    // Update reports for the next layer, or output.
                    match (upgrade_hint(lists0), upgrade_hint(lists1)) {
                        (Some(4), Some(4)) => {
                            let lists0 = upgrade::<4>(lists0).unwrap();
                            let lists1 = upgrade::<4>(lists1).unwrap();
                            intersection::<Vec<[u8; 4]>>(lists0, lists1, &mut reports);
                        }
                        __________________ => {
                            intersection::<Terms>(lists0, lists1, &mut reports);
                        }
                    };
                }
                // Mark shared paths appropriately.
                for (index,_) in reports.drain(..) {
                    include[index] = SEMI;
                }
            }

            // If not all items are included, restrict layers of `self`.
            if include.iter().all(|x| *x) { return self; }
            else {

                // If there are additional layers, clone `include` and update unexplored layers.
                if self.layers.len() > other_arity {
                    let mut include = include.clone();
                    for layer in self.layers[other_arity..].iter_mut() {
                        let lists = layer.borrow();
                        layer.list = match upgrade_hint(lists) {
                            Some(4) => { downgrade(retain_lists(upgrade::<4>(lists).unwrap(), &mut include)) }
                            _______ => { retain_lists(lists, &mut include) }
                        };
                    }
                }
                // In any case, update prior layers from `other_arity` back to the first.
                for layer in self.layers[..other_arity].iter_mut().rev() {
                    if include.iter().all(|x| *x) { return self; }  // TODO: make this test cheaper.
                    let lists = layer.borrow();
                    layer.list = match upgrade_hint(lists) {
                        Some(4) => { downgrade(retain_items(upgrade::<4>(lists).unwrap(), &mut include)) }
                        _______ => { retain_items(lists, &mut include) }
                    };
                }
            }
            self
        }
    }

    /// Intersects aligned lists from two inputs, recording common list items in `reports`.
    ///
    /// The `reports` input should contain pairs of list indices that should be intersected,
    /// and it will be populated with pairs of item indices (not list indices) that reference
    /// equal items in indicated lists.
    #[inline(never)]
    pub fn intersection<'a, C: Container<Ref<'a>: Ord>>(
        list0: <Lists<C> as Container>::Borrowed<'a>,
        list1: <Lists<C> as Container>::Borrowed<'a>,
        reports: &mut std::collections::VecDeque<(usize, usize)>,
    ) {
        let report_count = reports.len();
        for _ in 0 .. report_count {
            let (index0, index1) = reports.pop_front().unwrap();

            // Fetch the bounds from the layers.
            let (mut lower0, upper0) = list0.bounds.bounds(index0);
            let (mut lower1, upper1) = list1.bounds.bounds(index1);

            // Scour the intersecting range for matches.
            while lower0 < upper0 && lower1 < upper1 {
                let val0 = list0.values.get(lower0);
                let val1 = list1.values.get(lower1);
                match val0.cmp(&val1) {
                    std::cmp::Ordering::Less => {
                        lower0 += 1;
                        crate::join::gallop(list0.values, &mut lower0, upper0, |x| x < val1);
                    },
                    std::cmp::Ordering::Equal => {
                        reports.push_back((lower0, lower1));
                        lower0 += 1;
                        lower1 += 1;
                    },
                    std::cmp::Ordering::Greater => {
                        lower1 += 1;
                        crate::join::gallop(list1.values, &mut lower1, upper1, |x| x < val0);
                    },
                }
            }
        }
    }

    /// Restrict lists based on per-list bools, producing a new layer and updating `bools` for the items.
    #[inline(never)]
    pub fn retain_lists<'a, C: Container>(
        lists: <Lists<C> as Container>::Borrowed<'a>,
        bools: &mut std::collections::VecDeque<bool>,
    ) -> Lists<C> {

        // In principle we can copy runs described in `bools` for bulk copying.
        let mut output = <Lists::<C> as Container>::with_capacity_for([lists].into_iter());

        assert_eq!(bools.len(), lists.len());
        for list_index in 0 .. lists.len() {
            let present = bools.pop_front().unwrap();
            if present { use columnar::Push; output.push(lists.get(list_index)); }
            bools.extend(std::iter::repeat(present).take(lists.get(list_index).len()));
        }

        assert_eq!(bools.len(), lists.values.len());
        output
    }

    /// Restrict lists based on per-item bools, producing a new layer and updating `bools` for the lists.
    #[inline(never)]
    pub fn retain_items<'a, C: Container>(
        lists: <Lists<C> as Container>::Borrowed<'a>,
        bools: &mut std::collections::VecDeque<bool>,
    ) -> Lists<C> {

        // In principle we can copy runs described in `bools` for bulk copying.
        let mut output = <Lists::<C> as Container>::with_capacity_for([lists].into_iter());

        assert_eq!(bools.len(), lists.values.len());
        for list_index in 0 .. lists.len() {
            let (lower, upper) = lists.bounds.bounds(list_index);
            for item_index in lower .. upper {
                if bools.pop_front().unwrap() {
                    output.values.push(lists.values.get(item_index));
                }
            }
            if output.values.len() > output.bounds.borrow().last().unwrap_or(0) as usize {
                output.bounds.push(output.values.len() as u64);
                bools.push_back(true);
            }
            else {
                bools.push_back(false);
            }
        }

        assert_eq!(bools.len(), lists.len());
        output
    }

    /// Merges two sequences of lists using alignment information in `reports`.
    ///
    /// The `NEXT` parameter indicates whether the next round of reports should be prepared,
    /// which is for example not necessary in the last layer of a union, as there is no next
    /// layer to prepare reports for, and the cost can be higher there than for prior layers.
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
                                lower0 += 1;
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
                                lower1 += 1;
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