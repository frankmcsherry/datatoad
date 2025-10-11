//! A layered trie representation in columns.
//!
//! The type is designed to represented sorted lists of tuples of a common arity,
//! through a sequence of layers that represent the distinct tuple prefixes that
//! increase in length as we increase the layers.
//!
//! Each "layer" is a list of sets of items, where each set contains values that
//! extend a prefix that corresponds to the sets position. We'll treat the sets
//! as having an order on their elements (e.g. a sorted list) so that the layer's
//! extended paths also have an order, and the next layer (or layers) can align
//! their sets of extensions with the prior extensions.
//!
//! Another way to arrive at the same layout is to start with the full list of
//! sorted tuples, record the sequence of last tuple items as a column of data,
//! and then to deduplicate the (still sorted) tuples with these values removed,
//! recording the number of occurrences of each duplicate and using it to group
//! the extracted column of values (forming runs of sorted values for prefixes).

use columnar::{Container, Index};
use crate::facts::Lists;

/// A sequence of layers, each a list of extensions for items of the prior layer.
///
/// This type houses many columns, and is meant to be demonstrative of how on can
/// use column-oriented data to perform various collection-oriented tasks. Often,
/// we'll want to use other types, perhaps of borrowed data, and it shouldn't be
/// important to return to this type.
///
/// Although `Forest` will have many methods, the intent is that eventually all of
/// these methods become relatively few calls into methods on the layers. When not
/// the case, this is a bit of a bug.
#[derive(Clone, Debug, Default)]
pub struct Forest<C> { pub layers: Vec<Layer<C>> }

impl<C: Container> Forest<C> {
    pub fn len(&self) -> usize { self.layers.last().map(|l| l.list.values.len()).unwrap_or(0) }
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    fn borrow<'a>(&'a self) -> Vec<<Lists<C> as Container>::Borrowed<'a>> {
        self.layers.iter().map(|x| x.list.borrow()).collect::<Vec<_>>()
    }
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

/// Methods that are currently non-columnar, all of which we'd like to convert.
pub mod non_columnar {

    use columnar::{Index, Len, Vecs};

    /// From `index`, build all extensions and invoke `action` on each.
    pub fn apply<'a, F, TC>(
        layers: &[Vecs<TC, crate::facts::Strides<&'a [u64], &'a u64>>],
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
    pub fn align<'a, F, TC> (
        this: &[Vecs<TC, crate::facts::Strides<&'a [u64], &'a u64>>],
        that: &[Vecs<TC, crate::facts::Strides<&'a [u64], &'a u64>>],
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
                        crate::facts::gallop(borrow0, l0, *u0, |x| x < item1);
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
                        crate::facts::gallop(borrow1, l1, *u1, |x| x < item0);
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

}

/// Implementations for `Forest<Terms>`, for generic byte slices.
pub mod terms {

    use columnar::{Container, Index, Len, Vecs};
    use crate::facts::{Facts, FactBuilder, FactContainer, FactLSM, Lists, Terms};
    use crate::facts::trie::layers::Report;
    use crate::types::Action;

    use super::{Forest, Layer, non_columnar};

    impl Forest<Terms> {
        /// Attempts to borrow `self` and convert to a list of fixed-size arrays.
        pub fn upgrade<'a, const K: usize>(&'a self) -> Option<Vec<<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>>> {
            self.layers.iter().map(|l| crate::facts::upgrade(l.list.borrow())).collect()
        }
        /// Converts a list of fixed-sized arrays to a list of byte slices.
        pub fn downgrade<const K: usize>(arrays: Forest<Vec<[u8; K]>>) -> Self {
            Self { layers: arrays.layers.into_iter().map(|l| { Layer { list: crate::facts::downgrade(l.list) } }).collect() }
        }
    }

    impl crate::facts::Merge for Forest<Terms> {
        fn merge(self, other: Self) -> Self {
            if self.is_empty() { return other; }
            if other.is_empty() { return self; }

            assert_eq!(self.layers.len(), other.layers.len());

            let mut layers = Vec::with_capacity(self.layers.len());
            let mut reports = std::collections::VecDeque::default();
            reports.push_back(Report::Both(0, 0));
            for (layer0, layer1) in self.layers.iter().zip(other.layers.iter()) {
                layers.push(layer0.union(layer1, &mut reports, layers.len() + 1 < self.layers.len()));
            }

            Self { layers }
        }
    }

    impl crate::facts::Length for Forest<Terms> {
        fn len(&self) -> usize { self.layers.last().map(|x| x.list.values.len()).unwrap_or(0) }
    }

    impl FactContainer for Forest<Terms> {

        fn act_on(&self, action: &Action<String>) -> FactLSM<Self> {

            if self.is_empty() { return FactLSM::default(); }
            if action.is_identity() { return FactLSM::from(self.clone()); }

            //  TODO:   A better implementation would identify unique columns and act on them,
            //          followed by clean-up actions to install literals and repeated columns.
            //  TODO:   The structure of `action` may mean that we can steal columns directly
            //          from `self`, for example when they project a prefix of the columns.

            // A special case of byte arrays and no literals can be specialized.
            if let Some(this) = self.upgrade::<4>() {
                if let Ok(columns) = action.projection.iter().cloned().collect::<Result<Vec<_>,_>>() {

                    // Specialized builder, using a more specific `buffer` for byte arrays.
                    let mut buffer: Vec<[u8;4]> = Vec::with_capacity(1_000_000 * columns.len());
                    let mut builder: FactLSM<Forest<Terms>> = FactLSM::default();

                    non_columnar::apply(&this[..], 0, |row| {
                        let lit_filtered = action.lit_filter.iter().all(|(index, value)| row[*index].as_slice() == value.as_bytes());
                        let var_filtered = action.var_filter.iter().all(|columns| columns[1..].iter().all(|c| row[*c] == row[columns[0]]));
                        if lit_filtered && var_filtered {
                            if buffer.len() == buffer.capacity() {
                                builder.push(Forest::downgrade(Forest::from_bytes(&mut buffer, columns.len())));
                                buffer.clear();
                            }
                            buffer.extend(columns.iter().map(|c| row[*c]));
                        }
                    });

                    builder.push(Forest::downgrade(Forest::from_bytes(&mut buffer, columns.len())));
                    buffer.clear();
                    return builder;
                }
            }

            // Fall through to a general case.
            let this = self.borrow();
            let mut builder = FactBuilder::default();
            non_columnar::apply(&this[..], 0, |row| {
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

        fn join<'a>(&'a self, other: &'a Self, arity: usize, projections: &[&[usize]]) -> Vec<FactLSM<Self>> {

            if self.layers.len() < arity || other.layers.len() < arity {
                assert!(self.is_empty() || other.is_empty());
                return vec![FactLSM::default(); projections.len()];
            }

            if let (Some(this), Some(that)) = (self.upgrade::<4>(), other.upgrade::<4>()) {
                return super::byte_array::join_help(&this[..], &that[..], arity, projections);
            }

            let mut builders = vec![FactBuilder::default(); projections.len()];

            let shared0 = self.layers.iter().take(arity).map(|x| x.list.borrow()).collect::<Vec<_>>();
            let shared1 = other.layers.iter().take(arity).map(|x| x.list.borrow()).collect::<Vec<_>>();

            let unique0 = self.layers.iter().skip(arity).map(|x| x.list.borrow()).collect::<Vec<_>>();
            let unique1 = other.layers.iter().skip(arity).map(|x| x.list.borrow()).collect::<Vec<_>>();

            // Allocations to stash the post-`arity` extensions for each of `self` and `other`.
            let mut extensions0: Vec<<Terms as Container>::Ref<'a>> = Vec::with_capacity(unique0.len());
            let mut extensions1: Vec<<Terms as Container>::Ref<'a>> = Vec::with_capacity(unique1.len());

            non_columnar::align(&shared0[..], &shared1[..], |prefix, order, (index0, index1)| {
                if let std::cmp::Ordering::Equal = order {

                    // TODO: Project away columns not referenced by any projection.
                    non_columnar::apply(&unique0[..], index0, |list| Extend::extend(&mut extensions0, list.iter().cloned()));
                    non_columnar::apply(&unique1[..], index1, |list| Extend::extend(&mut extensions1, list.iter().cloned()));

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

        fn antijoin<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { self.retain_join::<'a>(others, false) }

        fn semijoin<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { self.retain_join::<'a>(others, true) }
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

    impl Forest<Terms> {
        /// Produces elements in `self` based on their presence in any of `others`.
        ///
        /// The `semi` argument controls whether this performs a semijoin or an antijoin,
        /// where a semijoin retains elements that are in common with `others`, whereas
        /// an antijoin retains elements not in common with `others`.
        ///
        /// All of `others` should have the same number of layers, and no more than `self`.
         #[inline(never)]
        pub fn retain_join<'a>(mut self, others: impl Iterator<Item = &'a Self>, semi: bool) -> Self {

            use std::collections::VecDeque;

            let others = others.collect::<Vec<_>>();
            if others.is_empty() { return if semi { Self::default() } else { self }; }
            let other_arity = others[0].layers.len();
            others.iter().for_each(|other| {
                assert!(self.layers.len() >= other.layers.len());
                assert_eq!(other.layers.len(), other_arity);
            });

            // First, collect reports to determine paths to retain to `self`.
            let mut include = std::iter::repeat(!semi).take(self.layers[other_arity-1].list.values.len()).collect::<VecDeque<_>>();
            let mut reports = VecDeque::default();
            for other in others.iter() {
                reports.push_back((0, 0));
                for (layer0, layer1) in self.layers.iter().zip(other.layers.iter()) {
                    layer0.intersection(layer1, &mut [reports.len()], &mut reports);
                }
                // Mark shared paths appropriately.
                for (index,_) in reports.drain(..) {
                    include[index] = semi;
                }
            }

            // If not all items are included, restrict layers of `self`.
            if include.iter().all(|x| *x) { return self; }
            else {
                // If there are additional layers, clone `include` and update unexplored layers.
                if self.layers.len() > other_arity {
                    let mut include = include.clone();
                    for layer in self.layers[other_arity..].iter_mut() {
                        layer.retain_lists(&mut include);
                    }
                }
                // In any case, update prior layers from `other_arity` back to the first.
                for layer in self.layers[..other_arity].iter_mut().rev() {
                    if include.iter().all(|x| *x) { return self; }  // TODO: make this test cheaper.
                    layer.retain_items(&mut include);
                }
            }
            self
        }
    }
}

/// Implementations for `Forest<Vec<[u8; K]>>`, for fixed-width byte arrays.
///
/// These implementations are all a smell, in that their requirement that all columns have the same type
/// speaks to non-columnar implementations.
pub mod byte_array {

    use columnar::{Container, Len};
    use crate::facts::{FactLSM, Lists, Terms};
    use super::{Forest, Layer};

    /// Support method for binary joins on arrays of bytes.
    ///
    /// Identifies prefixes `this[..arity]` and `that[..arity]` that match, and populates fact lsms
    /// based on requested `projections`. Each projection contains integers that call out columns as
    /// if columns of `this` and `that` were simply appended.
    #[inline(never)]
    pub fn join_help<'a, const K: usize>(
        this: &[<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>],
        that: &[<Lists<Vec<[u8; K]>> as Container>::Borrowed<'a>],
        arity: usize,
        projections: &[&[usize]],
    ) -> Vec<FactLSM<Forest<Terms>>> {

        if projections.is_empty() { return Vec::default(); }
        if this.len() < arity || that.len() < arity { return Vec::default(); }

        let mut builders: Vec<FactLSM<Forest<Terms>>> = vec![FactLSM::default(); projections.len()];

        if this.last().is_some_and(|l| l.is_empty()) || that.last().is_some_and(|l| l.is_empty()) { return builders; }

        use std::collections::BTreeMap;

        // Recording the column identifiers needed for each by reason.
        let mut both_need: BTreeMap<usize, Vec<usize>> = Default::default();
        let mut this_need: BTreeMap<usize, Vec<usize>> = Default::default();
        let mut that_need: BTreeMap<usize, Vec<usize>> = Default::default();

        // Introduce empty lists for columns we must retain.
        for column in projections.iter().flat_map(|x| x.iter()).copied() {
            if column < arity { both_need.insert(column, Vec::default()); }
            else if column < this.len() { this_need.insert(column - arity, Vec::default()); }
            else if column < this.len() + arity { both_need.insert(column - this.len(), Vec::default()); }
            else { that_need.insert(column - this.len() - arity, Vec::default()); }
        }

        // Determine the alignments of shared prefixes.
        // `reports` will contain all pairs of matching path prefixes, from `this` and `that`.
        let mut reports = std::collections::VecDeque::default();
        reports.push_back((0, 0));
        for (index, (layer0, layer1)) in this[..arity].iter().zip(that[..arity].iter()).enumerate() {
            crate::facts::trie::layers::intersection::<Vec<[u8;K]>>(*layer0, *layer1, &mut [reports.len()], &mut reports);
            // If we need to retain the column, then record the aligned indexes in the `this` layer.
            both_need.get_mut(&index).map(|a| a.extend(reports.iter().map(|(i,_)| *i)));
        }

        // NB: From this point on the method is "less columnar". The plan is to improve this.

        /// Establishes multiplicities for layers of `targets` starting from lists in `aligned`.
        #[inline(never)]
        fn flattening<'a, const K: usize>(
            targets: impl Iterator<Item=usize>,
            layers: &[<Lists<Vec<[u8;K]>> as Container>::Borrowed<'a>],
            aligned: impl Iterator<Item=usize> + Clone,
        ) -> (BTreeMap<usize, Vec<[u8;K]>>, Vec<usize>) {

            // For each retained layer other than the last, for each present item, the number of times we need it repeated.
            let this_counts: BTreeMap::<usize, Vec<[u8;K]>> =
            targets.map(|key| {
                let mut layer = 0;
                let mut bounds = aligned.clone().map(|i| layers[0].bounds.bounds(i)).collect::<Vec<_>>();
                // Project forward until we identify the *items* of layer `key`.
                while layer < key {
                    layer += 1;
                    for (lower, upper) in bounds.iter_mut() {
                        *lower = layers[layer].bounds.bounds(*lower).0;
                        *upper = layers[layer].bounds.bounds(*upper - 1).1;
                    }
                }

                let flat = if layer + 1 == layers.len() {
                    bounds.iter().copied().flat_map(|(lower, upper)| (lower .. upper).map(|i| columnar::Index::get(layers[layer].values, i))).collect::<Vec<_>>()
                }
                else {
                    let indexes = bounds.iter().copied().flat_map(|(lower, upper)| lower .. upper).collect::<Vec<_>>();
                    // Project forward to determine the counts required for each item.
                    let mut bounds = indexes.iter().copied().map(|i| (i, i+1)).collect::<Vec<_>>();
                    while layer + 1 < layers.len() {
                        layer += 1;
                        for (lower, upper) in bounds.iter_mut() {
                            *lower = layers[layer].bounds.bounds(*lower).0;
                            *upper = layers[layer].bounds.bounds(*upper - 1).1;
                        }
                    }
                    let counts = bounds.into_iter().map(|(l,u)| u - l);
                    // Flatten the (index, count) into repetitions.
                    indexes.iter().zip(counts).flat_map(|(i,c)| {
                        let bytes: [u8; K] = columnar::Index::get(layers[key].values, *i);
                        std::iter::repeat(bytes).take(c)
                    }).collect::<Vec<_>>()
                };
                (key, flat)
            }).collect::<BTreeMap<_,_>>();

            // Teaches us about the length of each interval, which we may not otherwise record.
            // Crucial for the blocking of flattened extensions.
            let mut this_bounds = aligned.map(|i| (i,i+1)).collect::<Vec<_>>();
            for layer in layers.iter() {
                for (lower, upper) in this_bounds.iter_mut() {
                    *lower = layer.bounds.bounds(*lower).0;
                    *upper = layer.bounds.bounds(*upper - 1).1;
                }
            }

            let counts = this_bounds.into_iter().map(|(l,u)| u - l).collect::<Vec<_>>();

            (this_counts, counts)
        }

        // TODO: walk backwards through retained layers, then project forwards until a retained layer is found.
        let mut both_flat: BTreeMap::<usize, Vec<[u8;K]>> = Default::default();
        for (key, val) in both_need.into_iter() {
            // map bounds for `key` forward until they reach `result`.
            let mut bounds = val.iter().copied().map(|i| (i,i+1)).collect::<Vec<_>>();
            for layer in (key .. arity).skip(1) {
                for (lower, upper) in bounds.iter_mut() {
                    *lower = this[layer].bounds.bounds(*lower).0;
                    *upper = this[layer].bounds.bounds(*upper - 1).1;
                }
            }
            // intersect each bound with `reports`.
            let mut aligned = reports.iter().map(|(i,_)| *i).peekable();
            let counts = bounds.iter().map(|(l,u)| {
                let mut count = 0;
                while aligned.next_if(|x| x < l).is_some() { }
                while aligned.next_if(|x| x < u).is_some() { count += 1; }
                count
            });

            // Flatten the (index, count) into repetitions.
            let flat = val.iter().zip(counts).flat_map(|(i,c)| {
                let bytes: [u8; K] = columnar::Index::get(this[key].values, *i);
                std::iter::repeat(bytes).take(c)
            }).collect::<Vec<_>>();

            both_flat.insert(key, flat);
        }

        // Produce flattening instructions, and blocking information.
        let (this_flat, this_counts) = flattening(this_need.keys().copied(), &this[arity..], reports.iter().map(|x| x.0));
        let (that_flat, that_counts) = flattening(that_need.keys().copied(), &that[arity..], reports.iter().map(|x| x.1));

        // Move through `reports` and populate allocations to provide to builders.
        let mut buffered = 0;
        let mut buffers: Vec<Vec<[u8; K]>> = projections.iter().map(|p| Vec::with_capacity(1_000_000 * p.len())).collect();

        let mut this_cursor = 0;
        let mut that_cursor = 0;
        for (index, (count0, count1)) in this_counts.iter().zip(that_counts.iter()).enumerate() {
            if buffered + count0 * count1 > 1_000_000 {
                for index in 0 .. projections.len() {
                    builders[index].push(Forest::downgrade(Forest::from_bytes(&mut buffers[index], projections[index].len())));
                    buffers[index].clear();
                }
                buffered = 0;
            }
            // blat down the bytes for each projection.
            for (projection, buffer) in projections.iter().zip(buffers.iter_mut()) {
                let buffer_start = buffer.len();
                buffer.resize((buffered + count0 * count1) * projection.len(), [255; K]);
                for (p_index, column) in projection.iter().copied().enumerate() {
                    if column < arity {
                        let value = both_flat[&column][index];
                        for pos in 0 .. count0 * count1 {
                            buffer[buffer_start + p_index + (projection.len() * pos)] = value;
                        }
                    }
                    else if column < this.len() {
                        let values = &this_flat[&(column-arity)][this_cursor ..][..*count0];
                        for this_idx in 0 .. *count0 {
                            for that_idx in 0 .. *count1 {
                                buffer[buffer_start + p_index + (projection.len() * (count1 * this_idx + that_idx))] = values[this_idx];
                            }
                        }
                    }
                    else if column < this.len() + arity {
                        unimplemented!()
                    }
                    else {
                        let values = &that_flat[&(column-arity-this.len())][that_cursor ..][..*count1];
                        for this_idx in 0 .. *count0 {
                            for that_idx in 0 .. *count1 {
                                buffer[buffer_start + p_index + (projection.len() * (count1 * this_idx + that_idx))] = values[that_idx];
                            }
                        }
                    }
                }
            }

            this_cursor += count0;
            that_cursor += count1;
            buffered += count0 * count1;
        }

        for index in 0 .. projections.len() {
            builders[index].push(Forest::downgrade(Forest::from_bytes(&mut buffers[index], projections[index].len())));
        }

        builders
    }

    impl<const K: usize> Forest<Vec<[u8; K]>> {
        /// Produce a forest of `width` layers from byte arrays.
        pub fn from_bytes(bytes: &mut [[u8; K]], width: usize) -> Self {
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
                if let Some(pos) = facts[i].iter().zip(facts[i-1].iter()).position(|(i0, i1)| i0 != i1) {
                    for to_seal in pos+1 .. W { layers[to_seal].list.bounds.push(layers[to_seal].list.values.len() as u64); }
                    for to_push in pos   .. W { layers[to_push].list.values.push(facts[i][to_push]); }
                }
            }

            layers.iter_mut().for_each(|layer| layer.list.bounds.push(layer.list.values.len() as u64));

            Self { layers: layers.into_iter().collect() }
        }
    }
}

/// Layer-at-a-time functionality.
///
/// These are meant to be the high-performance kernels used by forests of more general layers.
/// Implementations for `Layer<Terms>` are "abstract" and not performance optimized, whereas
/// the implementations for generic container types are "specialized" and potentially efficient.
pub mod layers {

    use std::collections::VecDeque;
    use columnar::{Columnar, Container, Index, Len};

    use crate::facts::{Lists, Terms};
    use crate::facts::{upgrade_hint, upgrade, downgrade};
    use super::Layer;

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

    /// Layer-at-a-time methods for general `Layer<Term>` types, specialized as appropriate.
    ///
    /// These methods are specialized to various array sizes, mostly for demonstration purposes.
    /// These sizes are not specifically important, but we do want to support this sort of thing.
    impl Layer<Terms> {
        /// Unions two layers, aligned through `reports`, which is refilled if `next` is set.
        pub fn union(&self, other: &Self, reports: &mut VecDeque<Report>, next: bool) -> Self {
            let lists0 = self.borrow();
            let lists1 = other.borrow();
            let list = match (upgrade_hint(lists0), upgrade_hint(lists1)) {
                (Some(1), Some(1)) => { downgrade(union(upgrade::<1>(lists0).unwrap(), upgrade::<1>(lists1).unwrap(), reports, next)) }
                (Some(2), Some(2)) => { downgrade(union(upgrade::<2>(lists0).unwrap(), upgrade::<2>(lists1).unwrap(), reports, next)) }
                (Some(3), Some(3)) => { downgrade(union(upgrade::<3>(lists0).unwrap(), upgrade::<3>(lists1).unwrap(), reports, next)) }
                (Some(4), Some(4)) => { downgrade(union(upgrade::<4>(lists0).unwrap(), upgrade::<4>(lists1).unwrap(), reports, next)) }
                _ => { union(lists0, lists1, reports, next) }
            };
            Layer { list }
        }
        /// Intersects two layers, aligned through `aligns`.
        pub fn intersection(&self, other: &Self, counts: &mut [usize], aligns: &mut VecDeque<(usize, usize)>) {
            // Borrow the layers for read-only access.
            let lists0 = self.borrow();
            let lists1 = other.borrow();
            // Update `aligns` for the next layer, or output.
            match (upgrade_hint(lists0), upgrade_hint(lists1)) {
                (Some(1), Some(1)) => { intersection::<Vec<[u8; 1]>>(upgrade::<1>(lists0).unwrap(), upgrade::<1>(lists1).unwrap(), counts, aligns); }
                (Some(2), Some(2)) => { intersection::<Vec<[u8; 2]>>(upgrade::<2>(lists0).unwrap(), upgrade::<2>(lists1).unwrap(), counts, aligns); }
                (Some(3), Some(3)) => { intersection::<Vec<[u8; 3]>>(upgrade::<3>(lists0).unwrap(), upgrade::<3>(lists1).unwrap(), counts, aligns); }
                (Some(4), Some(4)) => { intersection::<Vec<[u8; 4]>>(upgrade::<4>(lists0).unwrap(), upgrade::<4>(lists1).unwrap(), counts, aligns); }
                _ => { intersection::<Terms>(lists0, lists1, counts, aligns); }
            };
        }
        /// Retains lists indicated by `retain`, which is refilled.
        pub fn retain_lists(&mut self, retain: &mut VecDeque<bool>) {
            let lists = self.borrow();
            self.list = match upgrade_hint(lists) {
                Some(1) => { downgrade(retain_lists(upgrade::<1>(lists).unwrap(), retain)) }
                Some(2) => { downgrade(retain_lists(upgrade::<2>(lists).unwrap(), retain)) }
                Some(3) => { downgrade(retain_lists(upgrade::<3>(lists).unwrap(), retain)) }
                Some(4) => { downgrade(retain_lists(upgrade::<4>(lists).unwrap(), retain)) }
                _______ => { retain_lists(lists, retain) }
            };
        }
        /// Retains items indicated by `retain`, which is refilled.
        pub fn retain_items(&mut self, retain: &mut VecDeque<bool>) {
            let lists = self.borrow();
            self.list = match upgrade_hint(lists) {
                Some(1) => { downgrade(retain_items(upgrade::<1>(lists).unwrap(), retain)) }
                Some(2) => { downgrade(retain_items(upgrade::<2>(lists).unwrap(), retain)) }
                Some(3) => { downgrade(retain_items(upgrade::<3>(lists).unwrap(), retain)) }
                Some(4) => { downgrade(retain_items(upgrade::<4>(lists).unwrap(), retain)) }
                _______ => { retain_items(lists, retain) }
            };
        }
    }

    /// Merges two sequences of lists using alignment information in `reports`.
    ///
    /// The `next` parameter indicates whether the next round of reports should be prepared,
    /// which is for example not necessary in the last layer of a union, as there is no next
    /// layer to prepare reports for, and the cost can be higher there than for prior layers.
    #[inline(never)]
    pub fn union<'a, C: Container<Ref<'a>: Ord>>(
        lists0: <Lists<C> as Container>::Borrowed<'a>,
        lists1: <Lists<C> as Container>::Borrowed<'a>,
        reports: &mut VecDeque<Report>,
        next: bool,
    ) -> Lists<C> {

        let mut list = <Lists::<C> as Container>::with_capacity_for([lists0, lists1].into_iter());

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
                                crate::facts::gallop(lists0.values, &mut lower0, upper0, |x| x < val1);
                                if next { reports.push_back(Report::This(start, lower0)); }
                                list.values.extend_from_self(lists0.values, start .. lower0);
                            },
                            std::cmp::Ordering::Equal => {
                                if next { reports.push_back(Report::Both(lower0, lower1)); }
                                list.values.extend_from_self(lists0.values, lower0 .. lower0+1);
                                lower0 += 1;
                                lower1 += 1;
                            },
                            std::cmp::Ordering::Greater => {
                                let start = lower1;
                                lower1 += 1;
                                crate::facts::gallop(lists1.values, &mut lower1, upper1, |x| x < val0);
                                if next { reports.push_back(Report::That(start, lower1)); }
                                list.values.extend_from_self(lists1.values, start .. lower1);
                            },
                        }
                    }
                    if lower0 < upper0 {
                        list.values.extend_from_self(lists0.values, lower0 .. upper0);
                        if next { reports.push_back(Report::This(lower0, upper0)); }
                    }
                    if lower1 < upper1 {
                        list.values.extend_from_self(lists1.values, lower1 .. upper1);
                        if next { reports.push_back(Report::That(lower1, upper1)); }
                    }
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

    /// Intersects pairs of lists aligned by `aligns`, refilling it with aligned list items.
    ///
    /// The `counts` argument blocks the aligns, and we update it to maintain this property.
    /// The sum of `counts` should equal the length of `aligns`, and this should remain true
    /// after the method returns. Each count should be updated to the number of matched
    /// items among the aligned lists associated with the count. The counts allow us to move
    /// in the reverse direction, from aligned indexes back to prefixes that gave rise to them.
    #[inline(never)]
    pub fn intersection<'a, C: Container<Ref<'a>: Ord>>(
        list0: <Lists<C> as Container>::Borrowed<'a>,
        list1: <Lists<C> as Container>::Borrowed<'a>,
        counts: &mut [usize],
        aligns: &mut VecDeque<(usize, usize)>,
    ) {
        assert_eq!(counts.iter().sum::<usize>(), aligns.len());
        for count in counts.iter_mut() {

            let aligns_len = aligns.len();
            for _ in 0 .. *count {

                let (index0, index1) = aligns.pop_front().unwrap();

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
                            crate::facts::gallop(list0.values, &mut lower0, upper0, |x| x < val1);
                        },
                        std::cmp::Ordering::Equal => {
                            aligns.push_back((lower0, lower1));
                            lower0 += 1;
                            lower1 += 1;
                        },
                        std::cmp::Ordering::Greater => {
                            lower1 += 1;
                            crate::facts::gallop(list1.values, &mut lower1, upper1, |x| x < val0);
                        },
                    }
                }
            }
            // New count is the number we've added, equal to what we have now, minus what we could have with no additions.
            *count = aligns.len() - (aligns_len - *count);
        }
    }

    // TODO: This method needs to be at most ~linear in the number of items that will be written out.
    // TODO: Invocations of this method will not have their bounds grow in number of intervals, and so
    //       we can re-use an argument `&mut [(usize, usize)]` to house the output bounds.
    /// Restrict lists based on per-list bools, producing a new layer and updating `bools` for the items.
    #[inline(never)]
    pub fn retain_lists<'a, C: Container>(lists: <Lists<C> as Container>::Borrowed<'a>, bools: &mut VecDeque<bool>) -> Lists<C> {

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

    // TODO: This method needs to be at most ~linear in the number of items that will be written out.
    // TODO: Invocations of this method will not have their bounds grow in number of intervals, and so
    //       we can re-use an argument `&mut [(usize, usize)]` to house the output bounds.
    /// Restrict lists based on per-item bools, producing a new layer and updating `bools` for the lists.
    #[inline(never)]
    pub fn retain_items<'a, C: Container>(lists: <Lists<C> as Container>::Borrowed<'a>, bools: &mut VecDeque<bool>) -> Lists<C> {

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
}
