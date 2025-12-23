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

use columnar::Container;
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

    pub fn borrow<'a>(&'a self) -> Vec<<Lists<C> as Container>::Borrowed<'a>> {
        self.layers.iter().map(|x| x.list.borrow()).collect::<Vec<_>>()
    }
}

/// Advances pairs of lower and upper bounds on lists through each presented layer, to lower and upper bounds on items.
pub fn advance_bounds<C: Container>(layers: &[<Lists<C> as Container>::Borrowed<'_>], bounds: &mut[(usize, usize)]) {
    for layer in layers.iter() { crate::facts::trie::layers::advance_bounds::<C>(*layer, bounds); }
}

/// A sequence of `[T]` ordered lists, each acting as a map.
///
/// For each integer input, corresponding to a path to a tree node,
/// the node forks by way of the associated list of `T`, where each
/// child has an index that can be used in a next layer (or not!).
#[derive(Clone, Debug, Default)]
pub struct Layer<C> { pub list: Lists<C> }

impl<C: Container> Layer<C> {
    pub fn borrow(&self) -> <Lists<C> as Container>::Borrowed<'_> { self.list.borrow() }
}

/// Implementations for `Forest<Terms>`, for generic byte slices.
pub mod terms {

    use std::rc::Rc;
    use columnar::{Container, Index, Len};
    use crate::facts::{FactContainer, FactLSM, Lists, Terms};
    use crate::facts::trie::layers::Report;
    use crate::types::Action;

    use super::{Forest, Layer};

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

    impl Forest<Terms> {
        /// Forms a forest trie from a sequence of columns of identical lengths.
        ///
        /// This method takes ownership of the columns in order to drop them as they are processed.
        /// It could be generalized to `Vec<C>` for any `C` that can be borrowed as `Terms` can be.
        pub fn from_columns<'a>(columns: Vec<Terms>) -> Self {
            let (mut groups, indexs): (Vec<_>, Vec<_>) = (0 .. columns.first().map(columnar::Len::len).unwrap_or(0)).map(|i| (0, i)).unzip();
            let columns_len = columns.len();
            let layers = columns.into_iter().enumerate().map(|(index, column)| {

                use columnar::{Vecs, primitive::offsets::Strides};
                let bounds = Strides::new(1, column.len() as u64);
                let lists = Vecs {
                    bounds: bounds.borrow(),
                    values: column.borrow(),
                };
                // TODO: Figure out how to avoid `indexs` being literally just `0 .. len`.
                Layer { list: crate::facts::trie::layers::sort_terms(lists, &mut groups[..], &indexs[..], index == columns_len-1) }
            }).collect();
            Self { layers }
        }
    }

    // Support methods for `<Forest<Terms> as FactContainer>::act_on`.
    impl Forest<Terms> {
        /// Filters `self` to facts satisfying literal and inter-column equalities.
        ///
        /// The argument `lit_filters` names columns and a literal they must equal, and `var_filters`
        /// identifies sets of column identifiers whose values must be equal.
        ///
        /// Each column should occur in at most one constraint, as otherwise they could be strengthened.
        /// For the moment, this is the caller's responsibility.
        #[inline(never)]
        fn filter(&self, lit_filters: &[(usize, Vec<u8>)], var_filters: &[Vec<usize>]) -> Self {

            // Plan the constraints applied to each column, to visit them in order.
            let mut constraints = std::collections::BTreeMap::<usize, Result<usize, &[u8]>>::default();
            for (col, lit) in lit_filters.iter() { constraints.insert(*col, Err(lit)); }
            for group in var_filters.iter().filter(|g| g.len() > 1) {
                let min = group.iter().min().unwrap();
                for col in group.iter() { if col > min { constraints.insert(*col, Ok(*min)); } }
            }

            let mut active = (0 .. self.layers[0].list.values.len()).collect::<Vec<_>>();
            let mut cursor = 0;
            for (col, filter) in constraints {
                self.layers[cursor+1 .. col+1].iter().for_each(|l| {
                    active = active.drain(..).flat_map(|i| { let (l,u) = l.list.bounds.bounds(i); l .. u}).collect::<Vec<_>>();
                });
                cursor = col;
                // `bounds` are now in terms of `col`s items.
                match filter {
                    Ok(idx) => {
                        // naively start from all items at layer `idx`; could optimize to the active subset at the time.
                        let mut bounds = (0 .. self.layers[idx].list.values.len()).map(|i| (i, i+1)).collect::<Vec<_>>();
                        crate::facts::trie::advance_bounds::<Terms>(&self.borrow()[idx+1..col+1], &mut bounds);

                        let mut active_peek = active.iter().copied().peekable();
                        let aligned = bounds.iter().enumerate().flat_map(|(i,(l,u))| {
                            let mut count = 0;
                            while active_peek.next_if(|x| x < l).is_some() { }
                            while active_peek.next_if(|x| x < u).is_some() { count += 1; }
                            std::iter::repeat(i).take(count)
                        }).collect::<Vec<_>>();

                        crate::facts::trie::layers::filter_items::<Terms>(self.layers[col].borrow(), &mut active, self.layers[idx].list.values.borrow(), &aligned[..]);
                    }
                    Err(lit) => {
                        let mut literal = Lists::<Terms>::default();
                        use columnar::Push; literal.push([lit]);
                        let aligned = std::iter::repeat(0).take(active.len()).collect::<Vec<_>>();
                        crate::facts::trie::layers::filter_items::<Terms>(self.layers[col].borrow(), &mut active, literal.values.borrow(), &aligned[..])
                    }
                }
            }

            // use `active` at `cursor` to retain lists and items.
            let mut include = std::iter::repeat(false).take(self.layers[cursor].list.values.len()).collect::<std::collections::VecDeque<_>>();
            for idx in active.iter().copied() { include[idx] = true; }
            let mut result = self.clone();
            // If there are additional layers, clone `include` and update unexplored layers.
            if result.layers.len() > cursor {
                let mut bounds = active.iter().copied().map(|i| (i,i+1)).collect::<Vec<_>>();
                for layer in result.layers[cursor..].iter_mut().skip(1) {
                    *layer = layer.retain_lists(&mut bounds);
                }
            }
            // In any case, update prior layers from `other_arity` back to the first.
            for layer in result.layers[..cursor+1].iter_mut().rev() {
                if include.iter().all(|x| *x) { return result; }  // TODO: make this test cheaper.
                *layer = layer.retain_items(&mut include);
            }

            result
        }
        /// Produces columns in the order indicated by `projection`. Each column should appear at most once.
        #[inline(never)]
        fn permute(&self, projection: &[usize]) -> Self {
            let indexs = (0 .. self.layers[0].list.len()).collect::<Vec<_>>();
            Self { layers: permute_subset(&self.borrow()[..], projection, &indexs) }
        }
        /// Introduces repeated and literal columns.
        ///
        /// It is important that `projection` introduce columns in strict numeric order, but it can repeat
        /// an introduced column or a introduce a literal column at any point.
        #[inline(never)]
        fn embellish(&mut self, projection: &[Result<usize, Vec<u8>>]) {

            let mut layers = Vec::with_capacity(projection.len());
            for (pos, col) in projection.iter().enumerate().rev() {
                layers.push(match col {
                    Ok(col) => {
                        let first_pos = projection.iter().position(|c| c == &Ok(*col)).unwrap();
                        if first_pos == pos { self.layers.pop().unwrap() }
                        else {  // create a copy of this column at the end of `layers`.
                            let mut bounds = (0 .. self.layers[*col].list.values.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
                            for layer in self.layers[*col..].iter().skip(1) { crate::facts::trie::layers::advance_bounds::<Terms>(layer.borrow(), &mut bounds[..]); }
                            let mut list = Lists::<Terms>::default();
                            for (index, (lower, upper)) in bounds.into_iter().enumerate() {
                                for _ in lower .. upper { use columnar::Push; list.push([self.layers[*col].list.values.borrow().get(index)]); }
                            }
                            Layer { list }
                        }
                    },
                    Err(lit) => {
                        let count = self.layers.last().map(|l| l.list.values.len()).expect("prepending literals isn't yet correct");
                        let mut list = Lists::<Terms>::default();
                        for _ in 0 .. count { use columnar::Push; list.push([lit]); }
                        Layer { list }
                    },
                });
            }
            layers.reverse();
            self.layers = layers;
        }
    }

    /// Produces columns in the order indicated by `projection`, for the subset of indexes in `indexs`.
    #[inline(never)]
    fn permute_subset(in_layers: &[<Lists<Terms> as Container>::Borrowed<'_>], projection: &[usize], indexs: &[usize]) -> Vec<Layer<Terms>> {

        for index in 1 .. in_layers.len() {
            assert_eq!(in_layers[index-1].values.len(), in_layers[index].len());
        }

        // Determine a leading prefix of the form `0 ..`. These columns can be extracted efficiently.
        let mut prefix = 0;
        while projection.get(prefix) == Some(&prefix) { prefix += 1; }

        if prefix > 0 {

            let mut output = Vec::with_capacity(projection.len());

            let mut bounds = indexs.iter().copied().map(|i| (i,i+1)).collect::<Vec<_>>();
            for layer in 0 .. prefix {
                let mut out_layer = <Lists::<Terms> as Container>::with_capacity_for([in_layers[layer]].into_iter());
                for (lower, upper) in bounds.iter().copied() { out_layer.extend_from_self(in_layers[layer], lower .. upper); }
                output.push(Layer { list: out_layer });
                crate::facts::trie::layers::advance_bounds::<Terms>(in_layers[layer], &mut bounds);
            }

            // If columns remain, we should reform the input and call into `permute_subset_inner`.
            if projection.len() > prefix {
                let in_layers2 = &in_layers[prefix..];
                let projection2 = projection[prefix..].iter().map(|c| *c - prefix).collect::<Vec<_>>();
                let indexs2 = bounds.iter().copied().flat_map(|(l,u)| l..u).collect::<Vec<_>>();
                output.extend(permute_subset_inner(in_layers2, &projection2, &indexs2));
            }

            output
        }
        else { permute_subset_inner(in_layers, projection, indexs) }
    }

    /// Produces the sequence of layers described by `projection` for the subset of root indexes `indexs` of `in_layers`.
    ///
    /// The implementation is based on the observation that the columns in `projection` come in one of two forms: they are
    /// either strictly greater than all prior column indexes in `projection` or they are not. In the former case we must
    /// expand the number of paths under discussion by moving indexes forward to the indicated column, and in the latter we
    /// only need to advance corresponding values of a prior column forward 1:1 to the current indexes.
    #[inline(never)]
    fn permute_subset_inner(in_layers: &[<Lists<Terms> as Container>::Borrowed<'_>], projection: &[usize], indexs: &[usize]) -> Vec<Layer<Terms>> {

        if projection.is_empty() { return Vec::default(); }

        // The plan is to maintain a list `groups` of ordering/grouping identifiers that will correspond with the subset of
        // items in some maximum layer in `in_layers` determined by starting from `indexs`.
        // As these paths are shuffled based on `projection`, `group` will reveal where each input path has ended up in the output.
        // As the maximum layer of `in_layers` advances we'll need to update (and likely expand) `group` to speak to paths identified by that layer's items.

        use crate::facts::trie::advance_bounds;

        // Retain the input indexes, from which we'll need to restart.
        let in_idxs = indexs;

        // Group always tracks the subset of lists at some layer; initially the 0th layer.
        // This will update as soon as we produce any columns, and will track the largest column index observed, plus one.
        let mut group_list_layer = 0;
        let mut groups = (0 .. indexs.len()).collect::<Vec<_>>();
        let mut indexs = indexs.to_vec();

        // Each column of `projection` produces an output layer.
        projection.iter().copied().enumerate().map(|(idx, col)| {

            // The column will advance `group_list_layer` if it is equal or greater, as we must move to that item layer.
            if col < group_list_layer {
                // First find the ranges of item identifiers in layer `col` we'll want to involve, by projecting forward.
                let mut idents = in_idxs.iter().copied().map(|i| (i,i+1)).collect::<Vec<_>>();
                advance_bounds::<Terms>(&in_layers[..col+1], &mut idents);
                // Next determine the number of repetitions needed for each individual identifier, by projecting forward.
                let mut bounds = Vec::with_capacity(idents.iter().map(|(l,u)| u-l).sum());
                bounds.extend(idents.iter().copied().flat_map(|(l,u)| (l..u).map(|i| (i,i+1))));
                advance_bounds::<Terms>(&in_layers[col+1..group_list_layer], &mut bounds);
                // Explicitly repeat each item identifier from layer `col` the appropriate number of times.
                // The length of `indexs` does not increase, so we only need to clear it and refill it.
                indexs.clear();
                indexs.extend(idents.iter().copied().flat_map(|(l,u)| l..u).zip(bounds.iter().copied().map(|(l,u)| u-l)).flat_map(|(i,c)| std::iter::repeat(i).take(c)));
            }
            else {
                // First, find the ranges of item identifiers in layer `group_list_layer`, by projecting forward.
                let mut idents = in_idxs.iter().copied().map(|i| (i,i+1)).collect::<Vec<_>>();
                advance_bounds::<Terms>(&in_layers[..group_list_layer], &mut idents);
                // Next determine the number of repetitions needed for each group identifier, by projecting forward.
                assert_eq!(groups.len(), idents.iter().map(|(l,u)| u-l).sum());
                let mut bounds = Vec::with_capacity(groups.len());
                bounds.extend(idents.iter().copied().flat_map(|(l,u)| (l..u).map(|i| (i,i+1))));
                advance_bounds::<Terms>(&in_layers[group_list_layer .. col+1], &mut bounds);
                // Explicitly repeat each group identifier the appropriate number of times.
                let new_count = bounds.iter().copied().map(|(l,u)| u-l).sum();
                let mut new_groups = Vec::with_capacity(new_count);
                let mut new_indexs = Vec::with_capacity(new_count);
                new_groups.extend(groups.iter().copied().zip(bounds.iter().map(|(l,u)| u-l)).flat_map(|(g,c)| std::iter::repeat(g).take(c)));
                new_indexs.extend(bounds.iter().copied().flat_map(|(l,u)| l..u));
                groups = new_groups;
                indexs = new_indexs;
                group_list_layer = col+1
            }

            let last = idx+1 == projection.len();
            Layer { list: crate::facts::trie::layers::sort_terms(in_layers[col], &mut groups, &indexs, last) }

        }).collect()

    }

    /// Aligns blocks of `self` and `other` by their first `arity` columns, and applies supplied projections.
    ///
    /// This method works column-by-column, first identifying pairs of item indexes in layers `arity-1` which
    /// correspond to equal paths in both inputs, then producing the results for each projection by column.
    ///
    /// Each projection should contain each column at most once. Repeated columns can be introduced afterwards,
    /// for example by the `Forest::embellish` method.
    #[inline(never)]
    fn join_cols(
        this: &[<Lists<Terms> as Container>::Borrowed<'_>],
        thats: &[&[<Lists<Terms> as Container>::Borrowed<'_>]],
        arity: usize,
        projection: &[usize],
    ) -> FactLSM<Forest<Terms>> {

        if thats.len() == 0 { return Default::default(); }
        if this.len() < arity { return Default::default(); }
        if this.last().is_some_and(|l| l.is_empty()){ return Default::default(); }

        assert!(thats.iter().all(|t| t.len() >= arity));

        // Determine the alignments of shared prefixes.
        let mut aligned = vec![(Rc::new(vec![0]), Rc::new(vec![0])); thats.len()];
        let mut aligneds = Vec::with_capacity(arity);
        for layer in 0 .. arity {
            let layer0 = &this[layer];
            let mut this_aligned = Vec::new();
            for other in 0 .. thats.len() {
                let layer1 = &thats[other][layer];
                let results = crate::facts::trie::layers::intersection::<Terms>(*layer0, *layer1, &aligned[other].0, &aligned[other].1);
                this_aligned.extend_from_slice(&results.0);
                aligned[other] = (Rc::new(results.0), Rc::new(results.1));
            }
            this_aligned.sort();
            this_aligned.dedup();
            aligneds.push(Rc::new(this_aligned));
        }

        // Produce `this_i` and `this_values`, indexes into columns in the order they appear in `projection`.
        let mut this_i = aligneds.last().unwrap().clone();
        let mut this_values = None;
        let mut this_order = Vec::default();
        for col in projection.iter().copied() { if arity <= col && col < this.len() && !this_order.contains(&(col - arity)) { this_order.push(col - arity); } }
        if this_order != (0 .. this_order.len()).collect::<Vec<_>>() {
            let layers = permute_subset(&this[arity..], &this_order[..], &this_i[..]);
            this_values = Some(Forest { layers });
            let this_i = Rc::make_mut(&mut this_i);
            for i in 0 .. this_i.len() { this_i[i] = i; }
        }
        let this_values = this_values.as_ref().map(|x| x.borrow()).unwrap_or(this[arity..].to_vec());

        // Produce `that_j` and `that_values`, indexes into columns in the order they appear in `projection`.
        // We'll default to the indexes and layers of `thats[0]`, and override them if more thats, or if the projection is non-trivial.
        let mut that_j = aligned[0].1.clone();
        let mut that_values = None;
        let mut that_order = Vec::default();
        for col in projection.iter().copied() { if this.len() + arity <= col && !that_order.contains(&(col - arity - this.len())) { that_order.push(col - arity - this.len()); } }
        if thats.len() > 1 || that_order != (0 .. that_order.len()).collect::<Vec<_>>() {
            let thats_values = thats.iter().map(|t| &t[arity..]).collect::<Vec<_>>();
            let thats_groups = aligned.iter().map(|(i,_)| &i[..]).collect::<Vec<_>>();
            let thats_indexs = aligned.iter().map(|(_,j)| &j[..]).collect::<Vec<_>>();
            that_values = Some( Forest { layers: restrict_project_merge(&thats_values, &thats_groups, &thats_indexs, &that_order) });
            let that_j = Rc::make_mut(&mut that_j); that_j.clear(); that_j.extend(0 .. this_i.len());
        }
        let that_values = that_values.as_ref().map(|x| x.borrow()).unwrap_or(thats[0][arity..].to_vec());

        // At this point we can see the work we have to do, and may want to stage it to avoid doing everything at once.
        // We'll scan forward from `this_i` and `that_j` to assess the cardinality we'll produce, and only peel off as
        // much work as we feel comfortable doing before taking a beat to deduplicate (forming and pushing into an LSM).
        // We can work on an arbitrary subset of the aligned indexes, as long as we copy the indexes for manipulation.

        // Restarting points for counting sizes for pre-`arity` columns.
        let aligned = (this_i.clone(), that_j.clone());

        // A list of counts of the numbers of outputs for each aligned index.
        // We will reference this in determining how many aligned indexes to pull off at a time.
        let counts = {
            let mut this_bounds = aligned.0.iter().map(|i| (*i,*i+1)).collect::<Vec<_>>();
            crate::facts::trie::advance_bounds::<Terms>(&this_values[..], &mut this_bounds[..]);
            let mut that_bounds = aligned.1.iter().map(|j| (*j,*j+1)).collect::<Vec<_>>();
            crate::facts::trie::advance_bounds::<Terms>(&that_values[..], &mut that_bounds[..]);
            this_bounds.iter().zip(that_bounds.iter()).map(|((l0,u0),(l1,u1))| (u0-l0) * (u1-l1)).collect::<Vec<_>>()
        };

        let mut output_lsm: FactLSM<Forest<Terms>> = Default::default();
        let mut aligned_pos = 0;
        while aligned_pos < counts.len() {

            // Assess the size of the output we'll produce, in order to judge if we should parcel out the work.
            let aligned_prev = aligned_pos;
            let mut aligned_sum = 0;
            while aligned_pos < counts.len() && aligned_sum < 100_000_000 { aligned_sum += counts[aligned_pos]; aligned_pos += 1; }

            // Going in to the next phase, we'll need the following variables in scope:
            // 1. `this_i` and `this_values`: indexes of one into the other; same length as `that_j`. columns in order of appearance in `projection`.
            // 2. `that_j` and `that_values`: indexes of one into the other; same length as `this_i`. columns in order of appearance in `projection`.
            // 3. `old_aligned`: `this_i` for `this[arity..]` (not always `this_values`).
            // 4. `aligneds`: initial values of `this_i` for pre-`arity` layers.

            let mut this_i = Rc::new(this_i[aligned_prev .. aligned_pos].to_vec());
            let mut that_j = Rc::new(that_j[aligned_prev .. aligned_pos].to_vec());
            let old_aligned = Rc::new(aligneds.last().unwrap()[aligned_prev .. aligned_pos].to_vec());

            // The reference `this` indexes, used as a hand-off for pre-`arity` columns.
            // let old_aligned = aligneds.last().unwrap().clone();

            // Constraints on the grouping of the lists of the remaining columns to produce.
            let mut groups = std::iter::repeat(0).take(this_i.len()).collect::<Vec<_>>();

            // Cursors into `this_i` and `that_j`, respectively.
            let mut this_cursor = 0;
            let mut that_cursor = 0;

            // Layers correspond to the columns of `projection`, which we produce in turn.
            let layers = projection.iter().copied().enumerate().map(|(idx, column)| {

                use crate::facts::trie::layers::sort_terms;

                let last = idx+1 == projection.len();

                let list = if column < arity {
                    // Flow the column bounds forward to `aligned`, then count.

                    // First, let's determine the counts for each of `this` and `that` at `aligned`.
                    let mut this_bounds = aligned.0[aligned_prev .. aligned_pos].iter().map(|i| (*i,*i+1)).collect::<Vec<_>>();
                    crate::facts::trie::advance_bounds::<Terms>(&this_values[0 .. this_cursor], &mut this_bounds[..]);
                    let mut that_bounds = aligned.1[aligned_prev .. aligned_pos].iter().map(|j| (*j,*j+1)).collect::<Vec<_>>();
                    crate::facts::trie::advance_bounds::<Terms>(&that_values[0 .. that_cursor], &mut that_bounds[..]);

                    // Now let's project forward from `both_need[column]`.
                    let mut bounds = aligneds[column].iter().map(|i| (*i,*i+1)).collect::<Vec<_>>();
                    crate::facts::trie::advance_bounds::<Terms>(&this[column+1 .. arity], &mut bounds);

                    let mut products = this_bounds.iter().zip(that_bounds.iter()).map(|((l0,u0), (l1,u1))| (u0-l0)*(u1-l1))
                                                        .zip(old_aligned.iter().copied()).peekable();

                    let counts = bounds.iter().map(|(l,u)| {
                        let mut count = 0;
                        while products.next_if(|(_,x)| x < l).is_some() { }
                        while let Some((c,_)) = products.next_if(|(_,x)| x < u) { count += c; }
                        count
                    });

                    // Flatten the (index, count) into repetitions.
                    let mut flat = Vec::with_capacity(groups.len());
                    flat.extend(aligneds[column].iter().zip(counts).flat_map(|(i,c)| std::iter::repeat(*i).take(c)));
                    sort_terms(this[column], &mut groups, &flat, last)
                }
                else if column < this.len() {
                    // We expect this to be the next column in `this_values`.
                    let values = this_values[this_cursor];
                    this_cursor += 1;

                    // Expand `this_i`, and corresponding repetitions in `groups` and `that_j`.
                    let mut others = if that_cursor < that_values.len() { vec![&mut groups, Rc::make_mut(&mut that_j)] } else { vec![&mut groups] };
                    expand(Rc::make_mut(&mut this_i), values, &mut others);
                    sort_terms(values, &mut groups, &this_i, last)
                }
                else if column < this.len() + arity {
                    unimplemented!("reference equated column of first join argument")
                }
                else {
                    // We expect this to be the next column in `that_values`.
                    let values = that_values[that_cursor];
                    that_cursor += 1;

                    // Expand `that_j`, and corresponding repetitions in `groups` and `this_i`.
                    let mut others = if this_cursor < this_values.len() { vec![&mut groups, Rc::make_mut(&mut this_i)] } else { vec![&mut groups] };
                    expand(Rc::make_mut(&mut that_j), values, &mut others);
                    sort_terms(values, &mut groups, &that_j, last)
                };
                Layer { list }
            }).collect();

            output_lsm.push(Forest { layers });
        }

        output_lsm
    }

    /// For a list of tries with the same shape, extract lists at `[index]` and merge by `[group]`, yielding one sequence of layers in `projection` order.
    ///
    /// The first layer of the result should have as many lists as there are distinct values of `group`, with the implied correspondence.
    #[inline(never)]
    fn restrict_project_merge<'a>(
        layers: &[&[<Lists<Terms> as Container>::Borrowed<'a>]],
        groups: &[&[usize]],
        indexs: &[&[usize]],
        projection: &[usize],
    ) -> Vec<Layer<Terms>> {

        assert!(!layers.is_empty());
        assert_eq!(layers.len(), groups.len());
        assert_eq!(layers.len(), indexs.len());

        // TODO: can union from indexed layers without having to copy first.

        if layers.len() == 1 { permute_subset(&layers[0][..], &projection[..], &indexs[0]) }
        else {
            let mut extracted = FactLSM::default();
            for index in 0 .. layers.len() {

                let mut layers = permute_subset(&layers[index][..], &projection[..], &indexs[index]);
                let mut base: Layer<Terms> = Default::default();
                use columnar::Push;
                // TODO: rework layers to allow this to be something akin to `&groups[index]` without the copy.
                base.list.values.extend(groups[index].iter().map(|g| (*g as u32).to_be_bytes()));
                base.list.bounds.push(groups[index].len() as u64);
                layers.insert(0, base);
                extracted.layers.push(Forest { layers });

            }

            let mut merged = extracted.flatten().unwrap().layers;
            merged.remove(0);
            merged
        }
    }

    /// Expand vectors to track the bounds found in `lists` using indexes in `index`.
    ///
    /// The `index` vector has each item expanded in-place to the range found in `bounds`, while the other vectors have their
    /// indexes repeated a corresponding number of times to match the lengths of these ranges.
    ///
    /// In principle the explicit representation of the ranges and repetitions could be avoided, by updating `index` and reporting the range lengths.
    /// This would avoid resizing any of the vectors, only rewriting `index`, and pushing the work of unpacking any until later when actually needed.
    #[inline(never)]
    fn expand<'a>(index: &mut Vec<usize>, lists: <Lists<Terms> as Container>::Borrowed<'a>, others: &mut [&mut Vec<usize>]) {

        // Map out the number of repetitions for each position, and tally the total for pre-allocation.
        let mut total = 0;
        let mut counts = Vec::with_capacity(index.len());
        for i in index.iter_mut() {
            let (l,u) = lists.bounds.bounds(*i);
            *i = l;
            counts.push(u-l);
            total += u-l;
        }

        let mut index_new = Vec::with_capacity(total);
        for (index, count) in index.iter().copied().zip(counts.iter().copied()) { index_new.extend(index .. (index + count)); }
        *index = index_new;

        for other in others.iter_mut() {
            let mut other_new = Vec::with_capacity(total);
            for (other, count) in other.iter().copied().zip(counts.iter().copied()) { other_new.extend(std::iter::repeat(other).take(count)); }
            **other = other_new;
        }
    }

    impl FactContainer for Forest<Terms> {

        #[inline(never)]
        fn act_on(&self, action: &Action<Vec<u8>>) -> FactLSM<Self> {

            if self.is_empty() { return FactLSM::default(); }
            if action.is_identity() { return self.clone().into(); }

            //  Informally, we will stage the evaluation as three distinct actions:
            //  1.  An action that applies filtering operations to the input columns.
            //  2.  An action that permutes columns to the order they are introduced.
            //  3.  An action that inserts literal and repeated columns, as required.
            //  Ideally these actions would be fused, and not record intermediate work.
            //  Practically, that seems complicated and we'll start as easily as we can.

            //  1.  Filter by literal and variable equalities.
            let mut filtered = None;
            if !action.lit_filter.is_empty() || !action.var_filter.is_empty() {
                filtered = Some(self.filter(&action.lit_filter, &action.var_filter));
            }
            let new_self = filtered.as_ref().unwrap_or(self);

            //  2.  Produce distinct columns in order. Literals and repeats will be added next.
            let mut projection = Vec::with_capacity(action.projection.len());
            for col in action.projection.iter().flatten() { if !projection.contains(col) { projection.push(*col); } }
            let mut result = new_self.permute(&projection[..]);

            //  3.  If there were literals or repeats in projected columns, we need to add them in.
            let new_projection = action.projection.iter().cloned().map(|c| c.map(|i| projection.iter().position(|j| i == *j).unwrap())).collect::<Vec<_>>();
            result.embellish(&new_projection[..]);
            result.into()
        }

        fn join_many<'a>(&'a self, others: impl Iterator<Item = &'a Self>, arity: usize, projection: &[usize]) -> FactLSM<Self> {
            let others = others.filter(|o| !o.is_empty()).map(|o| o.borrow()).collect::<Vec<_>>();
            let others = others.iter().map(|o| &o[..]).collect::<Vec<_>>();
            join_cols(&self.borrow()[..], &others[..], arity, projection)
        }

        fn antijoin<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { self.retain_join::<'a>(others, false) }

        #[inline(never)] fn semijoin<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { self.retain_join::<'a>(others, true) }
    }

    impl Forest<Terms> {
        /// Produces elements in `self` based on their presence in any of `others`.
        ///
        /// The `semi` argument controls whether this performs a semijoin or an antijoin,
        /// where a semijoin retains elements that are in common with `others`, whereas
        /// an antijoin retains elements not in common with `others`.
        ///
        /// All of `others` should have the same number of layers, and no more than `self`.
        pub fn retain_join<'a>(self, others: impl Iterator<Item = &'a Self>, semi: bool) -> Self {
            let others = others.map(|o| o.borrow()).collect::<Vec<_>>();
            self.retain_inner(others.iter().map(|o| &o[..]), semi)
        }

        #[inline(never)]
        pub fn retain_inner<'a>(self, others: impl Iterator<Item = &'a [<Lists<Terms> as Container>::Borrowed<'a>]>, semi: bool) -> Self {

            if self.is_empty() { return self; }

            use std::collections::VecDeque;

            let others = others.collect::<Vec<_>>();
            if others.is_empty() { return if semi { Self::default() } else { self }; }
            let other_arity = others[0].len();
            others.iter().for_each(|other| {
                assert!(self.layers.len() >= other.len());
                assert_eq!(other.len(), other_arity);
            });

            // First, collect reports to determine paths to retain to `self`.
            let mut include = std::iter::repeat(!semi).take(self.layers[other_arity-1].list.values.len()).collect::<VecDeque<_>>();
            for other in others.iter() {
                let mut reports = (vec![0], vec![0]);
                for (layer0, layer1) in self.layers.iter().zip(other.iter()) {
                    reports = crate::facts::trie::layers::terms::intersection(layer0.borrow(), *layer1, &reports.0, &reports.1);
                }
                // Mark shared paths appropriately.
                for index in reports.0.iter().copied() {
                    include[index] = semi;
                }
            }

            self.retain_core(other_arity, include)
        }

        /// Retains facts based on a bitmap for a layer of the trie.
        ///
        /// The bitmap is inserted between layer_index - 1 and layer_index, restricting either the items of layer_index-1 or the lists of layer_index.
        pub fn retain_core(mut self, layer_index: usize, mut include: std::collections::VecDeque<bool>) -> Self {

            if layer_index > 0 { assert_eq!(include.len(), self.layers[layer_index-1].list.values.len()); }
            if layer_index < self.layers.len() { assert_eq!(include.len(), self.layers[layer_index].list.len()); }

            // If not all items are included, restrict layers of `self`.
            if include.iter().all(|x| *x) { return self; }
            else {
                // If there are additional layers, clone `include` and update unexplored layers.
                if self.layers.len() > layer_index {

                    let mut prev = None;
                    let mut bounds = Vec::default();
                    for (idx, retain) in include.iter().chain([&false]).enumerate() {
                        match (retain, &mut prev) {
                            (true, None) => { prev = Some(idx); },
                            (false, Some(lower) ) => { bounds.push((*lower, idx)); prev = None; }
                            _ => { },
                        }
                    }

                    for layer in self.layers[layer_index..].iter_mut() {
                        *layer = layer.retain_lists(&mut bounds);
                    }
                }
                // In any case, update prior layers from `layer_index` back to the first.
                for layer in self.layers[..layer_index].iter_mut().rev() {
                    if include.iter().all(|x| *x) { return self; }  // TODO: make this test cheaper.
                    *layer = layer.retain_items(&mut include);
                }
            }
            self
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
        pub fn union(&self, other: &Self, reports: &mut VecDeque<Report>, next: bool) -> Self { Self { list: terms::union(self.borrow(), other.borrow(), reports, next) } }

        /// Intersects two layers, aligned through `aligns`.
        pub fn intersection(&self, other: &Self, both0: &[usize], both1: &[usize]) -> (Vec<usize>, Vec<usize>) { terms::intersection(self.borrow(), other.borrow(), both0, both1) }

        /// Retains lists indicated by `retain`, which is refilled.
        pub fn retain_lists(&self, bounds: &mut [(usize, usize)]) -> Self { Self { list: terms::retain_lists(self.borrow(), bounds) } }

        /// Retains items indicated by `retain`, which is refilled.
        pub fn retain_items(&self, retain: &mut VecDeque<bool>) -> Self { Self { list: terms::retain_items(self.borrow(), retain) } }
    }

    pub mod terms {

        use std::collections::VecDeque;
        use columnar::Container;
        use crate::facts::{Lists, Terms};
        use crate::facts::trie::layers::Report;
        use crate::facts::{upgrade_hint, upgrade, downgrade};

        /// Unions two layers, aligned through `reports`, which is refilled if `next` is set.
        pub fn union(lists0: <Lists<Terms> as Container>::Borrowed<'_>, lists1: <Lists<Terms> as Container>::Borrowed<'_>, reports: &mut VecDeque<Report>, next: bool) -> Lists<Terms> {
            match (upgrade_hint(lists0), upgrade_hint(lists1)) {
                (Some(1), Some(1)) => { downgrade(super::union(upgrade::<1>(lists0).unwrap(), upgrade::<1>(lists1).unwrap(), reports, next)) }
                (Some(2), Some(2)) => { downgrade(super::union(upgrade::<2>(lists0).unwrap(), upgrade::<2>(lists1).unwrap(), reports, next)) }
                (Some(3), Some(3)) => { downgrade(super::union(upgrade::<3>(lists0).unwrap(), upgrade::<3>(lists1).unwrap(), reports, next)) }
                (Some(4), Some(4)) => { downgrade(super::union(upgrade::<4>(lists0).unwrap(), upgrade::<4>(lists1).unwrap(), reports, next)) }
                _ => { super::union(lists0, lists1, reports, next) }
            }
        }
        /// Intersects two layers, aligned through `aligns`.
        pub fn intersection(lists0: <Lists<Terms> as Container>::Borrowed<'_>, lists1: <Lists<Terms> as Container>::Borrowed<'_>, both0: &[usize], both1: &[usize]) -> (Vec<usize>, Vec<usize>) {
            // Update `aligns` for the next layer, or output.
            match (upgrade_hint(lists0), upgrade_hint(lists1)) {
                (Some(1), Some(1)) => { super::intersection::<Vec<[u8; 1]>>(upgrade::<1>(lists0).unwrap(), upgrade::<1>(lists1).unwrap(), both0, both1) }
                (Some(2), Some(2)) => { super::intersection::<Vec<[u8; 2]>>(upgrade::<2>(lists0).unwrap(), upgrade::<2>(lists1).unwrap(), both0, both1) }
                (Some(3), Some(3)) => { super::intersection::<Vec<[u8; 3]>>(upgrade::<3>(lists0).unwrap(), upgrade::<3>(lists1).unwrap(), both0, both1) }
                (Some(4), Some(4)) => { super::intersection::<Vec<[u8; 4]>>(upgrade::<4>(lists0).unwrap(), upgrade::<4>(lists1).unwrap(), both0, both1) }
                _ => { super::intersection::<Terms>(lists0, lists1, both0, both1) }
            }
        }
        /// Retains lists indicated by `retain`, which is refilled.
        pub fn retain_lists(lists: <Lists<Terms> as Container>::Borrowed<'_>, bounds: &mut [(usize, usize)]) -> Lists<Terms> {
            match upgrade_hint(lists) {
                Some(1) => { downgrade(super::retain_lists(upgrade::<1>(lists).unwrap(), bounds)) }
                Some(2) => { downgrade(super::retain_lists(upgrade::<2>(lists).unwrap(), bounds)) }
                Some(3) => { downgrade(super::retain_lists(upgrade::<3>(lists).unwrap(), bounds)) }
                Some(4) => { downgrade(super::retain_lists(upgrade::<4>(lists).unwrap(), bounds)) }
                _______ => { super::retain_lists(lists, bounds) }
            }
        }
        /// Retains items indicated by `retain`, which is refilled.
        pub fn retain_items(lists: <Lists<Terms> as Container>::Borrowed<'_>, retain: &mut VecDeque<bool>) -> Lists<Terms> {
            match upgrade_hint(lists) {
                Some(1) => { downgrade(super::retain_items(upgrade::<1>(lists).unwrap(), retain)) }
                Some(2) => { downgrade(super::retain_items(upgrade::<2>(lists).unwrap(), retain)) }
                Some(3) => { downgrade(super::retain_items(upgrade::<3>(lists).unwrap(), retain)) }
                Some(4) => { downgrade(super::retain_items(upgrade::<4>(lists).unwrap(), retain)) }
                _______ => { super::retain_items(lists, retain) }
            }
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
        both0: &[usize],
        both1: &[usize],
    ) -> (Vec<usize>, Vec<usize>) {

        assert_eq!(both0.len(), both1.len());

        let mut match0 = Vec::new();
        let mut match1 = Vec::new();

        for (index0, index1) in both0.iter().copied().zip(both1.iter().copied()) {

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
                        match0.push(lower0);
                        match1.push(lower1);
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

        (match0, match1)
    }

    // TODO: This method needs to be at most ~linear in the number of items that will be written out.
    // TODO: Invocations of this method will not have their bounds grow in number of intervals, and so
    //       we can re-use an argument `&mut [(usize, usize)]` to house the output bounds.
    /// Restrict lists based on per-list bools, producing a new layer and updating `bools` for the items.
    #[inline(never)]
    pub fn retain_lists<'a, C: Container>(lists: <Lists<C> as Container>::Borrowed<'a>, bounds: &mut [(usize, usize)]) -> Lists<C> {

        // In principle we can copy runs described in `bools` for bulk copying.
        let mut output = <Lists::<C> as Container>::with_capacity_for([lists].into_iter());

        for (lower, upper) in bounds.iter_mut() {
            output.extend_from_self(lists, *lower..*upper);
            *lower = lists.bounds.bounds(*lower).0;
            *upper = lists.bounds.bounds(*upper-1).1;
        }

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

    /// Advances (lower, upper] bounds on lists to the corresponding bounds on items.
    pub fn advance_bounds<'a, C: Container>(lists: <Lists<C> as Container>::Borrowed<'a>, bounds: &mut [(usize, usize)]) {
        if let Some(stride) = lists.bounds.strided() {
            let stride = stride as usize;
            if stride > 1 { for (lower, upper) in bounds.iter_mut() { *lower *= stride; *upper *= stride; } }
        }
        else {
            for (lower, upper) in bounds.iter_mut() {
                *lower = lists.bounds.bounds(*lower).0;
                *upper = lists.bounds.bounds(*upper-1).1;
            }
        }
    }

    /// Restricts `active` to indexes that equal the corresponding element in `other[aligned]`.
    pub fn filter_items<'a, C: Container<Ref<'a>: Ord>>(lists: <Lists<C> as Container>::Borrowed<'a>, active: &mut Vec<usize>, other: C::Borrowed<'a>, aligned: &[usize]) {
        assert_eq!(active.len(), aligned.len());
        let mut aligned = aligned.iter().copied();
        active.retain(|i| lists.values.get(*i) == other.get(aligned.next().unwrap()));
    }

    pub fn sort_terms(lists: <Lists<Terms> as Container>::Borrowed<'_>, groups: &mut [usize], indexs: &[usize], last: bool) -> Lists<Terms> {
        match upgrade_hint(lists) {
            Some(1) => { downgrade(col_sort(upgrade::<1>(lists).unwrap().values, groups, indexs, last)) }
            Some(2) => { downgrade(col_sort(upgrade::<2>(lists).unwrap().values, groups, indexs, last)) }
            Some(3) => { downgrade(col_sort(upgrade::<3>(lists).unwrap().values, groups, indexs, last)) }
            Some(4) => { downgrade(u32_sort(upgrade::<4>(lists).unwrap().values, groups, indexs, last)) }
            _______ => { col_sort(lists.values, groups, indexs, last) }
        }
    }

    /// Sort the items of `lists` subject to the grouping/ordering of `group` of the lists.
    #[inline(never)]
    pub fn col_sort<'a, C: Container<Ref<'a>: Ord>>(items: C::Borrowed<'a>, groups: &mut [usize], indexs: &[usize], last: bool) -> Lists<C> {

        let mut output = Lists::<C>::default();
        let mut to_sort = groups.iter().zip(indexs.iter()).enumerate().map(|(i, (group, index))| (*group, items.get(*index), i)).collect::<Vec<_>>();
        to_sort.sort_unstable();

        // We want to mint a new item for each distinct (group, value).
        // We want to seal a new list for each distinct group.
        let mut iter = to_sort.iter_mut();
        if let Some((group, value, _index)) = iter.next() {
            output.values.push(*value);
            let mut prev = (*group, value);
            *group = 0;
            for (group, value, _index) in iter {
                if prev.0 != *group { output.bounds.push(output.values.len() as u64); }
                if prev != (*group, value) { output.values.push(*value); }
                prev = (*group, value);
                *group = output.values.len() - 1;
            }
        }
        output.bounds.push(output.values.len() as u64);

        if !last { for (g, _, i) in to_sort { groups[i] = g; } }

        output
    }

    /// Sort the items of `lists` subject to the grouping/ordering of `group` of the lists.
    pub fn u32_sort<'a>(items: &'a [[u8;4]], groups: &mut [usize], indexs: &[usize], last: bool) -> Lists<Vec<[u8;4]>> {

        if last { return u32_sort_last(items, groups, indexs); }

        assert_eq!(groups.len(), indexs.len());

        let mut output = Lists::<Vec<[u8;4]>>::default();

        // Populate a byte vector with the content we want.
        let mut to_sort: Vec<u8> = Vec::with_capacity(12 * groups.len());
        for (i,(group,index)) in groups.iter().zip(indexs.iter()).enumerate() {
            to_sort.extend(&(*group as u32).to_be_bytes());
            to_sort.extend(&items[*index]);
            to_sort.extend(&(i as u32).to_be_bytes());
        }

        crate::facts::radix_sort::lsb_range(to_sort.as_chunks_mut::<12>().0, 0, 8);

        let to_sort = to_sort.as_chunks_mut::<4>().0.as_chunks_mut::<3>().0;

        // We want to mint a new item for each distinct (group, value).
        // We want to seal a new list for each distinct group.
        let mut iter = to_sort.iter_mut();
        if let Some([group, value, _index]) = iter.next() {
            output.values.push(*value);
            let mut prev = (*group, value);
            *group = 0u32.to_be_bytes();
            for [group, value, _index] in iter {
                if prev.0 != *group { output.bounds.push(output.values.len() as u64); }
                if prev != (*group, value) { output.values.push(*value); }
                prev = (*group, value);
                *group = ((output.values.len() - 1) as u32).to_be_bytes();
            }
            output.bounds.push(output.values.len() as u64);
        }

        if !last {
            // Sorting is optional, and could improve performance for large, disordered lists, or cost otherwise.
            // If we retained the counts and allocation from the previous invocation it might be faster.
            // crate::facts::radix_sort::lsb_range(&mut to_sort, 8, 12);
            for [g, _, i] in to_sort { groups[u32::from_be_bytes(*i) as usize] = u32::from_be_bytes(*g) as usize; }
        }

        output
    }

    pub fn u32_sort_last<'a>(items: &'a [[u8;4]], groups: &mut [usize], indexs: &[usize]) -> Lists<Vec<[u8;4]>> {

        assert_eq!(groups.len(), indexs.len());

        let mut output = Lists::<Vec<[u8;4]>>::default();

        // Populate a byte vector with the content we want.
        let mut to_sort: Vec<u8> = Vec::with_capacity(8 * groups.len());
        for (group, index) in groups.iter().zip(indexs.iter()) {
            to_sort.extend(&(*group as u32).to_be_bytes());
            to_sort.extend(&items[*index]);
        }

        crate::facts::radix_sort::lsb_range(to_sort.as_chunks_mut::<8>().0, 0, 8);

        let to_sort = to_sort.as_chunks_mut::<4>().0.as_chunks_mut::<2>().0;

        // We want to mint a new item for each distinct (group, value).
        // We want to seal a new list for each distinct group.
        let mut iter = to_sort.iter_mut();
        if let Some([group, value]) = iter.next() {
            output.values.push(*value);
            let mut prev = (*group, value);
            for [group, value] in iter {
                if prev.0 != *group { output.bounds.push(output.values.len() as u64); }
                if prev != (*group, value) { output.values.push(*value); }
                prev = (*group, value);
            }
            output.bounds.push(output.values.len() as u64);
        }

        output
    }

}
