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

    fn borrow<'a>(&'a self) -> Vec<<Lists<C> as Container>::Borrowed<'a>> {
        self.layers.iter().map(|x| x.list.borrow()).collect::<Vec<_>>()
    }

    /// Forms a forest trie from a sequence of columns of identical lengths.
    pub fn from_columns<'a>(columns: &[C::Borrowed<'a>]) -> Self where C::Ref<'a>: Ord {
        let mut groups = (0 .. columns.first().map(columnar::Len::len).unwrap_or(0)).map(|i| (0, i)).collect::<Vec<_>>();
        let layers = columns.iter().map(|column| Layer { list: crate::facts::trie::layers::col_sort(*column, &mut groups[..], false) }).collect();
        Self { layers }
    }

    /// Advances bounds on items through layers `lower .. upper`.
    ///
    /// The bounds should start in terms of items of layer `lower`, and will end in terms of items of layer `upper`.
    fn advance_item_bounds(&self, bounds: &mut [(usize, usize)], lower: usize, upper: usize) {
        advance_bounds::<C>(&self.borrow()[lower+1 .. upper+1], bounds)
    }
}

fn advance_bounds<C: Container>(layers: &[<Lists<C> as Container>::Borrowed<'_>], bounds: &mut[(usize, usize)]) {
    for layer in layers.iter() { crate::facts::trie::layers::advance_bounds::<C>(*layer, bounds); }
}

fn advance_item_bounds<C: Container>(layers: &[<Lists<C> as Container>::Borrowed<'_>], bounds: &mut[(usize, usize)], lower: usize, upper: usize) {
    advance_bounds::<C>(&layers[lower+1 .. upper+1], bounds)
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

/// Implementations for `Forest<Terms>`, for generic byte slices.
pub mod terms {

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
        fn filter(&self, lit_filters: &[(usize, String)], var_filters: &[Vec<usize>]) -> Self {

            // Plan the constraints applied to each column, to visit them in order.
            let mut constraints = std::collections::BTreeMap::<usize, Result<usize, &String>>::default();
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
                        self.advance_item_bounds(&mut bounds[..], idx, col);

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
                        use columnar::Push; literal.push([lit.as_bytes()]);
                        let aligned = std::iter::repeat(0).take(active.len()).collect::<Vec<_>>();
                        crate::facts::trie::layers::filter_items::<Terms>(self.layers[col].borrow(), &mut active, literal.values.borrow(), &aligned[..])
                    }
                }
            }

            // use `active` at `cursor` to retain lists and items.
            let mut include = std::iter::repeat(false).take(self.layers[cursor].list.values.len()).collect::<std::collections::VecDeque<_>>();
            for idx in active { include[idx] = true; }
            let mut result = self.clone();
            // If there are additional layers, clone `include` and update unexplored layers.
            if result.layers.len() > cursor {
                let mut include = include.clone();
                for layer in result.layers[cursor..].iter_mut().skip(1) {
                    layer.retain_lists(&mut include);
                }
            }
            // In any case, update prior layers from `other_arity` back to the first.
            for layer in result.layers[..cursor+1].iter_mut().rev() {
                if include.iter().all(|x| *x) { return result; }  // TODO: make this test cheaper.
                layer.retain_items(&mut include);
            }

            result
        }
        /// Produces columns in the order indicated by `projection`. Each column should appear at most once.
        #[inline(never)]
        fn permute(&self, projection: &[usize]) -> Self {
            let groups = (0 .. self.layers[0].list.len()).map(|i| (0, i)).collect::<Vec<_>>();
            Self { layers: permute_subset(&self.borrow()[..], projection, &groups[..]) }
        }
        /// Introduces repeated and literal columns.
        ///
        /// It is important that `projection` introduce columns in strict numeric order, but it can repeat
        /// an introduced column or a introduce a literal column at any point.
        #[inline(never)]
        fn embellish(&mut self, projection: &[Result<usize, String>]) {

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
                        for _ in 0 .. count { use columnar::Push; list.push([lit.as_bytes()]); }
                        Layer { list }
                    },
                });
            }
            layers.reverse();
            self.layers = layers;
        }
    }

    /// Produces columns in the order indicated by `projection`, for the distinguished prefixes of `groups`.
    ///
    /// The `groups` input identifies lists in the first layer, and groupings associated with them, which
    /// constrain the permutation to distinguish lists with different groups, merge lists with equal groups,
    /// and discard lists that are not referenced at all.
    fn permute_subset(in_layers: &[<Lists<Terms> as Container>::Borrowed<'_>], projection: &[usize], in_groups: &[(usize, usize)]) -> Vec<Layer<Terms>> {

        use crate::facts::trie::advance_item_bounds;

        let mut layers: Vec<Layer<Terms>> = Vec::with_capacity(projection.len());
        let in_bounds = in_groups.iter().copied().map(|(_g,i)| in_layers[0].bounds.bounds(i)).collect::<Vec<_>>();

        let mut columns = projection.iter().copied().peekable();
        if let Some(col) = columns.next() {

            // We'll track with `maxima` the greatest layer index so far, with `groups.len()` equal to the items in the layer.
            let last = columns.peek().is_none();
            let mut maxima = col;
            let mut bounds = in_bounds.clone();
            advance_item_bounds::<Terms>(in_layers, &mut bounds[..], 0, col);
            let mut groups = in_groups.iter().copied().zip(bounds.iter().copied()).flat_map(|((g,_i),(l,u))| (l..u).map(move |i| (g,i))).collect::<Vec<_>>();
            layers.push(Layer { list: crate::facts::trie::layers::sort_terms(in_layers[col], &mut groups, last) });

            while let Some(col) = columns.next() {

                if col < maxima {
                    // if col < maxima, we'll need to project forward to find bounds and repeat indexes.
                    // we start with bounds read out of layer col+1, and advance to `maxima` as necessary.
                    // we start from all items in layer `col`, but if this were a subset it could be fewer.
                    let mut my_bounds = in_bounds.clone();
                    advance_item_bounds::<Terms>(in_layers, &mut my_bounds[..], 0, col);
                    let mut bounds = my_bounds.iter().copied().flat_map(|(l,u)| l .. u).map(|i| in_layers[col+1].bounds.bounds(i)).collect::<Vec<_>>();
                    if col+1 < maxima { advance_item_bounds::<Terms>(in_layers, &mut bounds[..], col+1, maxima); }
                    my_bounds.iter().copied().flat_map(|(l,u)| l..u).zip(bounds.iter()).flat_map(|(i, (l,u))| std::iter::repeat(i).take(u-l)).zip(groups.iter_mut()).for_each(|(x,(_g,i))| *i = x);
                }
                else {
                    assert!(col > maxima);
                    // if col > maxima, we'll need to project forward to find bounds and repeat groups.
                    // we start with bounds read out of layer `maxima`, and advance to `col` as necessary.
                    // we start from all items in layer `maxima`, but if this were a subset it could be fewer.
                    let mut bounds = in_bounds.clone();
                    advance_item_bounds::<Terms>(in_layers, &mut bounds[..], 0, maxima);
                    let mut bounds = bounds.into_iter().flat_map(|(l,u)| l .. u).map(|i| in_layers[maxima+1].bounds.bounds(i)).collect::<Vec<_>>();
                    if maxima+1 < col { advance_item_bounds::<Terms>(in_layers, &mut bounds[..], maxima+1, col); }
                    groups = groups.into_iter().zip(bounds).flat_map(|((g,_),(l,u))| (l..u).map(move |i| (g, i))).collect::<Vec<_>>();
                }

                maxima = std::cmp::max(maxima, col);
                let last = columns.peek().is_none();
                layers.push(Layer { list: crate::facts::trie::layers::sort_terms(in_layers[col], &mut groups, last) });
            }
        }

        layers
    }

    /// Aligns blocks of `self` and `other` by their first `arity` columns, and applies supplied projections.
    ///
    /// This method works column-by-column, first identifying pairs of item indexes in layers `arity-1` which
    /// correspond to equal paths in both inputs, then producing the results for each projection by column.
    ///
    /// Each projection should contain each column at most once. Repeated columns can be introduced afterwards,
    /// for example by the `Forest::embellish` method.
    fn join_cols<'a>(
        this: &[<Lists<Terms> as Container>::Borrowed<'a>],
        that: &[<Lists<Terms> as Container>::Borrowed<'a>],
        arity: usize,
        projections: &[&[usize]],
    ) -> Vec<FactLSM<Forest<Terms>>> {

        if projections.is_empty() { return Vec::default(); }
        if this.len() < arity || that.len() < arity { return Vec::default(); }

        let mut builders: Vec<FactLSM<Forest<Terms>>> = Vec::with_capacity(projections.len());

        if this.last().is_some_and(|l| l.is_empty()) || that.last().is_some_and(|l| l.is_empty()) { return builders; }

        // Introduce empty lists for prefix columns we must retain.
        use std::collections::BTreeMap;
        let mut both_need: BTreeMap<usize, Vec<usize>> = Default::default();
        for column in projections.iter().flat_map(|x| x.iter()).copied() {
            if column < arity { both_need.insert(column, Vec::default()); }
            else if column >= this.len() && column < this.len() + arity { both_need.insert(column - this.len(), Vec::default()); }
        }

        // Determine the alignments of shared prefixes.
        // `aligned` will contain all pairs of matching path prefixes, from `this` and `that`.
        let mut aligned = std::collections::VecDeque::default();
        aligned.push_back((0, 0));
        for (index, (layer0, layer1)) in this[..arity].iter().zip(that[..arity].iter()).enumerate() {
            crate::facts::trie::layers::intersection::<Terms>(*layer0, *layer1, &mut [aligned.len()], &mut aligned);
            // If we need to retain the column, then record the aligned indexes in the `this` layer.
            both_need.get_mut(&index).map(|a| a.extend(aligned.iter().map(|(i,_)| *i)));
        }

        // Handle each projection independently.
        for projection in projections {

            // Introduce columns one-by-one.
            let mut layers = Vec::with_capacity(projection.len());
            // Pairs of lists of list indexes in `this` and `that` that need to be joined, in this order.
            let (mut this_i, mut that_j): (Vec<_>, Vec<_>) = aligned.iter().copied().unzip();
            // TODO: remove second coordinate (believed redundant with `tojoin`).
            // Maintains grouping information for each element of `tojoin`.
            let mut groups = (0 .. aligned.len()).map(|i| (0, i)).collect::<Vec<_>>();

            // Orient `this[arity..]` and `that[arity..]` to match the order introduced in `projection`.
            let mut this_values = None;
            let mut this_order = Vec::default();
            for col in projection.iter().copied() { if arity <= col && col < this.len() && !this_order.contains(&(col - arity)) { this_order.push(col - arity); } }
            if this_order != (0 .. this_order.len()).collect::<Vec<_>>() {
                let groups = aligned.iter().map(|(i,_)| *i).enumerate().collect::<Vec<_>>();
                let layers = permute_subset(&this[arity..], &this_order[..], &groups[..]);
                this_values = Some(Forest { layers });
                for i in 0 .. this_i.len() { this_i[i] = i; }
            }

            let mut that_values = None;
            let mut that_order = Vec::default();
            for col in projection.iter().copied() { if this.len() + arity <= col && !that_order.contains(&(col - arity - this.len())) { that_order.push(col - arity - this.len()); } }
            if that_order != (0 .. that_order.len()).collect::<Vec<_>>() {
                let groups = aligned.iter().map(|(_,j)| *j).enumerate().collect::<Vec<_>>();
                let layers = permute_subset(&that[arity..], &that_order[..], &groups[..]);
                that_values = Some(Forest { layers });
                for j in 0 .. that_j.len() { that_j[j] = j; }
            }

            // Lists of non-shared layers for `this` and `that` in the order introduced by `projection`.
            let this_values = this_values.as_ref().map(|x| x.borrow()).unwrap_or(this[arity..].to_vec());
            let that_values = that_values.as_ref().map(|x| x.borrow()).unwrap_or(that[arity..].to_vec());

            let mut this_cursor = 0;
            let mut that_cursor = 0;

            for (idx, column) in projection.iter().copied().enumerate() {

                use crate::facts::trie::layers::sort_terms;

                let last = idx+1 == projection.len();

                let list = if column < arity {
                    // Flow the column bounds forward to `aligned`, then count.

                    // First, let's determine the counts for each of `this` and `that` at `aligned`.
                    let mut this_bounds = aligned.iter().map(|(i,_)| (*i,*i+1)).collect::<Vec<_>>();
                    crate::facts::trie::advance_bounds::<Terms>(&this_values[0 .. this_cursor], &mut this_bounds[..]);
                    let mut that_bounds = aligned.iter().map(|(_,j)| (*j,*j+1)).collect::<Vec<_>>();
                    crate::facts::trie::advance_bounds::<Terms>(&that_values[0 .. that_cursor], &mut that_bounds[..]);

                    // Now let's project forward from `both_need[column]`.
                    let mut bounds = both_need[&column].iter().map(|i| (*i,*i+1)).collect::<Vec<_>>();
                    crate::facts::trie::advance_bounds::<Terms>(&this[column+1 .. arity], &mut bounds);

                    let mut products = this_bounds.iter().zip(that_bounds.iter()).map(|((l0,u0), (l1,u1))| (u0-l0)*(u1-l1))
                                                     .zip(aligned.iter().map(|(i,_)| *i)).peekable();

                    let counts = bounds.iter().map(|(l,u)| {
                        let mut count = 0;
                        while products.next_if(|(_,x)| x < l).is_some() { }
                        while let Some((c,_)) = products.next_if(|(_,x)| x < u) { count += c; }
                        count
                    });

                    // Flatten the (index, count) into repetitions.
                    let flat = both_need[&column].iter().zip(counts).flat_map(|(i,c)| std::iter::repeat(*i).take(c)).collect::<Vec<_>>();
                    assert_eq!(flat.len(), groups.len());
                    groups.iter_mut().zip(flat.iter()).for_each(|((_,x),i)| { *x = *i; });
                    sort_terms(this[column], &mut groups, last)
                }
                else if column < this.len() {
                    // We expect this to be the next column in `this_values`.
                    let values = this_values[this_cursor];

                    // Expand `groups` to call out items in `values`.
                    groups = groups.into_iter().zip(this_i.iter().copied()).flat_map(|((g,_),i)| { let (l,u) = values.bounds.bounds(i); (l .. u).map(move |i| (g,i)) }).collect();
                    if !last {
                        (this_i, that_j) = this_i.iter().zip(that_j.iter()).flat_map(|(i,j)| { let (l,u) = values.bounds.bounds(*i); (l .. u).map(move |i| (i,*j)) }).unzip();
                    }
                    this_cursor += 1;
                    sort_terms(values, &mut groups, last)
                }
                else if column < this.len() + arity {
                    unimplemented!("reference equated column of first join argument")
                }
                else {
                    // We expect this to be the next column in `that_values`.
                    let values = that_values[that_cursor];

                    // Expand `groups` to call out items in `values`.
                    groups = groups.into_iter().zip(that_j.iter().copied()).flat_map(|((g,_),j)| { let (l,u) = values.bounds.bounds(j); (l .. u).map(move |j| (g,j)) }).collect();
                    if !last {
                        (this_i, that_j) = this_i.iter().zip(that_j.iter()).flat_map(|(i,j)| { let (l,u) = values.bounds.bounds(*j); (l .. u).map(move |j| (*i,j)) }).unzip();
                    }
                    that_cursor += 1;
                    sort_terms(values, &mut groups, last)
                };

                layers.push(Layer { list } );
            }

            builders.push(Forest { layers }.into());
        }

        builders
    }

    impl FactContainer for Forest<Terms> {

        fn act_on(&self, action: &Action<String>) -> FactLSM<Self> {

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

        fn join<'a>(&'a self, other: &'a Self, arity: usize, projections: &[&[usize]]) -> Vec<FactLSM<Self>> { join_cols(&self.borrow()[..], &other.borrow()[..], arity, projections) }

        fn antijoin<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { self.retain_join::<'a>(others, false) }

        fn semijoin<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self where Self: 'a { self.retain_join::<'a>(others, true) }
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

        pub fn sort(&self, groups: &mut [(usize, usize)], last: bool) -> Self {
            Self { list: sort_terms(self.borrow(), groups, last) }
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

    pub fn sort_terms(lists: <Lists<Terms> as Container>::Borrowed<'_>, groups: &mut [(usize, usize)], last: bool) -> Lists<Terms> {
        match upgrade_hint(lists) {
            Some(1) => { downgrade(col_sort(upgrade::<1>(lists).unwrap().values, groups, last)) }
            Some(2) => { downgrade(col_sort(upgrade::<2>(lists).unwrap().values, groups, last)) }
            Some(3) => { downgrade(col_sort(upgrade::<3>(lists).unwrap().values, groups, last)) }
            Some(4) => { downgrade(u32_sort(upgrade::<4>(lists).unwrap().values, groups, last)) }
            _______ => { col_sort(lists.values, groups, last) }
        }
    }

    /// Sort the items of `lists` subject to the grouping/ordering of `group` of the lists.
    pub fn col_sort<'a, C: Container<Ref<'a>: Ord>>(items: C::Borrowed<'a>, group: &mut [(usize, usize)], last: bool) -> Lists<C> {

        let mut output = Lists::<C>::default();
        let mut to_sort = group.iter().copied().enumerate().map(|(idx,(g,i))| (g, items.get(i), idx)).collect::<Vec<_>>();
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

        if !last { for (g, _, i) in to_sort { group[i] = (g, i); } }

        output
    }

    /// Sort the items of `lists` subject to the grouping/ordering of `group` of the lists.
    pub fn u32_sort<'a>(items: &'a [[u8;4]], group: &mut [(usize, usize)], last: bool) -> Lists<Vec<[u8;4]>> {

        let mut output = Lists::<Vec<[u8;4]>>::default();

        // Populate a byte vector with the content we want.
        let mut to_sort: Vec<u8> = Vec::with_capacity(12 * group.len());
        for (idx,(g,i)) in group.iter().copied().enumerate() {
            to_sort.extend(&(g as u32).to_be_bytes());
            to_sort.extend(&items[i]);
            to_sort.extend(&(idx as u32).to_be_bytes());
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
            for [g, _, index] in to_sort { group[u32::from_be_bytes(*index) as usize] = (u32::from_be_bytes(*g) as usize, u32::from_be_bytes(*index) as usize); }
        }

        output
    }
}
