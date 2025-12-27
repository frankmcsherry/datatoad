//! Traits and logic associated with executing rules.

use std::collections::BTreeSet;
use std::rc::Rc;
use crate::types::Action;
use crate::facts::{FactContainer, FactLSM};

/// An atom over terms `T` that supports execution.
///
/// The things we'll ask an atom to do to a collection of facts are:
///     1.  appraise (count) the number of extensions the atom would propose for some grounded terms.
///     2.  propose (join) the actual extensions for some grounded terms.
///     3.  validate (join) proposed exensions using some grounded terms.
/// The methods `count` and `join` have further detail about their requirements.
pub trait ExecAtom<T: Ord> {

    /// Terms present in the atom, in the preferred order.
    ///
    /// This is used primarily as a hint for how to lay out facts that will next interact with the atom.
    fn terms(&self) -> &[T];

    /// Update the number of distinct values of `added` terms that would extend each fact.
    ///
    /// The last layer of `facts` is expected to be a 1:1 layer `[u8;4]` containing `[log1p(count), index, 255u8, 255u8]`.
    /// For prefixes where this atom would add a less-or-equal log(1+count), it should overwrite that value and the index.
    /// The implementor is not required to update any counts, for example if it is unable to provide ground values.
    /// In this case, the implementor is not expected to respond to `join` for the same arguments.
    fn count(
        &self,
        facts: &mut FactLSM<Forest<Terms>>,
        terms: &mut Vec<T>,
        added: &BTreeSet<T>,
        index: u8,
    );

    /// Join or semijoin `facts` with `self` on the shared `terms`, introducing `added`.
    ///
    /// If `terms` is empty, a semijoin is intended.
    /// If `terms` plus `added` cover all of `self.terms()` the result must contain no facts not satisfying `self`.
    /// The `after` term sequence is the order to which `terms` will next be permuted (an optional hint to lay out output).
    fn join(
        &self,
        facts: &mut FactLSM<Forest<Terms>>,
        terms: &mut Vec<T>,
        added: &BTreeSet<T>,
        after: &[T],
    );
}

/// Permute `facts` from its current order, `terms` to one that matches `align` on common terms.
///
/// The method updates both `facts` and `terms`.
/// The method assumes that some prefix of `align` is present in `terms`, and no further terms
/// from `align` around found there. The caller must restrict `align` to make this the case.
///
/// The `prune` argument indicates that columns in `terms` absent from `align` should be discarded.
/// When `prune` is not set, all of `terms` are retained but re-ordered to start with `align`.
pub fn permute_delta<F: FactContainer, T: Ord + Copy>(
    facts: &mut FactLSM<F>,
    terms: &mut Vec<T>,
    align: impl Iterator<Item = T>,
    prune: bool,
) {
    let mut permutation: Vec<usize> = align.flat_map(|t1| terms.iter().position(|t2| &t1 == t2)).collect();
    if !prune { for index in 0 .. terms.len() { if !permutation.contains(&index) { permutation.push(index); }} }

    if permutation.iter().enumerate().any(|(index, i)| &index != i) {
        if let Some(flattened) = facts.flatten() {
            facts.extend(flattened.act_on(&Action::permutation(permutation.iter().copied())));
        }
        *terms = permutation.iter().map(|i| terms[*i]).collect::<Vec<_>>();
    }
}

use crate::facts::{Forest, Terms};
#[inline(never)]
pub fn wco_join<T: Ord + Copy + std::fmt::Debug>(
    delta_lsm: &mut FactLSM<Forest<Terms>>,
    delta_terms: &mut Vec<T>,
    terms: &BTreeSet<T>,
    others: &[Box<dyn ExecAtom<T> + '_>],
    potato: T,
    target: &[T],
) {
    if others.len() == 1 {
        others[0].join(delta_lsm, delta_terms, terms, target);
        permute_delta(delta_lsm, delta_terms, target.iter().copied(), true);
        return;
    }

    //  0.  Add a new column containing `[255u8, 255u8]` named `potato`, to house our by-atom count and index information.
    if let Some(delta) = delta_lsm.flatten() {

        use columnar::Len;

        let active = delta_terms.iter().filter(|t| others.iter().any(|o| o.terms().contains(t))).copied().collect::<Vec<_>>();

        if active.len() == delta_terms.len() {
            delta_lsm.push(delta);
            wco_join_inner(delta_lsm, delta_terms, terms, others, potato, target);
        }
        else {
            assert_eq!(&active[..], &delta_terms[..active.len()]);
            delta_lsm.push((0..active.len()).map(|i| Rc::clone(delta.layer(i))).collect::<Vec<_>>().try_into().expect("non-empty as copied from delta"));
            let mut active_clone = active.clone();
            let mut active_target = active.clone();
            active_target.extend(terms.iter().copied());
            wco_join_inner(delta_lsm, &mut active_clone, terms, others, potato, &active_target);
            permute_delta(delta_lsm, &mut active_clone, delta_terms[..active.len()].iter().copied(), false);

            let mut crossed_terms = delta_terms.clone();
            crossed_terms.extend(delta_terms[..active.len()].iter().copied());
            crossed_terms.extend(terms.iter().copied());
            let projection = target.iter().map(|t| crossed_terms.iter().position(|t2| t == t2).unwrap()).collect::<Vec<_>>();
            *delta_lsm = delta.join_many(delta_lsm.contents(), active.len(), &projection[..]);
            delta_terms.clear();
            delta_terms.extend_from_slice(target);
        }
    }
    else { delta_terms.extend(terms.iter().copied()); }
}

#[inline(never)]
fn wco_join_inner<T: Ord + Copy + std::fmt::Debug>(
    delta_lsm: &mut FactLSM<Forest<Terms>>,
    delta_terms: &mut Vec<T>,
    terms: &BTreeSet<T>,
    others: &[Box<dyn ExecAtom<T> + '_>],
    potato: T,
    target: &[T],
) {

    use columnar::Len;
    use columnar::primitive::offsets::Strides;

    use crate::facts::{trie::Layer, Lists};

    if let Some(mut delta) = delta_lsm.flatten() {

        let values = vec![255u8; 4 * delta.len()];
        delta.push_layer(Rc::new(Layer { list: Lists {
            bounds: Strides::new(1, delta.len() as u64),
            values: Lists {
                bounds: Strides::new(4, delta.len() as u64),
                values,
            },
        }}));
        delta_lsm.push(delta);
        delta_terms.push(potato);

        //  1.  For each atom, update proposals (count, index) for each path in `delta` to track the minimum count.
        for (index, other) in others.iter().enumerate() { other.count(delta_lsm, delta_terms, terms, index as u8); }

        //  2.  Partition `delta_lsm` by atom index, and join to get proposals.
        // Extract the (count, index) layer to shard paths by index.
        if let Some(mut delta) = delta_lsm.flatten() {

            // This `Rc::unwrap_or_clone` could be `Rc::try_unwrap` as there *should* be unique ownership, other than bugs in `other.count` above.
            let notes = Rc::unwrap_or_clone(delta.pop_layer().unwrap()).list.values.values;
            let mut bools = std::collections::VecDeque::with_capacity(notes.len()/4);
            delta_terms.pop();

            for (other_index, other) in others.iter().enumerate().rev() {

                // Extract the shard of `delta` marked for this index.
                bools.clear();
                bools.extend((0 .. notes.len()/4).map(|i| notes[4*i] > 0 && notes[4*i+1] == other_index as u8));
                let mut delta_shard = FactLSM::default();
                if bools.iter().any(|x| *x) {
                    let mut layers = Vec::default();
                    for index in (0 .. delta_terms.len()).rev() { layers.insert(0, Rc::new(delta.layer(index).retain_items(&mut bools))); }
                    delta_shard.push(layers.try_into().expect("non-empty due to bools.any() test"));
                }

                // join with atom: permute `delta_shard` into the right order, join adding the new column, permute into target order (`delta_terms_new`).
                let mut delta_shard_terms = delta_terms.clone();
                let next_other_idx = if other_index == 0 { 1 } else { 0 };
                let mut after = Vec::default();
                after.extend(others[next_other_idx].terms().iter().take_while(|t| delta_terms.contains(t) || terms.contains(t)));
                after.extend(delta_terms.iter().filter(|t| !others[next_other_idx].terms().contains(t)));
                other.join(&mut delta_shard, &mut delta_shard_terms, terms, &after);

                // semijoin with other atoms.
                for (next_other_index, next_other) in others.iter().enumerate() {
                    if next_other_index != other_index {
                        next_other.join(&mut delta_shard, &mut delta_shard_terms, &Default::default(), Default::default());
                    }
                }

                // Put in common layout (`target`) then merge.
                permute_delta(&mut delta_shard, &mut delta_shard_terms, target.iter().copied(), true);
                if let Some(mut delta) = delta_shard.flatten() {
                    while delta.arity() > target.len() { delta.pop_layer(); }
                    delta_lsm.push(delta);
                }
            }
        }

        delta_terms.clear();
        delta_terms.extend_from_slice(target);
    }
}
