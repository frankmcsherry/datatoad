//! Traits and logic associated with executing rules.

use std::collections::BTreeSet;
use crate::types::Action;
use crate::facts::{FactContainer, FactLSM};

/// An atom over terms `T` that supports execution.
///
/// The things we'll ask an atom to do to a collection of facts are:
/// 1.  appraise (count) the number of extensions the atom would propose for some grounded terms.
/// 2.  propose (join) the actual extensions for some grounded terms.
/// 3.  validate (join) proposed exensions using some grounded terms.
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

/// Permute `delta` from its current order, `delta_terms` to one that matches `other_terms` on common terms.
///
/// The method updates both `delta` and `delta_terms`.
/// The method assumes that some prefix of `other_terms` is present in `delta_terms`, and no further terms
/// from `other_terms` around found there. The caller must restrict `other_terms` to make this the case.
///
/// The `align` argument indicates that columns in `delta_terms` absent from `other_terms` should be added afterwards.
/// When `align` is not set, only those terms present in both `delta_terms` and `other_terms` are produced.
pub fn permute_delta<F: FactContainer, T: Ord + Copy>(
    delta: &mut FactLSM<F>,
    delta_terms: &mut Vec<T>,
    other_terms: impl Iterator<Item = T>,
    align: bool,
) {
    let mut permutation: Vec<usize> = other_terms.flat_map(|t1| delta_terms.iter().position(|t2| &t1 == t2)).collect();
    if align { for index in 0 .. delta_terms.len() { if !permutation.contains(&index) { permutation.push(index); }} }

    if permutation.iter().enumerate().any(|(index, i)| &index != i) {
        let mut flattened = delta.flatten().unwrap_or_default().act_on(&Action::permutation(permutation.iter().copied()));
        delta.extend(&mut flattened);
        *delta_terms = permutation.iter().map(|i| delta_terms[*i]).collect::<Vec<_>>();
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
        return;
    }

    //  0.  Add a new column containing `[255u8, 255u8]` named `potato`, to house our by-atom count and index information.
    let delta = delta_lsm.flatten().unwrap_or_default();
    if delta.is_empty() { delta_terms.extend(terms.iter().copied()); }
    else {

        use columnar::Len;

        let active = delta_terms.iter().filter(|t| others.iter().any(|o| o.terms().contains(t))).copied().collect::<Vec<_>>();

        if active.len() == delta_terms.len() {
            delta_lsm.push(delta);
            wco_join_inner(delta_lsm, delta_terms, terms, others, potato, target);
        }
        else {
            assert_eq!(&active[..], &delta_terms[..active.len()]);
            let delta_clone = Forest { layers: delta.layers[..active.len()].to_vec() };
            delta_lsm.push(delta_clone);
            let mut active_clone = active.clone();
            let mut active_target = active.clone();
            active_target.extend(terms.iter().copied());
            wco_join_inner(delta_lsm, &mut active_clone, terms, others, potato, &active_target);
            permute_delta(delta_lsm, &mut active_clone, delta_terms[..active.len()].iter().copied(), true);

            let mut crossed_terms = delta_terms.clone();
            crossed_terms.extend(delta_terms[..active.len()].iter().copied());
            crossed_terms.extend(terms.iter().copied());
            let projection = target.iter().map(|t| crossed_terms.iter().position(|t2| t == t2).unwrap()).collect::<Vec<_>>();
            *delta_lsm = delta.join_many(delta_lsm.contents(), active.len(), &projection[..]);
            delta_terms.clear();
            delta_terms.extend_from_slice(target);
        }
    }

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

    let mut delta = delta_lsm.flatten().unwrap_or_default();

    let values = vec![255u8; 4 * delta.len()];
    delta.layers.push(Layer { list: Lists {
        bounds: Strides::new(1, delta.len() as u64),
        values: Lists {
            bounds: Strides::new(4, delta.len() as u64),
            values,
        },
    }});
    delta_lsm.push(delta);
    delta_terms.push(potato);

    //  1.  For each atom, update proposals (count, index) for each path in `delta` to track the minimum count.
    for (index, other) in others.iter().enumerate() { other.count(delta_lsm, delta_terms, terms, index as u8); }

    //  2.  Partition `delta_lsm` by atom index, and join to get proposals.
    // Extract the (count, index) layer to shard paths by index.
    let mut delta = delta_lsm.flatten().unwrap_or_default();
    let notes = delta.layers.pop().unwrap_or_default().list.values.values;
    let mut bools = std::collections::VecDeque::with_capacity(notes.len()/4);
    delta_terms.pop();

    if !delta.is_empty() {
        for (other_index, other) in others.iter().enumerate().rev() {

            // Extract the shard of `delta` marked for this index.
            bools.clear();
            bools.extend((0 .. notes.len()/4).map(|i| notes[4*i] > 0 && notes[4*i+1] == other_index as u8));
            let mut layers = Vec::default();
            for index in (0 .. delta_terms.len()).rev() { layers.insert(0, delta.layers[index].retain_items(&mut bools)); }
            let delta_shard = crate::facts::Forest { layers };
            let mut delta_shard: FactLSM<_> = delta_shard.into();

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
            permute_delta(&mut delta_shard, &mut delta_shard_terms, target.iter().copied(), false);
            let mut delta_shard = delta_shard.flatten().unwrap_or_default();
            delta_shard.layers.truncate(target.len());
            delta_lsm.push(delta_shard);
        }
    }

    delta_terms.clear();
    delta_terms.extend_from_slice(target);

}
