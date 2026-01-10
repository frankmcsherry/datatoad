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
    fn count(&self, salad: &mut Salad<T>, added: &BTreeSet<T>, index: u8 );

    /// Join or semijoin `facts` with `self` on the shared `terms`, introducing `added`.
    ///
    /// If `terms` is empty, a semijoin is intended.
    /// If `terms` plus `added` cover all of `self.terms()` the result must contain no facts not satisfying `self`.
    /// The `after` term sequence is the order to which `terms` will next be permuted (an optional hint to lay out output).
    fn join(&self, salad: &mut Salad<T>, added: &BTreeSet<T>, after: &[T]);
}

/// Facts of multiple columns and the names for those columns.
///
/// This type is intended for fact collections that support shuffling of the columns, i.e. in-flight facts rather than at-rest facts.
/// It would be surprising to use this type to wrap collections of facts that are not actively moving through rules.
#[derive(Clone)]
pub struct Salad<T> {
    /// Many facts represented as a sequence of layers in correspondence with columns.
    pub facts: FactLSM<Forest<Terms>>,
    /// Names for the sequence of columns.
    pub terms: Vec<T>,
}

impl<T: Ord+Copy> Salad<T> {
    /// Constructs a new `Self` from facts and terms.
    pub fn new(facts: FactLSM<Forest<Terms>>, terms: Vec<T>) -> Self { Self { facts, terms } }

    /// Permutes columns to start with those present in `align`, followed by those not present.
    pub fn align_to(&mut self, align: impl Iterator<Item = T>) { Self::permute(self, align, PermuteMode::Align); }
    /// Permutes columns to start with those present in `align`, dropping those not present.
    pub fn prune_to(&mut self, align: impl Iterator<Item = T>) { Self::permute(self, align, PermuteMode::Prune); }

    /// Permute `facts` from its current order, `terms` to one that matches `align` on common terms.
    ///
    /// The method updates both `facts` and `terms`.
    /// The method assumes that some prefix of `align` is present in `terms`, and no further terms
    /// from `align` around found there. The caller must restrict `align` to make this the case.
    ///
    /// The `mode` argument indicates whther columns in `terms` absent from `align` should be discarded.
    /// When `prune` is set they are; otherwise all of `terms` are retained but re-ordered to start with `align`.
    fn permute(
        salad: &mut Salad<T>,
        align: impl Iterator<Item = T>,
        mode: PermuteMode,
    ) {
        let mut permutation: Vec<usize> = align.flat_map(|t1| salad.terms.iter().position(|t2| &t1 == t2)).collect();
        if let PermuteMode::Align = mode { for index in 0 .. salad.terms.len() { if !permutation.contains(&index) { permutation.push(index); }} }

        if permutation.iter().enumerate().any(|(index, i)| &index != i) {
            if let Some(flattened) = salad.facts.flatten() {
                salad.facts.extend(flattened.act_on(&Action::permutation(permutation.iter().copied())));
            }
            salad.terms = permutation.iter().map(|i| salad.terms[*i]).collect::<Vec<_>>();
        }
    }

}

/// Indicates behavior of `permute`, either aligned extra columns or pruning them.
enum PermuteMode { Align, Prune }


use crate::facts::{Forest, Terms};
#[inline(never)]
pub fn wco_join<T: Ord + Copy + std::fmt::Debug>(
    salad: &mut Salad<T>,
    terms: &BTreeSet<T>,
    others: &[Box<dyn ExecAtom<T> + '_>],
    potato: T,
    target: &[T],
) {
    if others.len() == 1 {
        others[0].join(salad, terms, target);
        salad.prune_to(target.iter().copied());
        return;
    }

    if let Some(facts) = salad.facts.flatten() {

        let active = salad.terms.iter().filter(|t| others.iter().any(|o| o.terms().contains(t))).copied().collect::<Vec<_>>();

        if active.len() == salad.terms.len() {
            salad.facts.push(facts);
            wco_join_inner(salad, terms, others, potato, target);
        }
        else {
            assert_eq!(&active[..], &salad.terms[..active.len()]);

            let mut prefix = salad.clone();
            let mut clone = facts.clone();
            clone.truncate(active.len());
            prefix.facts.push(clone);
            prefix.terms.truncate(active.len());

            let mut active_target = active.clone();
            active_target.extend(terms.iter().copied());
            wco_join_inner(&mut prefix, terms, others, potato, &active_target);
            prefix.align_to(salad.terms[..active.len()].iter().copied());

            let mut crossed_terms = salad.terms.clone();
            crossed_terms.extend(salad.terms[..active.len()].iter().copied());
            crossed_terms.extend(terms.iter().copied());
            let projection = target.iter().map(|t| crossed_terms.iter().position(|t2| t == t2).unwrap()).collect::<Vec<_>>();
            salad.facts = facts.join_many(prefix.facts.contents(), active.len(), &projection[..]);
            salad.terms.clear();
            salad.terms.extend_from_slice(target);
        }
    }
    else { salad.terms.extend(terms.iter().copied()); }
}

#[inline(never)]
fn wco_join_inner<T: Ord + Copy + std::fmt::Debug>(
    salad: &mut Salad<T>,
    terms: &BTreeSet<T>,
    others: &[Box<dyn ExecAtom<T> + '_>],
    potato: T,
    target: &[T],
) {
    use columnar::primitive::offsets::Strides;
    use crate::facts::{trie::Layer, Lists};

    if let Some(mut facts) = salad.facts.flatten() {

        let values = vec![255u8; 4 * facts.len()];
        facts.push_layer(Rc::new(Layer { list: Lists {
            bounds: Strides::new(1, facts.len() as u64),
            values: Lists {
                bounds: Strides::new(4, facts.len() as u64),
                values,
            },
        }}));
        salad.facts.push(facts);
        salad.terms.push(potato);

        //  1.  For each atom, update proposals (count, index) for each path in `delta` to track the minimum count.
        for (index, other) in others.iter().enumerate() { other.count(salad, terms, index as u8); }

        //  2.  Partition `salad.facts` by atom index, and join to get proposals.
        // Extract the (count, index) layer to shard paths by index.
        if let Some(mut facts) = salad.facts.flatten() {

            // This `Rc::unwrap_or_clone` could be `Rc::try_unwrap` as there *should* be unique ownership, other than bugs in `other.count` above.
            let notes = Rc::unwrap_or_clone(facts.pop_layer().unwrap()).list.values.values;
            let mut bools = std::collections::VecDeque::with_capacity(notes.len()/4);
            salad.terms.pop();

            for (other_index, other) in others.iter().enumerate().rev() {

                // Extract the shard of `delta` marked for this index.
                bools.clear();
                bools.extend((0 .. notes.len()/4).map(|i| notes[4*i] > 0 && notes[4*i+1] == other_index as u8));
                let mut shard = Salad::new(FactLSM::default(), salad.terms.clone());
                if bools.iter().any(|x| *x) {
                    let mut layers = Vec::default();
                    for index in (0 .. salad.terms.len()).rev() { layers.insert(0, Rc::new(facts.layer(index).retain_items(&mut bools))); }
                    shard.facts.push(layers.try_into().expect("non-empty due to bools.any() test"));
                }

                // join with atom: permute `shard` into the right order, join adding the new column, permute into target order (`delta_terms_new`).
                let next_other_idx = if other_index == 0 { 1 } else { 0 };
                let mut after = Vec::default();
                after.extend(others[next_other_idx].terms().iter().filter(|t| salad.terms.contains(t) || terms.contains(t)));
                after.extend(salad.terms.iter().filter(|t| !others[next_other_idx].terms().contains(t)));
                other.join(&mut shard, terms, &after);

                // semijoin with other atoms.
                for (next_other_index, next_other) in others.iter().enumerate() {
                    if next_other_index != other_index {
                        next_other.join(&mut shard, &Default::default(), Default::default());
                    }
                }

                // Put in common layout (`target`) then merge.
                shard.prune_to(target.iter().copied());
                if let Some(mut facts) = shard.facts.flatten() {
                    while facts.arity() > target.len() { facts.pop_layer(); }
                    salad.facts.push(facts);
                }
            }
        }

        salad.terms.clear();
        salad.terms.extend_from_slice(target);
    }
}
