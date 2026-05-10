//! Atom trait implementations for relations that are the complement of a collection of data.

use std::collections::BTreeSet;
use crate::facts::Terms;
use crate::facts::trie::Forest;
use crate::rules::{PlanAtom, ExecAtom};
use crate::rules::exec::Salad;
use crate::comms::Comms;

/// Wrapper type for antijoins.
pub struct Anti<T>(pub T);

impl <T: Ord + Clone> PlanAtom<T> for Anti<BTreeSet<T>> {
    fn terms(&self) -> BTreeSet<T> { self.0.clone() }
    fn ground(&self, _terms: &BTreeSet<T>) -> BTreeSet<T> { Default::default() }
}

impl<T: Ord + Clone+std::fmt::Debug> ExecAtom<T> for Anti<(Vec<Forest<Terms>>, Vec<T>)> {

    fn terms(&self) -> &[T] { &self.0.1 }

    fn seed(&self, _comms: &mut Comms, _recent: bool) -> Salad<T> { unimplemented!("Anti cannot seed facts") }

    fn count(&self, _: &mut Comms, _: &mut Salad<T>, _: &BTreeSet<T>, _: u8) { }

    fn join(&self, comms: &mut Comms, salad: &mut Salad<T>, terms: &BTreeSet<T>, _after: &[T]) {
        let (my_facts, my_terms) = &self.0;
        let prefix = my_terms.iter().take_while(|t| salad.terms.contains(t)).count();
        salad.align_to(comms, my_terms[..prefix].iter().cloned());
        // FIXME: the shuffling above is insufficient if the arity is zero and there are multiple workers.
        assert!(prefix > 0 || comms.peers() == 1);
        if let Some(delta) = salad.facts.flatten() {
            assert!(terms.is_empty());
            let others = my_facts.iter().map(|o| o.borrow()).collect::<Vec<_>>();
            salad.extend(delta.retain_inner(others.iter().map(|o| &o[..prefix]), false));
        }
    }
}
