//! Atom trait implementations for relations that are collections of data.

use std::collections::BTreeSet;
use std::rc::Rc;
use crate::facts::{FactContainer, Terms};
use crate::facts::trie::Forest;
use crate::rules::{PlanAtom, ExecAtom};
use crate::rules::exec::Salad;
use crate::comms::Comms;

impl<T: Ord + Copy> PlanAtom<T> for BTreeSet<T> {
    fn terms(&self) -> BTreeSet<T> { self.clone() }
    fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T> { self.difference(terms).cloned().collect() }
}

impl<T: Ord + Copy + std::fmt::Debug> ExecAtom<T> for (Vec<Forest<Terms>>, Vec<T>, Option<Forest<Terms>>) {

    fn terms(&self) -> &[T] { &self.1 }

    fn seed(&self, _comms: &mut Comms, recent: bool) -> Salad<T> {
        let mut salad = crate::rules::exec::Salad::new(Default::default(), Vec::default());
        salad.terms = self.1.clone();
        if recent { salad.extend(self.2.iter().cloned()) }
        else { salad.extend(self.0.iter().cloned()) }
        salad
    }

    fn count(&self, comms: &mut Comms, salad: &mut Salad<T>, terms: &BTreeSet<T>, other_index: u8) {

        use columnar::Len;
        use crate::facts::trie::layers::advance_bounds;
        use crate::facts::trie::layers::intersection;

        let (other_facts, other_terms, _other_recent) = self;

        let prefix = other_terms.iter().take_while(|t| salad.terms.contains(t)).count();
        salad.align_to(comms, other_terms[..prefix].iter().copied());
        // FIXME: the shuffling above is insufficient if the arity is zero and there are multiple workers.
        assert!(prefix > 0 || comms.peers() == 1);
        if let Some(mut delta) = salad.facts.flatten() {
            let length = if prefix > 0 { delta.layer(prefix-1).list.values.len() } else { 1 };
            let mut counts = vec![0; length];
            for other_part in other_facts.iter() {
                let mut delta_idxs = vec![0];
                let mut other_idxs = vec![0];
                for layer in 0 .. prefix { (delta_idxs, other_idxs) = intersection::<Terms>(delta.layer(layer).borrow(), other_part.layer(layer).borrow(), &delta_idxs, &other_idxs); }
                // The count derives from projecting `other_idxs` forward through `terms`.
                let mut ranges = other_idxs.iter().map(|i| (*i,*i+1)).collect::<Vec<_>>();
                for layer in prefix .. (prefix + terms.len()) { advance_bounds::<Terms>(other_part.layer(layer).borrow(), &mut ranges); }
                for (delta_idx, range) in delta_idxs.iter().zip(ranges.iter()) { counts[*delta_idx] += range.1-range.0; }
            }

            // We now project `counts` forward through `delta` to the `potato` column.
            // If any of `counts` are zero, we have the option to first restrict `delta` to only those prefixes.
            // We don't have to do this, can choose to avoid if there are only *few* zeros, and generally don't expect this if semijoins have already happened.
            let remove_zeros = counts.iter().filter(|c| c == &&0).count() > 0;
            if remove_zeros {
                let mut bools = std::collections::VecDeque::with_capacity(counts.len());
                bools.extend(counts.iter().map(|c| c > &0));
                counts.retain(|c| c > &0);
                // SUBTLE: `delta_lsm` is empty so returning communicates zeroing out everything. But also this guards Forest contruction to ensure it is non-empty.
                if counts.is_empty() { return; }

                let mut layers = Vec::with_capacity(salad.arity());
                if salad.arity() > prefix {

                    let mut prev = None;
                    let mut bounds = Vec::default();
                    for (idx, retain) in bools.iter().chain([&false]).enumerate() {
                        match (retain, &mut prev) {
                            (true, None) => { prev = Some(idx); },
                            (false, Some(lower) ) => { bounds.push((*lower, idx)); prev = None; }
                            _ => { },
                        }
                    }

                    for index in prefix .. delta.arity() { layers.push(Rc::new(delta.layer(index).retain_lists(&mut bounds))); }
                }
                for index in (0 .. prefix).rev() { layers.insert(0, Rc::new(delta.layer(index).retain_items(&mut bools))); }

                assert_eq!(counts.len(), layers[prefix-1].list.values.len());
                delta = layers.try_into().expect("non-empty due to count.is_empty() guard");
            }

            // Must now project `counts` forward to leaves of `delta`, where we expect to find installed counts.
            let mut ranges = (0 .. counts.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
            for layer in prefix .. delta.arity() { advance_bounds::<Terms>(delta.layer(layer).borrow(), &mut ranges); }

            let mut notes_rc = delta.pop_layer().unwrap();
            let notes = &mut Rc::make_mut(&mut notes_rc).list.values.values;
            for (count, range) in counts.iter().zip(ranges.iter()) {
                let order = (count+1).ilog2() as u8;
                for index in range.0 .. range.1 {
                    if notes[4 * index] >= order {
                        notes[4 * index] = order;
                        notes[4 * index + 1] = other_index;
                    }
                }
            }
            delta.push_layer(notes_rc);
            salad.extend([delta]);
        }
    }

    fn join(&self, comms: &mut Comms, salad: &mut Salad<T>, terms: &BTreeSet<T>, after: &[T]) {
        let (my_facts, my_terms, _) = self;
        let prefix = my_terms.iter().take_while(|t| salad.terms.contains(t)).count();
        salad.align_to(comms, my_terms[..prefix].iter().copied());
        // FIXME: the shuffling above is insufficient if the arity is zero and there are multiple workers.
        assert!(prefix > 0 || comms.peers() == 1);
        if !terms.is_empty() {
            // join with atom: permute `salad.terms` into the right order, join adding the new column, permute into target order (`delta_terms_new`).
            let conduit = comms.conduit();
            if let Some(delta) = salad.facts.flatten() {
                let join_terms = salad.terms.iter().chain(salad.terms[..prefix].iter()).chain(terms.iter()).copied().collect::<Vec<_>>();
                // Our output join order (until we learn how to do FDB shapes) is the first of `others` not equal to ourself.
                let projection = after.iter().map(|t| join_terms.iter().position(|t2| t == t2).unwrap()).collect::<Vec<_>>();
                salad.facts.extend(delta.join_many(my_facts.iter(), prefix, &projection[..], conduit));
            }
            else {
                salad.facts.extend(conduit.finish());
            }
            salad.terms.clear();
            salad.terms.extend_from_slice(after);
        }
        else {
            if let Some(delta) = salad.facts.flatten() {
                let others = my_facts.iter().map(|o| o.borrow()).collect::<Vec<_>>();
                salad.facts.extend(delta.retain_inner(others.iter().map(|o| &o[..prefix]), true));
            }
        }
    }
}
