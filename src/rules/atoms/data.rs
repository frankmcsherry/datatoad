//! Atom trait implementations for relations that are collections of data.

use std::collections::BTreeSet;
use std::rc::Rc;
use crate::facts::{FactContainer, Terms};
use crate::facts::trie::Forest;
use crate::rules::{PlanAtom, ExecAtom};
use crate::rules::exec::Salad;
use crate::comms::Comms;

impl<T: Ord + Clone> PlanAtom<T> for BTreeSet<T> {
    fn terms(&self) -> BTreeSet<T> { self.clone() }
    fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T> { self.difference(terms).cloned().collect() }
}

impl<T: Ord + Clone + std::fmt::Debug> ExecAtom<T> for (Vec<Forest<Terms>>, Vec<T>, Option<Forest<Terms>>) {

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
        salad.align_to(comms, other_terms[..prefix].iter().cloned());

        // When `prefix == 0` and we have peers, the count must be summed across workers.
        // This work needs to be done here, rather than conditionally for non-empty salad,
        // to avoid workers hanging their peers by failing to participate.
        let global_zero_count: Option<usize> = if prefix == 0 && comms.peers() > 1 {
            let mut local: usize = 0;
            for other_part in other_facts.iter() {
                let mut ranges = vec![(0usize, 1usize)];
                for layer in 0 .. terms.len() { advance_bounds::<Terms>(other_part.layer(layer).borrow(), &mut ranges); }
                local += ranges[0].1 - ranges[0].0;
            }
            Some(comms.all_reduce_sum(local as u64) as usize)
        } else { None };

        if let Some(mut delta) = salad.facts.flatten() {
            let length = if prefix > 0 { delta.layer(prefix-1).list.borrow().values.len() } else { 1 };
            let mut counts = vec![0; length];
            // We may have a count override; if so, just apply it.
            if let Some(g) = global_zero_count { counts[0] = g; }
            else {
                for other_part in other_facts.iter() {
                    let mut delta_idxs = vec![0];
                    let mut other_idxs = vec![0];
                    for layer in 0 .. prefix { (delta_idxs, other_idxs) = intersection::<Terms>(delta.layer(layer).borrow(), other_part.layer(layer).borrow(), &delta_idxs, &other_idxs); }
                    // The count derives from projecting `other_idxs` forward through `terms`.
                    let mut ranges = other_idxs.iter().map(|i| (*i,*i+1)).collect::<Vec<_>>();
                    for layer in prefix .. (prefix + terms.len()) { advance_bounds::<Terms>(other_part.layer(layer).borrow(), &mut ranges); }
                    for (delta_idx, range) in delta_idxs.iter().zip(ranges.iter()) { counts[*delta_idx] += range.1-range.0; }
                }
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

                assert_eq!(counts.len(), layers[prefix-1].list.borrow().values.len());
                delta = layers.try_into().expect("non-empty due to count.is_empty() guard");
            }

            // Must now project `counts` forward to leaves of `delta`, where we expect to find installed counts.
            let mut ranges = (0 .. counts.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
            for layer in prefix .. delta.arity() { advance_bounds::<Terms>(delta.layer(layer).borrow(), &mut ranges); }

            let mut notes_rc = delta.pop_layer().unwrap();
            let notes = &mut Rc::make_mut(&mut notes_rc).list.make_typed().values.values;
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
        salad.align_to(comms, my_terms[..prefix].iter().cloned());
        if prefix == 0 && terms.is_empty() {
            // Zero-prefix semijoin: retain salad iff atom is globally non-empty.
            // `retain_inner` with empty prefix slices underflows (`other_arity - 1`
            // when `other_arity == 0`), so we must short-circuit even in
            // single-worker runs.
            if !comms.any(!my_facts.is_empty()) { salad.facts = Default::default(); }
            return;
        }
        if prefix == 0 && comms.peers() > 1 {
            // Zero-prefix multi-worker cross-product. Broadcast the salad so
            // every worker holds the full union, then locally cross-join with
            // this worker's atom shard. The output's column 0 is from the atom
            // side, preserving the "column 0 is the partition key" invariant
            // without any further coordination. Single-worker prefix-0 falls
            // through to `join_many` below, which handles the local Cartesian.
            use columnar::{Container, Len};
            use crate::facts::trie::Layer;
            comms.broadcast(&mut salad.facts);
            if let Some(salad_full) = salad.facts.flatten() {
                for atom_part in my_facts.iter() {
                    let n = atom_part.len();
                    if n == 0 { continue; }
                    let mut layers: Vec<Rc<Layer<Terms>>> = (0..atom_part.arity()).map(|i| atom_part.layer(i).clone()).collect();
                    for j in 0..salad_full.arity() {
                        let sj = salad_full.layer(j);
                        let mut list = sj.list.clone();
                        for _ in 1..n {
                            list.extend_from_self(sj.list.borrow(), 0..sj.list.len());
                        }
                        layers.push(Rc::new(Layer { list }));
                    }
                    salad.facts.extend([layers.try_into().expect("non-empty by construction")]);
                }
            }
            let prior_terms = std::mem::take(&mut salad.terms);
            salad.terms = my_terms.iter().chain(prior_terms.iter()).cloned().collect();
            salad.align_to(comms, after.iter().cloned());
            return;
        }
        if !terms.is_empty() {
            // join with atom: permute `salad.terms` into the right order, join adding the new column, permute into target order (`delta_terms_new`).
            let conduit = comms.conduit();
            if let Some(delta) = salad.facts.flatten() {
                let join_terms = salad.terms.iter().chain(salad.terms[..prefix].iter()).chain(terms.iter()).cloned().collect::<Vec<_>>();
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
