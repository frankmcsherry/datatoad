//! Types, traits, and logic for planning and evaluating rules.
//!
//! Rules have a head and a body, each a list of atoms (though multi-atom heads are inconsistently supported).
//! Each binding of variable terms that satisfies all body atoms results in satisfaction of the head atoms.
//! Usually this means producing the terms in the head atoms, and introducing them to the data backing the atom.
//!
//! Each body atom implements two traits: `PlanAtom` and `ExecAtom`, for planning and execution respectively.
//!
//! The `PlanAtom` trait identifies terms known to the atom, and any terms that can be derived from other terms.
//! It is used in planning, when we need to determine which atoms can be relied on to bind which terms.
//!
//! The `ExecAtom` trait provides the two operations an atom performs: counting and enumerating values that extend a partial binding of terms.
//! The operations are "columnar", acting on large blocks of data to allow the implementor to specialize their execution.
//!
//! These traits are implemented for relations that are *explicit* (represented by data) and *implicit* (represented by code), and in-between (e.g. antijoins).

use crate::types::{Rule, Action, Atom, Term};
use crate::facts::{FactContainer, FactLSM, Relations};

pub mod plan;
pub mod exec;

pub use plan::PlanAtom;
pub use exec::ExecAtom;

/// Implements a provided rule in the context of various facts.
///
/// The `stable` argument indicates whether we should perform a join with all facts (true),
/// or only a join that involves novel facts (false).
pub fn implement(rule: &Rule, stable: bool, facts: &mut Relations) {
    match (&rule.head[..], &rule.body[..]) {
        (head, [body]) => { implement_action(head, body, stable, facts) },
        (head, body) => { implement_joins(head, body, stable, facts) },
    }
}

/// Maps an action across a single atom in the body.
fn implement_action(head: &[Atom], body: &Atom, stable: bool, facts: &mut Relations) {

    // The body provides filters and an association between columns and names,
    // which we expect to find in the atoms of the head. We'll need to form up
    // actions for each head that perform the compound actions.
    let load_action = Action::from_body(body);
    let head_actions = head.iter().map(|atom| {
        let mut action = load_action.clone();
        action.projection = atom.terms.iter().map(|term| {
            match term {
                Term::Var(____) => { action.projection[body.terms.iter().position(|t| t == term).unwrap()].clone() },
                Term::Lit(data) => { Err(data.to_vec()) },
            }
        }).collect();
        action
    }).collect::<Vec<_>>();
    // TODO: perform all actions at the same time. Likely extend `FactContainer::act_on`.
    for (head_atom, action) in head.iter().zip(head_actions.iter()) {
        if let Some(found) = facts.get(body.name.as_str()) {
            let mut derived = FactLSM::default();
            for layer in found.stable.contents().filter(|_| stable).chain(Some(&found.recent)) {
                derived.extend(&mut layer.act_on(action));
            }
            facts.entry(head_atom.name.clone()).extend(derived);
        }
    }
}

/// The complicated implementation case where these is at least one join.
fn implement_joins(head: &[Atom], body: &[Atom], stable: bool, facts: &mut Relations) {

    let (plans, loads) = plan::plan_rule::<plan::ByTerm>(head, body);

    let plan_atoms = if stable { 1 } else { body.len() };

    let potato = "potato".to_string();

    for (plan_atom, atom) in body[..plan_atoms].iter().enumerate() {

        if !plans.contains_key(&plan_atom) { continue; }
        if !stable && facts.get(atom.name.as_str()).unwrap().recent.is_empty() { continue; }

        let plan = &plans[&plan_atom];

        // Stage 0: Load the recently added facts.
        let (action, terms) = &loads[&plan_atom][&plan_atom];
        facts.ensure_action(body[plan_atom].name.as_str(), action);

        let mut delta_terms = terms.clone();
        let mut delta_lsm = FactLSM::default();
        if stable {
            let facts = &facts.get_action(atom.name.as_str(), action).unwrap();
            for layer in facts.stable.contents().chain([&facts.recent]) {
                delta_lsm.push(layer.clone());
            }
        }
        else {
            let facts = &facts.get_action(atom.name.as_str(), action).unwrap();
            delta_lsm.push(facts.recent.clone());
        };

        if delta_lsm.is_empty() { continue; }

        for (load_atom, (action, _)) in loads[&plan_atom].iter() {
            facts.ensure_action(body[*load_atom].name.as_str(), action);
        }

        // Stage 1: Semijoin with other atoms that are subsumed by the initial terms.
        let (init_atoms, _init_terms, init_order) = &plan[0];
        for load_atom in init_atoms.iter().filter(|a| a != &&plan_atom) {
            let (load_action, load_terms) = &loads[&plan_atom][load_atom];
            let other = &facts.get_action(body[*load_atom].name.as_str(), load_action).unwrap();
            let to_chain = if load_atom > &plan_atom { Some(&other.recent) } else { None };
            let other_facts = other.stable.contents().chain(to_chain).filter(|l| !l.is_empty()).collect::<Vec<_>>();
            let boxed_atom: Box::<dyn exec::ExecAtom<&String>+'_> = {
                if let Some(logic) = logic::resolve(&body[*load_atom]) { Box::new(logic) }
                else if body[*load_atom].anti { Box::new(antijoin::Anti((other_facts, load_terms))) }
                else { Box::new((other_facts, load_terms)) }
            };
            boxed_atom.join(&mut delta_lsm, &mut delta_terms, &Default::default(), &init_order);
        }
        // We may need to produce the result in a different order.
        crate::rules::exec::permute_delta(&mut delta_lsm, &mut delta_terms, init_order.iter().copied(), true);

        // Stage 2: Each other plan stage.
        for (atoms, terms, order) in plan.iter().skip(1) {

            let others = atoms.iter().map(|load_atom| {
                let (load_action, load_terms) = &loads[&plan_atom][load_atom];
                let other = &facts.get_action(body[*load_atom].name.as_str(), load_action).unwrap();
                let to_chain = if load_atom > &plan_atom && !other.recent.is_empty() { Some(&other.recent) } else { None };
                let other_facts = other.stable.contents().chain(to_chain).collect::<Vec<_>>();
                let boxed_atom: Box::<dyn exec::ExecAtom<&String>+'_> = {
                    if let Some(logic) = logic::resolve(&body[*load_atom]) { Box::new(logic) }
                    else if body[*load_atom].anti { Box::new(antijoin::Anti((other_facts, load_terms))) }
                    else { Box::new((other_facts, load_terms)) }
                };
                boxed_atom
            }).collect::<Vec<_>>();

            exec::wco_join(&mut delta_lsm, &mut delta_terms, &terms, &others[..], &potato, &order[..]);
        }

        // Stage 3: We now need to form up the facts to commit back to `facts`.
        // It is possible that with a single head we have the terms in the right order,
        // and can simply commit `delta`. There could be multiple heads, and the action
        // could be not the identity.
        let exact_match = head.iter().position(|a| {
            a.terms.len() == delta_terms.len() &&
            a.terms.iter().zip(delta_terms.iter()).all(|(h,d)| h.as_var() == Some(d))
        });

        for (_, atom) in head.iter().enumerate().filter(|(pos,_)| Some(*pos) != exact_match) {
            let mut action = Action::with_arity(delta_terms.len());
            action.projection = atom.terms.iter().map(|t| match t {
                Term::Var(name) => Ok(delta_terms.iter().position(|t2| t2 == &name).expect(format!("Failed to find {:?} in {:?}", name, delta_terms).as_str())),
                Term::Lit(data) => Err(data.clone()),
            }).collect();
            let delta = delta_lsm.flatten().unwrap_or_default();
            facts.entry(atom.name.clone()).extend(delta.act_on(&action));
            delta_lsm.push(delta);
        }
        if let Some(pos) = exact_match {
            facts.entry(head[pos].name.clone()).extend(delta_lsm);
        }
    }
}

/// Atom trait implementations for relations that are collections of data.
pub mod data {

    use std::collections::BTreeSet;
    use crate::facts::{FactLSM, FactContainer, Terms};
    use crate::facts::trie::Forest;
    use crate::rules::{PlanAtom, ExecAtom};

    impl<T: Ord + Copy> PlanAtom<T> for BTreeSet<T> {
        fn terms(&self) -> BTreeSet<T> { self.clone() }
        fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T> { self.difference(terms).cloned().collect() }
    }

    impl<'a, T: Ord + Copy> ExecAtom<T> for (Vec<&'a Forest<Terms>>, &'a Vec<T>) {

        fn terms(&self) -> &[T] { self.1 }

        fn count(
            &self,
            delta_lsm: &mut FactLSM<Forest<Terms>>,
            delta_terms: &mut Vec<T>,
            terms: &BTreeSet<T>,
            other_index: u8,
        ) {

            use columnar::Len;
            use crate::facts::trie::layers::advance_bounds;
            use crate::facts::trie::layers::intersection;

            let (other_facts, other_terms) = self;

            let prefix = other_terms.iter().take_while(|t| delta_terms.contains(t)).count();
            crate::rules::exec::permute_delta(delta_lsm, delta_terms, other_terms[..prefix].iter().copied(), true);
            let mut delta = delta_lsm.flatten().unwrap_or_default();
            if !delta.is_empty() {
                let mut counts = vec![0; delta.layers[prefix-1].list.values.len()];
                for other_part in other_facts.iter() {
                    let mut delta_idxs = vec![0];
                    let mut other_idxs = vec![0];
                    for layer in 0 .. prefix { (delta_idxs, other_idxs) = intersection::<Terms>(delta.layers[layer].borrow(), other_part.layers[layer].borrow(), &mut delta_idxs, &mut other_idxs); }
                    // The count derives from projecting `other_idxs` forward through `terms`.
                    let mut ranges = other_idxs.iter().map(|i| (*i,*i+1)).collect::<Vec<_>>();
                    for layer in prefix .. (prefix + terms.len()) { advance_bounds::<Terms>(other_part.layers[layer].borrow(), &mut ranges); }
                    for (delta_idx, range) in delta_idxs.iter().zip(ranges.iter()) { counts[*delta_idx] += range.1-range.0; }
                }

                // We now project `counts` forward through `delta` to the `potato` column.
                // If any of `counts` are zero, we have the option to first restrict `delta` to only those prefixes.
                // We don't have to do this, can choose to avoid if there are only *few* zeros, and generally don't expect this is semijoins have already happened.
                let remove_zeros = counts.iter().filter(|c| c == &&0).count() > 0;
                if remove_zeros {
                    let mut bools = std::collections::VecDeque::with_capacity(counts.len());
                    bools.extend(counts.iter().map(|c| c > &0));
                    counts.retain(|c| c > &0);

                    let mut layers = Vec::with_capacity(delta_terms.len());
                    if delta_terms.len() > prefix {

                        let mut prev = None;
                        let mut bounds = Vec::default();
                        for (idx, retain) in bools.iter().chain([&false]).enumerate() {
                            match (retain, &mut prev) {
                                (true, None) => { prev = Some(idx); },
                                (false, Some(lower) ) => { bounds.push((*lower, idx)); prev = None; }
                                _ => { },
                            }
                        }

                        for layer in delta.layers[prefix..].iter() { layers.push(layer.retain_lists(&mut bounds)); }
                    }
                    for layer in delta.layers[..prefix].iter().rev() { layers.insert(0, layer.retain_items(&mut bools)); }

                    assert_eq!(counts.len(), layers[prefix-1].list.values.len());
                    delta = Forest { layers };
                }


                // Must now project `counts` forward to leaves of `delta`, where we expect to find installed counts.
                let mut ranges = (0 .. counts.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
                for layer in prefix .. delta.layers.len() { advance_bounds::<Terms>(delta.layers[layer].borrow(), &mut ranges); }
                let notes = &mut delta.layers.last_mut().unwrap().list.values.values;
                for (count, range) in counts.iter().zip(ranges.iter()) {
                    let order = (count+1).ilog2() as u8;
                    for index in range.0 .. range.1 {
                        if notes[4 * index] >= order {
                            notes[4 * index] = order;
                            notes[4 * index + 1] = other_index as u8;
                        }
                    }
                }
                delta_lsm.push(delta);

            }
        }

        fn join(
            &self,
            delta_shard: &mut FactLSM<Forest<Terms>>,
            delta_terms: &mut Vec<T>,
            terms: &BTreeSet<T>,
            after: &[T],
        ) {
            if !terms.is_empty() {
                let (other_facts, other_terms) = self;

                // join with atom: permute `delta_shard` into the right order, join adding the new column, permute into target order (`delta_terms_new`).
                let prefix = other_terms.iter().take_while(|t| delta_terms.contains(t)).count();
                crate::rules::exec::permute_delta(delta_shard, delta_terms, other_terms[..prefix].iter().copied(), true);
                let delta = delta_shard.flatten().unwrap_or_default();
                let join_terms = delta_terms.iter().chain(delta_terms[..prefix].iter()).chain(terms.iter()).copied().collect::<Vec<_>>();
                // Our output join order (until we learn how to do FDB shapes) is the first of `others` not equal to ourself.
                let projection = after.iter().map(|t| join_terms.iter().position(|t2| t == t2).unwrap()).collect::<Vec<_>>();
                let mut delta = delta.join_many(other_facts.iter().copied(), prefix, &projection[..]);
                let delta = delta.flatten().unwrap_or_default();
                delta_terms.clear();
                delta_terms.extend_from_slice(after);
                delta_shard.push(delta);
            }
            else {
                let (next_other_facts, next_other_terms) = self;

                let prefix = next_other_terms.iter().take_while(|t| delta_terms.contains(t)).count();
                crate::rules::exec::permute_delta(delta_shard, delta_terms, next_other_terms[..prefix].iter().copied(), true);
                let mut delta = delta_shard.flatten().unwrap_or_default();
                let others = next_other_facts.iter().map(|o| o.borrow()).collect::<Vec<_>>();
                delta = delta.retain_inner(others.iter().map(|o| &o[..prefix]), true);
                delta_shard.push(delta);
            }
        }
    }
}

/// Atom trait implementations for relations that are the complement of a collection of data.
pub mod antijoin {

    use std::collections::BTreeSet;
    use crate::facts::{FactLSM, Terms};
    use crate::facts::trie::Forest;
    use crate::rules::{PlanAtom, ExecAtom};

    /// Wrapper type for antijoins.
    pub struct Anti<T>(pub T);

    impl <T: Ord + Copy> PlanAtom<T> for Anti<BTreeSet<T>> {
        fn terms(&self) -> BTreeSet<T> { self.0.clone() }
        fn ground(&self, _terms: &BTreeSet<T>) -> BTreeSet<T> { Default::default() }
    }

    impl<'a, T: Ord + Copy> ExecAtom<T> for Anti<(Vec<&'a Forest<Terms>>, &'a Vec<T>)> {

        fn terms(&self) -> &[T] { self.0.1 }

        fn count(
            &self,
            _: &mut FactLSM<Forest<Terms>>,
            _: &mut Vec<T>,
            _: &BTreeSet<T>,
            _: u8,
        ) {
            // Antijoins propose nothing
        }

        fn join(
            &self,
            delta_shard: &mut FactLSM<Forest<Terms>>,
            delta_terms: &mut Vec<T>,
            terms: &BTreeSet<T>,
            _after: &[T],
        ) {
            let (next_other_facts, next_other_terms) = &self.0;

            let prefix = next_other_terms.iter().take_while(|t| delta_terms.contains(t)).count();
            crate::rules::exec::permute_delta(delta_shard, delta_terms, next_other_terms[..prefix].iter().copied(), true);
            let mut delta = delta_shard.flatten().unwrap_or_default();
            assert!(terms.is_empty() || delta.is_empty());
            let others = next_other_facts.iter().map(|o| o.borrow()).collect::<Vec<_>>();
            delta = delta.retain_inner(others.iter().map(|o| &o[..prefix]), false);
            delta_shard.push(delta);
        }
    }
}

/// Atom trait implementations for relations that are implemented by computation.
pub mod logic {

    //! Implementations for named relations that are backed by computation.
    //!
    //! The traits `Logic` and `BatchLogic` try to make it easier to implement a new relation than from scratch.
    //! The `Logic` trait provides per-record functions, which are meant to be inlined for performance.
    //! The `BatchLogic` trait provides batch functions, and expects to be invoked through a virtual call.

    use std::collections::BTreeSet;

    use columnar::{Container, Index, Len, Push, Clear};

    use crate::types::{Atom, Term};
    use crate::facts::FactLSM;
    use crate::facts::{Forest, Lists, Terms};
    use crate::facts::trie::Layer;
    use crate::facts::trie::layers::advance_bounds;
    use crate::rules::{exec, plan};

    /// Looks for the atom's name in a known list, and returns an implementation if found.
    ///
    /// The implementation is a type that implements both `PlanAtom` and `ExecAtom`, and can be boxed as either.
    pub fn resolve<'a>(atom: &'a Atom) -> Option<LogicRel<&'a String>> {
        match atom.name.as_str() {
            ":noteq" => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::NotEq } ), &atom)),
            ":range" => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::Range } ), &atom)),
            ":plus"  => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::Plus } ),  &atom)),
            ":times" => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::Times } ), &atom)),
            ":print" => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::Print(atom.terms.len()) } ), &atom)),
            _ => None,
        }
    }


    /// A type that can behave as a relation in the context of join planning.
    pub trait Logic {
        /// The number of columns in the relation.
        fn arity(&self) -> usize;

        /// For input columns, any other columns the type can fully substantiate from concrete values of the input columns.
        ///
        /// Returning output columns introduces an obligation that the type can be relied on to substantiate concrete values.
        /// The obligation means that `self.count` must be non-`None` for concrete values of these columns, and `self.delve`
        /// must provide values for those columns (it can produce zero values, but cannot panic or otherwise nope out).
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize>;

        /// For values of some input columns, an upper bound on the number of distinct corresponding tuples in `output`.
        ///
        /// This method may be invoked with input and output column pairs returned by `self.bound` and no others, and must return `Some`
        /// values for concrete values of any input columns for which `self.bound` indicated the output columns.
        /// If this method is called on input columns not advertised by `self.bound`, it may return either `Some` or `None` values.
        ///
        /// When `output` is empty, it is important to emit either `Some(0)` or `Some(1)` to indicate respectively absence or presence.
        /// It is important that this result be accurate, as the type will not be given another chance to decline the records.
        fn count(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], output: &BTreeSet<usize>) -> Option<usize>;

        /// For values of some input columns, populate distinct values for arguments in `output`.
        ///
        /// This method may be called for any concrete values for which `self.count` returned a specific non-zero value (neither `None` nor `Some(0)`).
        /// The number of results should not exceed the value reported by `self.count`, though the only certain correctness requirement
        /// is that it should not plan to return any values if the count was advertised as `Some(0)`, as it may not get the chance.
        fn delve(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], output: (usize, &mut Terms));
    }

    pub trait BatchLogic {
        /// The number of arguments the logic expects.
        fn arity(&self) -> usize;
        /// For concrete values of the supplied arguments, which other arguments can be produced as concrete values.
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize>;
        /// For a subset of arguments, an upper bound on the number of distinct set of values for arguments in `output`.
        ///
        /// When `output` is empty, it is important to emit variously `Some(0)` or `Some(1)` to indicate respectively absence or presence.
        fn count(&self, args: &[Option<(<Terms as columnar::Container>::Borrowed<'_>, Vec<usize>)>], output: &BTreeSet<usize>) -> Vec<Option<usize>>;
        /// For a subset of arguments, populate distinct values for arguments in `output`.
        fn delve(&self, args: &[Option<(<Terms as columnar::Container>::Borrowed<'_>, Vec<usize>)>], output: usize) ->Lists<Terms>;
    }

    /// A wrapper for general logic-backed relations that manages the terms in each position.
    pub struct LogicRel<T> {
        pub logic: Box<dyn super::logic::BatchLogic>,
        /// In order: `[lower, value, upper]`.
        ///
        /// Each are either a term name, or a literal.
        pub bound: Vec<Result<T, Vec<u8>>>,
        /// Terms of `bound` in some order, used by exec to lay out records "favorably".
        pub terms: Vec<T>,
    }

    impl<'a> LogicRel<&'a String> {
        /// Create a new instance of `Self` from batch logic and the atom itself.
        pub fn new(logic: Box<dyn super::logic::BatchLogic>, atom: &'a Atom) -> Self {
            let bound = atom.terms.iter().map(|t| match t { Term::Var(name) => Ok(name), Term::Lit(data) => Err(data.clone()) }).collect::<Vec<_>>();
            let terms = bound.iter().flatten().collect::<BTreeSet<_>>().into_iter().copied().collect::<Vec<_>>();
            Self { logic, bound, terms }
        }
    }

    impl <T: Ord + Copy> plan::PlanAtom<T> for LogicRel<T> {
        fn terms(&self) -> BTreeSet<T> { self.terms.iter().cloned().collect() }
        fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T> {
            let indexes = self.bound.iter().enumerate().filter(|(_index, term)| match term {
                Ok(name) => terms.contains(name),
                Err(_) => true,
            }).map(|(index,_term)| index).collect();
            self.logic.bound(&indexes).into_iter().map(|index| self.bound[index].as_ref().unwrap()).copied().collect()
        }
    }

    impl<'a, T: Ord + Copy> exec::ExecAtom<T> for LogicRel<T> {

        // Lightly odd, in that we have no preference on term order.
        fn terms(&self) -> &[T] { &self.terms }

        fn count(
            &self,
            facts: &mut FactLSM<Forest<Terms>>,
            terms: &mut Vec<T>,
            added: &BTreeSet<T>,
            my_index: u8,
        ) {
            //  Flatten the input, to make our life easier.
            let mut delta = facts.flatten().unwrap_or_default();
            if delta.is_empty() { return; }

            //  1.  Prepare the function arguments, a `Vec<Option<(Borrowed, Vec<usize>)>>` indicating present elements of `self.bound`.
            //      Each present element of `self.bound` presents as a pair of borrowed container and list of counts for each element.
            //      All present pairs should have the same sum of counts, indicating the total number of argument tuples.
            let max = self.bound.iter().flatten().flat_map(|term| terms.iter().position(|t| t == term)).max();
            let cnt = max.map(|col| delta.layers[col].list.values.len()).unwrap_or(1);

            //  Long-lived containers for literal values.
            //  In an FDB world, we would put these at the root, independent of any input data, rather than to the side.
            let mut lits = vec![Terms::default(); self.bound.len()];
            for (index, arg) in self.bound.iter().enumerate() { if let Err(lit) = arg { lits[index].push(lit); } }

            //  The arguments themselves, from indicated layers with counts projected forward to `max` layer.
            let args: Vec<Option<(<Terms as Container>::Borrowed<'_>, Vec<usize>)>> =
            self.bound.iter().enumerate().map(|(index, arg)| {
                match arg {
                    Ok(term) => {
                        terms.iter().position(|t| t == term).map(|col| {
                            let mut bounds = (0 .. delta.layers[col].list.values.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
                            for i in col+1 .. max.unwrap()+1 { advance_bounds::<Terms>(delta.layers[i].borrow(), &mut bounds)};
                            let counts = bounds.into_iter().map(|(l, u)| u-l).collect::<Vec<_>>();
                            (delta.layers[col].list.values.borrow(), counts)
                        })
                    },
                    Err(_) => { Some((lits[index].borrow(), vec![cnt] )) },
                }
            }).collect();

            //  2.  Evaluate the function for each setting of the arguments.
            let added = added.iter().map(|term| self.bound.iter().position(|t| t.as_ref() == Ok(term)).unwrap()).collect::<BTreeSet<_>>();
            let output = self.logic.count(&args, &added);

            //  3.  Project the output forward to the count column, potentially update count and index.
            let orders = match max {
                Some(col) => {
                    let mut bounds = (0 .. delta.layers[col].list.values.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
                    for i in col+1 .. delta.layers.len() { advance_bounds::<Terms>(delta.layers[i].borrow(), &mut bounds)};
                    bounds.into_iter().map(|(l,u)| u-l).collect::<Vec<_>>()
                },
                None => { vec![delta.layers.last().unwrap().list.values.len()] }
            };

            let notes = &mut delta.layers.last_mut().unwrap().list.values.values;
            for (index, order) in orders.into_iter().enumerate().flat_map(|(i,c)| std::iter::repeat(output[i]).take(c)).enumerate() {
                if let Some(order) = order {
                    let order: u8 = (order+1).ilog2() as u8;
                    if notes[4 * index] >= order {
                        notes[4 * index] = order;
                        notes[4 * index + 1] = my_index as u8;
                    }
                }
            }

            facts.push(delta);
        }

        fn join(
            &self,
            facts: &mut FactLSM<Forest<Terms>>,
            terms: &mut Vec<T>,
            added: &BTreeSet<T>,
            _after: &[T],
        ) {
            //  Flatten the input, to make our life easier.
            let mut delta = facts.flatten().unwrap_or_default();
            if delta.is_empty() { terms.push(added.iter().next().unwrap().clone()); return; }

            //  1.  Prepare the function arguments, a `Vec<Option<(Borrowed, Vec<usize>)>>` indicating present elements of `self.bound`.
            //      Each present element of `self.bound` presents as a pair of borrowed container and list of counts for each element.
            //      All present pairs should have the same sum of counts, indicating the total number of argument tuples.
            let max = self.bound.iter().flatten().flat_map(|term| terms.iter().position(|t| t == term)).max();
            let cnt = max.map(|col| delta.layers[col].list.values.len()).unwrap_or(1);

            //  Long-lived containers for literal values.
            //  In an FDB world, we would put these at the root, independent of any input data, rather than to the side.
            let mut lits = vec![Terms::default(); self.bound.len()];
            for (index, arg) in self.bound.iter().enumerate() { if let Err(lit) = arg { lits[index].push(lit); } }

            //  The arguments themselves, from indicated layers with counts projected forward to `max` layer.
            let args: Vec<Option<(<Terms as Container>::Borrowed<'_>, Vec<usize>)>> =
            self.bound.iter().enumerate().map(|(index, arg)| {
                match arg {
                    Ok(term) => {
                        terms.iter().position(|t| t == term).map(|col| {
                            let mut bounds = (0 .. delta.layers[col].list.values.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
                            for i in col+1 .. max.unwrap()+1 { advance_bounds::<Terms>(delta.layers[i].borrow(), &mut bounds)};
                            let counts = bounds.into_iter().map(|(l, u)| u-l).collect::<Vec<_>>();
                            (delta.layers[col].list.values.borrow(), counts)
                        })
                    },
                    Err(_) => { Some((lits[index].borrow(), vec![cnt] )) },
                }
            }).collect();

            if added.is_empty() {
                // Semijoin case.
                let added = added.iter().map(|term| self.bound.iter().position(|t| t.as_ref() == Ok(term)).unwrap()).collect::<BTreeSet<_>>();
                let keep = self.logic.count(&args, &added).into_iter().map(|x| x != Some(0)).collect::<std::collections::VecDeque<_>>();
                delta = delta.retain_core(max.map(|c| c+1).unwrap_or(0), keep);
            }
            else {
                let colidx = added.iter().map(|term| self.bound.iter().position(|t| t.as_ref() == Ok(term)).unwrap()).next().unwrap();
                let column = self.logic.delve(&args, colidx);
                assert_eq!(added.len(), 1);
                // TODO: Need to advance to the last layer; in an FDB we could just branch at `max`.
                let pos = max.map(|c| c+1).unwrap_or(0);
                //  We are initially 1:1 with the lists of layer pos, or items of layer pos-1.
                //  We'll want to advance through each of the layers `pos..`.
                let mut bounds = (0 .. column.len()).map(|i| (i, i+1)).collect::<Vec<_>>();
                for idx in pos .. delta.layers.len() { advance_bounds::<Terms>(delta.layers[idx].borrow(), &mut bounds); }
                let mut colnew: Lists<Terms> = Default::default();
                for idx in 0 .. column.len() {
                    for _ in bounds[idx].0 .. bounds[idx].1 {
                        colnew.push(column.borrow().get(idx));
                    }
                }
                delta.layers.push(Layer { list: colnew });//insert(pos, Layer { list: column });
                terms.push(added.iter().next().unwrap().clone());
            }

            facts.push(delta);
        }
    }

    pub struct BatchedLogic<L: Logic> { pub logic: L }

    impl<L: Logic> BatchLogic for BatchedLogic<L> {
        fn arity(&self) -> usize { self.logic.arity() }
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> { self.logic.bound(args) }
        fn count(&self, args: &[Option<(<Terms as columnar::Container>::Borrowed<'_>, Vec<usize>)>], output: &BTreeSet<usize>) -> Vec<Option<usize>> {

            // The following is .. neither clear nor performant. It should be at least one of those two things.
            let length = args.iter().flatten().next().map(|a| a.1.iter().sum()).unwrap_or(1);
            let mut counts = Vec::with_capacity(length);
            let mut indexs = args.iter().map(|opt| opt.as_ref().map(|(_, counts)| counts.iter().copied().enumerate().flat_map(|(index, count)| std::iter::repeat(index).take(count)))).collect::<Vec<_>>();
            let mut values: Vec<Option<<Terms as columnar::Container>::Ref<'_>>> = Vec::default();
            for _ in 0 .. length {
                values.clear();
                Extend::extend(&mut values, indexs.iter_mut().enumerate().map(|(col, i)| i.as_mut().map(|j| args[col].as_ref().unwrap().0.get(j.next().unwrap()))));
                counts.push(self.logic.count(&values, output));
            }

            counts
        }
        fn delve(&self, args: &[Option<(<Terms as columnar::Container>::Borrowed<'_>, Vec<usize>)>], output: usize) -> Lists<Terms> {

            // The following is .. neither clear nor performant. It should be at least one of those two things.
            let length = args.iter().flatten().next().map(|a| a.1.iter().sum()).unwrap_or(1);
            let mut indexs = args.iter().map(|opt| opt.as_ref().map(|(_, counts)| counts.iter().copied().enumerate().flat_map(|(index, count)| std::iter::repeat(index).take(count)))).collect::<Vec<_>>();
            let mut values: Vec<Option<<Terms as columnar::Container>::Ref<'_>>> = Vec::default();
            let mut terms = Terms::default();
            let mut result: Lists<Terms> = Default::default();
            for _ in 0 .. length {
                values.clear();
                Extend::extend(&mut values, indexs.iter_mut().enumerate().map(|(col, i)| i.as_mut().map(|j| args[col].as_ref().unwrap().0.get(j.next().unwrap()))));
                self.logic.delve(&values, (output, &mut terms));
                result.push(terms.borrow().into_index_iter());
                terms.clear();
            }
            assert_eq!(result.len(), length);
            result
        }

    }

    pub mod relations {

        use std::collections::BTreeSet;
        use columnar::Push;
        use crate::facts::Terms;

        /// Big-endian interpretation of `bytes` as `u64`, if the length is at most eight.
        fn as_u64(bytes: &[u8]) -> Option<u64> {
            if bytes.len() > 8 { None }
            else {
                let mut slice = [0u8; 8];
                slice[8-bytes.len() ..].copy_from_slice(bytes);
                Some(u64::from_be_bytes(slice))
            }
        }

        /// Decodes a number of optional byte slices as correspondingly optional `u64` data.
        ///
        /// The method returns `None` if the number of arguments is not `K`, if the slice lengths differ, or if any exceed eight.
        fn decode_u64<const K: usize>(args: &[Option<<Terms as columnar::Container>::Ref<'_>>]) -> Option<([Option<u64>; K], usize)> {
            let mut width: Option<usize> = None;
            let mut result: [Option<u64>; K] = [None; K];
            for index in 0 .. K {
                if let Some(bytes) = &args[index] {
                    if width.is_some() && width != Some(bytes.len()) { None?; }
                    width = Some(bytes.len());
                    result[index] = Some(as_u64(bytes.as_slice())?);
                }
            }
            Some((result, width?))
        }

        /// The relation R(x,y) : x != y.
        pub struct NotEq;
        impl super::Logic for NotEq {
            fn arity(&self) -> usize { 2 }
            fn bound(&self, _args: &BTreeSet<usize>) -> BTreeSet<usize> { Default::default() }
            fn count(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
                match (&args[0], &args[1]) {
                    (Some(x), Some(y)) => { if x.as_slice() == y.as_slice() { Some(0) } else { Some(1) } },
                    _ => None,
                }
            }
            fn delve(&self, _args: &[Option<<Terms as columnar::Container>::Ref<'_>>], _output: (usize, &mut Terms)) { panic!("NotEq asked to enumerate values"); }
        }

        /// The relation R(x,y,z) : x * y = z, for terms all of the same length (up to eight bytes).
        pub struct Times;
        impl super::Logic for Times {
            fn arity(&self) -> usize { 3 }
            fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> {
                if args.len() > 1 || args.contains(&2) { (0 .. 2).filter(|i| !args.contains(i)).collect() } else { Default::default() }
            }
            fn count(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
                // Any two+ bound terms should lead to a `Some(0)` or `Some(1)` determination.
                if let Some((decoded, width)) = decode_u64::<3>(args) {
                    match decoded {
                        [Some(x), Some(y), Some(z)] => { let (mul, ovr) = u64::overflowing_mul(x, y); if !ovr && mul == z { Some(1) } else { Some(0) }},
                        [Some(x), Some(y),    None] => { let (mul, ovr) = u64::overflowing_mul(x, y); if !ovr && ((mul >> width) == 0) { Some(1) } else { Some(0) } },
                        [None,    Some(y), Some(z)] => { if y > 0 && y <= z && (z / y) * y == z { Some(1) } else { Some(0) } },
                        [Some(x), None,    Some(z)] => { if x > 0 && x <= z && (z / x) * x == z { Some(1) } else { Some(0) } },
                        // If we only have z, we there are only so many products that can form `z`.
                        [None,    None,    Some(z)] => { Some((z.isqrt() + 1) as usize) },
                        _ => None
                    }
                }
                else { Some(0) }
            }
            fn delve(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], output: (usize, &mut Terms)) {
                if let Some((decoded, width)) = decode_u64::<3>(args) {
                    match decoded {
                        [Some(x), Some(y),    None] => { let (mul, ovr) = u64::overflowing_mul(x, y); if !ovr && ((mul >> width) == 0) { output.1.push(&mul.to_be_bytes()[(8-width)..]) } },
                        [None,    Some(y), Some(z)] => { if y > 0 && y <= z && (z / y) * y == z { output.1.push(&(z/y).to_be_bytes()[(8-width)..]) } },
                        [Some(x), None,    Some(z)] => { if x > 0 && x <= z && (z / x) * x == z { output.1.push(&(z/x).to_be_bytes()[(8-width)..]) } },
                        // If we only have z, we there are only so many products that can form `z`.
                        [None,    None,    Some(z)] => {
                            for i in 0 .. z.isqrt()+1 {
                                if (z / i) * i == z { output.1.push(&i.to_be_bytes()[(8-width)..]); }
                            }
                        },
                        _ => { }
                    }
                }
            }
        }

        /// The relation R(x,y,z) : x + y = z, for terms all of the same length (up to eight bytes).
        pub struct Plus;
        impl super::Logic for Plus {
            fn arity(&self) -> usize { 3 }
            fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> { if args.len() > 1 { (0 .. 2).filter(|i| !args.contains(i)).collect() } else { Default::default() } }
            fn count(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
                // Any two+ bound terms should lead to a `Some(0)` or `Some(1)` determination.
                if let Some((decoded, width)) = decode_u64::<3>(args) {
                    match decoded {
                        [Some(x), Some(y), Some(z)] => { let (sum, ovr) = u64::overflowing_add(x, y); if !ovr && sum == z { Some(1) } else { Some(0) }},
                        [Some(x), Some(y),    None] => { let (sum, ovr) = u64::overflowing_add(x, y); if !ovr && ((sum >> width) == 0) { Some(1) } else { Some(0) } },
                        [Some(x),    None, Some(z)] => { if x <= z { Some(1) } else { Some(0) } },
                        [None,    Some(y), Some(z)] => { if y <= z { Some(1) } else { Some(0) } },
                        // TODO: There are some things that we could say more about, e.g. that a `z` has a count of `z+1` because there are that many ways to add up to `z`.
                        //       Based on unsigned math, as signed integers would have unbounded options. Seems likely to be a bad idea to propose this, without a better upper bound.
                        _ => None
                    }
                }
                else { Some(0) }
            }
            fn delve(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], output: (usize, &mut Terms)) {
                if let Some((decoded, width)) = decode_u64::<3>(args) {
                    match decoded {
                        [Some(x), Some(y),    None] => { let (sum, ovr) = u64::overflowing_add(x, y); if !ovr && ((sum >> width) == 0) { output.1.push(&sum.to_be_bytes()[(8-width)..]) } },
                        [Some(x), None,    Some(z)] => { if x <= z { output.1.push(&(z-x).to_be_bytes()[(8-width)..]) } },
                        [None,    Some(y), Some(z)] => { if y <= z { output.1.push(&(z-y).to_be_bytes()[(8-width)..]) } },
                        _ => { }
                    }
                }
            }
        }

        /// The relation R(x,y,z) : x <= y < z, for terms all of the same length (up to eight bytes).
        pub struct Range;
        impl super::Logic for Range {
            fn arity(&self) -> usize { 3 }
            fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> { if args.contains(&0) && args.contains(&2) && !args.contains(&1) { [1].into_iter().collect() } else { Default::default() } }
            fn count(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
                if let Some((decoded, _width)) = decode_u64::<3>(args) {
                    match decoded {
                        [Some(l), None,    Some(u)] => { if l < u { Some((u-l) as usize) } else { Some(0) } },
                        [Some(l), Some(v), Some(u)] => { if l <= v && v < u { Some(1) } else { Some(0) } },
                        _ => None,
                    }
                }
                else { Some(0) }
            }
            fn delve(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], output: (usize, &mut Terms)) {
                assert_eq!(output.0, 1);
                let length = args[0].unwrap().as_slice().len();
                let lower: u64 = as_u64(args[0].unwrap().as_slice()).unwrap();
                let upper: u64 = as_u64(args[2].unwrap().as_slice()).unwrap();
                for value in lower .. upper {
                    output.1.push(&value.to_be_bytes()[(8-length)..]);
                }
            }
        }

        /// The relation R(x,y,z) : x <= y < z, for terms all of the same length (up to eight bytes).
        pub struct Print(pub usize);
        impl super::Logic for Print {
            fn arity(&self) -> usize { self.0 }
            fn bound(&self, _args: &BTreeSet<usize>) -> BTreeSet<usize> { Default::default() }
            fn count(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], output: &BTreeSet<usize>) -> Option<usize> { if output.is_empty() {
                for arg in args.iter() { print!("0x"); for byte in arg.unwrap().as_slice().iter() { print!("{:0>2x}", byte); } print!("\t"); }
                println!();
                Some(1)
            } else { None } }
            fn delve(&self, _args: &[Option<<Terms as columnar::Container>::Ref<'_>>], _output: (usize, &mut Terms)) { unimplemented!() }
        }
    }
}
