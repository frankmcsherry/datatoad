use std::collections::BTreeSet;
use crate::types::{Rule, Action, Atom, Term};
use crate::facts::{FactContainer, FactLSM, Relations};

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
                else if body[*load_atom].anti { Box::new(Anti((other_facts, load_terms))) }
                else { Box::new((other_facts, load_terms)) }
            };
            boxed_atom.join(&mut delta_lsm, &mut delta_terms, &Default::default(), &init_order);
        }
        // We may need to produce the result in a different order.
        exec::permute_delta(&mut delta_lsm, &mut delta_terms, init_order.iter().copied());

        // Stage 2: Each other plan stage.
        for (atoms, terms, order) in plan.iter().skip(1) {

            let others = atoms.iter().map(|load_atom| {
                let (load_action, load_terms) = &loads[&plan_atom][load_atom];
                let other = &facts.get_action(body[*load_atom].name.as_str(), load_action).unwrap();
                let to_chain = if load_atom > &plan_atom && !other.recent.is_empty() { Some(&other.recent) } else { None };
                let other_facts = other.stable.contents().chain(to_chain).collect::<Vec<_>>();
                let boxed_atom: Box::<dyn exec::ExecAtom<&String>+'_> = {
                    if let Some(logic) = logic::resolve(&body[*load_atom]) { Box::new(logic) }
                    else if body[*load_atom].anti { Box::new(Anti((other_facts, load_terms))) }
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
                Term::Var(name) => Ok(delta_terms.iter().position(|t2| t2 == &name).unwrap()),
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

/// Traits and logic associated with planning rules.
pub mod plan {

    /// An atom over terms `T` that supports planning.
    ///
    /// More general than a fully grounded relation, implementors of this trait expose the terms they
    /// recognize, and their ability to ground some terms as a function of other terms. For a standard
    /// relation the terms would be the terms, and for any subset the remaining terms can be grounded.
    /// For more general implementors, there must be a full set of terms but perhaps no further terms
    /// may be grounded from any subset.
    pub trait PlanAtom<T: Ord> {

        /// Terms the atom references.
        fn terms(&self) -> BTreeSet<T>;

        /// Terms that the atom can produce ground values for, given ground values of the input terms.
        ///
        /// This can be empty for any `terms` arguments, for example with an antijoin or complex predicate.
        /// Implementors should only return non-empty collections when they can produce ground terms for
        /// any grounding of the input terms, as they may be called upon to be the ones to do this.
        fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T>;

    }

    use std::collections::{BTreeSet, BTreeMap};
    use crate::types::{Atom, Action};

    /// A plan is a sequence of sets of atoms and terms, and an output term order.
    ///
    /// Each plan stage uses the atoms to express their thoughts about the terms,
    /// each either joining or semijoining, depending on which terms are present.
    /// The term sets are disjoint, as each term can be *introduced* at most once,
    /// but the atom sets may repeat atoms as their many terms are introduced.
    ///
    /// The output term order discards columns that are no longer needed, and in
    /// the last plan stage ensures that the order matches that of the rule head.
    pub type Plan<A, T> = Vec<(BTreeSet<A>, BTreeSet<T>, Vec<T>)>;
    pub type Plans<A, T> = BTreeMap<A, Plan<A, T>>;
    pub type Load<T> = (Action<Vec<u8>>, Vec<T>);
    pub type Loads<A, T> = BTreeMap<A, BTreeMap<A, Load<T>>>;

    pub fn plan_rule<'a, S: Strategy<usize, &'a String>>(head: &'a [Atom], body: &'a [Atom]) -> (Plans<usize, &'a String>, Loads<usize, &'a String>) {

        // We'll pick a target term order for the first head; other heads may require transforms.
        // If we have multiple heads and one has no literals or repetitions, that would be best.
        let head_terms = head_order(head);

        // Map from atom identifier to boxed `PlanAtom`, containing term and grounding information.
        let atoms = body.iter().enumerate().map(|(index, atom)| {
            let terms = atom.terms.iter().filter_map(|term| term.as_var()).collect::<BTreeSet<_>>();
            if let Some(logic) = crate::plan::logic::resolve(atom) { (index, Box::new(logic) as Box::<dyn PlanAtom<&'a String> + 'a>) }
            else if !atom.anti { (index, Box::new(terms) as Box::<dyn PlanAtom<&'a String> + 'a>) }
            else { (index, Box::new(crate::plan::Anti(terms)) as Box::<dyn PlanAtom<&'a String> + 'a>) }
        }).collect::<BTreeMap<_,_>>();

        // We'll want to pre-plan the term orders for each atom update rule, so that we can
        // pre-ensure that the necessary input shapes exist, with each atom in term order.
        let plans = S::plan_rule(&atoms, &head_terms);

        // Actions for each atom that would produce the output in `terms` order.
        // Their output columns should now be ordered as `atoms_to_terms[atom]`.
        // We use these as reference points, and don't intend to load with them.
        let base_actions = body.iter().enumerate().map(|(index, atom)| {
            let mut action = Action::from_body(atom);
            action.projection.sort_by_key(|p| atom.terms[*p.as_ref().unwrap()].as_var().unwrap());
            (index, action)
        }).collect::<BTreeMap<_,_>>();

        let atoms_to_terms = atoms.iter().map(|(index, boxed)| (*index, boxed.terms())).collect::<BTreeMap<_,_>>();
        let mut load_actions = load_actions(&plans, &atoms_to_terms, &base_actions);

        // Insert loading actions for plan atoms themselves.
        for (plan_atom, _atom) in body.iter().enumerate() {
            if plans.contains_key(&plan_atom) {
                // We would like to order the terms by the order they'll be used in the next stage, which will be
                // by atom foremost, breaking ties by T::cmp. Only really appropriate if the first stage is empty,
                // other than the plan atom (e.g. if we must semijoin, this order likely won't say put).
                let plan_terms = atoms[&plan_atom].terms();
                let mut order = Vec::new();
                if plans[&plan_atom].len() > 1 {
                    for atom in plans[&plan_atom][1].0.iter() {
                        let atom_terms = atoms[&atom].terms();
                        for term in plan_terms.iter() {
                            if atom_terms.contains(term) && !order.contains(term) { order.push(*term); }
                        }
                    }
                }
                for term in plan_terms.iter() { if !order.contains(term) { order.push(*term); } }

                let mut action = base_actions[&plan_atom].clone();
                action.projection =
                order.iter()
                    .flat_map(|t1| plan_terms.iter().position(|t2| t1 == t2))
                    .map(|p| base_actions[&plan_atom].projection[p].clone())
                    .collect();

                load_actions.get_mut(&plan_atom).map(|l| l.insert(plan_atom, (action, order)));
            }
        }

        (plans, load_actions)
    }

    /// From per-atom plans, per-atom loading action required to for the right term order.
    ///
    /// The loading instructions ensure that each occurrence of an atom in a plan has an
    /// action that will load with all prior bound terms followed by newly bound terms.
    /// In the simplest, this could just order the terms in order they are bound.
    pub fn load_actions<A: Ord + Copy, T: Ord + Copy>(
        plans: &BTreeMap<A, Plan<A, T>>,
        atoms_to_terms: &BTreeMap<A, BTreeSet<T>>,
        base_actions: &BTreeMap<A, Action<Vec<u8>>>,
    ) -> Loads<A, T> {

        // This could be quite general, and use an arbitrary action for each atom in each stage.
        // For example, it needn't even be the same action across uses of the same atom.
        let mut result: Loads<A, T> = BTreeMap::default();
        for (plan_atom, plan) in plans.iter() {
            let mut all_terms = BTreeSet::default();
            let mut in_order = Vec::default();
            for (_atoms, terms, _out_order) in plan.iter() {
                let new_terms = terms.difference(&all_terms);
                in_order.extend(new_terms);
                all_terms.extend(terms.iter().copied());
            }
            let mut loads = BTreeMap::default();
            for load_atom in atoms_to_terms.keys().filter(|a| *a != plan_atom) {

                let load_terms = in_order.iter().filter(|t| atoms_to_terms[load_atom].contains(t)).copied().collect::<Vec<_>>();

                let mut action = base_actions[load_atom].clone();
                action.projection =
                in_order.iter()
                        .flat_map(|t1| atoms_to_terms[load_atom].iter().position(|t2| t1 == t2))
                        .map(|p| base_actions[load_atom].projection[p].clone())
                        .collect();

                loads.insert(*load_atom, (action, load_terms));
            }
            result.insert(*plan_atom, loads);
        }

        result
    }

    /// Produces a term order for head atoms.
    ///
    /// The order is of distinct terms in order of presentation.
    /// Repeated terms and literals should be added in post.
    fn head_order<'a>(head: &'a [Atom]) -> Vec<&'a String> {
        let mut seen: BTreeSet<&'a String> = BTreeSet::default();
        head.iter().flat_map(|a| a.terms.iter()).filter_map(|t| t.as_var()).filter(|t| seen.insert(t)).collect()
    }

    /// A type that can produce an update plan for a rule.
    pub trait Strategy<A: Ord+Copy, T: Ord+Copy> {
        /// For `atom`, a sequence of (atoms, terms) pairs to introduce to effect a join.
        ///
        /// The `atoms_to_terms` map is to a plannable atom, and the `terms_to_atoms` the inverse map of their `terms()` functions.
        /// Plan strategies should take care to consult each atom's `ground(terms)` method which indicates which terms the atom can produce;
        /// it may not be the case that an atom can ground any of their terms as a function of other ground terms.
        fn plan_atom(atom: A, atoms_to_terms: &BTreeMap<A, Box<dyn PlanAtom<T> + '_>>, terms_to_atoms: &BTreeMap<T, BTreeSet<A>>) -> Plan<A, T>;

        /// Plans updates for each atom in the rule.
        fn plan_rule(boxed_atoms: &BTreeMap<A, Box<dyn PlanAtom<T> + '_>>, head_terms: &[T]) -> BTreeMap<A, Plan<A, T>> {

            let mut terms_to_atoms: BTreeMap<T, BTreeSet<A>> = Default::default();
            for (atom, boxed) in boxed_atoms.iter() { for term in boxed.terms() { terms_to_atoms.entry(term).or_default().insert(*atom); } }

            let mut rule_plan = BTreeMap::default();
            for atom in boxed_atoms.keys().copied() {
                if boxed_atoms[&atom].terms() == boxed_atoms[&atom].ground(&Default::default()) {
                    let mut atom_plan = Self::plan_atom(atom, &boxed_atoms, &terms_to_atoms);

                    // Fuse plan stages with identical atoms.
                    for index in (1 .. atom_plan.len()).rev() {
                        if atom_plan[index].0 == atom_plan[index-1].0 {
                            let stage = atom_plan.remove(index);
                            atom_plan[index-1].1.extend(stage.1);
                        }
                    }

                    // Plan outgoing projections, based on demand and ending with `head_terms`.
                    for index in 1 .. atom_plan.len() {
                        let (this, rest) = atom_plan.split_at_mut(index);
                        let present = this.iter().flat_map(|(_, terms, _)| terms.iter()).copied().collect::<Vec<_>>();
                        let demanded = present.iter().copied().filter(|t| rest.iter().any(|(atoms,_,_)| atoms.iter().any(|a| terms_to_atoms[t].contains(a)) || head_terms.contains(t))).collect::<Vec<_>>();

                        // Set the target order by the terms in common with atoms of the next stage, in atom order, then uninvolved terms.
                        let order = &mut this[index-1].2;
                        order.clear();
                        for atom in rest[0].0.iter() {
                            for term in demanded.iter() {
                                if terms_to_atoms[term].contains(atom) && !order.contains(term) { order.push(*term); }
                            }
                        }
                        for term in demanded.iter() { if !order.contains(term) { order.push(*term); } }

                    }
                    atom_plan.last_mut().unwrap().2 = head_terms.to_vec();

                    rule_plan.insert(atom, atom_plan);
                }
            }
            rule_plan
        }
    }

    /// Plans updates for an atom by repeatedly introducing individual terms and all supported atoms.
    pub struct ByTerm;
    impl<A: Ord+Copy, T: Ord+Copy> Strategy<A, T> for ByTerm {
        fn plan_atom(atom: A, atoms_to_terms: &BTreeMap<A, Box<dyn PlanAtom<T> + '_>>, terms_to_atoms: &BTreeMap<T, BTreeSet<A>>) -> Plan<A, T> {

            assert!(atoms_to_terms[&atom].terms() == atoms_to_terms[&atom].ground(&Default::default()));

            let init_terms: BTreeSet<T> = atoms_to_terms[&atom].terms();
            let init_atoms: BTreeSet<A> = init_terms.iter().flat_map(|t| terms_to_atoms[t].iter()).filter(|a| atoms_to_terms[a].terms().iter().all(|t| init_terms.contains(t))).copied().collect();

            // One approach: grow terms through adjacent atoms.
            let mut terms: BTreeSet<T> = init_terms.clone();
            let mut plan: Plan<A, T> = vec![(init_atoms, init_terms, Vec::new())];
            while terms.len() < terms_to_atoms.len() {

                // Terms that can be ground through an atom from `terms`, but not yet in `terms`.
                let mut next_terms =
                terms.iter()
                     .flat_map(|term| terms_to_atoms[term].iter())
                     .flat_map(|atom| atoms_to_terms[atom].ground(&terms))
                     .filter(|term| !terms.contains(term))
                     .collect::<Vec<_>>();

                // Choose the term incident on the most atoms.
                next_terms.sort_by_key(|t| terms_to_atoms[t].len());
                let next_term = *next_terms.last().unwrap();
                let next_atoms = terms_to_atoms[&next_term].iter().filter(|a| atoms_to_terms[a].terms().iter().any(|t| terms.contains(t))).copied().collect();

                terms.insert(next_term);
                plan.push((next_atoms, [next_term].into_iter().collect(), Vec::new()));
            }
            plan
        }
    }

    /// Plans updates for an atom by repeatedly adding individual atoms and all of their terms.
    pub struct ByAtom;
    impl<A: Ord+Copy, T: Ord+Copy> Strategy<A, T> for ByAtom {
        fn plan_atom(atom: A, atoms_to_terms: &BTreeMap<A, Box<dyn PlanAtom<T> + '_>>, terms_to_atoms: &BTreeMap<T, BTreeSet<A>>) -> Plan<A, T> {

            assert!(atoms_to_terms[&atom].terms() == atoms_to_terms[&atom].ground(&Default::default()));

            // We start with `atom`, but also semijoin subsumed atoms.
            let init_atoms: BTreeSet<A> = [atom].into_iter().collect();
            let init_terms: BTreeSet<T> = atoms_to_terms[&atom].terms();

            // One approach: grow terms through adjacent atoms.
            let mut atoms: BTreeSet<A> = init_atoms.clone();
            let mut terms = init_terms.clone();
            let mut plan: Plan<A, T> = vec![(init_atoms, init_terms, Vec::new())];
            while atoms.len() < atoms_to_terms.len() {

                // Atoms are available if they can be fully enumerated from the bound terms.
                let mut next_atoms =
                atoms.iter()
                     .flat_map(|atom| atoms_to_terms[atom].terms())
                     .flat_map(|term| terms_to_atoms[&term].iter())
                     .filter(|atom| !atoms.contains(atom) && atoms_to_terms[atom].terms().difference(&atoms_to_terms[atom].ground(&terms)).all(|t| terms.contains(t)));

                // Choose the first available atom. This can be dramatically improved.
                let next_atom = next_atoms.next().unwrap_or_else(|| atoms_to_terms.keys().find(|a| !atoms.contains(a)).unwrap());
                let next_terms: BTreeSet<_> = atoms_to_terms[next_atom].terms().iter().filter(|t| terms_to_atoms[t].iter().all(|a| !atoms.contains(a))).copied().collect();
                terms.extend(next_terms.iter().copied());

                atoms.insert(*next_atom);
                plan.push(([*next_atom].into_iter().collect(), next_terms, Vec::new()));
            }
            plan
        }
    }
}

/// Traits and logic associated with executing rules.
pub mod exec {

    use std::collections::BTreeSet;
    use crate::types::Action;
    use crate::plan::{FactContainer, FactLSM};

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
    pub fn permute_delta<F: FactContainer, T: Ord + Copy>(
        delta: &mut FactLSM<F>,
        delta_terms: &mut Vec<T>,
        other_terms: impl Iterator<Item = T>,
    ) {
        let mut permutation: Vec<usize> = other_terms.flat_map(|t1| delta_terms.iter().position(|t2| &t1 == t2)).collect();
        for index in 0 .. delta_terms.len() { if !permutation.contains(&index) { permutation.push(index); }}

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
                permute_delta(delta_lsm, &mut active_clone, delta_terms[..active.len()].iter().copied());

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
                permute_delta(&mut delta_shard, &mut delta_shard_terms, target.iter().copied());
                delta_lsm.extend(&mut delta_shard);
            }
        }

        delta_terms.clear();
        delta_terms.extend_from_slice(target);

    }
}

use crate::facts::{Forest, Terms};


impl<T: Ord + Copy> plan::PlanAtom<T> for BTreeSet<T> {
    fn terms(&self) -> BTreeSet<T> { self.clone() }
    fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T> { self.difference(terms).cloned().collect() }
}

impl<'a, T: Ord + Copy> exec::ExecAtom<T> for (Vec<&'a Forest<Terms>>, &'a Vec<T>) {

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
        exec::permute_delta(delta_lsm, delta_terms, other_terms[..prefix].iter().copied());
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
            exec::permute_delta(delta_shard, delta_terms, other_terms[..prefix].iter().copied());
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
            exec::permute_delta(delta_shard, delta_terms, next_other_terms[..prefix].iter().copied());
            let mut delta = delta_shard.flatten().unwrap_or_default();
            let others = next_other_facts.iter().map(|o| o.borrow()).collect::<Vec<_>>();
            delta = delta.retain_inner(others.iter().map(|o| &o[..prefix]), true);
            delta_shard.push(delta);
        }
    }
}

/// Wrapper type for antijoins.
struct Anti<T>(T);

impl <T: Ord + Copy> plan::PlanAtom<T> for Anti<BTreeSet<T>> {
    fn terms(&self) -> BTreeSet<T> { self.0.clone() }
    fn ground(&self, _terms: &BTreeSet<T>) -> BTreeSet<T> { Default::default() }
}

impl<'a, T: Ord + Copy> exec::ExecAtom<T> for Anti<(Vec<&'a Forest<Terms>>, &'a Vec<T>)> {

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
        assert!(terms.is_empty());

        let (next_other_facts, next_other_terms) = &self.0;

        let prefix = next_other_terms.iter().take_while(|t| delta_terms.contains(t)).count();
        exec::permute_delta(delta_shard, delta_terms, next_other_terms[..prefix].iter().copied());
        let mut delta = delta_shard.flatten().unwrap_or_default();
        let others = next_other_facts.iter().map(|o| o.borrow()).collect::<Vec<_>>();
        delta = delta.retain_inner(others.iter().map(|o| &o[..prefix]), false);
        delta_shard.push(delta);
    }
}

/// Types and traits for relations implemented by computation rather than data.
pub mod logic {

    use std::collections::BTreeSet;

    use columnar::{Container, Index, Len, Push, Clear};

    use crate::types::{Atom, Term};
    use crate::facts::FactLSM;
    use crate::facts::{Forest, Lists, Terms};
    use crate::facts::trie::Layer;
    use crate::facts::trie::layers::advance_bounds;
    use crate::plan::{exec, plan};

    /// Looks for the atom's name in a known list, and returns an implementation if found.
    ///
    /// The implementation is a type that implements both `PlanAtom` and `ExecAtom`, and can be boxed as either.
    pub fn resolve<'a>(atom: &'a Atom) -> Option<LogicRel<&'a String>> {
        match atom.name.as_str() {
            ":range" => {
                let logic: Box<dyn BatchLogic> = Box::new(BatchedLogic { logic: Range } );
                let bound = atom.terms.iter().map(|t| match t { Term::Var(name) => Ok(name), Term::Lit(data) => Err(data.clone()) }).collect::<Vec<_>>();
                let terms = bound.iter().flatten().collect::<BTreeSet<_>>().into_iter().copied().collect::<Vec<_>>();
                Some(LogicRel { logic, bound, terms })
            },
            _ => None,
        }
    }


    /// A type that can behave as a relation in the context of join planning.
    pub trait Logic {
        /// The number of columns in the relation.
        fn arity(&self) -> usize;
        /// Non-input columns such that for any fixed setting of the input columns, the number of values in the output column is finite.
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize>;
        /// For a subset of arguments, an upper bound on the number of distinct set of values for arguments in `output`.
        ///
        /// When `output` is empty, it is important to emit either `Some(0)` or `Some(1)` to indicate respectively absence or presence.
        fn count(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], output: &BTreeSet<usize>) -> Option<usize>;
        /// For a subset of arguments, populate distinct values for arguments in `output`.
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

    /// Relation containing triples lower <= value < upper, all of the same length.
    pub struct LogicRel<T> {
        pub logic: Box<dyn super::logic::BatchLogic>,
        /// In order: `[lower, value, upper]`.
        ///
        /// Each are either a term name, or a literal.
        pub bound: Vec<Result<T, Vec<u8>>>,
        /// Terms of `bound` in some order, used by exec to lay out records "favorably".
        pub terms: Vec<T>,
    }

    impl <T: Ord + Copy> plan::PlanAtom<T> for LogicRel<T> {
        fn terms(&self) -> BTreeSet<T> { self.terms.iter().cloned().collect() }
        fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T> {
            // If `lower` and `upper` are given, we can generate `value`.
            let lower = match &self.bound[0] { Ok(term) => terms.contains(term), Err(_) => true };
            let upper = match &self.bound[2] { Ok(term) => terms.contains(term), Err(_) => true };
            let mut result = BTreeSet::default();
            if lower && upper { if let Ok(value) = &self.bound[1] { result.insert(value.clone()); } }
            result
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

            if added.is_empty() {
                // Semijoin case.
                let added = added.iter().map(|term| self.bound.iter().position(|t| t.as_ref() == Ok(term)).unwrap()).collect::<BTreeSet<_>>();
                let keep = self.logic.count(&args, &added).into_iter().map(|x| x != Some(0)).collect::<std::collections::VecDeque<_>>();
                if let Some(col) = max { delta = delta.retain_core(col, keep); }
                else if !keep[0] { delta = Default::default(); }
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

    /// The relation R(x,y,z) : x <= y < z, for terms all of the same length (up to eight bytes).
    pub struct Range;
    impl Logic for Range {
        fn arity(&self) -> usize { 3 }
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> { if args.contains(&0) && args.contains(&2) && !args.contains(&1) { [1].into_iter().collect() } else { Default::default() } }
        fn count(&self, args: &[Option<<Terms as columnar::Container>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
            let result = match (&args[0], &args[1], &args[2]) {
                (Some(l), None, Some(u)) => {
                    let mut count = 0;
                    if l.len() == u.len() {
                        let l = as_u64(l.as_slice())?;
                        let u = as_u64(u.as_slice())?;
                        if l < u { count = u - l; }
                    }
                    Some(count as usize)
                },
                (Some(l), Some(v), Some(u)) => {
                    let mut count = 0;
                    if l.len() == v.len() && l.len() == u.len() {
                        let l = as_u64(l.as_slice())?;
                        let v = as_u64(v.as_slice())?;
                        let u = as_u64(u.as_slice())?;
                        if l <= v && v < u { count = 1; }
                    }
                    Some(count as usize)
                },
                _ => None,
            };
            result
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

    fn as_u64(bytes: &[u8]) -> Option<u64> {
        if bytes.len() > 8 { None }
        else {
            let mut slice = [0u8; 8];
            slice[8-bytes.len() ..].copy_from_slice(bytes);
            Some(u64::from_be_bytes(slice))
        }
    }

    pub struct BatchedLogic<L: Logic> { pub logic: L }

    impl<L: Logic> BatchLogic for BatchedLogic<L> {
        fn arity(&self) -> usize { self.logic.arity() }
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> { self.logic.bound(args) }
        fn count(&self, args: &[Option<(<Terms as columnar::Container>::Borrowed<'_>, Vec<usize>)>], output: &BTreeSet<usize>) -> Vec<Option<usize>> {

            assert!(output.len() < 2);

            // Panic if no arguments are bound; figure out those functions later (how many outputs to produce? one?)
            // The following is .. neither clear nor performant. It should be at least one of those two things.
            let length = args.iter().flatten().next().unwrap().1.iter().sum();
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

            // Panic if no arguments are bound; figure out those functions later (how many outputs to produce? one?)
            // The following is .. neither clear nor performant. It should be at least one of those two things.
            let length = args.iter().flatten().next().unwrap().1.iter().sum();
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
}
