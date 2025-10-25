use crate::types::{Rule, Action, Atom, Term};
use crate::facts::{FactContainer, FactLSM, FactSet, Relations};

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
                Term::Lit(data) => { Err(data.to_string()) },
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

    let (plans, loads) = plan::plan_rule::<plan::ByAtom>(head, body);

    let plan_atoms = if stable { 1 } else { body.len() };

    for (plan_atom, atom) in body[..plan_atoms].iter().enumerate() {

        let plan = &plans[&plan_atom];

        // Stage 0: Load the recently added facts.
        let (action, terms) = &loads[&plan_atom][&plan_atom];
        facts.ensure_action(body[plan_atom].name.as_str(), action);

        let mut delta_terms = terms.clone();
        let mut delta_lsm = FactLSM::default();
        if stable {
            let facts = &facts.get(atom.name.as_str()).unwrap();
            for layer in facts.stable.contents().chain([&facts.recent]) {
                delta_lsm.extend(&mut layer.act_on(action));
            }
        }
        else {
            let facts = &facts.get(atom.name.as_str()).unwrap();
            delta_lsm.extend(&mut facts.recent.act_on(action));
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
            let load_terms = load_terms.iter().take_while(|t| delta_terms.contains(t)).copied().collect::<Vec<_>>().into_iter();
            permute_delta(&mut delta_lsm, &mut delta_terms, load_terms);
            let delta = delta_lsm.flatten().unwrap_or_default();
            delta_lsm.push(delta.semijoin(other.stable.contents().chain(to_chain)));
        }
        // We may need to produce the result in a different order.
        permute_delta(&mut delta_lsm, &mut delta_terms, init_order.iter().copied());

        // Stage 2: Each other plan stage.
        for (atoms, terms, order) in plan.iter().skip(1) {

            // A single atom stage can just be a join.
            if atoms.len() == 1 {
                let load_atom = atoms.first().unwrap();
                let (load_action, load_terms) = &loads[&plan_atom][load_atom];
                let other = &facts.get_action(body[*load_atom].name.as_str(), load_action).unwrap();
                let other_terms = load_terms.iter().take_while(|t| delta_terms.contains(t) || terms.contains(*t)).copied().collect::<Vec<_>>().into_iter();

                join_delta(&mut delta_lsm, &mut delta_terms, other, other_terms, load_atom > &plan_atom, order);
            }
            // Multi-atom stages call for different logic.
            else {

                // // We may have terms that are not needed for the term extensions,
                // // in which case we should know, and perhaps project them away.
                // for term in delta_terms.iter().filter(|t| atoms.iter().all(|a| loads[&(plan_atom, *a)].1.contains(t))) {
                //     println!("Non-anchor term: {:?} (could project away for the moment)", term);
                // }

                // For each atom, we'll need to permute `delta` to start with their terms.
                // Then we'll want to join, and capture the number of extensions, somehow.
                // Then we'll need to update any recorded numbers, recording smaller counts
                // and indexes where appropriate.
                // We could, naively, just start with a new column that is the count of extensions,
                // and just join using it, and then apply an action to the last two layers.
                // It's more of a semijoin, and using the general join logic would be more
                // expensive than we really need.

                // Our plan is to identify an extending atom for each delta fact,
                // then propose extensions for each fact from their identified atom,
                // then semijoin with other atoms (perhaps union and semijoin all).

                // Informally, we'll identify a set of columns as the "active" columns,
                // which contain all pre-active terms in the listed atoms. We'll then
                // develop a list of `(count, index)` for each fact among these columns.
                // Each will likely require appending the list as a layer, then permuting.
                // Permuted, we are able to semijoin/align and read out the counts for
                // each other layer, and then update the list to track the index with
                // the smallest count.
                //
                // Having done this, we'd then like to perform multiple restrictions
                // to the facts by their identified index, so that they can join with
                // the atoms themselves to propose extensions.
                //
                // Finally, we could/should semijoin with the atoms, to provide the
                // full information about the terms the atoms can provide. We can defer
                // this, but we do need to perform the operation at some point (e.g.
                // later, if we revisit the atom)

                unimplemented!("Multi-atom join stages not yet implemented");
            }
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


pub mod plan {

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
    pub type Load<T> = (Action<String>, Vec<T>);
    pub type Loads<A, T> = BTreeMap<A, BTreeMap<A, Load<T>>>;

    pub fn plan_rule<'a, S: Strategy<usize, &'a String>>(head: &'a [Atom], body: &'a [Atom]) -> (Plans<usize, &'a String>, Loads<usize, &'a String>) {

        // We'll pick a target term order for the first head; other heads may require transforms.
        // If we have multiple heads and one has no literals or repetitions, that would be best.
        let head_terms = head_order(head);

        // Distinct (atom, term) pairs of integers.
        let atoms_terms =
        body.iter()
            .enumerate()
            .flat_map(|(index, atom)| atom.terms.iter().map(move |term| (index, term)))
            .filter_map(|(index, term)| term.as_var().map(|t| (index, t)))
            .collect::<BTreeSet<_>>();

        // Maps from atoms to terms and terms to atoms.
        let mut atoms_to_terms: BTreeMap<_, BTreeSet<_>> = BTreeMap::default();
        let mut terms_to_atoms: BTreeMap<_, BTreeSet<_>> = BTreeMap::default();
        for (atom, term) in atoms_terms.iter() {
            atoms_to_terms.entry(*atom).or_default().insert(*term);
            terms_to_atoms.entry(*term).or_default().insert(*atom);
        }

        // We'll want to pre-plan the term orders for each atom update rule, so that we can
        // pre-ensure that the necessary input shapes exist, with each atom in term order.
        let plans = S::plan_rule(&atoms_to_terms, &terms_to_atoms, &head_terms);

        // Actions for each atom that would produce the output in `terms` order.
        // Their output columns should now be ordered as `atoms_to_terms[atom]`.
        // We use these as reference points, and don't intend to load with them.
        let base_actions = body.iter().enumerate().map(|(index, atom)| {
            let mut action = Action::from_body(atom);
            action.projection.sort_by_key(|p| atom.terms[*p.as_ref().unwrap()].as_var().unwrap());
            (index, action)
        }).collect::<BTreeMap<_,_>>();

        let mut load_actions = load_actions(&plans, &atoms_to_terms, &base_actions);

        // Insert loading actions for plan atoms themselves.
        for (plan_atom, atom) in body.iter().enumerate() {
            let action = Action::from_body(atom);
            let terms = action.projection.iter().flatten().map(|c| atom.terms[*c].as_var().unwrap()).collect::<Vec<_>>();
            load_actions.get_mut(&plan_atom).map(|l| l.insert(plan_atom, (action, terms)));
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
        base_actions: &BTreeMap<A, Action<String>>,
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
        /// For `atom`, a sequence of (atoms, terms) to introduce to effect a join.
        fn plan_atom(atom: A, atoms_to_terms: &BTreeMap<A, BTreeSet<T>>, terms_to_atoms: &BTreeMap<T, BTreeSet<A>>) -> Plan<A, T>;

        /// Plans updates for each atom in the rule.
        fn plan_rule(atoms_to_terms: &BTreeMap<A, BTreeSet<T>>, terms_to_atoms: &BTreeMap<T, BTreeSet<A>>, head_terms: &[T]) -> BTreeMap<A, Plan<A, T>> {
            let mut rule_plan = BTreeMap::default();
            for atom in atoms_to_terms.keys().copied() {
                let mut atom_plan = Self::plan_atom(atom, atoms_to_terms, terms_to_atoms);

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
                    let present = this.iter().flat_map(|(atoms, _, _)| atoms.iter()).flat_map(|a| atoms_to_terms[a].iter()).collect::<BTreeSet<_>>();
                    let demanded = rest.iter().flat_map(|(atoms, _, _)| atoms.iter()).flat_map(|a| atoms_to_terms[a].iter()).chain(head_terms.iter()).filter(|t| present.contains(t)).collect::<BTreeSet<_>>();

                    let order = &mut this[index-1].2;
                    order.clear();
                    order.extend(demanded.iter().filter(|t| rest[0].0.iter().any(|a| atoms_to_terms[a].contains(t))).copied());
                    order.extend(demanded.iter().filter(|t| !rest[0].0.iter().any(|a| atoms_to_terms[a].contains(t))).copied());
                }
                atom_plan.last_mut().unwrap().2 = head_terms.to_vec();

                rule_plan.insert(atom, atom_plan);
            }
            rule_plan
        }
    }

    /// Plans updates for an atom by repeatedly introducing individual terms and all supported atoms.
    pub struct ByTerm;
    impl<A: Ord+Copy, T: Ord+Copy> Strategy<A, T> for ByTerm {
        fn plan_atom(atom: A, atoms_to_terms: &BTreeMap<A, BTreeSet<T>>, terms_to_atoms: &BTreeMap<T, BTreeSet<A>>) -> Plan<A, T> {

            let init_terms: BTreeSet<T> = atoms_to_terms[&atom].clone();
            let init_atoms: BTreeSet<A> = init_terms.iter().flat_map(|t| terms_to_atoms[t].iter()).filter(|a| atoms_to_terms[a].iter().all(|t| init_terms.contains(t))).copied().collect();

            // One approach: grow terms through adjacent atoms.
            let mut terms: BTreeSet<T> = init_terms.clone();
            let mut plan: Plan<A, T> = vec![(init_atoms, init_terms, Vec::new())];
            while terms.len() < terms_to_atoms.len() {

                // Terms that can be reached through an atom from `output`, but not yet in `output`.
                let mut next_terms =
                terms.iter()
                     .flat_map(|term| terms_to_atoms[term].iter())
                     .flat_map(|atom| atoms_to_terms[atom].iter())
                     .filter(|term| !terms.contains(term));

                // Choose the first available term. This can be dramatically improved.
                let next_term = next_terms.next().unwrap_or_else(|| terms_to_atoms.keys().find(|t| !terms.contains(t)).unwrap());
                let next_atoms = terms_to_atoms[next_term].iter().filter(|a| atoms_to_terms[a].iter().any(|t| terms.contains(t))).copied().collect();

                terms.insert(*next_term);
                plan.push((next_atoms, [*next_term].into_iter().collect(), Vec::new()));
            }
            plan
        }
    }

    /// Plans updates for an atom by repeatedly adding individual atoms and all of their terms.
    pub struct ByAtom;
    impl<A: Ord+Copy, T: Ord+Copy> Strategy<A, T> for ByAtom {
        fn plan_atom(atom: A, atoms_to_terms: &BTreeMap<A, BTreeSet<T>>, terms_to_atoms: &BTreeMap<T, BTreeSet<A>>) -> Plan<A, T> {

            // We start with `atom`, but also semijoin subsumed atoms.
            let init_atoms: BTreeSet<A> = [atom].into_iter().collect();
            let init_terms: BTreeSet<T> = atoms_to_terms[&atom].clone();

            // One approach: grow terms through adjacent atoms.
            let mut atoms: BTreeSet<A> = init_atoms.clone();
            let mut plan: Plan<A, T> = vec![(init_atoms, init_terms, Vec::new())];
            while atoms.len() < atoms_to_terms.len() {

                // Atoms that can be reached through an atom's terms.
                let mut next_atoms =
                atoms.iter()
                     .flat_map(|atom| atoms_to_terms[atom].iter())
                     .flat_map(|term| terms_to_atoms[term].iter())
                     .filter(|atom| !atoms.contains(atom));

                // Choose the first available atom. This can be dramatically improved.
                let next_atom = next_atoms.next().unwrap_or_else(|| atoms_to_terms.keys().find(|a| !atoms.contains(a)).unwrap());
                let next_terms = atoms_to_terms[next_atom].iter().filter(|t| terms_to_atoms[t].iter().all(|a| !atoms.contains(a))).copied().collect();

                atoms.insert(*next_atom);
                plan.push(([*next_atom].into_iter().collect(), next_terms, Vec::new()));
            }
            plan
        }
    }
}

/// Permute `delta` from its current order, `delta_terms` to one that matches `other_terms` on common terms.
///
/// The method updates both `delta` and `delta_terms`.
/// The method assumes that some prefix of `other_terms` is present in `delta_terms`, and no further terms
/// from `other_terms` around found there. The caller must restrict `other_terms` to make this the case.
fn permute_delta<F: FactContainer, T: Ord + Copy>(
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

/// Join `delta` with `other`, by permuting `delta` to match columns in `other`.
fn join_delta<F: FactContainer, T: Ord + Copy + std::fmt::Debug>(
    delta: &mut FactLSM<F>,
    delta_terms: &mut Vec<T>,
    other: &FactSet<F>,
    other_terms: impl Iterator<Item = T>,
    with_recent: bool,
    yield_order: &[T],
) {
    let other_terms = other_terms.collect::<Vec<_>>();
    permute_delta(delta, delta_terms, other_terms.iter().copied());

    let join_arity = delta_terms.iter().zip(other_terms.iter()).take_while(|(d, o)| d == o).count();

    let to_chain = if with_recent { Some(&other.recent) } else { None };

    let projection = yield_order.iter().map(|t| {
        let this_term = delta_terms.iter().position(|t2| t == t2);
        let that_term = other_terms.iter().position(|t2| t == t2).map(|p| p + delta_terms.len());
        this_term.or(that_term).unwrap()
    }).collect::<Vec<_>>();

    let flattened = delta.flatten().unwrap_or_default();
    delta.extend(&mut flattened.join_many(other.stable.contents().chain(to_chain), join_arity, &[&projection]).pop().unwrap());
    *delta_terms = yield_order.to_vec();
}
