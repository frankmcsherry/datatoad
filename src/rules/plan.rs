//! Traits and logic associated with planning rules.


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
        if let Some(logic) = crate::rules::logic::resolve(atom) { (index, Box::new(logic) as Box::<dyn PlanAtom<&'a String> + 'a>) }
        else if !atom.anti { (index, Box::new(terms) as Box::<dyn PlanAtom<&'a String> + 'a>) }
        else { (index, Box::new(crate::rules::antijoin::Anti(terms)) as Box::<dyn PlanAtom<&'a String> + 'a>) }
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
            // If we can't find a term, we'll need to pick any groundable term (e.g. a cross join with a data-backed relation).
            let next_term = next_terms.last().copied().unwrap_or_else(|| atoms_to_terms.values().flat_map(|a| a.ground(&terms)).filter(|t| !terms.contains(t)).next().unwrap());
            let next_atoms = terms_to_atoms[&next_term].iter().filter(|a| atoms_to_terms[a].terms().contains(&next_term)).copied().collect();

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
