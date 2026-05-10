//! Rule planning: turn a rule body into a sequenced execution plan.
//!
//! # What this produces
//!
//! A [`Plan`] is a sequence of stages. Each stage names a set of atoms to apply, a set
//! of new variable terms that stage *introduces*, and a projection target — the column
//! order to leave the salad in before moving on. The terms across stages partition the
//! body's variables: each variable is introduced exactly once. The final stage's target
//! matches the rule head's variable order.
//!
//! Alongside each plan we compute [`Loads`]: per-atom `(Action, Vec<Term>)` instructions
//! describing how to materialize that atom's facts in a column order compatible with
//! the plan's stage progression.
//!
//! # Two entry points
//!
//! - [`plan_rule`] — semi-naive case. Given a body and a list of candidate *seed*
//!   atoms (one per delta), produces one plan per seed. The seed atom's terms are
//!   pre-bound when the stages start; the body-without-seed is sequenced.
//! - [`plan_rule_seeded`] — view-atom case. The caller (e.g. a `View`) already holds
//!   bindings in a salad; it passes those terms as the seed and the full body is
//!   sequenced.
//!
//! Both wrappers call the same primitive — [`plan_body`] — then derive [`Loads`] via
//! [`body_load`].
//!
//! # The strategy: [`plan_body`]
//!
//! Term-at-a-time, most-constrained-first. Start with `init_terms` (seed terms that
//! some body atom mentions or that the head needs) and `init_atoms` (body atoms whose
//! terms are already covered by the seed). Then repeatedly pick a not-yet-bound term
//! reachable by some atom, introduce it as a new stage with the atoms that ground it.
//! Adjacent single-atom stages with the same atom set get fused. Projection targets are
//! computed by demand from later stages plus the head.
//!
//! # Stage 0
//!
//! Stage 0 is shaped differently from the rest. Its `terms` field documents the
//! seed-relevant pre-bound bindings (the columns the executor expects to find in the
//! salad on entry). Its `atoms` field holds `init_atoms` — body atoms whose terms are
//! all covered by the seed and which can semijoin without introducing anything new.
//! Stages 1+ follow the usual "this stage introduces these columns" semantics.
//!
//! The executor (`run_wco_stages`) handles the asymmetry: for stage 0 it semijoins
//! against `init_atoms` over an empty introduce-set; for stages 1+ it passes `terms`
//! through to `wco_join` as the new columns to bind. Keeping stage 0's `terms` as
//! the starting bindings means the Plan is self-describing — `body_load` and any
//! future consumer can read the expected starting state straight off it.
//!
//! # Atom kinds
//!
//! [`build_atoms_map`] dispatches each body atom to the appropriate [`PlanAtom`]
//! implementation: data relations, antijoins (`anti::Anti`), logic atoms
//! (`logic::resolve`), or views (`view::ViewPlan`). The planner only sees the
//! `terms()` / `ground()` interface — it doesn't care about the kind.


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
use crate::types::{Atom, Action, Term};

/// Substitution map: body var name → its replacement under composition.
///
/// Each entry rewrites a body var to either another var (`Term::Var` — rename, often
/// to a use-site var name to unify head and use-site spaces) or a literal
/// (`Term::Lit` — constant pushdown, baked into atom load actions as `lit_filter`).
/// Values are `&'a Term` borrowed from the use-site atom; refs have `'a` lifetime so
/// `PlanAtom` term sets and load actions can use the inner `&'a String`/`&'a Vec<u8>`
/// directly without allocation.
///
/// Used by the view planner to fold use-site constraints into the body's atom views
/// without allocating new `Atom` structs. `build_atoms_map` and `base_actions_for`
/// consult this when computing per-atom term sets and load actions.
pub type Subst<'a> = BTreeMap<&'a String, &'a Term>;

/// A plan is a sequence of stages, each a tuple of (atoms, terms, output order).
///
/// Each stage indicates terms that are added, and the atoms that participate in the
/// introduction of those terms. Each atom name restricts the solution space by their
/// projection onto all terms added through this stage. Each term is added only once.
///
/// The output term order indicates the terms that survive the stage, and a preference
/// for their order that may be beneficial for the next stage. Terms not present in the
/// output order should be pruned.
///
/// The first stage is special, in that its terms are specified exogenously by a "seed"
/// relation that starts the sequence of joins. The atoms of the first stage intersect
/// these terms, but they may not fully span it, and it should not be distressing that
/// the plan cannot independently substantiate those terms.
pub type Plan<A, T> = Vec<(BTreeSet<A>, BTreeSet<T>, Vec<T>)>;
pub type Plans<A, T> = BTreeMap<A, Plan<A, T>>;
pub type Load<T> = (Action<Vec<u8>>, Vec<T>);
pub type Loads<A, T> = BTreeMap<A, BTreeMap<A, Load<T>>>;

/// Plans a rule, producing a plan and load instructions per seed atom.
///
/// Each index in `seed_atoms` names a body atom that needs a plan to respond to new facts.
/// For each seed, the atom's terms feed [`plan_body`] with all other atoms, with an output
/// term order targeting the terms of `head`.
///
/// Seeds that cannot ground their own terms (e.g. logic atoms) are silently skipped.
pub fn plan_rule<'a>(
    head: &'a [Atom],
    body: &'a [Atom],
    seed_atoms: &[usize],
    decls: &'a std::collections::BTreeMap<String, crate::types::RelationDecl>,
) -> (Plans<usize, &'a String>, Loads<usize, &'a String>) {

    let empty_subst: Subst<'a> = BTreeMap::new();
    let head_terms = head_order(head, &empty_subst);
    let base_actions = base_actions_for(body, &empty_subst);

    let mut plans: Plans<usize, &'a String> = BTreeMap::default();
    let mut loads: Loads<usize, &'a String> = BTreeMap::default();

    // One atoms map; each iteration takes a seed_idx out as the seed and puts it back
    // at the end. Same round-robin shape as semi-naive: the body's atoms are stable;
    // which one supplies the novelty rotates.
    let mut atoms = build_atoms_map(body, &empty_subst, decls);
    for &seed_idx in seed_atoms {
        if let Some(seed_atom) = atoms.remove(&seed_idx) {
            if seed_atom.terms() == seed_atom.ground(&Default::default()) {
                let seed_terms = seed_atom.terms();
                // Body-positional, possibly with repeats — preserves the user-written
                // column order so the planner can prefer stage-0 atoms that align with
                // the seed's column prefix (avoiding a re-permute on first semijoin).
                let seed: Vec<&'a String> = body[seed_idx].terms.iter().filter_map(|t| t.as_var()).collect();
                let plan = plan_body(&seed, &atoms, &head_terms);
                let mut load = body_load(&plan, &atoms, &base_actions);
                load.insert(seed_idx, seed_load(&plan, &atoms, &seed_terms, &base_actions[&seed_idx]));
                plans.insert(seed_idx, plan);
                loads.insert(seed_idx, load);
            }
            atoms.insert(seed_idx, seed_atom);
        }
    }

    (plans, loads)
}

/// Determines the seed's own load action from an existing plan.
///
/// This is informed by `plan`, which reveals atoms in the first stages that we
/// may try to align the terms of `seed` to match.
/// It is unclear if this is worth the cost of a new form for the seed.
fn seed_load<'a>(
    plan: &Plan<usize, &'a String>,
    body: &BTreeMap<usize, Box<dyn PlanAtom<&'a String> + 'a>>,
    seed_terms: &BTreeSet<&'a String>,
    base_action: &Action<Vec<u8>>,
) -> Load<&'a String> {
    let mut order = Vec::new();
    if let Some((stage_atoms, _, _)) = plan.iter().find(|(a, _, _)| !a.is_empty()) {
        for atom in stage_atoms.iter() {
            for term in body[atom].terms().intersection(seed_terms) {
                if !order.contains(term) { order.push(*term); }
            }
        }
    }
    for term in seed_terms.iter() { if !order.contains(term) { order.push(*term); } }

    let mut action = base_action.clone();
    action.projection = order.iter()
        .flat_map(|t1| seed_terms.iter().position(|t2| t1 == t2))
        .map(|p| base_action.projection[p].clone())
        .collect();
    (action, order)
}

/// Load actions for each atom in `body`.
///
/// For each body atom, loads the atom's terms in the order the plan binds them.
/// This order aims to minimize the number of distinct term orders to maintain.
fn body_load<'a, A: Ord + Copy, T: Ord + Clone>(
    plan: &Plan<A, T>,
    body: &BTreeMap<A, Box<dyn PlanAtom<T> + 'a>>,
    base_actions: &BTreeMap<A, Action<Vec<u8>>>,
) -> BTreeMap<A, Load<T>> {

    // Term introduction order: walk stages, take each stage's new terms.
    let mut all_terms: BTreeSet<T> = BTreeSet::default();
    let mut in_order: Vec<T> = Vec::default();
    for (_atoms, terms, _out_order) in plan.iter() {
        in_order.extend(terms.difference(&all_terms).cloned());
        all_terms.extend(terms.iter().cloned());
    }

    body.iter().map(|(load_atom, boxed)| {
        let atom_terms = boxed.terms();
        let load_terms: Vec<T> = in_order.iter().filter(|t| atom_terms.contains(t)).cloned().collect();
        let mut action = base_actions[load_atom].clone();
        action.projection = in_order.iter()
            .flat_map(|t1| atom_terms.iter().position(|t2| t1 == t2))
            .map(|p| base_actions[load_atom].projection[p].clone())
            .collect();
        (*load_atom, (action, load_terms))
    }).collect()
}

/// Produces a term order for head atoms.
///
/// The order is of distinct terms in order of presentation, with `subst` applied
/// (Var→Var renames are reflected; Var→Lit substitutions drop out, as do raw lits).
/// Pass empty `Subst` for the non-view path.
fn head_order<'a>(head: &'a [Atom], subst: &Subst<'a>) -> Vec<&'a String> {
    let mut seen: BTreeSet<&'a String> = BTreeSet::default();
    head.iter()
        .flat_map(|a| a.terms.iter())
        .filter_map(|t| match t {
            Term::Var(name) => match subst.get(name) {
                Some(Term::Var(new_name)) => Some(new_name),
                Some(Term::Lit(_)) => None,
                None => Some(name),
            },
            Term::Lit(_) => None,
        })
        .filter(|t| seen.insert(t))
        .collect()
}

/// Plans a single-head rule body around a caller-provided seed of pre-bound terms.
///
/// No body atom is treated as the seed source — `seed` is just terms. Used when the
/// caller (e.g. a sum atom disjunct) already holds the seed bindings in an input
/// salad and wants stages that introduce the rest of the body's variables. The single
/// head atom matches the disjunct shape — multi-head rules don't arise on this path.
pub fn plan_rule_seeded<'a>(
    body: &'a [Atom],
    seed: &[&'a String],
    need: &[&'a String],
    subst: &Subst<'a>,
    decls: &'a std::collections::BTreeMap<String, crate::types::RelationDecl>,
) -> (Plan<usize, &'a String>, BTreeMap<usize, Load<&'a String>>) {
    let atoms = build_atoms_map(body, subst, decls);
    let base_actions = base_actions_for(body, subst);
    let plan = plan_body(seed, &atoms, need);
    let loads = body_load(&plan, &atoms, &base_actions);
    (plan, loads)
}

/// Plan a body around a seed of pre-bound terms by repeatedly introducing one
/// most-constrained term (and any atoms it newly enables) until every body term is bound.
///
/// The seed is *not* one of the body atoms — it represents bindings provided by the
/// caller (the seed atom's terms in the `plan_rule` case, or a salad's terms in the
/// `plan_rule_seeded` case). `body` is everything the planner sequences into stages.
/// `need` is the set of terms the result must carry through to its last stage
/// (typically the rule head's variable terms).
///
/// `seed` is a slice (not a set) because the caller's column order carries information
/// the planner should use: stage-0 atoms whose terms align with a prefix of `seed` can
/// semijoin without re-permuting the salad. The planner doesn't consult it today, but
/// the order is meaningful — callers should pass terms in the order their salad's
/// columns are arranged.
pub fn plan_body<A: Ord+Copy, T: Ord+Clone+std::fmt::Debug>(
    seed: &[T],
    body: &BTreeMap<A, Box<dyn PlanAtom<T> + '_>>,
    need: &[T],
) -> Plan<A, T> {

    let mut terms_to_atoms: BTreeMap<T, BTreeSet<A>> = Default::default();
    for (atom, boxed) in body.iter() {
        for term in boxed.terms() { terms_to_atoms.entry(term).or_default().insert(*atom); }
    }

    // Stage 0 carries seed terms that some body atom mentions or that the caller
    // needs in the output. Seed terms with no constraint and no demand are pruned —
    // there's nothing for the planner to do with them.
    let init_terms: BTreeSet<T> =
    seed.iter()
        .cloned()
        .filter(|t| terms_to_atoms.contains_key(t) || need.contains(t))
        .collect();
    // Body atoms whose terms are all already in `init_terms` should be present in stage 0.
    let init_atoms: BTreeSet<A> =
    body.iter()
        .filter(|(_, boxed)| boxed.terms().iter().all(|t| init_terms.contains(t)))
        .map(|(a, _)| *a)
        .collect();

    let mut terms: BTreeSet<T> = init_terms.clone();
    let mut plan: Plan<A, T> = vec![(init_atoms, init_terms, Vec::new())];
    // Loop while there are body terms not yet bound. (We can't compare cardinalities:
    // `terms` may include seed terms that aren't in `terms_to_atoms`, so a count
    // match doesn't mean coverage.)
    while terms_to_atoms.keys().any(|t| !terms.contains(t)) {

        // Terms that can be grounded by some atom from the bound `terms`, not yet bound.
        let mut next_terms = terms.iter()
            .flat_map(|term| terms_to_atoms.get(term).into_iter().flatten())
            .flat_map(|atom| body[atom].ground(&terms))
            .filter(|term| !terms.contains(term) && terms_to_atoms.contains_key(term))
            .collect::<Vec<_>>();

        // Pick the term incident on the most atoms (most-constrained-first).
        next_terms.sort_by_key(|t| terms_to_atoms[t].len());
        // Fallback: any groundable term, allowing cross joins with data-backed atoms.
        let next_term = next_terms.last().cloned().or_else(|| body.values()
            .flat_map(|a| a.ground(&terms))
            .filter(|t| !terms.contains(t) && terms_to_atoms.contains_key(t))
            .next());

        if let Some(next_term) = next_term {
            let mut next_atoms: BTreeSet<A> = terms_to_atoms[&next_term].iter()
                .filter(|a| body[a].terms().contains(&next_term) && terms.iter().any(|t| body[a].terms().contains(t)))
                .cloned()
                .collect();
            next_atoms.extend(body.iter()
                .filter(|(_a, boxed)| boxed.ground(&terms).contains(&next_term))
                .map(|(a, _)| *a));
            if next_atoms.is_empty() {
                next_atoms = terms_to_atoms[&next_term].iter()
                    .filter(|a| body[a].terms().contains(&next_term))
                    .cloned()
                    .collect();
            }
            terms.insert(next_term.clone());
            plan.push((next_atoms, [next_term].into_iter().collect(), Vec::new()));
        }
        else {
            panic!("Failed to find term to extend {:?} to {:?}", terms, terms_to_atoms.keys());
        }
    }

    // Fuse adjacent stages with the same single-atom set: the same atom introducing
    // multiple consecutive variables is one stage, not several.
    for index in (1 .. plan.len()).rev() {
        if plan[index].0 == plan[index-1].0 && plan[index].0.len() == 1 {
            let stage = plan.remove(index);
            plan[index-1].1.extend(stage.1);
        }
    }

    // Set each stage's projection target by demand from later stages plus `need`.
    for index in 1 .. plan.len() {
        let (this, rest) = plan.split_at_mut(index);
        let present: Vec<T> = this.iter().flat_map(|(_, terms, _)| terms.iter()).cloned().collect();
        let demanded: Vec<T> = present.iter().cloned().filter(|t| {
            rest.iter().any(|(atoms, _, _)| atoms.iter().any(|a| {
                terms_to_atoms.get(t).map_or(false, |set| set.contains(a))
            })) || need.contains(t)
        }).collect();

        let order = &mut this[index-1].2;
        order.clear();
        for atom in rest[0].0.iter() {
            for term in demanded.iter() {
                if terms_to_atoms.get(term).map_or(false, |set| set.contains(atom)) && !order.contains(term) {
                    order.push(term.clone());
                }
            }
        }
        for term in demanded.iter() { if !order.contains(term) { order.push(term.clone()); } }
    }
    if let Some(last) = plan.last_mut() { last.2 = need.to_vec(); }

    // Stage 0's `terms` documents the seed-relevant starting bindings; stages 1+ list
    // the columns each stage *introduces*. `run_wco_stages` knows to treat stage 0
    // specially (semijoin against `init_atoms`, don't try to re-introduce columns).
    plan
}

/// Wraps each body atom in the appropriate `PlanAtom` implementation, keyed by body index.
///
/// Dispatches on atom kind: logic atoms (`logic::resolve`), views
/// (`view::ViewPlan`), antijoins (`anti::Anti`), or plain data relations (a bare
/// `BTreeSet` of variable terms).
///
/// `subst` lets the caller fold composition-derived constraints into the per-atom view
/// without rewriting the atom: a body var mapped to `Term::Var(new_name)` is
/// renamed; a body var mapped to `Term::Lit(_)` drops out of the var set (it's
/// a known constant — the lit_filter is added by `base_actions_for`). Pass an empty
/// `Subst` for the non-view planning path. Logic atoms participate in subst via
/// `logic::resolve_with_subst`, so renamed/pushed vars also flow into their `bound`
/// and `terms`.
fn build_atoms_map<'a>(
    body: &'a [Atom],
    subst: &Subst<'a>,
    decls: &'a std::collections::BTreeMap<String, crate::types::RelationDecl>,
) -> BTreeMap<usize, Box<dyn PlanAtom<&'a String> + 'a>> {
    body.iter().enumerate().map(|(index, atom)| {
        let terms: BTreeSet<&'a String> = atom.terms.iter().filter_map(|t| match t {
            Term::Var(name) => match subst.get(name) {
                Some(Term::Var(new_name)) => Some(new_name),
                Some(Term::Lit(_)) => None,
                None => Some(name),
            },
            Term::Lit(_) => None,
        }).collect();
        let boxed_atom: Box<dyn PlanAtom<&'a String>+'a> =
        if let Some(logic) = crate::rules::atoms::logic::resolve_with_subst(atom, subst) { Box::new(logic) }
        else if decls.get(atom.name.as_str()).map_or(false, |d| d.view) {
            Box::new(crate::rules::atoms::view::ViewPlan { head_terms: terms })
        }
        else if !atom.anti { Box::new(terms) }
        else { Box::new(crate::rules::atoms::anti::Anti(terms)) };
        (index, boxed_atom)
    }).collect()
}

/// Per-atom action that materializes facts in the atom's variable-name-sorted order.
/// Reference point for deriving plan-specific load actions.
///
/// `subst` is applied while building each atom's action: a body var mapped to
/// `Term::Lit(value)` becomes a positional literal (lit_filter); a body var
/// mapped to `Term::Var(new_name)` is renamed (affecting var_filter detection
/// for repeats and the projection's sort order). Pass empty `Subst` for the
/// non-view path.
fn base_actions_for<'a>(body: &[Atom], subst: &Subst<'a>) -> BTreeMap<usize, Action<Vec<u8>>> {
    body.iter().enumerate().map(|(index, atom)| {
        let mut action = action_from_body_with_subst(atom, subst);
        // Sort projection by the substituted var name (the var name as the planner sees it).
        action.projection.sort_by_key(|p| {
            let pos = *p.as_ref().unwrap();
            // After substitution, projection only references positions whose effective term is a Var.
            match &atom.terms[pos] {
                Term::Var(name) => match subst.get(name) {
                    Some(Term::Var(new_name)) => new_name,
                    Some(Term::Lit(_)) => unreachable!("Lit positions don't appear in projection"),
                    None => name,
                },
                Term::Lit(_) => unreachable!("Lit positions don't appear in projection"),
            }
        });
        (index, action)
    }).collect()
}

/// Builds an `Action` from an atom, applying `subst` as it walks each term.
///
/// Mirrors `Action::from_body` but routes each var through `subst`: a Var → Lit
/// substitution becomes a positional `lit_filter`; a Var → Var substitution renames
/// (so repeats with the renamed name produce `var_filter` entries).
fn action_from_body_with_subst<'a>(atom: &Atom, subst: &Subst<'a>) -> Action<Vec<u8>> {
    let mut output = Action::default();
    let mut terms_seen: BTreeMap<&str, usize> = BTreeMap::default();
    for (index, term) in atom.terms.iter().enumerate() {
        // Resolve to the effective post-substitution view: either a var name or lit bytes.
        let (eff_var, eff_lit): (Option<&str>, Option<&[u8]>) = match term {
            Term::Var(name) => match subst.get(name) {
                Some(Term::Var(new_name)) => (Some(new_name.as_str()), None),
                Some(Term::Lit(value)) => (None, Some(value.as_slice())),
                None => (Some(name.as_str()), None),
            },
            Term::Lit(value) => (None, Some(value.as_slice())),
        };
        if let Some(var_name) = eff_var {
            if !terms_seen.contains_key(var_name) {
                let new_idx = terms_seen.len();
                terms_seen.insert(var_name, new_idx);
                output.var_filter.push(Vec::default());
                output.projection.push(Ok(index));
            }
            output.var_filter[terms_seen[var_name]].push(index);
        } else if let Some(value) = eff_lit {
            output.lit_filter.push((index, value.to_vec()));
        }
    }
    output.var_filter.retain(|list| list.len() > 1);
    output.input_arity = atom.terms.len();
    output
}
