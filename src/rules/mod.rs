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

use crate::types::{Atom, Rule, Action, Term};
use crate::facts::{FactContainer, Forest, Relations, Terms};

pub mod plan;
pub mod exec;
pub mod atoms;

pub use plan::PlanAtom;
pub use exec::ExecAtom;

/// Constructs a boxed `ExecAtom` for an atom in a rule body.
///
/// Dispatches between logic, view, antijoin, and data variants based on the
/// atom's name and the declarations. For data atoms, threads the appropriate
/// stable/recent split per the semi-naive convention. For view atoms, delegates
/// to `View::build`.
///
/// `parent_plan` is the surrounding rule's plan for this seed, threaded through so
/// view atoms can compute their approach pattern from where they appear. `None`
/// means the atom is itself the seed (no surrounding plan to inspect).
pub(crate) fn build_atom<'a>(
    facts: &mut Relations,
    comms: &mut crate::comms::Comms,
    decls: &'a std::collections::BTreeMap<String, crate::types::RelationDecl>,
    rules: &'a [(Rule, Vec<std::time::Duration>)],
    body: &'a [Atom],
    plan_atom: usize,
    load_atom: usize,
    loads: &std::collections::BTreeMap<usize, plan::Load<String>>,
    parent_plan: Option<&plan::Plan<usize, String>>,
    subst: &plan::Subst,
) -> Box<dyn exec::ExecAtom<String> + 'a> {
    use crate::rules::atoms;
    if let Some(logic) = atoms::logic::resolve_with_subst(&body[load_atom], subst) {
        Box::new(logic)
    } else if decls.get(body[load_atom].name.as_str()).map_or(false, |d| d.view) {
        Box::new(atoms::view::View::build(
            facts, comms, decls, rules, body, plan_atom, load_atom, parent_plan,
        ))
    } else {
        let (load_action, load_terms) = &loads[&load_atom];
        let other = facts.get_action(body[load_atom].name.as_str(), load_action).unwrap();
        let to_chain = if load_atom >= plan_atom { other.recent.as_ref() } else { None };
        let other_facts: Vec<Forest<Terms>> = other.stable.contents().chain(to_chain).cloned().collect();
        let other_recent: Option<Forest<Terms>> = if plan_atom == load_atom { other.recent.clone() } else { None };
        let owned_terms: Vec<String> = load_terms.clone();
        if body[load_atom].anti { Box::new(atoms::anti::Anti((other_facts, owned_terms))) }
        else                    { Box::new((other_facts, owned_terms, other_recent)) }
    }
}

/// One plan stage's pre-built non-seed atoms, in plan order.
pub type StageBoxes<'a> = Vec<Box<dyn exec::ExecAtom<String> + 'a>>;

/// One seed's pre-built apparatus: the seed atom (whose `.seed()` produces the initial
/// salad) and the per-stage non-seed atoms (used for `wco_join`).
type SeedWork<'a> = (Box<dyn exec::ExecAtom<String> + 'a>, Vec<StageBoxes<'a>>);

/// All seeds' apparatus, parallel to `Plans` iteration order.
type SeedApparatus<'a> = Vec<SeedWork<'a>>;

/// Plans a rule body and pre-builds the boxed atoms for every (seed, stage).
///
/// Lives as a free function (not a method) because view references recursively
/// invoke this with the same field borrows. Callers split a `&mut State` into its
/// fields and pass them through. `rules` is the State's rule list, used to look up
/// views' defining rules during view-atom construction.
pub fn plan_and_build_with_fields<'a>(
    facts: &mut Relations,
    comms: &mut crate::comms::Comms,
    decls: &'a std::collections::BTreeMap<String, crate::types::RelationDecl>,
    rules: &'a [(Rule, Vec<std::time::Duration>)],
    body: &'a [Atom],
    head: &'a [Atom],
    stable: bool,
    active_relations: Option<&std::collections::BTreeSet<&str>>,
) -> (
    plan::Plans<usize, String>,
    plan::Loads<usize, String>,
    SeedApparatus<'a>,
) {
    // Body atoms that should take a turn as the source of novelty this round.
    // In `stable` mode only the first body atom drives; in incremental mode every
    // atom takes a turn, optionally restricted to those whose relation has recent
    // facts on some worker.
    let delta_atoms: Vec<usize> = if stable {
        vec![0]
    } else if let Some(active) = active_relations {
        (0..body.len()).filter(|i| active.contains(body[*i].name.as_str())).collect()
    } else {
        (0..body.len()).collect()
    };

    let (plans, loads) = plan::plan_rule(head, body, &delta_atoms, decls);

    // Ensure arranged facts exist for every load atom across every plan_atom.
    for (plan_atom, _plan) in plans.iter() {
        ensure_actions_for_loads(facts, comms, decls, body, &loads[plan_atom]);
    }
    // Pre-build the seed atom and all non-seed stage atoms per planned seed.
    // Pre-building all seeds (rather than building them inline during execution)
    // means each seed sees the round's input state, not facts an earlier seed
    // committed mid-loop — keeping semi-naive's "this round vs. next round" line clean.
    let apparatus: SeedApparatus<'a> = plans.iter()
        .map(|(plan_atom, plan)| {
            let plan_loads = &loads[plan_atom];
            let empty_subst = plan::Subst::new();
            let driver = build_atom(facts, comms, decls, rules, body, *plan_atom, *plan_atom, plan_loads, None, &empty_subst);
            let stages: Vec<StageBoxes<'a>> = plan.iter()
                .map(|(atoms, _, _)| atoms.iter()
                    .map(|load_atom| build_atom(facts, comms, decls, rules, body, *plan_atom, *load_atom, plan_loads, Some(plan), &empty_subst))
                    .collect::<Vec<_>>())
                .collect();
            (driver, stages)
        })
        .collect();
    (plans, loads, apparatus)
}

impl crate::types::State {

    /// Implements a provided rule in the context of various facts.
    ///
    /// The `stable` argument indicates whether we should perform a join with all facts (true),
    /// or only a join that involves novel facts (false).
    pub fn implement(&mut self, rule: &Rule, stable: bool, active_relations: Option<&std::collections::BTreeSet<&str>>) {

        let head = &rule.head[..];
        let body = &rule.body[..];

        // Split `self` into independent field borrows so that the apparatus (which holds
        // a borrow of `decls` and `rules` for as long as it lives) can coexist with
        // mutations to `facts` and `comms` during per-seed execution and head emission.
        let facts = &mut self.facts;
        let comms = &mut self.comms;
        let decls = &self.decls;
        let rules = &self.rules[..];

        let (plans, _loads, apparatus) = plan_and_build_with_fields(facts, comms, decls, rules, body, head, stable, active_relations);

        let potato = ".potato".to_string();

        // Per seed: seed → wco_join stages → emit head facts.
        // Seed atoms are pre-built, so each seed sees the round's input state
        // rather than facts that earlier seeds may have committed.
        for ((_plan_atom, plan), (driver, stages_boxed)) in plans.iter().zip(apparatus) {
            let mut salad = driver.seed(comms, !stable);
            run_wco_stages(comms, &mut salad, plan, &stages_boxed, potato.clone());
            emit_head_facts(facts, comms, head, salad);
        }
    }
}

/// Projects `salad` through each head atom and extends the corresponding relation.
///
/// Free function so it can coexist with an outstanding apparatus borrow on `decls`.
fn emit_head_facts<'a>(
    facts: &mut Relations,
    comms: &mut crate::comms::Comms,
    head: &[Atom],
    mut salad: crate::rules::exec::Salad<String>,
) {
    let exact_match = head.iter().position(|a| {
        a.terms.len() == salad.arity() &&
        a.terms.iter().zip(salad.terms.iter()).all(|(h,d)| h.as_var() == Some(d))
    });

    let thresh = 200_000_000 / comms.peers();
    for (_, atom) in head.iter().enumerate().filter(|(pos,_)| Some(*pos) != exact_match) {
        let mut action = Action::with_arity(salad.arity());
        action.projection = atom.terms.iter().map(|t| match t {
            Term::Var(name) => Ok(salad.terms.iter().position(|t2| t2 == name).expect(format!("Failed to find {:?} in {:?}", name, salad.terms).as_str())),
            Term::Lit(data) => Err(data.clone()),
        }).collect();
        if let Some(delta) = salad.facts.flatten() {
            extend_facts_with_fields(facts, comms, atom, delta.act_on(&action, thresh));
            salad.extend([delta]);
        }
        else {
            extend_facts_with_fields(facts, comms, atom, Default::default());
        }
    }
    if let Some(pos) = exact_match {
        extend_facts_with_fields(facts, comms, &head[pos], salad.facts);
    }
}

/// Ensures index actions exist for every non-logic, non-view atom referenced by the
/// loads. This prepares the relations to serve queries in the orders the plan needs.
pub fn ensure_actions_for_loads<'a>(
    facts: &mut Relations,
    comms: &mut crate::comms::Comms,
    decls: &std::collections::BTreeMap<String, crate::types::RelationDecl>,
    body: &'a [Atom],
    loads: &std::collections::BTreeMap<usize, plan::Load<String>>,
) {
    for (load_atom, (action, _)) in loads.iter() {
        let name = body[*load_atom].name.as_str();
        let is_logic = crate::rules::atoms::logic::resolve(&body[*load_atom]).is_some();
        let is_view = decls.get(name).map_or(false, |d| d.view);
        if !is_logic && !is_view {
            facts.ensure_action(comms, name, action);
        }
    }
}

/// Runs the wco_join stages of a plan against a salad, mutating the salad in place.
///
/// The single shared loop pattern used by `State::implement`, `Sum::seed`, and
/// `Sum::join_seeded`. Each stage's `(terms, atoms, order)` triple feeds one
/// `wco_join` call; `potato` is the column-name placeholder for count metadata.
///
/// Stage 0 is special: its `terms` document the seed's pre-bound bindings (already
/// present in `salad`), not new columns to introduce. We pass an empty `terms` set so
/// `wco_join` semijoins against `init_atoms` instead of routing through
/// `wco_join_inner` and trying to re-introduce already-bound columns. Stages 1+
/// follow the usual interpretation of `terms` as the new columns to extend with.
pub fn run_wco_stages<'a>(
    comms: &mut crate::comms::Comms,
    salad: &mut exec::Salad<String>,
    plan: &plan::Plan<usize, String>,
    stages: &[StageBoxes<'a>],
    potato: String,
) {
    let empty: std::collections::BTreeSet<String> = std::collections::BTreeSet::default();
    for (i, ((_, terms, order), atoms)) in plan.iter().zip(stages.iter()).enumerate() {
        let stage_terms = if i == 0 { &empty } else { terms };
        exec::wco_join(comms, salad, stage_terms, atoms, potato.clone(), &order[..]);
    }
}

/// Free-function form of `State::extend_facts` so it can be called with split borrows.
pub fn extend_facts_with_fields(
    facts: &mut Relations,
    comms: &mut crate::comms::Comms,
    atom: &Atom,
    mut data: crate::facts::FactLSM<Forest<Terms>>,
) {
    comms.exchange(&mut data);
    if let Some(columns) = data.flatten() {
        facts.entry(atom).extend([columns]);
    }
}
