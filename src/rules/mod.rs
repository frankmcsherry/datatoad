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
/// Dispatches between logic, virtual (sum), antijoin, and data variants based on the
/// atom's name and the declarations. For data atoms, threads the appropriate
/// stable/recent split per the semi-naive convention: atoms whose index exceeds the
/// driver's contribute their `recent` facts, others contribute only `stable`. The
/// driver itself contributes both. For virtual atoms, recursively plans and builds
/// the defining rules' apparatus and constructs a `Sum`.
fn build_atom<'a>(
    facts: &mut Relations,
    comms: &mut crate::comms::Comms,
    decls: &'a std::collections::BTreeMap<String, crate::types::RelationDecl>,
    rules: &'a [(Rule, Vec<std::time::Duration>)],
    body: &'a [Atom],
    plan_atom: usize,
    load_atom: usize,
    loads: &std::collections::BTreeMap<usize, plan::Load<&'a String>>,
) -> Box<dyn exec::ExecAtom<&'a String> + 'a> {
    use crate::rules::atoms;
    if let Some(logic) = atoms::logic::resolve(&body[load_atom]) {
        Box::new(logic)
    } else if decls.get(body[load_atom].name.as_str()).map_or(false, |d| d.virt) {
        // Virtual: pre-build apparatus per defining rule, construct a Sum.
        let virt_name = body[load_atom].name.as_str();
        let defining: Vec<&'a Rule> = rules.iter()
            .map(|(r, _)| r)
            .filter(|r| !r.head.is_empty() && r.head[0].name.as_str() == virt_name)
            .collect();
        let mut disjuncts: Vec<atoms::sum::Disjunct<'a>> = Vec::with_capacity(defining.len());
        for rule in defining {
            let (plans, loads, apparatus) = plan_and_build_with_fields(
                facts, comms, decls, rules,
                &rule.body[..], &rule.head[..],
                true, None,
            );
            disjuncts.push(atoms::sum::Disjunct { rule, plans, loads, apparatus });
        }
        let use_site = &body[load_atom];
        let head_terms: Vec<&'a String> = use_site.terms.iter().filter_map(|t| t.as_var()).collect();
        Box::new(atoms::sum::Sum { use_site, head_terms, disjuncts })
    } else {
        let (load_action, load_terms) = &loads[&load_atom];
        let other = facts.get_action(body[load_atom].name.as_str(), load_action).unwrap();
        let to_chain = if load_atom >= plan_atom { other.recent.as_ref() } else { None };
        let other_facts: Vec<Forest<Terms>> = other.stable.contents().chain(to_chain).cloned().collect();
        let other_recent: Option<Forest<Terms>> = if plan_atom == load_atom { other.recent.clone() } else { None };
        let owned_terms: Vec<&'a String> = load_terms.clone();
        if body[load_atom].anti { Box::new(atoms::anti::Anti((other_facts, owned_terms))) }
        else                    { Box::new((other_facts, owned_terms, other_recent)) }
    }
}

/// One plan stage's pre-built non-driver atoms, in plan order.
type StageBoxes<'a> = Vec<Box<dyn exec::ExecAtom<&'a String> + 'a>>;

/// One driver's pre-built apparatus: the driver atom (used for `seed`) and the
/// per-stage non-driver atoms (used for `wco_join`).
type DriverWork<'a> = (Box<dyn exec::ExecAtom<&'a String> + 'a>, Vec<StageBoxes<'a>>);

/// All drivers' apparatus, parallel to `Plans` iteration order.
type DriverApparatus<'a> = Vec<DriverWork<'a>>;

/// Plans a rule body and pre-builds the boxed atoms for every (driver, stage).
///
/// Lives as a free function (not a method) because virtual references recursively
/// invoke this with the same field borrows. Callers split a `&mut State` into its
/// fields and pass them through. `rules` is the State's rule list, used to look up
/// virtual relations' defining rules during sum-atom construction.
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
    plan::Plans<usize, &'a String>,
    plan::Loads<usize, &'a String>,
    DriverApparatus<'a>,
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

    let (plans, loads) = plan::plan_rule::<plan::ByTerm>(head, body, &delta_atoms, decls).expect("Unable to plan");

    // Ensure arranged facts exist for every load atom across every plan_atom.
    // Skip logic and virtual atoms — neither has stored data to arrange.
    for (plan_atom, _plan) in plans.iter() {
        let plan_loads = &loads[plan_atom];
        for (load_atom, (action, _)) in plan_loads.iter() {
            let name = body[*load_atom].name.as_str();
            let is_logic = crate::rules::atoms::logic::resolve(&body[*load_atom]).is_some();
            let is_virtual = decls.get(name).map_or(false, |d| d.virt);
            if !is_logic && !is_virtual {
                facts.ensure_action(comms, name, action);
            }
        }
    }
    // Pre-build the driver atom and all non-driver stage atoms per planned driver.
    // Pre-building drivers (in addition to non-drivers) means the apparatus is
    // self-contained: callers can execute without any further trips into the state.
    let apparatus: DriverApparatus<'a> = plans.iter()
        .map(|(plan_atom, plan)| {
            let plan_loads = &loads[plan_atom];
            let driver = build_atom(facts, comms, decls, rules, body, *plan_atom, *plan_atom, plan_loads);
            let stages: Vec<StageBoxes<'a>> = plan.iter()
                .map(|(atoms, _, _)| atoms.iter()
                    .map(|load_atom| build_atom(facts, comms, decls, rules, body, *plan_atom, *load_atom, plan_loads))
                    .collect::<Vec<_>>())
                .collect();
            (driver, stages)
        })
        .collect();
    (plans, loads, apparatus)
}

impl crate::types::State {

    /// Plans a rule body and pre-builds the boxed non-driver atoms for every stage.
    ///
    /// Returns the planner's output (`plans`, `loads`) plus, in parallel with `plans`,
    /// the boxed atoms for each stage of each driver. The caller drives execution per
    /// driver against this apparatus (and may emit head facts, union into a sum, etc.).
    ///
    /// This is steps 1-4 of `implement`: choose drivers, plan, ensure index actions,
    /// and build boxed atoms. Execution and head emission are the caller's concern.
    /// Implements a provided rule in the context of various facts.
    ///
    /// The `stable` argument indicates whether we should perform a join with all facts (true),
    /// or only a join that involves novel facts (false).
    pub fn implement(&mut self, rule: &Rule, stable: bool, active_relations: Option<&std::collections::BTreeSet<&str>>) {

        let head = &rule.head[..];
        let body = &rule.body[..];

        // Split `self` into independent field borrows so that the apparatus (which holds
        // a borrow of `decls` and `rules` for as long as it lives) can coexist with
        // mutations to `facts` and `comms` during per-driver execution and head emission.
        let facts = &mut self.facts;
        let comms = &mut self.comms;
        let decls = &self.decls;
        let rules = &self.rules[..];

        let (plans, _loads, apparatus) = plan_and_build_with_fields(facts, comms, decls, rules, body, head, stable, active_relations);

        let potato = ".potato".to_string();

        // Per driver: seed → wco_join stages → emit head facts.
        // Driver atoms are pre-built, so each driver sees the round's input state
        // rather than facts that earlier drivers may have committed.
        for ((_plan_atom, plan), (driver, stages_boxed)) in plans.iter().zip(apparatus) {
            let mut salad = driver.seed(comms, !stable);
            for ((_, terms, order), others) in plan.iter().zip(stages_boxed) {
                exec::wco_join(comms, &mut salad, terms, &others[..], &potato, &order[..]);
            }
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
    mut salad: crate::rules::exec::Salad<&'a String>,
) {
    let exact_match = head.iter().position(|a| {
        a.terms.len() == salad.arity() &&
        a.terms.iter().zip(salad.terms.iter()).all(|(h,d)| h.as_var() == Some(d))
    });

    let thresh = 200_000_000 / comms.peers();
    for (_, atom) in head.iter().enumerate().filter(|(pos,_)| Some(*pos) != exact_match) {
        let mut action = Action::with_arity(salad.arity());
        action.projection = atom.terms.iter().map(|t| match t {
            Term::Var(name) => Ok(salad.terms.iter().position(|t2| t2 == &name).expect(format!("Failed to find {:?} in {:?}", name, salad.terms).as_str())),
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
