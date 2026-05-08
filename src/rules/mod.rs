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
/// Selects between logic, antijoin, and data variants based on the atom's
/// properties, and threads the appropriate stable/recent split per the
/// semi-naive convention: atoms whose index exceeds the driver's contribute
/// their `recent` facts, others contribute only `stable`.
/// The driver itself contributes both `recent` and `stable` facts.
fn build_atom<'a>(
    body: &'a [Atom],
    plan_atom: usize,
    load_atom: usize,
    loads: &std::collections::BTreeMap<usize, plan::Load<&'a String>>,
    facts: &Relations,
) -> Box<dyn exec::ExecAtom<&'a String> + 'a> {
    use crate::rules::atoms;
    if let Some(logic) = atoms::logic::resolve(&body[load_atom]) {
        Box::new(logic)
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

/// All driver-keyed plans' boxed stages, parallel to `Plans`.
type DriverStages<'a> = Vec<Vec<StageBoxes<'a>>>;

impl crate::types::State {

    /// Plans a rule body and pre-builds the boxed non-driver atoms for every stage.
    ///
    /// Returns the planner's output (`plans`, `loads`) plus, in parallel with `plans`,
    /// the boxed atoms for each stage of each driver. The caller drives execution per
    /// driver against this apparatus (and may emit head facts, union into a sum, etc.).
    ///
    /// This is steps 1-4 of `implement`: choose drivers, plan, ensure index actions,
    /// and build boxed atoms. Execution and head emission are the caller's concern.
    pub fn plan_and_build<'a>(
        &mut self,
        body: &'a [Atom],
        head: &'a [Atom],
        stable: bool,
        active_relations: Option<&std::collections::BTreeSet<&str>>,
    ) -> (
        plan::Plans<usize, &'a String>,
        plan::Loads<usize, &'a String>,
        DriverStages<'a>,
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

        let (plans, loads) = plan::plan_rule::<plan::ByTerm>(head, body, &delta_atoms).expect("Unable to plan");

        // Ensure arranged facts exist for every load atom across every plan_atom.
        for (plan_atom, _plan) in plans.iter() {
            let plan_loads = &loads[plan_atom];
            for (load_atom, (action, _)) in plan_loads.iter() {
                if crate::rules::atoms::logic::resolve(&body[*load_atom]).is_none() {
                    self.facts.ensure_action(&mut self.comms, body[*load_atom].name.as_str(), action);
                }
            }
        }
        // Pre-build all boxed atoms for every (plan_atom, stage).
        let all_stages_boxed: DriverStages<'a> = plans.iter()
            .map(|(plan_atom, plan)| {
                let plan_loads = &loads[plan_atom];
                plan.iter()
                    .map(|(atoms, _, _)| atoms.iter()
                        .map(|load_atom| build_atom(body, *plan_atom, *load_atom, plan_loads, &self.facts))
                        .collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            })
            .collect();
        (plans, loads, all_stages_boxed)
    }

    /// Implements a provided rule in the context of various facts.
    ///
    /// The `stable` argument indicates whether we should perform a join with all facts (true),
    /// or only a join that involves novel facts (false).
    pub fn implement(&mut self, rule: &Rule, stable: bool, active_relations: Option<&std::collections::BTreeSet<&str>>) {

        let head = &rule.head[..];
        let body = &rule.body[..];

        let (plans, loads, all_stages_boxed) = self.plan_and_build(body, head, stable, active_relations);

        let potato = ".potato".to_string();

        // Per driver: seed → wco_join stages → emit head facts.
        for ((plan_atom, plan), stages_boxed) in plans.iter().zip(all_stages_boxed) {
            let plan_atom = *plan_atom;
            let plan_loads = &loads[&plan_atom];

            // Step 1: Load the initial facts to seed the sequence of joins.
            let root = build_atom(body, plan_atom, plan_atom, plan_loads, &self.facts);
            let mut salad = root.seed(&mut self.comms, !stable);

            // Step 2: Repeatedly join in sets of terms through sets of atoms.
            for ((_, terms, order), others) in plan.iter().zip(stages_boxed) {
                exec::wco_join(&mut self.comms, &mut salad, terms, &others[..], &potato, &order[..]);
            }

            // Step 3: Commit produced facts back to head atoms in `self.facts`.
            self.emit_head_facts(head, salad);
        }
    }

    /// Projects `salad` through each head atom and extends the corresponding relation.
    ///
    /// If a head atom's term order matches `salad` exactly, its facts are committed
    /// without re-projection; otherwise, an `Action` is built for the head and applied.
    fn emit_head_facts(&mut self, head: &[Atom], mut salad: crate::rules::exec::Salad<&String>) {

        // It is possible that with a single head we have the terms in the right order,
        // and can simply commit `delta`. There could be multiple heads, and the action
        // could be not the identity.
        let exact_match = head.iter().position(|a| {
            a.terms.len() == salad.arity() &&
            a.terms.iter().zip(salad.terms.iter()).all(|(h,d)| h.as_var() == Some(d))
        });

        let thresh = 200_000_000 / self.comms.peers();
        for (_, atom) in head.iter().enumerate().filter(|(pos,_)| Some(*pos) != exact_match) {
            let mut action = Action::with_arity(salad.arity());
            action.projection = atom.terms.iter().map(|t| match t {
                Term::Var(name) => Ok(salad.terms.iter().position(|t2| t2 == &name).expect(format!("Failed to find {:?} in {:?}", name, salad.terms).as_str())),
                Term::Lit(data) => Err(data.clone()),
            }).collect();
            if let Some(delta) = salad.facts.flatten() {
                self.extend_facts(atom, delta.act_on(&action, thresh));
                salad.extend([delta]);
            }
            else {
                self.extend_facts(atom, Default::default());
            }
        }
        if let Some(pos) = exact_match {
            self.extend_facts(&head[pos], salad.facts);
        }
    }
}
