//! View atom: an `ExecAtom`/`PlanAtom` for view references (computed-on-demand
//! relations declared via `.decl name(_, _) view`).
//!
//! `ViewPlan` is the lightweight `PlanAtom` used during planning. `View` is the
//! `ExecAtom` constructed for execution; its `seed_disjuncts` and `join_apparatus`
//! fields are documented on the struct.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use crate::comms::Comms;
use crate::facts::{FactContainer, FactLSM, Forest, Relations, Terms};
use crate::rules::exec::Salad;
use crate::rules::plan::{self, PlanAtom};
use crate::rules::{ExecAtom, SeedExec, StageExec};
use crate::types::{Action, Atom, RelationDecl, Rule, Term};

/// PlanAtom proxy for view references — no apparatus, just term info.
pub struct ViewPlan {
    pub head_terms: BTreeSet<String>,
}

impl PlanAtom<String> for ViewPlan {
    fn terms(&self) -> BTreeSet<String> { self.head_terms.clone() }
    fn ground(&self, terms: &BTreeSet<String>) -> BTreeSet<String> {
        self.head_terms.difference(terms).cloned().collect()
    }
}

/// One disjunct of the apparatus used by `View::seed` (the full-materialization path).
/// Cloned head atom plus its planned execution.
pub struct SeedDisjunct {
    /// The disjunct's head atom (cloned from the defining rule). Used by `View::seed`
    /// to project results through the head's positional shape.
    pub head: Atom,
    /// The pre-built seed atom whose `.seed()` produces the initial salad.
    pub seed: Box<dyn ExecAtom<String>>,
    /// Pre-built per-stage executables (terms, output order, atoms), in plan order.
    pub stages: Vec<StageExec>,
}

/// One disjunct of the apparatus used by `View::join` (the seeded-evaluation path):
/// the seeded plan for the disjunct's body and the runtime Actions that translate
/// between use-site and disjunct schemas.
///
/// At runtime, evaluation is: canonicalize input salad to pattern order → apply
/// `input_action` → run plan stages → apply `output_action` → use-site-shaped salad.
pub struct JoinDisjunct {
    /// Applied to the (canonicalized) input salad before passing into the plan.
    /// Filters by use-site/head-derived constraints not pushable via substitution
    /// (e.g. head literal at use-site var position in pattern); projects to the
    /// seed columns.
    pub input_action: Action<Vec<u8>>,
    /// Applied to the disjunct's output salad to produce a use-site-shaped salad.
    /// Projects disjunct columns to use-site var positions and injects literals
    /// at positions where the (substituted) disjunct head emits constants.
    pub output_action: Action<Vec<u8>>,
    /// Pre-built per-stage executables (terms, output order, atoms), in plan order.
    pub stages: Vec<StageExec>,
}

/// Pre-built apparatus for `View::join` for one specific approach pattern.
pub struct JoinApparatus {
    /// The pre-bound subset of view's terms (in use-site space).
    pub pattern: BTreeSet<String>,
    pub disjuncts: Vec<JoinDisjunct>,
}

/// ExecAtom for a view reference.
pub struct View {
    /// The use-site atom (cloned at build time). Used by `View::seed` to shape output.
    pub use_site: Atom,
    pub head_terms: Vec<String>,
    /// Per-disjunct apparatus consumed by `View::seed` (full materialization, used
    /// when the view is itself the seed in a surrounding rule). Always present.
    pub seed_disjuncts: Vec<SeedDisjunct>,
    /// Apparatus consumed by `View::join` (seeded evaluation, for one pre-known
    /// approach pattern). Present when the construction site identified a pattern
    /// via the parent plan.
    pub join_apparatus: Option<JoinApparatus>,
}

impl View {
    /// Constructs a `View` for a view reference at `body[load_atom]`.
    ///
    /// Always builds the seed apparatus from the view's defining rules.
    /// If `parent_plan` is provided (view used as a non-seed in a join), also
    /// pre-plans a join apparatus for the inferred approach pattern. Per-disjunct
    /// composition contradictions (lit-vs-lit mismatch, substitution conflict) drop
    /// that disjunct from the apparatus.
    pub fn build(
        facts: &mut Relations,
        comms: &mut Comms,
        decls: &std::collections::BTreeMap<String, RelationDecl>,
        rules: &[(Rule, Vec<Vec<(usize, Duration)>>)],
        body: &[Atom],
        plan_atom: usize,
        load_atom: usize,
        parent_plan: Option<&plan::Plan<usize, String>>,
    ) -> View {
        let view_name = body[load_atom].name.as_str();
        let defining: Vec<&Rule> = rules.iter()
            .map(|(r, _)| r)
            .filter(|r| !r.head.is_empty() && r.head[0].name.as_str() == view_name)
            .collect();

        let mut seed_disjuncts: Vec<SeedDisjunct> = Vec::with_capacity(defining.len());
        for rule in &defining {
            let seed_execs = crate::rules::plan_and_build_with_fields(
                facts, comms, decls, rules,
                &rule.body[..], &rule.head[..],
                true, None,
            );
            // Stable mode (delta_atoms = [0]) yields at most one entry; if empty
            // (the body's first atom can't act as a seed, e.g. a logic atom), the
            // disjunct contributes nothing and we skip it.
            let SeedExec { seed, stages, .. } = match seed_execs.into_iter().next() {
                Some(s) => s,
                None => continue,
            };
            seed_disjuncts.push(SeedDisjunct {
                head: rule.head[0].clone(),
                seed, stages,
            });
        }

        let use_site_atom = body[load_atom].clone();
        let head_terms: Vec<String> = use_site_atom.terms.iter().filter_map(|t| t.as_var().cloned()).collect();

        let join_apparatus = parent_plan.and_then(|plan| {
            build_join_apparatus(facts, comms, decls, rules, plan, body, plan_atom, load_atom, &defining, &use_site_atom)
        });

        View { use_site: use_site_atom, head_terms, seed_disjuncts, join_apparatus }
    }
}

/// Computes the approach pattern for a view atom in a given (seed, stage) context
/// and pre-builds a `JoinApparatus` for it.
///
/// Returns `None` if the load atom isn't found in any plan stage. Per-disjunct,
/// `compose_disjunct` may return `None` (lit-vs-lit contradiction or substitution
/// conflict) and the disjunct is silently dropped from the apparatus.
fn build_join_apparatus(
    facts: &mut Relations,
    comms: &mut Comms,
    decls: &std::collections::BTreeMap<String, RelationDecl>,
    rules: &[(Rule, Vec<Vec<(usize, Duration)>>)],
    plan: &plan::Plan<usize, String>,
    body: &[Atom],
    plan_atom: usize,
    load_atom: usize,
    defining: &[&Rule],
    use_site: &Atom,
) -> Option<JoinApparatus> {

    // Find the stage in `plan` containing `load_atom`.
    let stage_idx = plan.iter().position(|(stage_atoms, _, _)| stage_atoms.contains(&load_atom))?;

    // Variables bound at the start of stage `stage_idx`: the seed's own terms plus
    // every prior stage's `terms_to_introduce`.
    let mut bound_at_stage: BTreeSet<String> =
        body[plan_atom].terms.iter().filter_map(|t| t.as_var().cloned()).collect();
    for (i, (_, terms_to_intro, _)) in plan.iter().enumerate() {
        if i >= stage_idx { break; }
        bound_at_stage.extend(terms_to_intro.iter().cloned());
    }

    let load_terms_set: BTreeSet<String> =
        body[load_atom].terms.iter().filter_map(|t| t.as_var().cloned()).collect();

    let (stage_atoms, stage_terms_field, _) = &plan[stage_idx];
    // Stage 0's `terms` field carries seed bindings (pre-bound), not introductions —
    // see `Plan` doc. For stages 1+, `terms` are the columns that stage introduces.
    let stage_terms_to_intro: BTreeSet<String> =
        if stage_idx == 0 { BTreeSet::default() } else { stage_terms_field.clone() };
    // If sum is the sole atom in this stage, it acts as the proposer (count protocol
    // short-circuits to atom.join with terms). Pattern is sum's terms minus what this
    // stage introduces. Otherwise sum is a validator and all of sum's terms are bound
    // by the time `join` is called.
    let pattern: BTreeSet<String> =
        if stage_atoms.len() == 1 && stage_atoms.contains(&load_atom) {
            load_terms_set.difference(&stage_terms_to_intro).cloned().collect()
        } else {
            let mut all_bound = bound_at_stage.clone();
            all_bound.extend(stage_terms_to_intro.iter().cloned());
            load_terms_set.intersection(&all_bound).cloned().collect()
        };

    // Build per-disjunct join apparatus.
    let mut disjuncts: Vec<JoinDisjunct> = Vec::with_capacity(defining.len());
    for rule in defining {
        let disjunct_head = &rule.head[0];

        // Compose use-site request with this disjunct's head. `None` means the
        // disjunct contributes nothing (lit-vs-lit contradiction or substitution
        // conflict) — we silently skip it.
        let comp = match compose_disjunct(&pattern, use_site, disjunct_head, &rule.body[..]) {
            Some(c) => c,
            None => continue,
        };

        // The composition produced a rewritten body (substitution applied) which is
        // owned locally. Plan, loads, and stage boxes don't borrow from it — data
        // and logic atoms own their data, and `View` (via `View::build`) clones any
        // atoms it needs. So `comp.body` can drop at the end of this iteration.
        let body = &comp.body[..];

        let (plan, loads) = plan::plan_rule_seeded(body, &comp.seed, &comp.need, decls);

        // Ensure index actions for each load action in the seeded plan.
        crate::rules::ensure_actions_for_loads(facts, comms, decls, body, &loads);

        // Build per-stage executables. Pass `parent_plan: None` so any nested views
        // in the disjunct's body fall back to materialize for now.
        let stages: Vec<StageExec> = plan.iter()
            .map(|(atom_set, terms, output_order)| {
                let atoms = atom_set.iter()
                    .map(|inner_load| crate::rules::build_atom(
                        facts, comms, decls, rules,
                        body, 0, *inner_load, &loads,
                        None,
                    ))
                    .collect();
                StageExec { terms: terms.clone(), output_order: output_order.clone(), atoms }
            })
            .collect();

        disjuncts.push(JoinDisjunct {
            input_action: comp.input_action,
            output_action: comp.output_action,
            stages,
        });
    }

    Some(JoinApparatus { pattern, disjuncts })
}

impl ExecAtom<String> for View {
    fn terms(&self) -> &[String] { &self.head_terms[..] }

    fn seed(&self, comms: &mut Comms, recent: bool) -> Salad<String> {
        let mut result = Salad::new(FactLSM::default(), self.head_terms.clone());
        for disjunct in &self.seed_disjuncts {
            let mut salad = disjunct.seed.seed(comms, recent);
            crate::rules::run_wco_stages(comms, &mut salad, &disjunct.stages);
            let projected = project_through_head(salad, &disjunct.head, &self.use_site, comms.thresh());
            result.facts.extend(projected.facts);
        }
        result
    }

    fn count(&self, _comms: &mut Comms, _salad: &mut Salad<String>, _added: &BTreeSet<String>, _index: u8) {
        // No-op: view atoms never propose values during the count protocol.
    }

    fn join(&self, comms: &mut Comms, salad: &mut Salad<String>, added: &BTreeSet<String>, _after: &[String]) {
        let ja = self.join_apparatus.as_ref()
            .expect("View::join: missing join_apparatus (only constructed for non-driver use)");
        let bound_in_salad: BTreeSet<String> = self.head_terms.iter()
            .filter(|t| salad.terms.contains(*t) && !added.contains(*t))
            .cloned()
            .collect();
        assert_eq!(
            ja.pattern, bound_in_salad,
            "View::join: apparatus pattern does not match runtime bound-in-salad",
        );
        self.join_seeded(ja, comms, salad);
    }
}

impl View {
    /// Seeded-evaluation join: run each disjunct constrained by the input salad,
    /// project results back to use-site space, replace `salad` with the union.
    fn join_seeded(&self, ja: &JoinApparatus, comms: &mut Comms, salad: &mut Salad<String>) {
        let mut result_facts: FactLSM<Forest<Terms>> = FactLSM::default();

        // Stable iteration order over the pattern; all disjuncts use the same pattern.
        let pattern_terms: Vec<String> = ja.pattern.iter().cloned().collect();

        // Canonicalize input salad to pattern-term order. Each disjunct's `input_action`
        // assumes columns are in this order.
        let canonical = match canonicalize_salad(salad, &pattern_terms, comms.thresh()) {
            Some(s) => s,
            None => { *salad = Salad::new(FactLSM::default(), self.head_terms.clone()); return; }
        };

        for disjunct in &ja.disjuncts {
            // The input salad enters the disjunct with stage 0's term set as its
            // column names — that's where the seed lands per `Plan`'s stage 0
            // semantics.
            let seed_terms: Vec<String> = disjunct.stages.first()
                .map(|stage| stage.terms.iter().cloned().collect())
                .unwrap_or_default();
            let mut disjunct_salad = apply_action_to_salad(
                &canonical, &disjunct.input_action, seed_terms, comms.thresh(),
            );
            // No early continue on empty salad: `run_wco_stages` allocates
            // conduits, and skipping it on only the empty-shard worker would
            // desync the per-worker channel count (same bug class as the
            // empty-shard relation-creation fix in rules/mod.rs).
            crate::rules::run_wco_stages(comms, &mut disjunct_salad, &disjunct.stages);
            let projected = apply_action_to_salad(
                &disjunct_salad, &disjunct.output_action, self.head_terms.clone(), comms.thresh(),
            );
            result_facts.extend(projected.facts);
        }

        *salad = Salad::new(result_facts, self.head_terms.clone());
    }
}

/// Projects input salad onto `target_terms` by column position. Returns `None` if
/// the salad is empty.
fn canonicalize_salad(
    salad: &Salad<String>,
    target_terms: &[String],
    thresh: usize,
) -> Option<Salad<String>> {
    let projection: Vec<Result<usize, Vec<u8>>> = target_terms.iter().map(|t| {
        let col = salad.terms.iter().position(|s| *s == *t)
            .expect("target term not in salad");
        Ok(col)
    }).collect();
    let mut action = Action::with_arity(salad.arity());
    action.projection = projection;

    let mut facts: FactLSM<Forest<Terms>> = FactLSM::default();
    let mut any = false;
    for forest in salad.facts.contents() {
        for f in forest.act_on(&action, thresh) { facts.extend([f]); }
        any = true;
    }
    if !any { return None; }

    Some(Salad::new(facts, target_terms.to_vec()))
}

/// Applies an Action to a salad, producing a new salad with the given `output_terms`.
fn apply_action_to_salad(
    salad: &Salad<String>,
    action: &Action<Vec<u8>>,
    output_terms: Vec<String>,
    thresh: usize,
) -> Salad<String> {
    let mut facts: FactLSM<Forest<Terms>> = FactLSM::default();
    for forest in salad.facts.contents() {
        for f in forest.act_on(action, thresh) { facts.extend([f]); }
    }
    Salad::new(facts, output_terms)
}

/// Projects a disjunct's result salad to the use-site's term space.
///
/// Walks (use_site_term, disjunct_head_term) position-by-position:
/// - (Var Vu, Var Vd): emit the salad column for Vd at output position (labeled Vu).
/// - (Var Vu, Lit Ld): emit Ld as a constant column at output position (labeled Vu).
/// - (Lit Lu, Var Vd): filter rows where the salad's Vd column equals Lu; don't emit
///   (use-site lit isn't a column in the output salad).
/// - (Lit Lu, Lit Ld): if equal, no-op; if not, the disjunct contributes nothing
///   (return empty salad with use-site var schema).
///
/// This is the no-substitution counterpart to `compose_disjunct`'s `output_action`,
/// used by `View::seed` (which materializes the full view without seeded
/// pushdown — see `seed_disjuncts`).
fn project_through_head(
    mut salad: Salad<String>,
    disjunct_head: &Atom,
    use_site: &Atom,
    thresh: usize,
) -> Salad<String> {
    assert_eq!(
        disjunct_head.terms.len(),
        use_site.terms.len(),
        "Disjunct head and use-site atom must have the same arity"
    );

    let head_terms: Vec<String> = use_site.terms.iter().filter_map(|t| t.as_var().cloned()).collect();
    let mut action = Action::with_arity(salad.arity());
    for (us_term, dj_term) in use_site.terms.iter().zip(disjunct_head.terms.iter()) {
        match (us_term, dj_term) {
            (Term::Var(_), Term::Var(vd)) => {
                let col = salad.terms.iter().position(|t| t.as_str() == vd.as_str())
                    .expect("disjunct head var not bound in disjunct's salad");
                action.projection.push(Ok(col));
            }
            (Term::Var(_), Term::Lit(ld)) => {
                action.projection.push(Err(ld.clone()));
            }
            (Term::Lit(lu), Term::Var(vd)) => {
                let col = salad.terms.iter().position(|t| t.as_str() == vd.as_str())
                    .expect("disjunct head var not bound in disjunct's salad");
                action.lit_filter.push((col, lu.clone()));
                // No projection entry — use-site lit doesn't appear in output salad.
            }
            (Term::Lit(lu), Term::Lit(ld)) => {
                if lu != ld {
                    return Salad::new(FactLSM::default(), head_terms);
                }
                // else: matching lits — no-op.
            }
        }
    }

    let mut result_facts: FactLSM<Forest<Terms>> = FactLSM::default();
    if let Some(flat) = salad.facts.flatten() {
        result_facts.extend(flat.act_on(&action, thresh));
    }
    Salad::new(result_facts, head_terms)
}

/// The runtime-ready result of composing a use-site request with one disjunct's head.
///
/// Each field carries information for a different lifecycle:
/// - `body`: the disjunct's body atoms with the composition's substitution applied
///   in-place. `Action::from_body` and `plan_body` consume it natively — no separate
///   subst channel needed downstream.
/// - `seed`: pre-bound terms (use-site vars in pattern, in BTreeSet order). Fed to
///   `plan_rule_seeded` as its seed slice.
/// - `need`: live disjunct vars that the use-site actually consumes (substituted-head
///   distinct vars filtered to those `output_action` references). Fed to
///   `plan_rule_seeded` as the last-stage projection target — terms in the substituted
///   head but not in `need` are dead from the use-site's perspective and get dropped
///   by `plan_body`'s projection-target loop.
/// - `input_action`: runtime Action applied to the input salad (columns in pattern
///   BTreeSet order) before passing to the disjunct. Filters by use-site/head
///   constraints not pushable via substitution; projects to seed columns.
/// - `output_action`: runtime Action applied to the disjunct's output salad to
///   produce a use-site-shaped salad. Its `Ok(col)` projection entries index into
///   `need`-order (the disjunct salad's actual column order after projection-pushdown).
struct DisjunctComposition {
    body: Vec<Atom>,
    seed: Vec<String>,
    need: Vec<String>,
    input_action: Action<Vec<u8>>,
    output_action: Action<Vec<u8>>,
}

/// Walks each atom's terms, replacing any `Term::Var(name)` whose name appears in
/// `subst` with the corresponding replacement term. Used by `compose_disjunct` to
/// fold use-site constraints into the disjunct's body before planning.
fn substitute_atoms(atoms: &[Atom], subst: &BTreeMap<String, Term>) -> Vec<Atom> {
    atoms.iter().map(|atom| Atom {
        name: atom.name.clone(),
        anti: atom.anti,
        terms: atom.terms.iter().map(|t| match t {
            Term::Var(name) => subst.get(name).cloned().unwrap_or_else(|| t.clone()),
            Term::Lit(_) => t.clone(),
        }).collect(),
    }).collect()
}

/// Composes a use-site request with one disjunct's head, producing the recipe for
/// evaluating the disjunct in service of the use-site.
///
/// Walks position-by-position through (use_site, disjunct_head). Each pair contributes
/// to the substitution (when the head term is a var that can be rewritten), to the
/// input filter (when the head term is a lit and the use-site var is in pattern), or
/// to a contradiction (lit vs. lit mismatch, or substitution conflict — the latter
/// arises when the head has a repeated var and the use-site disagrees, which v1 bails
/// on rather than emitting an `input_action.var_filter`).
///
/// Returns `None` for arity mismatch, lit-vs-lit contradictions, or substitution
/// conflicts.
fn compose_disjunct(
    pattern: &BTreeSet<String>,
    use_site: &Atom,
    disjunct_head: &Atom,
    disjunct_body: &[Atom],
) -> Option<DisjunctComposition> {
    if use_site.terms.len() != disjunct_head.terms.len() { return None; }

    // Pass 1: build the substitution and collect input lit filters.
    let mut subst: BTreeMap<String, Term> = BTreeMap::new();
    let mut input_lits: Vec<(String, Vec<u8>)> = Vec::new();

    for (us_term, dj_term) in use_site.terms.iter().zip(disjunct_head.terms.iter()) {
        match (us_term, dj_term) {
            (Term::Var(vu), Term::Var(vd)) => {
                // Substitute disjunct var with use-site var.
                match subst.get(vd) {
                    Some(Term::Var(prev)) if prev != vu => return None,
                    Some(Term::Lit(_)) => return None,
                    _ => { subst.insert(vd.clone(), us_term.clone()); }
                }
            }
            (Term::Var(vu), Term::Lit(ld)) => {
                if pattern.contains(vu) {
                    input_lits.push((vu.clone(), ld.clone()));
                }
                // Else: vu is not pre-bound; gets bound to ld at output via output_action.
            }
            (Term::Lit(lu), Term::Var(vd)) => {
                // Push literal into the disjunct's body planning via substitution.
                match subst.get(vd) {
                    Some(Term::Lit(prev)) if prev != lu => return None,
                    Some(Term::Var(_)) => return None,
                    _ => { subst.insert(vd.clone(), us_term.clone()); }
                }
            }
            (Term::Lit(lu), Term::Lit(ld)) => {
                if lu != ld { return None; }
            }
        }
    }

    // Seed: all pattern vars (BTreeSet order). `plan_body` filters out vars unused
    // by the (substituted) body via its `init_terms` step.
    let seed: Vec<String> = pattern.iter().cloned().collect();

    // Build input_action. Assumes the input salad has been canonicalized to
    // pattern-term order (BTreeSet iteration). Filters by collected lits, projects
    // to the seed columns.
    let pattern_terms: Vec<String> = pattern.iter().cloned().collect();
    let mut input_action = Action::with_arity(pattern_terms.len());
    for (vu, ld) in &input_lits {
        let col = pattern_terms.iter().position(|t| *t == *vu)
            .expect("input lit on var not in pattern");
        input_action.lit_filter.push((col, (*ld).clone()));
    }
    input_action.projection = seed.iter().map(|s| {
        Ok(pattern_terms.iter().position(|t| *t == *s)
            .expect("seed var not in pattern"))
    }).collect();

    // Determine which substituted-head vars are *live* — referenced by some use-site
    // var position. Vars in the substituted head but not live are dead from the
    // use-site's perspective; `plan_body` will drop them in its last-stage projection.
    let mut live: BTreeSet<String> = BTreeSet::default();
    for (i, us_term) in use_site.terms.iter().enumerate() {
        if let Term::Var(_) = us_term {
            if let Term::Var(vd) = &disjunct_head.terms[i] {
                let effective: Option<String> = match subst.get(vd) {
                    Some(Term::Var(new_name)) => Some(new_name.clone()),
                    Some(Term::Lit(_)) => None,
                    None => Some(vd.clone()),
                };
                if let Some(n) = effective { live.insert(n); }
            }
        }
    }
    // `need`: substituted head's distinct vars in presentation order, filtered to live.
    let need: Vec<String> = {
        let mut seen: BTreeSet<String> = BTreeSet::default();
        let mut out: Vec<String> = Vec::new();
        for t in disjunct_head.terms.iter() {
            if let Term::Var(name) = t {
                let effective: Option<String> = match subst.get(name) {
                    Some(Term::Var(new_name)) => Some(new_name.clone()),
                    Some(Term::Lit(_)) => None,
                    None => Some(name.clone()),
                };
                if let Some(n) = effective {
                    if live.contains(&n) && seen.insert(n.clone()) { out.push(n); }
                }
            }
        }
        out
    };

    // Build output_action. Disjunct salad columns (after the plan applies `need` as
    // the last-stage projection) are in `need` order. For each use-site var position,
    // emit `Ok(col)` indexed into `need`, or `Err(lit)` for emitted literals.
    let mut output_action = Action::with_arity(need.len());
    for (i, us_term) in use_site.terms.iter().enumerate() {
        if let Term::Var(_) = us_term {
            let emit: Result<usize, Vec<u8>> = match &disjunct_head.terms[i] {
                Term::Var(vd) => match subst.get(vd) {
                    Some(Term::Var(new_name)) => {
                        let col = need.iter().position(|t| t == new_name)
                            .expect("substituted var not in need");
                        Ok(col)
                    }
                    Some(Term::Lit(value)) => Err(value.clone()),
                    None => {
                        let col = need.iter().position(|t| t == vd)
                            .expect("disjunct head var not in need");
                        Ok(col)
                    }
                },
                Term::Lit(value) => Err(value.clone()),
            };
            output_action.projection.push(emit);
        }
    }

    let body = substitute_atoms(disjunct_body, &subst);
    Some(DisjunctComposition { body, seed, need, input_action, output_action })
}

