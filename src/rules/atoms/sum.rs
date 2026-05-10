//! Sum atom: an `ExecAtom`/`PlanAtom` for virtual relation references.
//!
//! `SumPlan` is the lightweight `PlanAtom` used during planning. `Sum` is the
//! `ExecAtom` constructed for execution; its `seed_disjuncts` and `join_apparatus`
//! fields are documented on the struct.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;
use std::time::Duration;

use crate::comms::Comms;
use crate::facts::{FactContainer, FactLSM, Forest, Relations, Terms};
use crate::rules::exec::Salad;
use crate::rules::plan::{self, PlanAtom, Subst};
use crate::rules::{ExecAtom, SeedApparatus, StageBoxes};
use crate::types::{Action, Atom, RelationDecl, Rule, Term};

/// A `&'static String` placeholder used as the count-metadata column name in `wco_join`.
///
/// Lives 'static so it can coerce to any `&'a String`. `wco_join` runs on salads
/// whose term type is `&'a String` for an `'a` we don't own; a local `String`
/// declared inside `Sum::seed`/`Sum::join_seeded` wouldn't live long enough.
fn potato() -> &'static String {
    static POTATO: OnceLock<String> = OnceLock::new();
    POTATO.get_or_init(|| ".potato".to_string())
}

/// PlanAtom proxy for virtual relation references — no apparatus, just term info.
pub struct SumPlan<'a> {
    pub head_terms: BTreeSet<&'a String>,
}

impl<'a> PlanAtom<&'a String> for SumPlan<'a> {
    fn terms(&self) -> BTreeSet<&'a String> { self.head_terms.clone() }
    fn ground(&self, terms: &BTreeSet<&'a String>) -> BTreeSet<&'a String> {
        self.head_terms.difference(terms).copied().collect()
    }
}

/// One disjunct of the seed apparatus: defining rule plus its standard apparatus.
pub struct SeedDisjunct<'a> {
    pub rule: &'a Rule,
    pub plans: plan::Plans<usize, &'a String>,
    pub loads: plan::Loads<usize, &'a String>,
    pub apparatus: SeedApparatus<'a>,
}

/// One disjunct of the join apparatus: the seeded plan for the disjunct's body and
/// the runtime Actions that translate between use-site and disjunct schemas.
///
/// At runtime, evaluation is: canonicalize input salad to pattern order → apply
/// `input_action` → run plan stages → apply `output_action` → use-site-shaped salad.
pub struct JoinDisjunct<'a> {
    pub rule: &'a Rule,
    /// Applied to the (canonicalized) input salad before passing into the plan.
    /// Filters by use-site/head-derived constraints not pushable via substitution
    /// (e.g. head literal at use-site var position in pattern); projects to the
    /// seed columns.
    pub input_action: Action<Vec<u8>>,
    /// Applied to the disjunct's output salad to produce a use-site-shaped salad.
    /// Projects disjunct columns to use-site var positions and injects literals
    /// at positions where the (substituted) disjunct head emits constants.
    pub output_action: Action<Vec<u8>>,
    /// The seeded plan for the disjunct's body, planned with substitution applied.
    pub plan: plan::Plan<usize, &'a String>,
    /// Pre-built atoms per stage, in plan order (one per atom in each stage).
    pub stages: Vec<StageBoxes<'a>>,
}

/// Pre-built apparatus for `Sum::join` for one specific approach pattern.
pub struct JoinApparatus<'a> {
    /// The pre-bound subset of sum's terms (in use-site space).
    pub pattern: BTreeSet<&'a String>,
    pub disjuncts: Vec<JoinDisjunct<'a>>,
}

/// ExecAtom for a virtual relation reference.
pub struct Sum<'a> {
    pub use_site: &'a Atom,
    pub head_terms: Vec<&'a String>,
    /// Apparatus for `seed` (when sum is itself the seed). Always present.
    pub seed_disjuncts: Vec<SeedDisjunct<'a>>,
    /// Apparatus for `join` for a single pre-known approach pattern. Present when
    /// the construction site identified a pattern via the parent plan.
    pub join_apparatus: Option<JoinApparatus<'a>>,
}

impl<'a> Sum<'a> {
    /// Constructs a `Sum` for a virtual reference at `body[load_atom]`.
    ///
    /// Always builds the seed apparatus from the virtual relation's defining rules.
    /// If `parent_plan` is provided (sum used as a non-seed in a join), also
    /// pre-plans a join apparatus for the inferred approach pattern. Per-disjunct
    /// composition contradictions (lit-vs-lit mismatch, substitution conflict) drop
    /// that disjunct from the apparatus; `Sum::join` falls back to materialize-and-
    /// delegate when no `parent_plan` was available or the runtime pattern doesn't
    /// match the apparatus pattern.
    pub fn build(
        facts: &mut Relations,
        comms: &mut Comms,
        decls: &'a std::collections::BTreeMap<String, RelationDecl>,
        rules: &'a [(Rule, Vec<Duration>)],
        body: &'a [Atom],
        plan_atom: usize,
        load_atom: usize,
        parent_plan: Option<&plan::Plan<usize, &'a String>>,
    ) -> Sum<'a> {
        let virt_name = body[load_atom].name.as_str();
        let defining: Vec<&'a Rule> = rules.iter()
            .map(|(r, _)| r)
            .filter(|r| !r.head.is_empty() && r.head[0].name.as_str() == virt_name)
            .collect();

        let mut seed_disjuncts: Vec<SeedDisjunct<'a>> = Vec::with_capacity(defining.len());
        for rule in &defining {
            let (plans, loads, apparatus) = crate::rules::plan_and_build_with_fields(
                facts, comms, decls, rules,
                &rule.body[..], &rule.head[..],
                true, None,
            );
            seed_disjuncts.push(SeedDisjunct { rule, plans, loads, apparatus });
        }

        let use_site = &body[load_atom];
        let head_terms: Vec<&'a String> = use_site.terms.iter().filter_map(|t| t.as_var()).collect();

        let join_apparatus = parent_plan.and_then(|plan| {
            build_join_apparatus(facts, comms, decls, rules, plan, body, plan_atom, load_atom, &defining, use_site)
        });

        Sum { use_site, head_terms, seed_disjuncts, join_apparatus }
    }
}

/// Computes the approach pattern for a virtual atom in a given (seed, stage) context
/// and pre-builds a `JoinApparatus` for it.
///
/// Returns `None` if the load atom isn't found in any plan stage. Per-disjunct,
/// `compose_disjunct` may return `None` (lit-vs-lit contradiction or substitution
/// conflict) and the disjunct is silently dropped from the apparatus.
fn build_join_apparatus<'a>(
    facts: &mut Relations,
    comms: &mut Comms,
    decls: &'a std::collections::BTreeMap<String, RelationDecl>,
    rules: &'a [(Rule, Vec<Duration>)],
    plan: &plan::Plan<usize, &'a String>,
    body: &'a [Atom],
    plan_atom: usize,
    load_atom: usize,
    defining: &[&'a Rule],
    use_site: &'a Atom,
) -> Option<JoinApparatus<'a>> {

    // Find the stage in `plan` containing `load_atom`.
    let stage_idx = plan.iter().position(|(stage_atoms, _, _)| stage_atoms.contains(&load_atom))?;

    // Variables bound at the start of stage `stage_idx`: the seed's own terms plus
    // every prior stage's `terms_to_introduce`.
    let mut bound_at_stage: BTreeSet<&'a String> =
        body[plan_atom].terms.iter().filter_map(|t| t.as_var()).collect();
    for (i, (_, terms_to_intro, _)) in plan.iter().enumerate() {
        if i >= stage_idx { break; }
        bound_at_stage.extend(terms_to_intro.iter().copied());
    }

    let load_terms_set: BTreeSet<&'a String> =
        body[load_atom].terms.iter().filter_map(|t| t.as_var()).collect();

    let (stage_atoms, stage_terms_field, _) = &plan[stage_idx];
    // Stage 0's `terms` field carries seed bindings (pre-bound), not introductions —
    // see `Plan` doc. For stages 1+, `terms` are the columns that stage introduces.
    let stage_terms_to_intro: BTreeSet<&'a String> =
        if stage_idx == 0 { BTreeSet::default() } else { stage_terms_field.clone() };
    // If sum is the sole atom in this stage, it acts as the proposer (count protocol
    // short-circuits to atom.join with terms). Pattern is sum's terms minus what this
    // stage introduces. Otherwise sum is a validator and all of sum's terms are bound
    // by the time `join` is called.
    let pattern: BTreeSet<&'a String> =
        if stage_atoms.len() == 1 && stage_atoms.contains(&load_atom) {
            load_terms_set.difference(&stage_terms_to_intro).copied().collect()
        } else {
            let mut all_bound = bound_at_stage.clone();
            all_bound.extend(stage_terms_to_intro.iter().copied());
            load_terms_set.intersection(&all_bound).copied().collect()
        };

    // Build per-disjunct join apparatus.
    let mut disjuncts: Vec<JoinDisjunct<'a>> = Vec::with_capacity(defining.len());
    for rule in defining {
        let disjunct_head = &rule.head[0];

        // Compose use-site request with this disjunct's head. `None` means the
        // disjunct contributes nothing (lit-vs-lit contradiction or substitution
        // conflict) — we silently skip it.
        let comp = match compose_disjunct(&pattern, use_site, disjunct_head) {
            Some(c) => c,
            None => continue,
        };

        let (plan, loads) = plan::plan_rule_seeded(
            &rule.body[..], &comp.seed, &comp.need, &comp.subst, decls,
        );

        // Ensure index actions for each load action in the seeded plan.
        crate::rules::ensure_actions_for_loads(facts, comms, decls, &rule.body[..], &loads);

        // Build per-stage atoms. Pass `pattern_info: None` so any nested virtuals
        // in the disjunct's body fall back to materialize for now.
        let stages: Vec<StageBoxes<'a>> = plan.iter()
            .map(|(atoms, _, _)| atoms.iter()
                .map(|inner_load| crate::rules::build_atom(
                    facts, comms, decls, rules,
                    &rule.body[..], 0, *inner_load, &loads,
                    None,
                    &comp.subst,
                ))
                .collect::<Vec<_>>())
            .collect();

        disjuncts.push(JoinDisjunct {
            rule,
            input_action: comp.input_action,
            output_action: comp.output_action,
            plan,
            stages,
        });
    }

    Some(JoinApparatus { pattern, disjuncts })
}

impl<'a> ExecAtom<&'a String> for Sum<'a> {
    fn terms(&self) -> &[&'a String] { &self.head_terms[..] }

    fn seed(&self, comms: &mut Comms, recent: bool) -> Salad<&'a String> {
        let mut result = Salad::new(FactLSM::default(), self.head_terms.clone());
        for disjunct in &self.seed_disjuncts {
            let disjunct_head = &disjunct.rule.head[0];
            for ((_plan_atom, plan), (driver, stages)) in disjunct.plans.iter().zip(&disjunct.apparatus) {
                let mut salad = driver.seed(comms, recent);
                crate::rules::run_wco_stages(comms, &mut salad, plan, stages, potato());
                let projected = project_through_head(salad, disjunct_head, self.use_site);
                result.facts.extend(projected.facts);
            }
        }
        result
    }

    fn count(&self, _comms: &mut Comms, _salad: &mut Salad<&'a String>, _added: &BTreeSet<&'a String>, _index: u8) {
        // No-op: sum atoms never propose values during the count protocol.
    }

    fn join(&self, comms: &mut Comms, salad: &mut Salad<&'a String>, added: &BTreeSet<&'a String>, after: &[&'a String]) {
        // The call's approach pattern: which sum terms are bound in the input salad,
        // excluding any that this call is supposed to introduce.
        let bound_in_salad: BTreeSet<&'a String> = self.head_terms.iter()
            .filter(|t| salad.terms.contains(*t) && !added.contains(*t))
            .copied()
            .collect();

        if let Some(ja) = self.join_apparatus.as_ref() {
            if ja.pattern == bound_in_salad {
                self.join_seeded(ja, comms, salad);
                return;
            }
        }

        // Fallback: materialize the full sum and delegate to the data-atom join.
        let materialized = self.seed(comms, false);
        let facts: Vec<Forest<Terms>> = materialized.facts.into_iter().collect();
        let temp: (Vec<Forest<Terms>>, Vec<&'a String>, Option<Forest<Terms>>) =
            (facts, materialized.terms, None);
        temp.join(comms, salad, added, after);
    }
}

impl<'a> Sum<'a> {
    /// Seeded-evaluation join: run each disjunct constrained by the input salad,
    /// project results back to use-site space, replace `salad` with the union.
    fn join_seeded(&self, ja: &JoinApparatus<'a>, comms: &mut Comms, salad: &mut Salad<&'a String>) {
        let mut result_facts: FactLSM<Forest<Terms>> = FactLSM::default();

        // Stable iteration order over the pattern; all disjuncts use the same pattern.
        let pattern_terms: Vec<&'a String> = ja.pattern.iter().copied().collect();

        // Canonicalize input salad to pattern-term order. Each disjunct's `input_action`
        // assumes columns are in this order.
        let canonical = match canonicalize_salad(salad, &pattern_terms) {
            Some(s) => s,
            None => { *salad = Salad::new(FactLSM::default(), self.head_terms.clone()); return; }
        };

        for disjunct in &ja.disjuncts {
            let mut disjunct_salad = apply_action_to_salad(
                &canonical, &disjunct.input_action, disjunct.seed_terms_for_action(),
            );
            if disjunct_salad.facts.is_empty() { continue; }
            crate::rules::run_wco_stages(
                comms, &mut disjunct_salad, &disjunct.plan, &disjunct.stages, potato(),
            );
            let projected = apply_action_to_salad(
                &disjunct_salad, &disjunct.output_action, self.head_terms.clone(),
            );
            result_facts.extend(projected.facts);
        }

        *salad = Salad::new(result_facts, self.head_terms.clone());
    }
}

impl<'a> JoinDisjunct<'a> {
    /// Term names corresponding to the columns `input_action` projects to. Computed
    /// from the plan's stage 0 terms — that's where the seed lands.
    fn seed_terms_for_action(&self) -> Vec<&'a String> {
        self.plan.first()
            .map(|(_, terms, _)| terms.iter().copied().collect())
            .unwrap_or_default()
    }
}

/// Projects input salad onto `target_terms` by column position. Returns `None` if
/// the salad is empty.
fn canonicalize_salad<'a>(
    salad: &Salad<&'a String>,
    target_terms: &[&'a String],
) -> Option<Salad<&'a String>> {
    let projection: Vec<Result<usize, Vec<u8>>> = target_terms.iter().map(|t| {
        let col = salad.terms.iter().position(|s| *s == *t)
            .expect("target term not in salad");
        Ok(col)
    }).collect();
    let mut action = Action::with_arity(salad.arity());
    action.projection = projection;

    let thresh = 200_000_000;
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
fn apply_action_to_salad<'a>(
    salad: &Salad<&'a String>,
    action: &Action<Vec<u8>>,
    output_terms: Vec<&'a String>,
) -> Salad<&'a String> {
    let thresh = 200_000_000;
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
/// used by `Sum::seed` (which materializes the full virtual relation without seeded
/// pushdown — see `seed_disjuncts`).
fn project_through_head<'a>(
    mut salad: Salad<&'a String>,
    disjunct_head: &Atom,
    use_site: &'a Atom,
) -> Salad<&'a String> {
    assert_eq!(
        disjunct_head.terms.len(),
        use_site.terms.len(),
        "Disjunct head and use-site atom must have the same arity"
    );

    let head_terms: Vec<&'a String> = use_site.terms.iter().filter_map(|t| t.as_var()).collect();
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

    let thresh = 200_000_000;
    let mut result_facts: FactLSM<Forest<Terms>> = FactLSM::default();
    if let Some(flat) = salad.facts.flatten() {
        result_facts.extend(flat.act_on(&action, thresh));
    }
    Salad::new(result_facts, head_terms)
}

/// The runtime-ready result of composing a use-site request with one disjunct's head.
///
/// Each field carries information for a different lifecycle:
/// - `subst`: planning-time substitution (body var → use-site var or literal). Fed to
///   `plan_rule_seeded`; consumed there to bias `build_atoms_map` and `base_actions_for`
///   without rewriting the body's `Atom` structs.
/// - `seed`: pre-bound terms (use-site vars in pattern, in BTreeSet order). Fed to
///   `plan_rule_seeded` as its seed slice.
/// - `need`: live disjunct vars that the use-site actually consumes (substituted-head
///   distinct vars filtered to those `output_action` references). Fed to
///   `plan_rule_seeded` as the last-stage projection target — terms in the substituted
///   head but not in `need` are dead from the use-site's perspective and get dropped
///   by `plan_body`'s projection-target loop.
/// - `input_action`: runtime Action applied to the input salad (columns in pattern
///   BTreeSet order) before passing to the disjunct. Filters by use-site/head
///   constraints not pushable via subst; projects to seed columns.
/// - `output_action`: runtime Action applied to the disjunct's output salad to
///   produce a use-site-shaped salad. Its `Ok(col)` projection entries index into
///   `need`-order (the disjunct salad's actual column order after projection-pushdown).
struct DisjunctComposition<'a> {
    subst: Subst<'a>,
    seed: Vec<&'a String>,
    need: Vec<&'a String>,
    input_action: Action<Vec<u8>>,
    output_action: Action<Vec<u8>>,
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
fn compose_disjunct<'a>(
    pattern: &BTreeSet<&'a String>,
    use_site: &'a Atom,
    disjunct_head: &'a Atom,
) -> Option<DisjunctComposition<'a>> {
    if use_site.terms.len() != disjunct_head.terms.len() { return None; }

    // Pass 1: build the substitution and collect input lit filters.
    let mut subst: Subst<'a> = BTreeMap::new();
    let mut input_lits: Vec<(&'a String, &'a Vec<u8>)> = Vec::new();

    for (us_term, dj_term) in use_site.terms.iter().zip(disjunct_head.terms.iter()) {
        match (us_term, dj_term) {
            (Term::Var(vu), Term::Var(vd)) => {
                // Substitute disjunct var with use-site var.
                match subst.get(vd) {
                    Some(Term::Var(prev)) if prev != vu => return None,
                    Some(Term::Lit(_)) => return None,
                    _ => { subst.insert(vd, us_term); }
                }
            }
            (Term::Var(vu), Term::Lit(ld)) => {
                if pattern.contains(vu) {
                    input_lits.push((vu, ld));
                }
                // Else: vu is not pre-bound; gets bound to ld at output via output_action.
            }
            (Term::Lit(lu), Term::Var(vd)) => {
                // Push literal into the disjunct's body planning via substitution.
                match subst.get(vd) {
                    Some(Term::Lit(prev)) if prev != lu => return None,
                    Some(Term::Var(_)) => return None,
                    _ => { subst.insert(vd, us_term); }
                }
            }
            (Term::Lit(lu), Term::Lit(ld)) => {
                if lu != ld { return None; }
            }
        }
    }

    // Seed: all pattern vars (BTreeSet order). `plan_body` filters out vars unused
    // by the (substituted) body via its `init_terms` step.
    let seed: Vec<&'a String> = pattern.iter().copied().collect();

    // Build input_action. Assumes the input salad has been canonicalized to
    // pattern-term order (BTreeSet iteration). Filters by collected lits, projects
    // to the seed columns.
    let pattern_terms: Vec<&'a String> = pattern.iter().copied().collect();
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
    let mut live: BTreeSet<&'a String> = BTreeSet::default();
    for (i, us_term) in use_site.terms.iter().enumerate() {
        if let Term::Var(_) = us_term {
            if let Term::Var(vd) = &disjunct_head.terms[i] {
                let effective: Option<&'a String> = match subst.get(vd) {
                    Some(Term::Var(new_name)) => Some(new_name),
                    Some(Term::Lit(_)) => None,
                    None => Some(vd),
                };
                if let Some(n) = effective { live.insert(n); }
            }
        }
    }
    // `need`: substituted head's distinct vars in presentation order, filtered to live.
    let need: Vec<&'a String> = {
        let mut seen: BTreeSet<&'a String> = BTreeSet::default();
        let mut out: Vec<&'a String> = Vec::new();
        for t in disjunct_head.terms.iter() {
            if let Term::Var(name) = t {
                let effective: Option<&'a String> = match subst.get(name) {
                    Some(Term::Var(new_name)) => Some(new_name),
                    Some(Term::Lit(_)) => None,
                    None => Some(name),
                };
                if let Some(n) = effective {
                    if live.contains(n) && seen.insert(n) { out.push(n); }
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
                        let col = need.iter().position(|t| *t as &String == new_name as &String)
                            .expect("substituted var not in need");
                        Ok(col)
                    }
                    Some(Term::Lit(value)) => Err(value.clone()),
                    None => {
                        let col = need.iter().position(|t| *t as &String == vd as &String)
                            .expect("disjunct head var not in need");
                        Ok(col)
                    }
                },
                Term::Lit(value) => Err(value.clone()),
            };
            output_action.projection.push(emit);
        }
    }

    Some(DisjunctComposition { subst, seed, need, input_action, output_action })
}

