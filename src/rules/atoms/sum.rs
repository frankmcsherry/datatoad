//! Sum atom: an `ExecAtom`/`PlanAtom` for virtual relation references.
//!
//! `SumPlan` is the lightweight `PlanAtom` used during planning. `Sum` is the
//! `ExecAtom` constructed for execution; its `seed_disjuncts` and `join_apparatus`
//! fields are documented on the struct.

use std::collections::BTreeSet;
use std::sync::OnceLock;
use std::time::Duration;

use crate::comms::Comms;
use crate::facts::{FactContainer, FactLSM, Forest, Relations, Terms};
use crate::rules::exec::Salad;
use crate::rules::plan::{self, PlanAtom};
use crate::rules::{ExecAtom, DriverApparatus, StageBoxes};
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
    pub apparatus: DriverApparatus<'a>,
}

/// One disjunct of the join apparatus: phantom-driven plan + per-stage atoms,
/// with the variable mapping from use-site space to disjunct head var space.
pub struct JoinDisjunct<'a> {
    pub rule: &'a Rule,
    /// For each pattern term (in use-site space), the disjunct's head var at the
    /// same position. Always populated for every pattern term: if any pattern
    /// position had a literal in the disjunct head instead of a var,
    /// `compute_var_mapping` returns `None` and this disjunct (and the surrounding
    /// `JoinApparatus`) is never built — `Sum::join` falls back to materialize.
    pub var_mapping: Vec<(&'a String, &'a String)>,
    /// The phantom-driven plan stages.
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
    /// Apparatus for `seed` (when sum is itself the driver). Always present.
    pub seed_disjuncts: Vec<SeedDisjunct<'a>>,
    /// Apparatus for `join` for a single pre-known approach pattern. Present when
    /// the construction site identified a pattern via the parent plan.
    pub join_apparatus: Option<JoinApparatus<'a>>,
}

impl<'a> Sum<'a> {
    /// Constructs a `Sum` for a virtual reference at `body[load_atom]`.
    ///
    /// Always builds the seed apparatus from the virtual relation's defining rules.
    /// If `parent_plan` is provided (sum used as a non-driver in a join), also
    /// pre-plans a join apparatus for the inferred approach pattern; if any disjunct
    /// can't support seeded eval at that pattern, the join apparatus is `None` and
    /// `Sum::join` falls back to materialize-and-delegate.
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

/// Computes the approach pattern for a virtual atom in a given (driver, stage) context
/// and pre-builds a `JoinApparatus` for it. Returns `None` if any disjunct can't
/// support seeded eval at this pattern (e.g., a disjunct head has a literal at a
/// pattern position).
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

    // Variables bound at the start of stage `stage_idx`: the driver's own terms plus
    // every prior stage's `terms_to_introduce`.
    let mut bound_at_stage: BTreeSet<&'a String> =
        body[plan_atom].terms.iter().filter_map(|t| t.as_var()).collect();
    for (i, (_, terms_to_intro, _)) in plan.iter().enumerate() {
        if i >= stage_idx { break; }
        bound_at_stage.extend(terms_to_intro.iter().copied());
    }

    let load_terms_set: BTreeSet<&'a String> =
        body[load_atom].terms.iter().filter_map(|t| t.as_var()).collect();

    let (stage_atoms, stage_terms_to_intro, _) = &plan[stage_idx];
    // If sum is the sole atom in this stage, it acts as the proposer (count protocol
    // short-circuits to atom.join with terms). Pattern is sum's terms minus what this
    // stage introduces. Otherwise sum is a validator and all of sum's terms are bound
    // by the time `join` is called.
    let pattern: BTreeSet<&'a String> =
        if stage_atoms.len() == 1 && stage_atoms.contains(&load_atom) {
            load_terms_set.difference(stage_terms_to_intro).copied().collect()
        } else {
            let mut all_bound = bound_at_stage.clone();
            all_bound.extend(stage_terms_to_intro.iter().copied());
            load_terms_set.intersection(&all_bound).copied().collect()
        };

    // Build per-disjunct join apparatus.
    let mut disjuncts: Vec<JoinDisjunct<'a>> = Vec::with_capacity(defining.len());
    for rule in defining {
        let disjunct_head = &rule.head[0];

        // Compute variable mapping from pattern (use-site) to disjunct head var space.
        // If the disjunct head has a literal at any pattern position, we can't seed it
        // without literal-filter support — bail and force the materialize fallback.
        let var_mapping = compute_var_mapping(&pattern, use_site, disjunct_head)?;
        let body_pre_bound: BTreeSet<&'a String> =
            var_mapping.iter().map(|(_, dj)| *dj).collect();

        // Phantom-driven plan for this disjunct's body.
        let (plan, loads) = plan::plan_rule_seeded::<plan::ByTerm>(
            &rule.head[..], &rule.body[..], body_pre_bound, decls,
        ).ok()?;

        // Ensure index actions for each load action in the seeded plan.
        crate::rules::ensure_actions_for_loads(facts, comms, decls, &rule.body[..], &loads);

        // Build per-stage atoms. Use the disjunct's body atoms as non-drivers (the
        // input salad acts as the driver). Pass `pattern_info: None` so any nested
        // virtuals in the disjunct's body fall back to materialize for now.
        let stages: Vec<StageBoxes<'a>> = plan.iter()
            .map(|(atoms, _, _)| atoms.iter()
                .map(|inner_load| crate::rules::build_atom(
                    facts, comms, decls, rules,
                    &rule.body[..], 0, *inner_load, &loads,
                    None,
                ))
                .collect::<Vec<_>>())
            .collect();

        disjuncts.push(JoinDisjunct { rule, var_mapping, plan, stages });
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

        for disjunct in &ja.disjuncts {
            let mut disjunct_salad = match project_and_rename(salad, &pattern_terms, &disjunct.var_mapping) {
                Some(s) => s,
                None => continue,
            };
            crate::rules::run_wco_stages(comms, &mut disjunct_salad, &disjunct.plan, &disjunct.stages, potato());
            let projected = project_through_head(disjunct_salad, &disjunct.rule.head[0], self.use_site);
            result_facts.extend(projected.facts);
        }

        *salad = Salad::new(result_facts, self.head_terms.clone());
    }
}

/// Projects input salad onto pattern terms (by column position) and renames each pattern
/// term from use-site var to the corresponding disjunct head var (per `var_mapping`).
///
/// Returns `None` if the input salad is empty (nothing to project).
fn project_and_rename<'a>(
    salad: &Salad<&'a String>,
    pattern_terms: &[&'a String],
    var_mapping: &[(&'a String, &'a String)],
) -> Option<Salad<&'a String>> {
    let projection: Vec<Result<usize, Vec<u8>>> = pattern_terms.iter().map(|us_var| {
        let col = salad.terms.iter().position(|t| *t == *us_var)
            .expect("pattern term not in salad");
        Ok(col)
    }).collect();
    let mut action = Action::with_arity(salad.arity());
    action.projection = projection;

    let thresh = 200_000_000;
    let mut facts: FactLSM<Forest<Terms>> = FactLSM::default();
    let mut any = false;
    for forest in salad.facts.contents() {
        let projected = forest.act_on(&action, thresh);
        for f in projected { facts.extend([f]); }
        any = true;
    }
    if !any { return None; }

    // Translate pattern terms to disjunct head var space via var_mapping.
    let disjunct_terms: Vec<&'a String> = pattern_terms.iter().map(|us_var| {
        var_mapping.iter().find(|(us, _)| us == us_var).map(|(_, dj)| *dj)
            .expect("pattern term not in var_mapping")
    }).collect();

    Some(Salad::new(facts, disjunct_terms))
}

/// Projects a disjunct's result salad to the use-site's term space.
fn project_through_head<'a>(
    mut salad: Salad<&'a String>,
    disjunct_head: &Atom,
    use_site: &'a Atom,
) -> Salad<&'a String> {
    let head_terms: Vec<&'a String> = use_site.terms.iter().filter_map(|t| t.as_var()).collect();
    assert_eq!(
        head_terms.len(),
        use_site.terms.len(),
        "Sum atom does not yet support literal terms in the use-site atom"
    );
    assert_eq!(
        disjunct_head.terms.len(),
        use_site.terms.len(),
        "Disjunct head and use-site atom must have the same arity"
    );

    let mut action = Action::with_arity(salad.arity());
    action.projection = disjunct_head.terms.iter().map(|t| match t {
        Term::Var(name) => Ok(
            salad.terms.iter().position(|t2| t2.as_str() == name.as_str())
                .expect("disjunct head var not bound in disjunct's salad")
        ),
        Term::Lit(data) => Err(data.clone()),
    }).collect();

    let thresh = 200_000_000;
    let mut result_facts: FactLSM<Forest<Terms>> = FactLSM::default();
    if let Some(flat) = salad.facts.flatten() {
        result_facts.extend(flat.act_on(&action, thresh));
    }
    Salad::new(result_facts, head_terms)
}

/// Computes the `var_mapping` for a disjunct given a use-site atom and the disjunct's
/// head atom, restricted to a pattern of pre-bound use-site vars.
///
/// Returns `None` if any pattern position has a literal in the disjunct's head (means
/// seeded eval can't be used for this disjunct without literal-filter support).
fn compute_var_mapping<'a>(
    pattern: &BTreeSet<&'a String>,
    use_site: &'a Atom,
    disjunct_head: &'a Atom,
) -> Option<Vec<(&'a String, &'a String)>> {
    if use_site.terms.len() != disjunct_head.terms.len() { return None; }
    let mut mapping = Vec::with_capacity(pattern.len());
    for (us_term, dj_term) in use_site.terms.iter().zip(disjunct_head.terms.iter()) {
        let us_var = us_term.as_var()?;
        if !pattern.contains(us_var) { continue; }
        let dj_var = dj_term.as_var()?;  // None if disjunct head has a Lit here
        mapping.push((us_var, dj_var));
    }
    Some(mapping)
}
