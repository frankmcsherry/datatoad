//! Sum atom: an `ExecAtom`/`PlanAtom` for virtual relation references.
//!
//! When a body atom names a virtual relation (declared via `.decl name(_, _, ...) virtual`),
//! the planner constructs a `SumPlan` for it (lightweight, no apparatus) and the executor
//! constructs a `Sum` whose disjuncts are the apparatus pre-built from each defining rule.
//!
//! For now: `Sum::seed` evaluates each disjunct, projects through the disjunct's head, and
//! unions the results. `Sum::count` is a no-op (sum atoms never propose values via the count
//! protocol). `Sum::join` is not yet implemented — the seeded variant would be needed for
//! sum atoms in non-driver positions.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use crate::comms::Comms;
use crate::facts::{FactContainer, FactLSM, Forest, Terms};
use crate::rules::exec::{self, Salad};
use crate::rules::plan::{self, PlanAtom};
use crate::rules::{ExecAtom, DriverApparatus};
use crate::types::{Action, Atom, Rule, Term};

/// A `&'static String` placeholder used as the count-metadata column name in `wco_join`.
///
/// Lives 'static so it can coerce to any `&'a String`. Necessary because Sum's `seed`
/// runs `wco_join` on salads whose term type is `&'a String` for an `'a` we don't own;
/// a local `String` declared inside `seed` wouldn't live long enough.
fn potato() -> &'static String {
    static POTATO: OnceLock<String> = OnceLock::new();
    POTATO.get_or_init(|| ".potato".to_string())
}

/// PlanAtom proxy for virtual relation references — no apparatus, just term info.
///
/// `terms` returns the use-site's variable terms; `ground` conservatively returns all
/// unbound use-site terms (over-claims what the sum can substantiate, which keeps the
/// planner happy at the cost of possibly suboptimal plans).
pub struct SumPlan<'a> {
    pub head_terms: BTreeSet<&'a String>,
}

impl<'a> PlanAtom<&'a String> for SumPlan<'a> {
    fn terms(&self) -> BTreeSet<&'a String> { self.head_terms.clone() }
    fn ground(&self, terms: &BTreeSet<&'a String>) -> BTreeSet<&'a String> {
        self.head_terms.difference(terms).copied().collect()
    }
}

/// One disjunct of a sum: a defining rule plus its pre-built evaluation apparatus.
pub struct Disjunct<'a> {
    /// The defining rule (head names the virtual; body is what gets evaluated).
    pub rule: &'a Rule,
    /// Plans returned by `plan_rule` for this disjunct's body.
    pub plans: plan::Plans<usize, &'a String>,
    /// Loads returned by `plan_rule` for this disjunct's body.
    pub loads: plan::Loads<usize, &'a String>,
    /// Pre-built per-driver apparatus for executing the disjunct.
    pub apparatus: DriverApparatus<'a>,
}

/// ExecAtom for a virtual relation reference. Holds the use-site atom (for term mapping
/// to the parent's variables), cached use-site variable terms, and per-disjunct apparatus.
pub struct Sum<'a> {
    /// The atom in the parent body that referenced the virtual.
    pub use_site: &'a Atom,
    /// Cached use-site variable terms (for `ExecAtom::terms`).
    pub head_terms: Vec<&'a String>,
    /// Pre-built apparatus for each defining rule.
    pub disjuncts: Vec<Disjunct<'a>>,
}

impl<'a> ExecAtom<&'a String> for Sum<'a> {
    fn terms(&self) -> &[&'a String] { &self.head_terms[..] }

    fn seed(&self, comms: &mut Comms, recent: bool) -> Salad<&'a String> {
        let mut result = Salad::new(FactLSM::default(), self.head_terms.clone());
        for disjunct in &self.disjuncts {
            let disjunct_head = &disjunct.rule.head[0];
            for ((_plan_atom, plan), (driver, stages)) in disjunct.plans.iter().zip(&disjunct.apparatus) {
                let mut salad = driver.seed(comms, recent);
                for ((_, terms, order), others) in plan.iter().zip(stages) {
                    exec::wco_join(comms, &mut salad, terms, others, potato(), &order[..]);
                }
                // Project through the disjunct's head to the use-site's term space.
                let projected = project_through_head(salad, disjunct_head, self.use_site);
                result.facts.extend(projected.facts);
            }
        }
        result
    }

    fn count(&self, _comms: &mut Comms, _salad: &mut Salad<&'a String>, _added: &BTreeSet<&'a String>, _index: u8) {
        // No-op: sum atoms never propose values during the count protocol. Some other
        // atom in the join always wins; the sum acts purely as a validator via `join`.
    }

    fn join(&self, comms: &mut Comms, salad: &mut Salad<&'a String>, added: &BTreeSet<&'a String>, after: &[&'a String]) {
        // Materialize the sum's full contents and delegate to the data-atom join logic.
        // This loses the WCOJ-as-participant property — the sum is fully expanded for
        // every join call — but it lets sums work as non-driver participants in joins.
        // Optimizing by caching across calls or by genuine count-protocol participation
        // is future work.
        let materialized = self.seed(comms, false);
        let facts: Vec<Forest<Terms>> = materialized.facts.into_iter().collect();
        let temp: (Vec<Forest<Terms>>, Vec<&'a String>, Option<Forest<Terms>>) =
            (facts, materialized.terms, None);
        temp.join(comms, salad, added, after);
    }
}

/// Projects a disjunct's result salad to the use-site's term space.
///
/// For each position of `use_site.terms`:
///   * If the corresponding position of `disjunct_head.terms` is `Var(name)`, take the
///     value from `salad`'s column for that name.
///   * If it's `Lit(data)`, emit the literal.
///
/// The resulting salad's term names are the use-site's variable terms.
///
/// Currently asserts the use-site has only variable terms (no literal filters). Lifting
/// that restriction would require additional filtering by the use-site's literals.
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
