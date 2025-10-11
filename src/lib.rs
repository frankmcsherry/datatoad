pub mod parse;
pub mod facts;

pub mod plan;

pub mod types {

    use crate::facts;

    #[derive(Clone, Debug)]
    pub struct Rule {
        pub head: Vec<Atom>,
        pub body: Vec<Atom>,
    }

    #[derive(Clone, Debug)]
    pub struct Atom {
        pub name: String,
        pub anti: bool,
        pub terms: Vec<Term>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Term {
        Var(String),
        Lit(String),
    }

    impl Term {
        /// If the term is `Term::Var(name)` return `Some(name)`.
        pub fn as_var(&self) -> Option<&String> { if let Term::Var(name) = self { Some(name) } else { None }}
    }

    #[derive(Default)]
    pub struct State {
        rules: Vec<Rule>,
        pub facts: facts::Relations,
    }

    impl State {
        /// Applies all rules to all facts.
        pub fn update(&mut self) {
            self.advance();
            while self.active() {
                for rule in self.rules.iter() {
                    crate::plan::implement(rule, false, &mut self.facts);
                }
                self.advance();
            }
        }

        pub fn advance(&mut self) {
            self.facts.advance();
        }

        fn active(&self) -> bool {
            self.facts.active()
        }

        pub fn extend(&mut self, rules: impl IntoIterator<Item=Rule>) {
            for rule in rules.into_iter() { self.push(rule); }
        }

        pub fn push(&mut self, rule: Rule) {
            if rule.body.is_empty() {
                for atom in rule.head.iter() {
                    let mut lits = Vec::with_capacity(atom.terms.len());
                    for term in atom.terms.iter() {
                        if let Term::Lit(text) = term {
                            lits.push(text.to_string().into_bytes());
                        }
                        else {
                            println!("Axioms not supported (all fact terms must be literals)");
                            continue;
                        }
                    }
                    let mut builder = facts::FactBuilder::default();
                    builder.push(lits.iter().map(|x| &x[..]));
                    self.facts
                        .entry(atom.name.to_owned())
                        .extend(builder.finish());
                }
            }
            else {
                crate::plan::implement(&rule, true, &mut self.facts);
                self.rules.push(rule);
            }
        }
    }

    /// Filters rows, re-orders columns, and groups by a prefix.
    #[derive(Clone, Default, Eq, Ord, PartialEq, PartialOrd)]
    pub struct Action<L> {
        /// Columns that must equal some literal.
        pub lit_filter: Vec<(usize, L)>,
        /// Lists of columns that must all be equal.
        pub var_filter: Vec<Vec<usize>>,
        /// The order of input columns or literals presented as output.
        pub projection: Vec<Result<usize, L>>,
        /// Number of input columns; important for testing identity.
        pub input_arity: usize,
    }

    impl Action<String> {
        /// Converts a body `Atom` to an `Action`.
        ///
        /// The names of the output columns can be read from `atom.terms`
        /// by way of the returned `Action::projection`.
        pub fn from_body(atom: &Atom) -> Self {
            let mut output = Action::default();
            let mut terms = std::collections::BTreeMap::default();
            for (index, term) in atom.terms.iter().enumerate() {
                match term {
                    Term::Var(name) => {
                        if !terms.contains_key(name) {
                            terms.insert(name, terms.len());
                            output.var_filter.push(Vec::default());
                            output.projection.push(Ok(index));
                        }
                        output.var_filter[terms[name]].push(index);
                    }
                    Term::Lit(data) => { output.lit_filter.push((index, data.to_owned())) }
                }
            }
            output.var_filter.retain(|list| list.len() > 1);
            output.input_arity = atom.terms.len();
            output
        }
        pub fn with_arity(arity: usize) -> Self { Self { input_arity: arity, ..Default::default() } }
    }

    impl<T> Action<T> {
        /// True when the action has no filters, and the projection is exactly `0 .. inner_arity`.
        pub fn is_identity(&self) -> bool {
            self.lit_filter.is_empty() && self.var_filter.is_empty() && self.projection.len() == self.input_arity && self.projection.iter().enumerate().all(|(index, proj)| proj.as_ref().ok() == Some(&index))
        }
        /// Produces a permuting action.
        ///
        /// It is important that `columns` is a permutation, in that it has exactly the values
        /// `0 .. k` for some `k`, although in an arbitrary order. The length of `columns` is
        /// used to infer the number of columns on which the permutation will act.
        pub fn permutation(columns: impl Iterator<Item = usize>) -> Self {
            let projection: Vec<Result<usize, T>> = columns.map(Ok).collect();
            Action {
                lit_filter: Vec::new(),
                var_filter: Vec::new(),
                input_arity: projection.len(),
                projection,
            }
        }
        /// True when filters are empty and each input column occurs exactly once, with no literals.
        ///
        /// Permutations are specifically helpful in that distinct fact sets that are permuted remain
        /// distinct, and we can avoid antijoins at various moments.
        pub fn is_permutation(&self) -> bool {
            self.lit_filter.is_empty() &&
            self.var_filter.is_empty() &&
            self.projection.len() == self.input_arity &&
            self.projection.iter().flatten().copied().collect::<std::collections::BTreeSet<_>>().into_iter().eq(0 .. self.input_arity)
        }
    }

    impl<T: std::fmt::Debug> std::fmt::Debug for Action<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.is_identity() {
                write!(f, "Identity")
            }
            else {
                let mut x = f.debug_struct("Action");
                if !self.lit_filter.is_empty() {
                    x.field("lit_filter", &self.lit_filter);
                }
                if !self.var_filter.is_empty() {
                    x.field("var_filter", &self.var_filter);
                }

                x.field("proj", &self.projection)
                .finish()
            }
        }
    }
}
