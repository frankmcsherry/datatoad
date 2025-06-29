pub mod parse;
pub mod facts;
pub mod join;

pub mod types {

    use crate::{facts, join};

    #[derive(Clone, Debug)]
    pub struct Rule {
        pub head: Vec<Atom>,
        pub body: Vec<Atom>,
    }

    #[derive(Clone, Debug)]
    pub struct Atom {
        pub name: String,
        pub terms: Vec<Term>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Term {
        Var(String),
        Lit(String),
    }

    #[derive(Default)]
    pub struct State {
        rules: Vec<Rule>,
        pub facts: facts::Facts,
    }

    impl State {
        /// Applies all rules to all facts.
        pub fn update(&mut self) {
            self.advance();
            while self.active() {
                for (index, rule) in self.rules.iter().enumerate() {
                    join::implement_plan(rule, index, false, &mut self.facts);
                }
                self.advance();
            }
        }

        pub fn advance(&mut self) {
            for facts in self.facts.values_mut() {
                facts.advance();
            }
        }

        fn active(&self) -> bool {
            self.facts.values().any(|x| x.active())
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
                    builder.push(lits);
                    self.facts
                        .entry(atom.name.to_owned())
                        .or_default()
                        .add_set(builder);
                }
            }
            else {
                join::implement_plan(&rule, self.rules.len(), true, &mut self.facts);
                self.rules.push(rule);
            }
        }
    }
}
