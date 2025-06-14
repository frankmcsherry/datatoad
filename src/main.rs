use std::collections::BTreeMap;

pub mod parse;
pub mod facts;
pub mod join;

fn main() {

    let mut state = State::default();

    for filename in std::env::args().skip(1) {

        // Read input data from a handy file.
        use std::fs::File;
        use std::io::{BufRead, BufReader};

        let mut dict: BTreeMap<String, facts::FactBuilder> = BTreeMap::default();
        let file = BufReader::new(File::open(filename).unwrap());
        for readline in file.lines() {
            let line = readline.expect("read error");
            if !line.is_empty() && !line.starts_with('#') {
                let mut elts = line.split_whitespace().rev();
                if let Some(name) = elts.next() {
                    dict.entry(name.to_string())
                        .or_default()
                        .push(elts.rev().map(|x| x.as_bytes()));
                }
            }
        }
        for (name, facts) in dict { state.facts.entry(name).or_default().add_set(facts); }
    }
    state.update();

    use std::io::Write;
    println!("");
    print!("> ");
    let _ = std::io::stdout().flush();

    let mut text = String::new();
    while let Ok(_size) = std::io::stdin().read_line(&mut text) {

        let timer = std::time::Instant::now();

        if let Some(parsed) = parse::datalog(&text) {
            state.extend(parsed);
            state.update();
        }

        else {
            match text.trim() {
                ".list" => {
                    for (name, facts) in state.facts.iter() {
                        println!("\t{}:\t{:?}", name, facts.len());
                    }    
                }
                ".load" => {

                }
                ".save" => {

                }
                _ => {
                    println!("Parse failure: {:?}", text);
                }
            }
        }

        println!("{:?}", timer.elapsed());

        println!("");
        print!("> ");
        let _ = std::io::stdout().flush();
        text.clear();
    }

}

use types::{Rule, Atom, Term, State};

mod types {

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
        /// Applies all rules to all facts, and indicates if new facts were
        pub fn update(&mut self) {
            self.advance();
            while self.active() {
                for (index, rule) in self.rules.iter().enumerate() {
                    let rule_plan = crate::join::JoinPlan::from(rule);
                    join::implement_plan(rule, &rule_plan, index, false, &mut self.facts);
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
                let rule_plan = crate::join::JoinPlan::from(&rule);
                join::implement_plan(&rule, &rule_plan, self.rules.len(), true, &mut self.facts);
                self.rules.push(rule);
            }
        }
    }
}
