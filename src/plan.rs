use columnar::Len;
use crate::types::{Rule, Term};
use crate::facts::Relations;

/// Implements a provided rule by way of a provided plan.
///
/// Additionally, a rule-unique identifier allows the logic to create new relation names.
/// The `stable` argument indicates whether we need to perform a full evaluation or only the changes.
pub fn implement_plan(rule: &Rule, pos: usize, stable: bool, facts: &mut Relations) {
    Plan::from(rule).implement(pos, stable, facts);
}

use std::fmt::Debug;
use std::collections::{BTreeMap, BTreeSet};
use eggsalad::{Function, egraph::{EGraph, ENode, Id}};

pub struct Plan<'a> {
    /// The original rule, used for finishing detail.
    pub rule: &'a Rule,
    /// The sequence of operations to apply, in order.
    pub plan: Vec<ENode<Op>>,
}

impl<'a> From<&'a Rule> for Plan<'a> {
    fn from(rule: &'a Rule) -> Self {
        Self {
            rule,
            plan: rule_to_ir(rule),
        }
    }
}

impl<'a> Plan<'a> {
    pub fn implement(&self, pos: usize, stable: bool, facts: &mut Relations) {

        use crate::{facts::FactBuilder, join::join_with, types::Atom};
        use crate::facts::FactContainer;

        // We'll need the input arities to judge identity-ness.
        let arities =
        self.rule.body.iter()
            .map(|b| (&b.name, b.terms.len()))
            .collect::<BTreeMap<_,_>>();

        /// Like an `Action` but with the opportunity to produce literal output columns.
        struct TempAction {
            lit_filter: Vec<(usize, String)>,
            var_filter: Vec<Vec<usize>>,
            projection: Vec<Result<usize, String>>,
        }

        impl TempAction {
            fn is_ident(&self, arity: usize) -> bool {
                self.lit_filter.is_empty() &&
                self.var_filter.is_empty() &&
                self.projection.len() == arity &&
                self.projection.iter().enumerate().all(|(i,c)| c == &Ok(i))
            }
            fn from_action(action: &Action) -> Self {
                Self {
                    lit_filter: action.lit_filter.clone(),
                    var_filter: action.var_filter.clone(),
                    projection: action.projection.iter().cloned().map(Ok).collect(),
                }
            }

            fn from_head(atom: &Atom, action: &Action) -> Self {
                let mut local_names = BTreeMap::<&str, usize>::default();
                Self {
                    lit_filter: action.lit_filter.clone(),
                    var_filter: action.var_filter.clone(),
                    projection: atom.terms.iter().map(|term| {
                        match term {
                            Term::Var(name) => {
                                let new_pos = local_names.len();
                                Ok(action.projection[*local_names.entry(name).or_insert(new_pos)])
                            },
                            Term::Lit(data) => Err(data.clone()),
                        }
                    }).collect(),
                }
            }
            /// Extracts from `projection` the sequence of distinct columns in order, minus literals.
            ///
            /// These columns are the minimal information needed for `join` to operate, and the columns
            /// that are projected away can all be added back relatively cheaply, without complicating
            /// the process of fact production (and e.g. gumming up sorting with duplicates or literals).
            ///
            /// The method leaves `self` as any necessary follow-up actions, and if it is not the identity
            /// action then it should still be applied to the facts from the support.
            fn extract_support(&mut self) -> Vec<usize> {
                let mut result = Vec::default();
                for column in self.projection.iter_mut() {
                    if let Ok(col) = column {
                        if !result.contains(col) { result.push(*col); }
                        *col = result.iter().position(|c| c == col).unwrap();
                    }
                }
                result
            }
        }

        // The head needs planning assistance from its atoms, wrt literals and repeats.
        let (body, head) = self.plan.split_at(self.plan.len() - self.rule.head.len());

        let mut steps = BTreeMap::<Id,Vec<(Id, TempAction)>>::default();

        // For all map actions in the body, place in the step they derive from.
        for (index, node) in body.iter().enumerate() {
            if let Op::Map(action) = &node.op {
                steps.entry(node.args[0])
                        .or_insert_with(Vec::new)
                        .push((index, TempAction::from_action(action)));
            }
        }
        // For all map actions in the head, place in the step they derive from.
        for ((index, node), atom) in head.iter().enumerate().zip(self.rule.head.iter()) {
            if let Op::Map(action) = &node.op {
                steps.entry(node.args[0])
                        .or_insert_with(Vec::new)
                        .push((body.len() + index, TempAction::from_head(atom, action)));
            }
            else { panic!("Malformed plan; head atom is not a map!"); }
        }

        let mut names = BTreeMap::<Id, String>::default();
        for (idx, mut actions) in steps {
            let node = &self.plan[idx];
            match &node.op {
                Op::Var(name) => {

                    let mut todos = Vec::default();
                    for (id, action) in actions.iter() {
                        // Head productions should write at their own name.
                        if *id >= body.len() {
                            names.insert(*id, self.rule.head[id-body.len()].name.clone());
                            todos.push((*id, action));
                        }
                        // Each action that is an identity can repeat the input name.
                        else if action.is_ident(*arities.get(name).unwrap()) {
                            names.insert(*id, name.clone());
                        }
                        // Each action that is not an identity will create a new name,
                        // and deposit the loading results behind that name.
                        else {
                            let new_name = format!(".temp-{}-{}", pos, id);
                            names.insert(*id, new_name);
                            todos.push((*id, action));
                        }
                    }

                    if !todos.is_empty() {
                        let mut builders = vec![FactBuilder::default(); todos.len()];
                        if let Some(found) = facts.get(name) {
                            for layer in found.stable.contents().filter(|_| stable).chain(Some(&found.recent)) {
                                for ((_id, action), builder) in todos.iter().zip(builders.iter_mut()) {
                                    layer.apply(|fact| {
                                        let lit_match = action.lit_filter.iter().all(|(i,l)| fact[*i].as_slice() == l.as_bytes());
                                        let var_match = action.var_filter.iter().all(|idxs| idxs.iter().all(|i| fact[*i] == fact[idxs[0]]));
                                        if lit_match && var_match {
                                            builder.push(action.projection.iter().map(|i|
                                                match i { Ok(col) => fact[*col].as_slice(),
                                                            Err(lit) => lit.as_bytes() }));
                                        }
                                    });
                                }
                            }
                        }

                        for ((id, _action), builder) in todos.iter().zip(builders.into_iter()) {
                            let new_name = names.get(id).unwrap();
                            facts.entry(new_name.clone()).extend(builder.finish());
                        }
                    }

                }
                Op::Mul(2) => {

                    let arity = if let Op::Map(action) = &self.plan[node.args[0]].op { action.key_arity } else { panic!("malformed plan") };

                    // Ensure entries exist, tidy each by the length of the other, then get shared borrows.
                    let len0 = facts.entry(names.get(&node.args[0]).unwrap().clone()).recent.len();
                    let len1 = facts.entry(names.get(&node.args[1]).unwrap().clone()).recent.len();
                    facts.get_mut(names.get(&node.args[0]).unwrap()).unwrap().stable.tidy_through(2 * len1);
                    facts.get_mut(names.get(&node.args[1]).unwrap()).unwrap().stable.tidy_through(2 * len0);
                    let facts0 = facts.get(names.get(&node.args[0]).unwrap()).unwrap();
                    let facts1 = facts.get(names.get(&node.args[1]).unwrap()).unwrap();

                    // let projections = actions.iter().map(|(_,a)| &a.projection[..]).collect::<Vec<_>>();

                    // Before invoking `join_with`, we'll need to convert the projections from potentially repeating
                    // bindings interspersed with literals to distinct bindings, after which we post-process.
                    let projections = actions.iter_mut().map(|(_, a)| a.extract_support()).collect::<Vec<_>>();
                    let projections = projections.iter().map(|x| &x[..]).collect::<Vec<_>>();

                    let built = join_with(facts0, facts1, stable, arity, &projections[..]);

                    for ((id,action), built) in actions.iter().zip(built.into_iter()) {
                        let name = if *id >= body.len() { self.rule.head[id-body.len()].name.clone() } else { format!(".temp-{}-{}", pos, id) };
                        if action.is_ident(action.projection.len()) {
                            facts.entry(name.clone()).extend(built);
                        }
                        else {
                            // The action included repetitions or literals.
                            // This is relatively easy to fix in a trie layout, and we should do that, but for the moment we go slow.
                            let mut act = crate::types::Action::default();
                            act.projection = action.projection.clone();
                            facts.entry(name.clone()).extend(built.into_iter().flat_map(|b| b.act_on(&act)));
                        }
                        names.insert(*id, name);
                    }

                }
                x => { panic!("Invalid plan: {:?}", x); }
            }
        }

    }
}

/// Converts a multi-head rule into assembly instructions.
///
/// The list of expressions should be built in order, and their identifiers
/// reference the ordinal position in the list, i.e. in `0 .. list.len()`.
///
/// The last `rule.head.len()` expressions correspond directly to the heads.
/// Their expressions only compute the support of the head atom, which means
/// that someone will need to slot those values in the right place along with
/// repetitions and literals.
pub fn rule_to_ir(rule: &Rule) -> Vec<ENode<Op>> {

    let mut head = Action::default();

    // Columns introduced with the same names (equality constraints).
    let mut bind = BTreeMap::<&str, Vec<usize>>::default();
    let mut prog = vec![Op::Mul(rule.body.len())];

    // Each atom is introduced with a no-op action.
    // Head rules will introduce filters and projections.
    for atom in rule.body.iter() {
        prog.extend([
            Op::nop(atom.terms.len()),
            Op::Var(atom.name.clone()),
        ]);
        for term in atom.terms.iter() {
            let column = head.projection.len();
            head.projection.push(column);
            match term {
                Term::Var(name) => { bind.entry(name).or_default().push(column); },
                Term::Lit(data) => { head.lit_filter.push((column, data.to_string())); },
            }
        }
    }
    head.var_filter.extend(bind.values().filter(|l| l.len() > 1).cloned());

    // Houses our options for the rule implementation.
    let mut e_graph: EGraph<Op> = Default::default();

    // We'll need `prog` for reference once we've saturated.
    let join = e_graph.insert(prog.clone());

    // Each head atom should personalize `act` and apply it to `join`.
    // The personalization projects out only the distinct names
    let heads = rule.head.iter().map(|atom| {
        let mut head_names = BTreeSet::<&str>::default();
        let mut head = head.clone();
        head.projection.clear();
        for term in atom.terms.iter() {
            match term {
                Term::Var(name) => {
                    if head_names.insert(name) {
                        head.projection
                            .push(bind.get(name.as_str()).unwrap()[0]);
                    }
                }
                Term::Lit(____) => { },
            }
        }

        e_graph.ensure(ENode::new(Op::Map(head.clone()), [join]));
        head
    }).collect::<Vec<_>>();

    // Time to optimize the e-graph!
    // We could sequence these optimizations rather than saturate;
    // this is based on all expressions starting as cross joins.
    e_iterate(&mut e_graph, &[
        &MulPermute,
        &MulPartition,
        &MulElimination,
        &MapPushdown,
    ]);

    // The e-graph is now locked down, so we can grab e-class identifiers.
    let body = e_graph.insert(prog);
    let heads = heads.into_iter().map(|a| e_graph.ensure(ENode::new(Op::Map(a), [body]))).collect::<Vec<_>>();

    // Establish a predicate for whether we consider an e-node or not.
    //
    // Naively, we imagine the cardinality as proportional to |vals|^cols,
    // for `cols` the number of independent (unequated) columns. For `Map`
    // this is its projected arity, and for `Mul` this is the sum of the
    // input arities, minus the key arity for all but one of the inputs.
    let filter = |node: &ENode<Op>, graph: &EGraph<Op>, thresh: usize| {
        match &node.op {
            Op::Var(_) => true,
            Op::Map(a) => {
                // Maps will do work proportional to their projection length.
                a.projection.len() <= thresh &&
                // All filters should be empty, or this should have a Var input.
                ((a.lit_filter.is_empty() && a.var_filter.is_empty()) || graph.members[&node.args[0]].iter().all(|x| if let Op::Var(_) = x.op { true } else { false }) )
            },
            Op::Mul(_) => {
                // Muls will do work proportional to the input key length
                // plus the sum of non-key columns over all inputs.
                let mut arity = 0;
                let mut key_arity = None;
                for a in node.args.iter() {
                    if let Op::Map(act) = &graph.members.get(a).unwrap().first().unwrap().op {
                        arity += act.projection.len() - act.key_arity;
                        key_arity = Some(act.key_arity);
                    }
                    else { panic!("Mal-typed expression"); }
                }
                let key_arity = key_arity.unwrap();
                arity + key_arity <= thresh
            }
        }
    };

    // For increasing `k`, look for an extraction that supports all heads.
    let (cost, need) = (0 .. ).filter_map(|k| {
        let eggstraction = eggstract(&e_graph, |n, g| filter(n,g,k));
        if heads.iter().all(|h| eggstraction.contains_key(h)) {
            Some((k, eggstraction))
        }
        else { None }
    }).next().unwrap();

    // We want to consider all ways of producing all heads.
    // Cross each list of support options, unioning the support.
    let mut supported = BTreeSet::default();
    supported.insert(BTreeSet::<Id>::default());
    for head in heads.iter() {
        supported = std::mem::take(&mut supported).into_iter().flat_map(|s| {
            need.get(head).unwrap().iter().map(move |head_option| s.union(head_option).copied().collect::<BTreeSet<Id>>())
        }).collect::<BTreeSet<_>>();
    }

    // Optimize for memory then computation.
    let mut best = supported.into_iter().min_by_key(|option| {
        let mut muls = 0;
        let mut maps = 0;
        let mut vars = 0;
        for class in option.iter() {
            match &e_graph.members.get(class).unwrap().first().unwrap().op {
                Op::Map(_) => { maps += 1; },
                Op::Mul(_) => { muls += 1; },
                Op::Var(_) => { vars += 1; },
            }
        }
        (maps, muls, vars)
    }).unwrap();

    best.extend(heads.iter().copied());

    // With `best` in hand, we can extract specific e-nodes from each e-class.
    let mut order = Vec::with_capacity(best.len());
    let mut e_nodes = BTreeMap::<Id, ENode<Op>>::default();
    // TODO: This loops forever if you have two heads with the same e-class.
    while e_nodes.len() < best.len() {
        for id in best.iter() {
            if !e_nodes.contains_key(id) {
                let mut active_nodes =
                e_graph.members.get(id).unwrap().iter()
                                .filter(|n| filter(n, &e_graph, cost))
                                .filter(|n| n.args.iter().all(|a| e_nodes.contains_key(a)));
                if let Some(node) = active_nodes.next() {
                    e_nodes.insert(*id, node.clone());
                    order.push(*id);
                }
            }
        }
    }

    //
    order.retain(|x| !heads.contains(x));
    order.extend(heads);
    let remap = order.iter().enumerate().map(|(i,o)| (o, i)).collect::<BTreeMap<_,_>>();

    e_nodes
        .into_iter()
        .map(|(c,n)| (remap[&c], ENode::new(n.op, n.args.into_iter().map(|a| remap[&a]))))
        .collect::<BTreeMap<_,_>>()
        .into_values()
        .collect()
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Op {
    Var(String),    // Data by name
    Map(Action),    // Linear action (filter, project)
    Mul(usize),     // Join by key (variadic arity)
}

impl Op {
    pub fn var(name: &str) -> Self { Op::Var(name.to_string()) }
    pub fn map(p: impl IntoIterator<Item=usize>, a: usize) -> Self { Op::Map(Action::shuffle(p, a)) }
    pub fn mul(a: usize) -> Self { Op::Mul(a) }
    pub fn nop(a: usize) -> Self { Op::Map(Action::nop(a)) }
}

impl Function for Op {
    fn inputs(&self) -> usize {
        match self {
            Op::Var(_) => 0,
            Op::Map(_) => 1,
            Op::Mul(k) => *k,
        }
    }
}

/// Filters rows, re-orders columns, and groups by a prefix.
#[derive(Clone, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Action {
    /// Columns that must equal some literal.
    lit_filter: Vec<(usize, String)>,
    /// Lists of columns that must all be equal.
    var_filter: Vec<Vec<usize>>,
    /// The order of input columns presented as output.
    projection: Vec<usize>,
    /// The prefix length by which the rows are grouped.
    key_arity:  usize,
}

impl Debug for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut x = f.debug_struct("Action");
        if !self.lit_filter.is_empty() {
            x.field("lit_filter", &self.lit_filter);
        }
        if !self.var_filter.is_empty() {
            x.field("var_filter", &self.var_filter);
        }

        x.field("proj", &self.projection)
        .field("arity", &self.key_arity)
        .finish()
    }
}

impl Action {
    /// Creates a no-op action on a specified number of columns.
    pub fn nop(arity: usize) -> Self { Action::shuffle(0..arity, 0) }
    /// Creates an action that permutes and keys, but does not filter.
    pub fn shuffle<I>(projection: I, key_arity: usize) -> Self
    where
        I: IntoIterator<Item=usize>,
    {
        Action {
            var_filter: Vec::default(),
            lit_filter: Vec::default(),
            projection: projection.into_iter().collect(),
            key_arity,
        }
    }
    /// Applies an action to each referenced column.
    pub fn permute(&mut self, cols: impl Fn(&mut usize)) {
        for (col, _) in self.lit_filter.iter_mut() { cols(col) }
        for list in self.var_filter.iter_mut() {
            for col in list.iter_mut() { cols(col); }
            list.sort();
            list.dedup();
        }
        for col in self.projection.iter_mut() { cols(col); }
    }
    pub fn compose(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.permute(|x| *x = other.projection[*x]);
        result.lit_filter.extend(other.lit_filter.clone());
        result.var_filter.extend(other.var_filter.clone());
        result
    }
}

use actions::{MulPermute, MulPartition, MulElimination, MapPushdown, e_iterate};
mod actions {

    use std::collections::BTreeMap;
    use eggsalad::{Function, egraph::{EGraph, ENode}};
    use super::{Op, Action};

    pub trait ERule {
        /// Act on the e-graph. No rules, despite the name.
        fn act(&self, e_graph: &mut EGraph<Op>);
    }

    pub fn e_iterate(e_graph: &mut EGraph<Op>, e_rules: &[& dyn ERule]) {
        let mut done = false;
        while !done {
            for rule in e_rules.iter() {
                rule.act(e_graph);
            }
            done = !e_graph.refresh();
            e_graph.validate();
        }
    }

    /// Equates `[Map, Mul(k), A, B, .. K]` with all permutations of `[A .. K]`.
    pub struct MulPermute;
    impl ERule for MulPermute {
        fn act(&self, e_graph: &mut EGraph<Op>) {
            let mut equate = Vec::new();
            for (class, nodes) in e_graph.members.iter() {
                for node1 in nodes.iter() {
                    if let Op::Map(act1) = &node1.op {
                        for node2 in e_graph.members.get(&node1.args[0]).unwrap().iter() {
                            if let Op::Mul(k) = &node2.op {

                                // With k arguments to permute, each requires a column permutation for `act1`.
                                let mut arities = Vec::with_capacity(node2.args.len());
                                for class in node2.args.iter() {
                                    if let Op::Map(act) = &e_graph.members.get(class).unwrap().first().unwrap().op {
                                        arities.push(act.projection.len());
                                    }
                                    else { panic!("Mal-typed expression") }
                                }

                                let old_input = arities.iter().enumerate().flat_map(|(i,a)| std::iter::repeat(i).enumerate().take(*a)).collect::<Vec<_>>();

                                use itertools::Itertools;
                                for permutation in (0 .. *k).permutations(*k) {

                                    let args = permutation.iter().map(|i| node2.args[*i]).collect::<Vec<_>>();
                                    let offset = permutation.iter().scan(0, |off, ind| { *off += arities[*ind]; Some(*off - arities[*ind]) }).collect::<Vec<_>>();
                                    let inv = permutation.iter().copied().enumerate().map(|(i,p)| (p,i)).collect::<BTreeMap<_,_>>();

                                    let mut act = act1.clone();
                                    act.permute(|c| {
                                        let (col, inp) = old_input[*c];
                                        *c = offset[inv[&inp]] + col;
                                    });

                                    let cmd1: Vec<EAct<Op>> = vec![EAct::EClass(*class)];
                                    // `[Mul, Map, A, B, .. K]`
                                    let mut cmd2 = vec![
                                        EAct::Operator(Op::Map(act)),
                                        EAct::Operator(Op::Mul(*k)),
                                    ];
                                    cmd2.extend(args.into_iter().map(EAct::EClass));
                                    equate.push((cmd1, cmd2));

            }   }   }   }   }   }

            for (a1, a2) in equate {
                let id1 = apply(&a1, e_graph);
                let id2 = apply(&a2, e_graph);
                e_graph.merge(id1, id2);
            }
        }
    }

    /// Equates `[Mul(k), A, B, .. K]` with `[Mul(2), Map, Mul(j), A .. J, Map, Mul(k-j), .. K]`.
    pub struct MulPartition;
    impl ERule for MulPartition {
        fn act(&self, e_graph: &mut EGraph<Op>) {
            let mut equate = Vec::new();
            for (class, nodes) in e_graph.members.iter() {
                for node in nodes.iter() {
                    if let Op::Mul(k) = &node.op {
                        // We only have something interesting to propose for multi-way joins.
                        if *k > 2 {
                            // Arities are important for the new `Map`s we introduce.
                            let mut arities = Vec::with_capacity(node.args.len());
                            let mut key_arity = None;
                            for class in node.args.iter() {
                                if let Op::Map(act) = &e_graph.members.get(class).unwrap().first().unwrap().op {
                                    arities.push(act.projection.len());
                                    key_arity = Some(act.key_arity);
                                }
                                else { panic!("Mal-typed expression") }
                            }
                            let key_arity = key_arity.unwrap();

                            // Each space between two arguments could be a break point.
                            // There are k-1 spaces, and so 2^{k-1} possible breaks.
                            use itertools::Itertools;
                            for mut splits in (1 .. *k-1).powerset() {
                                if !splits.is_empty() {
                                    splits.push(*k);
                                    let mut lower = 0;
                                    let cmd1: Vec<EAct<Op>> = vec![EAct::EClass(*class)];
                                    let mut cmd2 = vec![EAct::Operator(Op::Mul(splits.len()))];
                                    for upper in splits {
                                        let arity = (lower .. upper).map(|i| arities[i]).sum::<usize>();
                                        if upper - lower > 1 {
                                            cmd2.push(EAct::Operator(Op::Map(Action::shuffle(0 .. arity, key_arity))));
                                            cmd2.push(EAct::Operator(Op::Mul(upper-lower)));
                                            cmd2.extend((lower .. upper).map(|i| EAct::EClass(node.args[i])));
                                        }
                                        else {
                                            cmd2.push(EAct::EClass(node.args[lower]));
                                        }
                                        lower = upper;
                                    }
                                    equate.push((cmd1, cmd2));

            }   }   }   }   }   }

            for (a1, a2) in equate {
                let id1 = apply(&a1, e_graph);
                let id2 = apply(&a2, e_graph);
                e_graph.merge(id1, id2);
            }
        }
    }

    /// Equates `[A, Mul(1), B]` with `[C]` for C equal to A composed with B.
    pub struct MulElimination;
    impl ERule for MulElimination {
        fn act(&self, e_graph: &mut EGraph<Op>) {
            let mut equate = Vec::new();
            for (class, nodes) in e_graph.members.iter() {
                for node1 in nodes.iter() {
                    if let Op::Map(act1) = &node1.op {
                        for node2 in e_graph.members.get(&node1.args[0]).unwrap().iter() {
                            if let Op::Mul(1) = &node2.op {

                                for node3 in e_graph.members.get(&node2.args[0]).unwrap().iter() {
                                    if let Op::Map(act3) = &node3.op {
                                        let act = act1.compose(act3);
                                        let cmd1: Vec<EAct<Op>> = vec![EAct::EClass(*class)];
                                        let cmd2 = vec![
                                            EAct::Operator(Op::Map(act)),
                                            EAct::EClass(node3.args[0]),
                                        ];
                                        equate.push((cmd1, cmd2));

            }   }   }   }   }   }   }

            for (a1, a2) in equate {
                let id1 = apply(&a1, e_graph);
                let id2 = apply(&a2, e_graph);
                e_graph.merge(id1, id2);
            }
        }
    }

    /// Acts on `[Map, Mul, Map, _, Map, _]` in several ways.
    ///
    /// 1. Literal filters are pushed down to any corresponding inputs.
    /// 2. Variable filters are pushed to each input, and converted to keys if across inputs.
    /// 3. Projections are pushed down to each input.
    pub struct MapPushdown;
    impl ERule for MapPushdown {
        fn act(&self, e_graph: &mut EGraph<Op>) {

            let mut equate = Vec::new();

            // `[Map, Mul, Map, A, Map, B]`
            for (class, nodes) in e_graph.members.iter() {
                for node1 in nodes.iter() { if let Op::Map(act1) = &node1.op {
                for node2 in e_graph.members.get(&node1.args[0]).unwrap().iter() { if let Op::Mul(2) = &node2.op {
                for node3 in e_graph.members.get(&node2.args[0]).unwrap().iter() { if let Op::Map(act3) = &node3.op {
                for node4 in e_graph.members.get(&node2.args[1]).unwrap().iter() { if let Op::Map(act4) = &node4.op {

                // We'll fire only if all actions but `act1` are key-free.
                // Should still work out, if we start with cross joins and introduce keys later.
                if (act3.key_arity == 0 && act3.lit_filter.is_empty() && act3.var_filter.is_empty()) &&
                (act4.key_arity == 0 && act4.lit_filter.is_empty() && act4.var_filter.is_empty()) {

                    // We have found a pattern, and need to figure out what to do with it.
                    let a = node3.args[0];
                    let b = node4.args[0];

                    // Each list of variable equivalences can be pushed down, and create keys.
                    // Equivalent variables pushed down also projects away all but one column.
                    // Equivalences across the inputs result in keying for each of the inputs.
                    // Literal equivalences are pushed down either branch, or both if possible.
                    let mut act_0 = act1.clone();
                    let mut act_a = Action::default();
                    let mut act_b = Action::default();
                    let mut keys = Vec::new();
                    for list in act_0.var_filter.drain(..) {
                        let mut list_a = Vec::new();
                        let mut list_b = Vec::new();
                        for col in list.iter() {
                            if *col < act3.projection.len() { list_a.push(*col); }
                            else { list_b.push(*col - act3.projection.len()); }
                        }
                        if let (Some(a), Some(b)) = (list_a.first(), list_b.first()) {
                            keys.push((*a, *b));
                        }
                        if list_a.len() > 1 { act_a.var_filter.push(list_a); }
                        if list_b.len() > 1 { act_b.var_filter.push(list_b); }
                    }
                    for (col, lit) in act_0.lit_filter.drain(..) {
                        if col < act3.projection.len() { act_a.lit_filter.push((col, lit)); }
                        else { act_b.lit_filter.push((col - act3.projection.len(), lit)); }
                    }

                    // We will have this many keys.
                    act_a.key_arity = keys.len();
                    act_b.key_arity = keys.len();

                    // Now to sort out the projections
                    // We need to preserve any columns that occur in `act_0`.
                    // Ideally that would be just the projection, but we skipped literal filters.
                    let mut demanded = std::collections::BTreeSet::default();
                    demanded.extend(act_0.lit_filter.iter().map(|(i,_)| *i));
                    demanded.extend(act_0.projection.iter().copied());
                    for (key_a, key_b) in keys.iter() {
                        act_a.projection.push(*key_a);
                        act_b.projection.push(*key_b);
                        demanded.remove(key_a);
                        demanded.remove(&(key_b + act3.projection.len()));
                    }
                    for col in demanded {
                        if col < act3.projection.len() { act_a.projection.push(col); }
                        else { act_b.projection.push(col - act3.projection.len()); }
                    }

                    let mut act0_map = BTreeMap::default();
                    for col in act_a.projection.iter() { act0_map.insert(*col, act0_map.len()); }
                    for col in act_b.projection.iter() { act0_map.insert(act3.projection.len() + *col, act0_map.len()); }
                    act_0.permute(|c| *c = *act0_map.get(c).unwrap());

                    act_a.permute(|c| { *c = act3.projection[*c]; });
                    act_b.permute(|c| { *c = act4.projection[*c]; });

                    let cmd1: Vec<EAct<Op>> = vec![EAct::EClass(*class)];
                    // `[Map, Mul, Map A, Map, B]`
                    let cmd2 = vec![
                        EAct::Operator(Op::Map(act_0)),
                        EAct::Operator(Op::Mul(2)),
                        EAct::Operator(Op::Map(act_a)),
                        EAct::EClass(a),
                        EAct::Operator(Op::Map(act_b)),
                        EAct::EClass(b),
                    ];
                    equate.push((cmd1, cmd2));

                }
            // Avert your eyes
            }}}}}}}}}

            for (a1, a2) in equate {
                let id1 = apply(&a1, e_graph);
                let id2 = apply(&a2, e_graph);
                e_graph.merge(id1, id2);
            }

        }
    }

    use eggsalad::egraph::Id;
    #[derive(Debug)]
    enum EAct<T: Function> {
        Operator(T),
        EClass(Id),
    }

    fn apply<T: Clone + Ord + Function + std::fmt::Debug>(list: &[EAct<T>], e_graph: &mut EGraph<T>) -> Id {

        let mut ids = Vec::new();
        for sym in list.iter().rev() {
            match sym {
                EAct::Operator(op) => {
                    let inputs = op.inputs();
                    let args = &ids[ids.len() - inputs..];
                    let e_node = ENode::new(op.clone(), args.iter().cloned().rev());
                    ids.truncate(ids.len() - inputs);
                    ids.push(e_graph.ensure(e_node));
                }
                EAct::EClass(id) => {
                    ids.push(*id);
                }
            }
        }
        ids.pop().unwrap()
    }
}

use eggstraction::eggstract;
mod eggstraction {

    use std::collections::{BTreeMap, BTreeSet};

    use eggsalad::egraph::{EGraph, ENode, Id};
    use super::Op;

    pub fn eggstract(e_graph: &EGraph<Op>, active: impl Fn(&ENode<Op>, &EGraph<Op>)->bool) -> BTreeMap<Id, BTreeSet<BTreeSet<Id>>> {

        // We'll use the cost function that all k-arity relations are equally expensive,
        // and arbitrarily more expensive than a lesser arity relation.

        // Each e-class could be realized through the instantiation of various sets of other e-classes.
        // Any member can propose the e-classes that would work for it, and the distinct lists are the candidates.

        // Map from e-class to list of sets of e-classes each sufficient to reify an instance of the class.
        let mut needs: BTreeMap<Id, BTreeSet<BTreeSet<Id>>> = BTreeMap::default();
        let mut done = false;
        while !done {
            let prev = needs.clone();
            // We can saturate, but we can also stop once new costs are greater than the current best.

            for (class, nodes) in e_graph.members.iter() {
                let mut options = BTreeSet::default();
                for node in nodes.iter() {
                    if active(node, e_graph) {
                        match &node.op {
                            Op::Var(_) => { options.insert(BTreeSet::default()); },
                            Op::Mul(k) => {
                                assert_eq!(node.args.len(), *k);
                                let mut fold = BTreeSet::default();
                                fold.insert(BTreeSet::<Id>::default());
                                // Repeatedly cross each child with `fold`.
                                for child in node.args.iter().copied() {
                                    if let Some(need) = needs.get(&child) {
                                        fold =
                                        fold.into_iter()
                                            .flat_map(|f| need.iter().map(move |n| n.union(&f).copied().chain(Some(child)).collect()))
                                            .collect();
                                    }
                                    else { fold.clear(); }
                                }
                                options.extend(fold);
                            },
                            Op::Map(_) => {
                                if let Some(need) = needs.get(&node.args[0]) {
                                    options.extend(need.iter().map(|n| n.iter().copied().chain(Some(node.args[0])).collect()));
                                }
                            },
                        }
                    }
                }
                if !options.is_empty() { needs.entry(*class).or_default().extend(options); }
            }

            for need in needs.values_mut() {
                *need = thin(std::mem::take(need));
            }

            done = prev == needs;
        }

        needs
    }

    /// Remove any element that is a superset of another.
    fn thin(options: impl IntoIterator<Item=BTreeSet<Id>>) -> BTreeSet<BTreeSet<Id>> {
        let mut next = BTreeSet::default();
        for set in options {
            if next.iter().all(|x: &BTreeSet<Id>| !x.is_subset(&set)) {
                next.retain(|x| !set.is_subset(x));
                next.insert(set);
            }
        }
        next
    }
}
