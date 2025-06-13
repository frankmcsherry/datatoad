use std::collections::{BTreeMap, BTreeSet};
use columnar::{Columnar, Container, Index, Len};
use crate::{Rule, Atom, Term};
use crate::facts::{Fact, Facts, FactBuilder, FactContainer, FactSet};

/// Implements a provided rule by way of a provided plan.
///
/// Additionally, a rule-unique identifier allows the logic to create new relation names.
/// The `stable` argument indicates whether we need to perform a full evaluation or only the changes.
pub fn implement_plan(rule: &Rule, plan: &JoinPlan, pos: usize, stable: bool, facts: &mut Facts) {

    let name = format!(".temp-{:?}", pos);

    let mut names = Vec::with_capacity(rule.body.len());

    // First, for each body plan apply the plan to a newly named relation.
    for (index, (plan, atom)) in plan.bodys.iter().zip(rule.body.iter()).enumerate() {

        if plan.identity() {
            facts.entry(atom.name.clone()).or_default();
            names.push(atom.name.clone());
        }
        else {
            let new_name = format!("{}-{:?}-in", name, index);
            let mut builder = FactBuilder::default();
            let found = facts.entry(new_name.clone()).or_default();
            if stable {
                for layer in found.stable.layers.iter() {
                    plan.apply(layer, &mut builder);
                }
            }
            plan.apply(&found.recent, &mut builder);

            facts.get_mut(&new_name).unwrap().add_set(builder);
            names.push(new_name);
        }
    }

    // TODO: Unset `stable` if any of the join inputs have an empty `stable` plus `recent`.
    // This can happen when we have any new index built, as the updates above only land in `to_add`.

    // println!("names: {:?}", names);
    // println!("joins: {:?}", plan.joins.len());

    let mut r_name = names.pop().unwrap();
    if names.len() > 1 {
        // Burn down the joins until there are at most two collections left.
        for (index, (arity, projection)) in plan.joins.iter().enumerate().rev() {

            let l_name = names.pop().unwrap();
            let mut builder = FactBuilder::default();
            join_with(facts.get(&l_name).unwrap(), facts.get(&r_name).unwrap(), stable, *arity, |v1, v2| {
                builder.push(projection.iter().copied().map(|i| if i < v1.len() { v1.get(i) } else { v2.get(i - v1.len()) }));
            });

            // Stash the results under the name we'll use next.
            r_name = format!("{}-{:?}-mid", name, index + 1);
            facts.entry(r_name.clone()).or_default().add_set(builder);
        }
    }

    let mut results = vec![FactBuilder::default(); plan.heads.len()];

    // Perform the last join recording results for each head.
    // If there is no join, just read the one body atom.
    if let Some(arity) = plan.arity {
        let l_name = names.pop().unwrap();
        assert!(names.is_empty());    
        join_with(facts.get(&l_name).unwrap(), facts.get(&r_name).unwrap(), stable, arity, |v1, v2| {
            for (head, result) in plan.heads.iter().zip(results.iter_mut()) {
                result.push(head.iter().map(|term| {
                    match term {
                        Ok(col) => { 
                            if *col < v1.len() { v1.get(*col).as_slice() } 
                            else { v2.get(*col - v1.len()).as_slice() } 
                        },
                        Err(lit) => { lit.as_bytes() },
                    }
                }));
            }
        });
    }
    else {
        assert!(names.is_empty());    
        let facts1 = facts.get(&r_name).unwrap();
        if stable {
            for layer in facts1.stable.layers.iter() {
                let layer = layer.borrow();
                for datum in layer.into_index_iter() {
                    for (head, result) in plan.heads.iter().zip(results.iter_mut()) {
                        result.push(head.iter().map(|term| {
                            match term {
                                Ok(col) => datum.get(*col).as_slice(),
                                Err(lit) => { lit.as_bytes() },
                            }
                        }));
                    }
                }
            }
        }
        let recent = facts1.recent.borrow();
        for datum in recent.into_index_iter() {
            for (head, result) in plan.heads.iter().zip(results.iter_mut()) {
                result.push(head.iter().map(|term| {
                    match term {
                        Ok(col) => datum.get(*col).as_slice(),
                        Err(lit) => { lit.as_bytes() },
                    }
                }));
            }
        }
    }

    for (head, result) in rule.head.iter().zip(results) {
        facts.entry(head.name.clone()).or_default().add_set(result);
    }
}

/// A description of a linear join plan for a Datalog rule.
///
/// The plan goes right to left, joining pairs of atoms until there are at most two left.
/// With one or two body atoms, we either:
/// 1. map the single body atom onto the head atoms, or
/// 2. join the two body atoms and map the result onto the head atoms.
#[derive(Debug)]
pub struct JoinPlan {
    /// For each body atom, the pre-work to put it in the right shape.
    /// A `None` indicates that the atom can be used in its stated form.
    bodys: Vec<Plan>,
    /// For each join other than the leftmost, the input key arity and projection to apply to its output.
    ///
    /// This should land the results keyed appropriately, and pass along all demanded bindings.
    joins: Vec<(usize, Vec<usize>)>,
    /// For each head atom, the action to perform in the final join to correctly shape the result.
    ///
    /// An `Ok(index)` indicates a coordinate to copy, and an `Err(lit)` indicates a literal to copy.
    /// If `joins` is empty there is no final join, and each are applied to the rows of the body atom.
    heads: Vec<Vec<Result<usize, String>>>,

    /// The join arity for the final head-producing join, if such a join exists.
    arity: Option<usize>,
}

impl<'a> From<&'a Rule> for JoinPlan {
    fn from(rule: &'a Rule) -> Self {

        // For each variable, we track the leftmost and rightmost atoms in which they appear.
        // We use -1 for variables in the head, so that we can start at zero for the body.
        // These tell us 1. demand (leftmost), and 2. visibility (rightmost).
        let mut l_most = BTreeMap::new();
        let mut r_most = BTreeMap::new();
        for atom in rule.head.iter() {
            for term in atom.terms.iter() {
                if let Term::Var(name) = term {
                    l_most.insert(name, -1);
                    r_most.insert(name, -1);
                }
            }
        }
        for (index, atom) in rule.body.iter().enumerate() {
            for term in atom.terms.iter() {
                if let Term::Var(name) = term {
                    if !l_most.contains_key(name) {
                        l_most.insert(name, index as isize);
                    }
                    r_most.insert(name, index as isize);
                }
            }
        }

        // We should now be in a state where each body atom can
        // 1. Assess which of its own variables must be in its key, based on `r_most`: variables in scope at the time of the join.
        // 2. Assess which columns must be produced, based on `l_most`: variable that occur again to the left.
        // 3. Determine and implement the "schema" for the result of its join with the atoms to its right.
        // 4. Some nuance / corner cases around the heads: could be multiple, and they may have literals.

        // Form `keys` containing for each body atom the key it will use when joining to the right.
        // Each atom will need to be keyed by these variables, as will the result to the right.
        let mut keys = Vec::new();
        for (index, atom) in rule.body.iter().enumerate() {
            let mut key = BTreeSet::new();
            for term in atom.terms.iter() {
                if let Term::Var(name) = term {
                    if r_most.get(name).unwrap() > &(index as isize) {
                        key.insert(name);
                    }
                }
            }
            keys.push(key);
        }
        if keys.len() > 1 {
            keys.pop();
            let last = keys.pop().unwrap();
            keys.push(last.clone());
            keys.push(last);
        }
        // Each atom can now be locally planned, producing a `Plan` containing filters and a project.
        // This is also a moment where we could detect a no-op plan, and signal this to avoid copying.
        // We can also use demand information to project away columns; let's do that later for extra credit.
        let mut bodys = Vec::new();
        for (index, (atom, key)) in rule.body.iter().zip(keys.iter()).enumerate() {
            let mut plan = Plan::from_key(atom, key);
            for i in (key.len() .. plan.binding.len()).rev() {
                if l_most.get(&plan.binding[i]).unwrap() >= &(index as isize) {
                    plan.project.remove(i);
                    plan.binding.remove(i);
                }
            }
            bodys.push(plan);
        }

        // Each join, indexed by the leftmost input, can now determine a projection it applies to its result.
        // This should be first the key of the leftward join, and then any columns that are still demanded.
        // This should be in terms of indexes, and we should go right to left to find the specific values.
        // Getting started is a special case, and concluding with the head is also a special case.
        // If there are only two atoms in the body it is only special cases. T.T
        let mut joins = Vec::new();
        let mut schema: Vec<&String> = bodys.last().unwrap().binding.iter().collect();
        for index in (1 .. bodys.len() - 1).rev() {

            // Join `index` wants to produce data that aligns with `keys[index-1]`.
            // We only need to produce variables with `l_most` strictly less than `index`.
            // The inputs are two slices, each starting with `keys[index]` and continuing independently.
            // We need to find the indexes 
            let needed_keys = &keys[index-1];
            let mut needed_vals = bodys[index].binding.iter().chain(schema.iter().map(|x| *x)).collect::<BTreeSet<_>>();
            for key in needed_keys.iter() {
                needed_vals.remove(key);
            }
            needed_vals.retain(|v| l_most.get(v).unwrap() < &(index as isize));
            // Now need to find the locations of needed keys and then needed values, and record the schema.
            let mut permute = Vec::new();
            for key in needed_keys.iter().chain(needed_vals.iter()) {
                let pos1 = bodys[index].binding.iter().position(|x| &x == key);
                let pos2 = schema.iter().position(|x| x == key).map(|x| x + bodys[index].binding.len());
                permute.push(pos1.or(pos2).unwrap());
            }

            joins.push((keys[index].len(), permute));

            schema.clear();
            Extend::extend(&mut schema, needed_keys.into_iter().map(|x| *x).chain(needed_vals));
        }
        joins.reverse();

        // The plan is almost ready to go, but needs the special thought about how to handle the heads.
        // Each head has an order in mind, as well as the potential for literals to be scattered in its terms.
        // We don't yet have a schema for the last/leftmost join, so we'll have to cons that up using the same rules.
        let heads = 
        rule.head
            .iter()
            .map(|head| {
                head.terms
                    .iter()
                    .map(|term| {
                        match term {
                            Term::Lit(text) => Err(text.to_owned()),
                            Term::Var(name) => {
                                let pos1 = bodys[0].binding.iter().position(|x| x == name);
                                let pos2 = schema.iter().position(|x| x == &name).map(|x| x + bodys[0].binding.len());
                                Ok(pos1.or(pos2).unwrap())
                            }
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let arity = if keys.len() > 1 { Some(keys[0].len()) } else { None };

        JoinPlan { bodys, joins, heads, arity }
    }
}

/// Joins `body1` and `body2` using the first `arity` columns.
///
/// Matching elements are subjected to `action`.
/// When `stable` is set, we join the stable plus recent elements of each input;
/// when it is unset we exclude pairs of terms that are both stable.
pub fn join_with(
    body1: &FactSet,
    body2: &FactSet,
    stable: bool,
    arity: usize,
    mut action: impl FnMut(<Fact as Columnar>::Ref<'_>, <Fact as Columnar>::Ref<'_>),
)
{
    // Compare elements by their first `arity` columns only.
    // This is a moment where compile-time information about types would help us; perhaps column introspection can recover.
    let order = |x: <Fact as Columnar>::Ref<'_>, y: <Fact as Columnar>::Ref<'_>| { (0 .. arity).map(|i| x.get(i)).cmp((0 .. arity).map(|i| y.get(i))) };

    if stable {
        for layer1 in body1.stable.layers.iter() {
            for layer2 in body2.stable.layers.iter() {
                join::<Fact>(layer1, layer2, order, &mut action);
            }
        }
    }

    for stable2 in body2.stable.layers.iter() {
        join::<Fact>(&body1.recent, stable2, order, &mut action);
    }

    for stable1 in body1.stable.layers.iter() {
        join::<Fact>(stable1, &body2.recent, order, &mut action);
    }

    join::<Fact>(&body1.recent, &body2.recent, order, &mut action);
}

#[derive(Debug)]
pub struct Plan {
    var_filter: Vec<Vec<usize>>,
    lit_filter: Vec<(usize, String)>,
    project: Vec<usize>,
    binding: Vec<String>,
    in_arity: usize,
}

impl Plan {

    pub fn from_key(atom: &Atom, key: &BTreeSet<&String>) -> Self {
        // Extract literal and variable locations.
        let mut lit_filter = Vec::new();
        let mut locs = BTreeMap::new();
        for (idx, term) in atom.terms.iter().enumerate() {
            match term {
                Term::Var(name) => {
                    locs.entry(name)
                        .or_insert_with(Vec::new)
                        .push(idx);
                },
                Term::Lit(text) => {
                    lit_filter.push((idx, text.clone()));
                },
            }
        }

        // names that occur multiple times.
        let var_filter =
        locs.values()
            .filter(|x| x.len() > 1)
            .cloned()
            .collect::<Vec<_>>();

        // shared then unique variable names, each alphabetically.
        let shared =
        locs.iter()
            .filter(|(n,_)| key.contains(*n))
            .map(|(n,i)| (n.to_string(), i[0]));
        let unique =
        locs.iter()
            .filter(|(n,_)| !key.contains(*n))
            .map(|(n,i)| (n.to_string(), i[0]));

        let (binding, project) = shared.chain(unique).unzip();

        let in_arity = atom.terms.len();

        Plan { var_filter, lit_filter, project, binding, in_arity }
    }

    pub fn identity(&self) -> bool {
        self.project.iter().cloned().eq(0 .. self.in_arity) && self.var_filter.is_empty() && self.lit_filter.is_empty()
    }

    /// Filter and permute each `Fact`.
    pub fn apply(&self, data: &FactContainer, builder: &mut FactBuilder) {
        for item in data.borrow().into_index_iter() {
            if let Some(fact) = self.apply_once(item) {
                builder.push(fact);
            }
        }
    }

    /// Filter and permute one `Fact`.
    pub fn apply_once<'a>(&self, x: <Fact as Columnar>::Ref<'a>) -> Option<impl Iterator<Item = <Vec<u8> as Columnar>::Ref<'a>>> {
        let lit_match = self.lit_filter.iter().all(|(i,l)| x.get(*i).as_slice() == l.as_bytes());
        let var_match = self.var_filter.iter().all(|idxs| idxs.iter().all(|i| x.get(*i) == x.get(0)));
        if lit_match && var_match {
            Some(self.project.iter().map(move |i| x.get(*i)))
        }
        else { None }
    }
}

/// Match keys in `input1` and `input2` and act on matches.
fn join<'a, T: Columnar<Ref<'a> : Ord+std::fmt::Debug>> (
    input1: &'a T::Container,
    input2: &'a T::Container,
    mut order: impl FnMut(T::Ref<'a>, T::Ref<'a>) -> std::cmp::Ordering,
    mut action: impl FnMut(T::Ref<'a>, T::Ref<'a>),
) {
    use std::cmp::Ordering;

    let input1 = input1.borrow();
    let input2 = input2.borrow();

    let mut index1 = 0;
    let mut index2 = 0;

    // continue until either input is exhausted.
    while index1 < input1.len() && index2 < input2.len() {
        // compare the keys at this location.
        let pos1 = input1.get(index1);
        let pos2 = input2.get(index2);
        match order(pos1, pos2) {
            Ordering::Less => {
                // advance `index1` while strictly less than `pos2`.
                gallop::<T>(input1, &mut index1, |x| order(x, pos2) == Ordering::Less);
            },
            Ordering::Equal => {
                // Find *all* matches and increment indexes.
                let count1 = (index1..input1.len()).take_while(|i| order(input1.get(*i), pos1) == Ordering::Equal).count();
                let count2 = (index2..input2.len()).take_while(|i| order(input2.get(*i), pos2) == Ordering::Equal).count();

                for i1 in 0 .. count1 {
                    let row1 = input1.get(index1 + i1);
                    for i2 in 0 .. count2 {
                        let row2 = input2.get(index2 + i2);
                        action(row1, row2);
                    }
                }

                index1 += count1;
                index2 += count2;
            },
            std::cmp::Ordering::Greater => {
                // advance `index2` while strictly less than `pos1`.
                gallop::<T>(input2, &mut index2, |x| order(x, pos1) == Ordering::Less);
            },
        }
    }
}

/// Increments `index` until just after the last element of `input` to satisfy `cmp`.
///
/// The method assumes that `cmp` is monotonic, never becoming true once it is false.
/// If an `upper` is supplied, it acts as a constraint on the interval of `input` explored.
#[inline(always)]
pub(crate) fn gallop<'a, T: Columnar>(input: <T::Container as Container<T>>::Borrowed<'a>, index: &mut usize, mut cmp: impl FnMut(<T as Columnar>::Ref<'a>) -> bool) {
    let upper = input.len();
    // if empty input, or already >= element, return
    if *index < upper && cmp(input.get(*index)) {
        let mut step = 1;
        while *index + step < upper && cmp(input.get(*index + step)) {
            *index += step;
            step <<= 1;
        }

        step >>= 1;
        while step > 0 {
            if *index + step < upper && cmp(input.get(*index + step)) {
                *index += step;
            }
            step >>= 1;
        }

        *index += 1;
    }
}
