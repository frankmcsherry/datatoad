//! Model-based tests for `Forest` operations.
//!
//! Each operation is checked against a transparent model: facts as a
//! `BTreeSet<Vec<Vec<u8>>>`, with merge as set union, `act_on` as a
//! map/filter over tuples, join as a nested loop, and semi/antijoin as
//! retains by prefix.
//!
//! Data comes in two width regimes: uniform four-byte terms, which drive
//! the width-specialized (`upgrade`) kernel paths, and mixed-width terms,
//! which drive the generic fallback kernels. Both check against the same
//! oracles.

use std::collections::BTreeSet;

use columnar::{Borrow, Index, Len, Push};
use datatoad::comms::Comms;
use datatoad::facts::{FactContainer, FactLSM, Forest, Merge, Terms};
use datatoad::types::Action;

type Fact = Vec<Vec<u8>>;
type Model = BTreeSet<Fact>;

/// A deterministic pseudo-random number generator.
fn lcg(seed: u64) -> impl FnMut() -> u64 {
    let mut state = seed.wrapping_mul(2) + 1;
    move || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        state >> 33
    }
}

/// Tuples of uniformly four-byte terms, from a small domain to force duplicates.
fn fixed_tuples(count: usize, arity: usize, seed: u64) -> Vec<Fact> {
    let mut next = lcg(seed);
    (0..count).map(|_| (0..arity).map(|_| (next() as u32 % 64).to_be_bytes().to_vec()).collect()).collect()
}

/// Tuples of mixed-width terms (lengths zero through four), from a small domain.
fn mixed_tuples(count: usize, arity: usize, seed: u64) -> Vec<Fact> {
    let mut next = lcg(seed);
    (0..count).map(|_| (0..arity).map(|_| {
        let len = (next() % 5) as usize;
        (0..len).map(|_| (next() % 4) as u8).collect()
    }).collect()).collect()
}

fn forest(tuples: &[Fact]) -> Forest<Terms> {
    let arity = tuples[0].len();
    let mut cols = vec![Terms::default(); arity];
    for tuple in tuples.iter() {
        assert_eq!(tuple.len(), arity);
        for (col, term) in tuple.iter().enumerate() { cols[col].push(&term[..]); }
    }
    Forest::from_columns(cols).unwrap()
}

fn model(tuples: &[Fact]) -> Model { tuples.iter().cloned().collect() }

/// Extracts the facts of a forest by walking its layers.
fn extract(forest: &Forest<Terms>) -> Model {
    let mut paths: Vec<(Fact, usize)> = vec![(Vec::new(), 0)];
    for layer in 0..forest.arity() {
        let lists = forest.layer(layer).list.borrow();
        let mut next = Vec::with_capacity(paths.len());
        for (prefix, list) in paths {
            let (lower, upper) = lists.bounds.bounds(list);
            for item in lower..upper {
                let mut path = prefix.clone();
                path.push(lists.values.get(item).as_slice().to_vec());
                next.push((path, item));
            }
        }
        paths = next;
    }
    let facts: Model = paths.into_iter().map(|(path, _)| path).collect();
    assert_eq!(facts.len(), forest.len(), "forest len disagrees with its distinct facts");
    facts
}

fn extract_lsm(mut lsm: FactLSM<Forest<Terms>>) -> Model {
    lsm.flatten().as_ref().map(extract).unwrap_or_default()
}

/// The model form of `act_on`.
fn act_on_model(facts: &Model, action: &Action<Vec<u8>>) -> Model {
    facts.iter()
        .filter(|t| action.lit_filter.iter().all(|(col, lit)| &t[*col] == lit))
        .filter(|t| action.var_filter.iter().all(|group| group.iter().all(|col| t[*col] == t[group[0]])))
        .map(|t| action.projection.iter().map(|p| match p { Ok(col) => t[*col].clone(), Err(lit) => lit.clone() }).collect())
        .collect()
}

/// The model form of `join_many`: tuples agreeing with some other on the first
/// `arity` terms, projected by column index into the concatenated tuple space.
fn join_model(this: &Model, others: &Model, arity: usize, projection: &[usize]) -> Model {
    let mut result = Model::default();
    for x in this.iter() {
        for y in others.iter() {
            if x[..arity] == y[..arity] {
                result.insert(projection.iter().map(|c| if *c < x.len() { x[*c].clone() } else { y[*c - x.len()].clone() }).collect());
            }
        }
    }
    result
}

/// The model form of semijoin (`semi: true`) and antijoin (`semi: false`).
fn retain_model(this: &Model, others: &Model, semi: bool) -> Model {
    let arity = others.iter().next().map(|t| t.len()).unwrap_or(0);
    this.iter().filter(|t| others.contains(&t[..arity].to_vec()) == semi).cloned().collect()
}

/// Both width regimes, as (name, tuples) pairs for a given shape and seed.
fn regimes(count: usize, arity: usize, seed: u64) -> Vec<(&'static str, Vec<Fact>)> {
    vec![("fixed", fixed_tuples(count, arity, seed)), ("mixed", mixed_tuples(count, arity, seed))]
}

#[test]
fn model_build_and_merge() {
    for (name, xs) in regimes(500, 3, 1) {
        let ys = match name { "fixed" => fixed_tuples(500, 3, 2), _ => mixed_tuples(500, 3, 2) };
        let (fx, fy) = (forest(&xs), forest(&ys));
        assert_eq!(extract(&fx), model(&xs), "{}: build", name);
        let union: Model = model(&xs).union(&model(&ys)).cloned().collect();
        assert_eq!(extract(&fx.merge(fy)), union, "{}: merge", name);
    }
}

#[test]
fn model_act_on() {
    for (name, xs) in regimes(500, 3, 3) {
        let fx = forest(&xs);
        let mx = model(&xs);
        let lit = xs[0][1].clone();
        let absent = vec![0xFFu8; 3];

        let actions = vec![
            // Permutation with a repeated column and an introduced literal.
            Action { lit_filter: vec![], var_filter: vec![], projection: vec![Ok(2), Ok(0), Ok(2), Err(lit.clone())], input_arity: 3 },
            // Filter by a literal that has matches, and one that cannot.
            Action { lit_filter: vec![(1, lit.clone())], var_filter: vec![], projection: vec![Ok(0), Ok(2)], input_arity: 3 },
            Action { lit_filter: vec![(0, absent)], var_filter: vec![], projection: vec![Ok(0)], input_arity: 3 },
            // Filter by inter-column equality.
            Action { lit_filter: vec![], var_filter: vec![vec![0, 2]], projection: vec![Ok(1), Ok(0)], input_arity: 3 },
            // Project away all columns but one, deduplicating heavily.
            Action { lit_filter: vec![], var_filter: vec![], projection: vec![Ok(1)], input_arity: 3 },
        ];
        for (idx, action) in actions.iter().enumerate() {
            let expected = act_on_model(&mx, action);
            // A large threshold, and a small one to exercise the staged permutation paths.
            for thresh in [1 << 20, 64] {
                assert_eq!(extract_lsm(fx.act_on(action, thresh)), expected, "{}: action {} thresh {}", name, idx, thresh);
            }
        }
    }
}

#[test]
fn model_join_many() {
    for (name, xs) in regimes(300, 2, 4) {
        let (ys, zs) = match name {
            "fixed" => (fixed_tuples(300, 2, 5), fixed_tuples(300, 2, 6)),
            _ => (mixed_tuples(300, 2, 5), mixed_tuples(300, 2, 6)),
        };
        let (fx, fy, fz) = (forest(&xs), forest(&ys), forest(&zs));
        let (mx, my, mz) = (model(&xs), model(&ys), model(&zs));

        // Join on the first column, producing (key, x.1, y.1).
        let mut comms = Comms::default();
        let expected = join_model(&mx, &my, 1, &[0, 1, 3]);
        assert_eq!(extract_lsm(fx.join_many([&fy].into_iter(), 1, &[0, 1, 3], comms.conduit())), expected, "{}: join", name);

        // The same join against two others, whose union is the other relation.
        let union: Model = my.union(&mz).cloned().collect();
        let expected = join_model(&mx, &union, 1, &[0, 1, 3]);
        assert_eq!(extract_lsm(fx.join_many([&fy, &fz].into_iter(), 1, &[0, 1, 3], comms.conduit())), expected, "{}: join two", name);

        // A small memory budget, to exercise the staged output paths.
        comms.set_mem_budget(64);
        let expected = join_model(&mx, &my, 1, &[0, 1, 3]);
        assert_eq!(extract_lsm(fx.join_many([&fy].into_iter(), 1, &[0, 1, 3], comms.conduit())), expected, "{}: join staged", name);
    }
}

#[test]
fn model_anti_semi_join() {
    for (name, xs) in regimes(500, 2, 7) {
        let keys = match name { "fixed" => fixed_tuples(50, 1, 8), _ => mixed_tuples(50, 1, 8) };
        let fx = forest(&xs);
        let fk = forest(&keys);
        let (mx, mk) = (model(&xs), model(&keys));

        assert_eq!(extract_lsm(fx.clone().semijoin([&fk].into_iter())), retain_model(&mx, &mk, true), "{}: semijoin", name);
        assert_eq!(extract_lsm(fx.antijoin([&fk].into_iter())), retain_model(&mx, &mk, false), "{}: antijoin", name);
    }
}
