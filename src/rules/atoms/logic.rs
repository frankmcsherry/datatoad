//! Implementations for named relations that are backed by computation.
//!
//! The traits `Logic` and `BatchLogic` try to make it easier to implement a new relation than from scratch.
//! The `Logic` trait provides per-record functions, which are meant to be inlined for performance.
//! The `BatchLogic` trait provides batch functions, and expects to be invoked through a virtual call.

use std::collections::BTreeSet;
use std::rc::Rc;

use columnar::{Borrow, Index, Len, Push, Clear, Options};

use crate::types::{Atom, Term};
use crate::facts::{Lists, Terms};
use crate::facts::trie::Layer;
use crate::facts::trie::layers::advance_bounds;
use crate::rules::{exec, plan};
use crate::rules::exec::Salad;
use crate::comms::Comms;

/// Looks for the atom's name in a known list, and returns an implementation if found.
///
/// The implementation is a type that implements both `PlanAtom` and `ExecAtom`, and can be boxed as either.
pub fn resolve(atom: &Atom) -> Option<LogicRel<String>> {
    match atom.name.as_str() {
        ":noteq" => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::NotEq } ), atom)),
        ":range" => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::Range } ), atom)),
        ":plus"  => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::Plus } ),  atom)),
        ":times" => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::Times } ), atom)),
        ":print" => Some(LogicRel::new(Box::new(BatchedLogic { logic: relations::Print(atom.terms.len()) } ), atom)),
        _ => None,
    }
}


/// A type that can behave as a relation in the context of join planning.
pub trait Logic {
    /// The number of columns in the relation.
    fn arity(&self) -> usize;

    /// For input columns, any other columns the type can fully substantiate from concrete values of the input columns.
    ///
    /// Returning output columns introduces an obligation that the type can be relied on to substantiate concrete values.
    /// The obligation means that `self.count` must be non-`None` for concrete values of these columns, and `self.delve`
    /// must provide values for those columns (it can produce zero values, but cannot panic or otherwise nope out).
    fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize>;

    /// For values of some input columns, an upper bound on the number of distinct corresponding tuples in `output`.
    ///
    /// This method may be invoked with input and output column pairs returned by `self.bound` and no others, and must return `Some`
    /// values for concrete values of any input columns for which `self.bound` indicated the output columns.
    /// If this method is called on input columns not advertised by `self.bound`, it may return either `Some` or `None` values.
    ///
    /// When `output` is empty, it is important to emit either `Some(0)` or `Some(1)` to indicate respectively absence or presence.
    /// It is important that this result be accurate, as the type will not be given another chance to decline the records.
    fn count(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], output: &BTreeSet<usize>) -> Option<usize>;

    /// For values of some input columns, populate distinct values for arguments in `output`.
    ///
    /// This method may be called for any concrete values for which `self.count` returned a specific non-zero value (neither `None` nor `Some(0)`).
    /// The number of results should not exceed the value reported by `self.count`, though the only certain correctness requirement
    /// is that it should not plan to return any values if the count was advertised as `Some(0)`, as it may not get the chance.
    fn delve(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], output: (usize, &mut Terms));

    /// Static, mode-only cardinality bound on `output` (as a set) given concrete
    /// values for `args`, per input row. Distinct from `count`, which is the
    /// runtime per-input-row evaluation.
    ///
    /// `None` means the mode is unsupported (parallels `bound` returning a set
    /// that doesn't cover `output`). Default mirrors `bound`: `Some((0, None))`
    /// when `output ⊆ bound(args)`, `None` otherwise. Implementors override
    /// when they can say something tighter — most logic predicates are
    /// functional in well-formed modes and can claim `Some((0, Some(1)))`.
    fn range(&self, args: &BTreeSet<usize>, output: &BTreeSet<usize>) -> Option<(usize, Option<usize>)> {
        if output.is_subset(&self.bound(args)) { Some((0, None)) } else { None }
    }
}

pub trait BatchLogic {
    /// The number of arguments the logic expects.
    fn arity(&self) -> usize;
    /// For concrete values of the supplied arguments, which other arguments can be produced as concrete values.
    fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize>;
    /// For a subset of arguments, an upper bound on the number of distinct set of values for arguments in `output`.
    ///
    /// When `output` is empty, it is important to emit variously `Some(0)` or `Some(1)` to indicate respectively absence or presence.
    fn count(&self, args: &[Option<(<Terms as columnar::Borrow>::Borrowed<'_>, Vec<usize>)>], output: &BTreeSet<usize>) -> Vec<Option<usize>>;
    /// For a subset of arguments, populate distinct values for arguments in `output`.
    fn delve(&self, args: &[Option<(<Terms as columnar::Borrow>::Borrowed<'_>, Vec<usize>)>], output: usize) -> Options<Lists<Terms>>;
    /// Static, mode-only cardinality bound on `output` per input row. See `Logic::range`.
    fn range(&self, args: &BTreeSet<usize>, output: &BTreeSet<usize>) -> Option<(usize, Option<usize>)> {
        if output.is_subset(&self.bound(args)) { Some((0, None)) } else { None }
    }
}

/// A wrapper for general logic-backed relations that manages the terms in each position.
pub struct LogicRel<T> {
    pub logic: Box<dyn super::logic::BatchLogic>,
    /// In order: `[lower, value, upper]`.
    ///
    /// Each are either a term name, or a literal.
    pub bound: Vec<Result<T, Vec<u8>>>,
    /// Terms of `bound` in some order, used by exec to lay out records "favorably".
    pub terms: Vec<T>,
}

impl LogicRel<String> {
    /// Create a new instance of `Self` from batch logic and the atom itself.
    pub fn new(logic: Box<dyn super::logic::BatchLogic>, atom: &Atom) -> Self {
        let bound: Vec<Result<String, Vec<u8>>> = atom.terms.iter().map(|t| match t {
            Term::Var(name) => Ok(name.clone()),
            Term::Lit(data) => Err(data.clone()),
        }).collect();
        let terms = bound.iter().flatten().collect::<BTreeSet<_>>().into_iter().cloned().collect::<Vec<_>>();
        Self { logic, bound, terms }
    }
}

impl <T: Ord + Clone> plan::PlanAtom<T> for LogicRel<T> {
    fn terms(&self) -> BTreeSet<T> { self.terms.iter().cloned().collect() }
    fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T> {
        let indexes = self.bound.iter().enumerate().filter(|(_index, term)| match term {
            Ok(name) => terms.contains(name),
            Err(_) => true,
        }).map(|(index,_term)| index).collect();
        self.logic.bound(&indexes).into_iter().map(|index| self.bound[index].as_ref().unwrap()).cloned().collect()
    }
    fn range(&self, ins: &BTreeSet<T>, outs: &BTreeSet<T>) -> Option<(usize, Option<usize>)> {
        // Translate term-name modes to column-index modes for the inner BatchLogic.
        // Literal positions count as bound (their value is fixed at construction);
        // variable positions are bound iff the variable name is in `ins`.
        let in_idx: BTreeSet<usize> = self.bound.iter().enumerate().filter(|(_, t)| match t {
            Ok(name) => ins.contains(name),
            Err(_) => true,
        }).map(|(i, _)| i).collect();
        // Outputs must be variable positions whose name is in `outs`. Outputs naming
        // a literal-position term, or naming a term this atom doesn't reference, fall
        // through to the default behavior (which will refuse the mode).
        let out_idx: Option<BTreeSet<usize>> = outs.iter().map(|name| {
            self.bound.iter().position(|t| matches!(t, Ok(n) if n == name))
        }).collect();
        let out_idx = out_idx?;
        self.logic.range(&in_idx, &out_idx)
    }
}

impl<T: Ord + Clone> exec::ExecAtom<T> for LogicRel<T> {

    // Lightly odd, in that we have no preference on term order.
    fn terms(&self) -> &[T] { &self.terms }

    fn seed(&self, comms: &mut Comms, recent: bool) -> Salad<T> {
        if recent { return Salad::new(Default::default(), self.terms.clone()); }
        else {
            let mut salad = crate::rules::exec::Salad::new(Default::default(), Vec::default());
            salad.extend([Vec::default().try_into().unwrap()]);
            self.join(comms, &mut salad, &self.terms.iter().cloned().collect(), &self.terms);
            salad
        }
    }

    fn count(&self, _: &mut Comms, salad: &mut Salad<T>, added: &BTreeSet<T>, my_index: u8) {
        //  Flatten the input, to make our life easier.
        if let Some(mut delta) = salad.facts.flatten() {

            //  1.  Prepare the function arguments, a `Vec<Option<(Borrowed, Vec<usize>)>>` indicating present elements of `self.bound`.
            //      Each present element of `self.bound` presents as a pair of borrowed container and list of counts for each element.
            //      All present pairs should have the same sum of counts, indicating the total number of argument tuples.
            let max = self.bound.iter().flatten().flat_map(|term| salad.terms.iter().position(|t| t == term)).max();
            let cnt = max.map(|col| delta.layer(col).list.values.len()).unwrap_or(1);

            //  Long-lived containers for literal values.
            //  In an FDB world, we would put these at the root, independent of any input data, rather than to the side.
            let mut lits = vec![Terms::default(); self.bound.len()];
            for (index, arg) in self.bound.iter().enumerate() { if let Err(lit) = arg { lits[index].push(lit); } }

            //  The arguments themselves, from indicated layers with counts projected forward to `max` layer.
            let args: Vec<Option<(<Terms as Borrow>::Borrowed<'_>, Vec<usize>)>> =
            self.bound.iter().enumerate().map(|(index, arg)| {
                match arg {
                    Ok(term) => {
                        salad.terms.iter().position(|t| t == term).map(|col| {
                            let mut bounds = (0 .. delta.layer(col).list.values.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
                            for i in col+1 .. max.unwrap()+1 { advance_bounds::<Terms>(delta.layer(i).borrow(), &mut bounds)};
                            let counts = bounds.into_iter().map(|(l, u)| u-l).collect::<Vec<_>>();
                            (delta.layer(col).list.values.borrow(), counts)
                        })
                    },
                    Err(_) => { Some((lits[index].borrow(), vec![cnt] )) },
                }
            }).collect();

            //  2.  Evaluate the function for each setting of the arguments.
            let added = added.iter().map(|term| self.bound.iter().position(|t| t.as_ref() == Ok(term)).unwrap()).collect::<BTreeSet<_>>();
            let output = self.logic.count(&args, &added);

            //  3.  Project the output forward to the count column, potentially update count and index.
            let orders = match max {
                Some(col) => {
                    let mut bounds = (0 .. delta.layer(col).list.values.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
                    for i in col+1 .. delta.arity() { advance_bounds::<Terms>(delta.layer(i).borrow(), &mut bounds)};
                    bounds.into_iter().map(|(l,u)| u-l).collect::<Vec<_>>()
                },
                None => { vec![delta.len()] }
            };

            let mut notes_rc = delta.pop_layer().unwrap();
            let notes = &mut Rc::make_mut(&mut notes_rc).list.values.values;
            for (index, order) in orders.into_iter().enumerate().flat_map(|(i,c)| std::iter::repeat(output[i]).take(c)).enumerate() {
                if let Some(order) = order {
                    let order: u8 = (order+1).ilog2() as u8;
                    if notes[4 * index] >= order {
                        notes[4 * index] = order;
                        notes[4 * index + 1] = my_index;
                    }
                }
            }
            delta.push_layer(notes_rc);

            salad.extend([delta]);
        }
    }

    fn join(&self, _: &mut Comms, salad: &mut Salad<T>, added: &BTreeSet<T>, _after: &[T]) {
        //  Flatten the input, to make our life easier.
        if let Some(delta) = salad.facts.flatten() {

            //  1.  Prepare the function arguments, a `Vec<Option<(Borrowed, Vec<usize>)>>` indicating present elements of `self.bound`.
            //      Each present element of `self.bound` presents as a pair of borrowed container and list of counts for each element.
            //      All present pairs should have the same sum of counts, indicating the total number of argument tuples.
            let max = self.bound.iter().flatten().flat_map(|term| salad.terms.iter().position(|t| t == term)).max();
            let cnt = max.map(|col| delta.layer(col).list.values.len()).unwrap_or(1);

            //  Long-lived containers for literal values.
            //  In an FDB world, we would put these at the root, independent of any input data, rather than to the side.
            let mut lits = vec![Terms::default(); self.bound.len()];
            for (index, arg) in self.bound.iter().enumerate() { if let Err(lit) = arg { lits[index].push(lit); } }

            //  The arguments themselves, from indicated layers with counts projected forward to `max` layer.
            let args: Vec<Option<(<Terms as Borrow>::Borrowed<'_>, Vec<usize>)>> =
            self.bound.iter().enumerate().map(|(index, arg)| {
                match arg {
                    Ok(term) => {
                        salad.terms.iter().position(|t| t == term).map(|col| {
                            let mut bounds = (0 .. delta.layer(col).list.values.len()).map(|i| (i,i+1)).collect::<Vec<_>>();
                            for i in col+1 .. max.unwrap()+1 { advance_bounds::<Terms>(delta.layer(i).borrow(), &mut bounds)};
                            let counts = bounds.into_iter().map(|(l, u)| u-l).collect::<Vec<_>>();
                            (delta.layer(col).list.values.borrow(), counts)
                        })
                    },
                    Err(_) => { Some((lits[index].borrow(), vec![cnt] )) },
                }
            }).collect();

            if added.is_empty() {
                // Semijoin case.
                let added = added.iter().map(|term| self.bound.iter().position(|t| t.as_ref() == Ok(term)).unwrap()).collect::<BTreeSet<_>>();
                let keep = self.logic.count(&args, &added).into_iter().map(|x| x != Some(0)).collect::<std::collections::VecDeque<_>>();
                salad.facts.extend(delta.retain_core(max.map(|c| c+1).unwrap_or(0), keep));
            }
            else {
                let colidx = added.iter().map(|term| self.bound.iter().position(|t| t.as_ref() == Ok(term)).unwrap()).next().unwrap();
                let column = self.logic.delve(&args, colidx);
                let columnar::Options { indexes: columnar::RankSelect { values, counts: _ }, somes: column } = column;
                let keep = values.into_index_iter().collect();
                if let Some(mut delta) = delta.retain_core(max.map(|c| c+1).unwrap_or(0), keep).flatten() {
                    assert_eq!(added.len(), 1);
                    let pos = max.map(|c| c+1).unwrap_or(0);
                    let mut bounds = (0 .. column.len()).map(|i| (i, i+1)).collect::<Vec<_>>();
                    for idx in pos .. delta.arity() { advance_bounds::<Terms>(delta.layer(idx).borrow(), &mut bounds); }
                    let mut colnew: Lists<Terms> = Default::default();
                    for idx in 0 .. column.len() {
                        for _ in bounds[idx].0 .. bounds[idx].1 {
                            colnew.push(column.borrow().get(idx));
                        }
                    }
                    delta.push_layer(Rc::new(Layer { list: colnew }));
                    salad.facts.push(delta);
                }
                salad.terms.push(added.iter().next().unwrap().clone());
            }

        }
        else { Extend::extend(&mut salad.terms, added.iter().take(1).cloned()); }
    }
}

pub struct BatchedLogic<L: Logic> { pub logic: L }

impl<L: Logic> BatchLogic for BatchedLogic<L> {
    fn arity(&self) -> usize { self.logic.arity() }
    fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> { self.logic.bound(args) }
    fn range(&self, args: &BTreeSet<usize>, output: &BTreeSet<usize>) -> Option<(usize, Option<usize>)> { self.logic.range(args, output) }
    fn count(&self, args: &[Option<(<Terms as columnar::Borrow>::Borrowed<'_>, Vec<usize>)>], output: &BTreeSet<usize>) -> Vec<Option<usize>> {

        // The following is .. neither clear nor performant. It should be at least one of those two things.
        let length = args.iter().flatten().next().map(|a| a.1.iter().sum()).unwrap_or(1);
        let mut counts = Vec::with_capacity(length);
        let mut indexs = args.iter().map(|opt| opt.as_ref().map(|(_, counts)| counts.iter().cloned().enumerate().flat_map(|(index, count)| std::iter::repeat(index).take(count)))).collect::<Vec<_>>();
        let mut values: Vec<Option<<Terms as columnar::Borrow>::Ref<'_>>> = Vec::default();
        for _ in 0 .. length {
            values.clear();
            Extend::extend(&mut values, indexs.iter_mut().enumerate().map(|(col, i)| i.as_mut().map(|j| args[col].as_ref().unwrap().0.get(j.next().unwrap()))));
            counts.push(self.logic.count(&values, output));
        }

        counts
    }
    fn delve(&self, args: &[Option<(<Terms as columnar::Borrow>::Borrowed<'_>, Vec<usize>)>], output: usize) -> Options<Lists<Terms>> {

        // The following is .. neither clear nor performant. It should be at least one of those two things.
        let length = args.iter().flatten().next().map(|a| a.1.iter().sum()).unwrap_or(1);
        let mut indexs = args.iter().map(|opt| opt.as_ref().map(|(_, counts)| counts.iter().cloned().enumerate().flat_map(|(index, count)| std::iter::repeat(index).take(count)))).collect::<Vec<_>>();
        let mut values: Vec<Option<<Terms as columnar::Borrow>::Ref<'_>>> = Vec::default();
        let mut terms = Terms::default();
        let mut result: Options<Lists<Terms>> = Default::default();
        for _ in 0 .. length {
            values.clear();
            Extend::extend(&mut values, indexs.iter_mut().enumerate().map(|(col, i)| i.as_mut().map(|j| args[col].as_ref().unwrap().0.get(j.next().unwrap()))));
            self.logic.delve(&values, (output, &mut terms));
            if terms.is_empty() { result.push(None::<Vec<Vec<u8>>>); }
            else { result.push(Some(terms.borrow().into_index_iter())); }
            terms.clear();
        }
        assert_eq!(result.len(), length);
        result
    }

}

pub mod relations {

    use std::collections::BTreeSet;
    use columnar::Push;
    use crate::facts::Terms;


    /// Big-endian interpretation of `bytes` as `u64`, if the length is at most eight.
    fn as_u64(bytes: &[u8]) -> Option<u64> {
        if bytes.len() > 8 { None }
        else {
            let mut slice = [0u8; 8];
            slice[8-bytes.len() ..].copy_from_slice(bytes);
            Some(u64::from_be_bytes(slice))
        }
    }

    /// Decodes a number of optional byte slices as correspondingly optional `u64` data.
    ///
    /// The method returns `None` if the number of arguments is not `K`, if the slice lengths differ, or if any exceed eight.
    fn decode_u64<const K: usize>(args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>]) -> Option<([Option<u64>; K], usize)> {
        let mut width: Option<usize> = None;
        let mut result: [Option<u64>; K] = [None; K];
        for index in 0 .. K {
            if let Some(bytes) = &args[index] {
                if width.is_some() && width != Some(bytes.len()) { None?; }
                width = Some(bytes.len());
                result[index] = Some(as_u64(bytes.as_slice())?);
            }
        }
        Some((result, width?))
    }

    /// The relation R(x,y) : x != y.
    pub struct NotEq;
    impl super::Logic for NotEq {
        fn arity(&self) -> usize { 2 }
        fn bound(&self, _args: &BTreeSet<usize>) -> BTreeSet<usize> { Default::default() }
        fn count(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
            match (&args[0], &args[1]) {
                (Some(x), Some(y)) => { if x.as_slice() == y.as_slice() { Some(0) } else { Some(1) } },
                _ => None,
            }
        }
        fn delve(&self, _args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], _output: (usize, &mut Terms)) { panic!("NotEq asked to enumerate values"); }
        fn range(&self, args: &BTreeSet<usize>, output: &BTreeSet<usize>) -> Option<(usize, Option<usize>)> {
            // Pure filter: never produces values. `bound` is always empty, so
            // any non-empty `output` is unsupported.
            if !output.is_empty() { return None; }
            // Both args bound: actual x != y filter, 0 or 1 per input. Single or
            // no arg bound: trivially satisfiable (some y != x always exists),
            // so survives every input row — keep the (1, _) lower bound so the
            // planner doesn't pick it as a no-op semijoin.
            if args.contains(&0) && args.contains(&1) {
                Some((0, Some(1)))
            } else {
                Some((1, Some(1)))
            }
        }
    }

    /// The relation R(x,y,z) : x * y = z, for terms all of the same length (up to eight bytes).
    pub struct Times;
    impl super::Logic for Times {
        fn arity(&self) -> usize { 3 }
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> {
            if args.len() > 1 || args.contains(&2) { (0 .. 3).filter(|i| !args.contains(i)).collect() } else { Default::default() }
        }
        fn range(&self, args: &BTreeSet<usize>, output: &BTreeSet<usize>) -> Option<(usize, Option<usize>)> {
            if !output.is_subset(&self.bound(args)) { return None; }
            // Filter / functional factoring: z bound alongside x or y. See `Plus::range`
            // for the productive vs filter split; same shape applies here.
            if args.contains(&2) && (args.contains(&0) || args.contains(&1)) {
                return Some((0, Some(1)));
            }
            // z bound alone, asked to produce x or y: up to sqrt(z) factor pairs,
            // unbounded statically.
            if args.contains(&2) && !output.is_empty() {
                return Some((0, None));
            }
            // Productive (compute z) or trivially-satisfiable existence.
            Some((1, Some(1)))
        }
        fn count(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
            // Any two+ bound terms should lead to a `Some(0)` or `Some(1)` determination.
            if let Some((decoded, width)) = decode_u64::<3>(args) {
                match decoded {
                    [Some(x), Some(y), Some(z)] => { let (mul, ovr) = u64::overflowing_mul(x, y); if !ovr && mul == z { Some(1) } else { Some(0) }},
                    [Some(x), Some(y),    None] => { let (mul, ovr) = u64::overflowing_mul(x, y); if !ovr && ((mul >> (8*width)) == 0) { Some(1) } else { Some(0) } },
                    [None,    Some(y), Some(z)] => { if y > 0 && y <= z && (z / y) * y == z { Some(1) } else { Some(0) } },
                    [Some(x), None,    Some(z)] => { if x > 0 && x <= z && (z / x) * x == z { Some(1) } else { Some(0) } },
                    // If we only have z, we there are only so many products that can form `z`.
                    [None,    None,    Some(z)] => { Some((z.isqrt() + 1) as usize) },
                    _ => None
                }
            }
            else { Some(0) }
        }
        fn delve(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], output: (usize, &mut Terms)) {
            if let Some((decoded, width)) = decode_u64::<3>(args) {
                match decoded {
                    [Some(x), Some(y),    None] => { let (mul, ovr) = u64::overflowing_mul(x, y); if !ovr && ((mul >> (8*width)) == 0) { output.1.push(&mul.to_be_bytes()[(8-width)..]) } },
                    [None,    Some(y), Some(z)] => { if y > 0 && y <= z && (z / y) * y == z { output.1.push(&(z/y).to_be_bytes()[(8-width)..]) } },
                    [Some(x), None,    Some(z)] => { if x > 0 && x <= z && (z / x) * x == z { output.1.push(&(z/x).to_be_bytes()[(8-width)..]) } },
                    // If we only have z, we there are only so many products that can form `z`.
                    [None,    None,    Some(z)] => {
                        for i in 1 .. z.isqrt()+1 {
                            if (z / i) * i == z { output.1.push(&i.to_be_bytes()[(8-width)..]); }
                        }
                    },
                    _ => { }
                }
            }
        }
    }

    /// The relation R(x,y,z) : x + y = z, for terms all of the same length (up to eight bytes).
    pub struct Plus;
    impl super::Logic for Plus {
        fn arity(&self) -> usize { 3 }
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> { if args.len() > 1 { (0 .. 3).filter(|i| !args.contains(i)).collect() } else { Default::default() } }
        fn range(&self, args: &BTreeSet<usize>, output: &BTreeSet<usize>) -> Option<(usize, Option<usize>)> {
            if !output.is_subset(&self.bound(args)) { return None; }
            // z bound alongside x or y: filter shape (subtraction can fail when
            // the operand exceeds z; all-bound is a pure equality check). Every
            // other supported mode is either productive (compute z from x and y)
            // or trivially satisfiable (the relation always admits a completion),
            // so every input row survives — the (1, _) lower bound is what tells
            // the planner this would be a no-op as a pure semijoin.
            // Overflow caveat: at the byte-width boundary the (1, Some(1)) cases
            // can technically drop to 0; practical rules don't sit on that edge.
            if args.contains(&2) && (args.contains(&0) || args.contains(&1)) {
                Some((0, Some(1)))
            } else {
                Some((1, Some(1)))
            }
        }
        fn count(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
            // Any two+ bound terms should lead to a `Some(0)` or `Some(1)` determination.
            if let Some((decoded, width)) = decode_u64::<3>(args) {
                match decoded {
                    [Some(x), Some(y), Some(z)] => { let (sum, ovr) = u64::overflowing_add(x, y); if !ovr && sum == z { Some(1) } else { Some(0) }},
                    [Some(x), Some(y),    None] => { let (sum, ovr) = u64::overflowing_add(x, y); if !ovr && ((sum >> (8*width)) == 0) { Some(1) } else { Some(0) } },
                    [Some(x),    None, Some(z)] => { if x <= z { Some(1) } else { Some(0) } },
                    [None,    Some(y), Some(z)] => { if y <= z { Some(1) } else { Some(0) } },
                    // TODO: There are some things that we could say more about, e.g. that a `z` has a count of `z+1` because there are that many ways to add up to `z`.
                    //       Based on unsigned math, as signed integers would have unbounded options. Seems likely to be a bad idea to propose this, without a better upper bound.
                    _ => None
                }
            }
            else { Some(0) }
        }
        fn delve(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], output: (usize, &mut Terms)) {
            if let Some((decoded, width)) = decode_u64::<3>(args) {
                match decoded {
                    [Some(x), Some(y),    None] => { let (sum, ovr) = u64::overflowing_add(x, y); if !ovr && ((sum >> (8*width)) == 0) { output.1.push(&sum.to_be_bytes()[(8-width)..]) } },
                    [Some(x), None,    Some(z)] => { if x <= z { output.1.push(&(z-x).to_be_bytes()[(8-width)..]) } },
                    [None,    Some(y), Some(z)] => { if y <= z { output.1.push(&(z-y).to_be_bytes()[(8-width)..]) } },
                    _ => { }
                }
            }
        }
    }

    /// The relation R(x,y,z) : x <= y < z, for terms all of the same length (up to eight bytes).
    pub struct Range;
    impl super::Logic for Range {
        fn arity(&self) -> usize { 3 }
        fn bound(&self, args: &BTreeSet<usize>) -> BTreeSet<usize> { if args.contains(&0) && args.contains(&2) && !args.contains(&1) { [1].into_iter().collect() } else { Default::default() } }
        fn range(&self, args: &BTreeSet<usize>, output: &BTreeSet<usize>) -> Option<(usize, Option<usize>)> {
            if !output.is_subset(&self.bound(args)) { return None; }
            // Asked to produce v: enumerates `u - l` values, statically unbounded.
            if !output.is_empty() { return Some((0, None)); }
            // Existence modes. Trivially satisfiable when u is unbound and at
            // most one of l/v is bound — we can always pick the rest to satisfy
            // l <= v < u. Otherwise the inequality can fail per input.
            if !args.contains(&2) && args.len() <= 1 {
                Some((1, Some(1)))
            } else {
                Some((0, Some(1)))
            }
        }
        fn count(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], _output: &BTreeSet<usize>) -> Option<usize> {
            // `decode_u64` returns `None` on all input `None`, meaning we must handle that specially to avoid a `Some(0)` response.
            // TODO: Also, calling this method with all `None` seems like a bad use of everyone's time; find out why and prevent it.
            if args == &[None, None, None] { return None; }
            if let Some((decoded, _width)) = decode_u64::<3>(args) {
                match decoded {
                    [Some(l), None,    Some(u)] => { if l < u { Some((u-l) as usize) } else { Some(0) } },
                    // TODO: Seemingly, without these next two cases we get wrong results, which seems odd and not the intended/understood implementation requirement.
                    [None,    Some(v), Some(u)] => { if v < u { None } else { Some(0) } },
                    [Some(l), Some(v), None   ] => { if l <= v{ None } else { Some(0) } },
                    [Some(l), Some(v), Some(u)] => { if l <= v && v < u { Some(1) } else { Some(0) } },
                    _ => None,
                }
            }
            else { Some(0) }
        }
        fn delve(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], output: (usize, &mut Terms)) {
            assert_eq!(output.0, 1);
            let length = args[0].unwrap().as_slice().len();
            let lower: u64 = as_u64(args[0].unwrap().as_slice()).unwrap();
            let upper: u64 = as_u64(args[2].unwrap().as_slice()).unwrap();
            for value in lower .. upper {
                output.1.push(&value.to_be_bytes()[(8-length)..]);
            }
        }
    }

    /// The relation R(x,y,z) : x <= y < z, for terms all of the same length (up to eight bytes).
    pub struct Print(pub usize);
    impl super::Logic for Print {
        fn arity(&self) -> usize { self.0 }
        fn bound(&self, _args: &BTreeSet<usize>) -> BTreeSet<usize> { Default::default() }
        fn count(&self, args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], output: &BTreeSet<usize>) -> Option<usize> { if output.is_empty() {
            for arg in args.iter() { print!("0x"); for byte in arg.unwrap().as_slice().iter() { print!("{:0>2x}", byte); } print!("\t"); }
            println!();
            Some(1)
        } else { None } }
        fn delve(&self, _args: &[Option<<Terms as columnar::Borrow>::Ref<'_>>], _output: (usize, &mut Terms)) { unimplemented!() }
        fn range(&self, args: &BTreeSet<usize>, output: &BTreeSet<usize>) -> Option<(usize, Option<usize>)> {
            // Side-effect predicate: every input row survives and prints. The
            // truthful cardinality is (1, Some(1)), but we deliberately under-
            // claim it as (0, Some(1)) so a "skip pure no-op filters" planner
            // pass doesn't elide Print and silently drop its side effects.
            // Treat this as opting out of tight bounds rather than a lie:
            // (0, Some(1)) is still a correct over-approximation of (1, Some(1)).
            if !output.is_empty() { return None; }
            if (0 .. self.0).all(|i| args.contains(&i)) { Some((0, Some(1))) } else { None }
        }
    }
}
