use columnar::{Container, Index, Len};
use crate::facts::{FactBuilder, FactContainer, FactSet};

/// Joins `body1` and `body2` using the first `arity` columns.
///
/// Matching elements are subjected to `action`.
/// When `stable` is set, we join the stable plus recent elements of each input;
/// when it is unset we exclude pairs of terms that are both stable.
pub fn join_with<F: FactContainer>(
    body1: &FactSet<F>,
    body2: &FactSet<F>,
    stable: bool,
    arity: usize,
    projections: &[&[Result<usize, String>]],
    builders: &mut [FactBuilder<F>],
)
{
    if stable {
        for layer1 in body1.stable.contents() {
            for layer2 in body2.stable.contents() {
                layer1.join(layer2, arity, projections, builders);
            }
        }
    }

    for stable2 in body2.stable.contents() {
        body1.recent.join(stable2, arity, projections, builders);
    }

    for stable1 in body1.stable.contents() {
        stable1.join(&body2.recent, arity, projections, builders);
    }

    body1.recent.join(&body2.recent, arity, projections, builders);
}

/// Match keys in `input1` and `input2` and act on matches.
pub fn join<'a, TC: Container<Ref<'a> : Ord>> (
    input1: TC::Borrowed<'a>,
    input2: TC::Borrowed<'a>,
    mut order: impl FnMut(TC::Ref<'a>, TC::Ref<'a>) -> std::cmp::Ordering,
    mut action: impl FnMut(TC::Ref<'a>, TC::Ref<'a>),
) {
    use std::cmp::Ordering;

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
                gallop::<TC>(input1, &mut index1, input1.len(), |x| order(x, pos2) == Ordering::Less);
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
                gallop::<TC>(input2, &mut index2, input2.len(), |x| order(x, pos1) == Ordering::Less);
            },
        }
    }
}

/// Increments `index` until just after the last element of `input` to satisfy `cmp`.
///
/// The method assumes that `cmp` is monotonic, never becoming true once it is false.
/// If an `upper` is supplied, it acts as a constraint on the interval of `input` explored.
#[inline(always)]
pub(crate) fn gallop<'a, TC: Container>(input: TC::Borrowed<'a>, lower: &mut usize, upper: usize, mut cmp: impl FnMut(TC::Ref<'a>) -> bool) {
    // if empty input, or already >= element, return
    if *lower < upper && cmp(input.get(*lower)) {
        let mut step = 1;
        while *lower + step < upper && cmp(input.get(*lower + step)) {
            *lower += step;
            step <<= 1;
        }

        step >>= 1;
        while step > 0 {
            if *lower + step < upper && cmp(input.get(*lower + step)) {
                *lower += step;
            }
            step >>= 1;
        }

        *lower += 1;
    }
}
