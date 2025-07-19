use columnar::{Container, Index};
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
