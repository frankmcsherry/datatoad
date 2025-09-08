use columnar::Index;
use crate::facts::{FactContainer, FactLSM, FactSet};

/// Joins `body1` and `body2` using the first `arity` columns.
///
/// Matching elements are subjected to `action`.
/// When `stable` is set, we join the stable plus recent elements of each input;
/// when it is unset we exclude pairs of terms that are both stable.
pub fn join_with<F: FactContainer + Clone>(
    body1: &FactSet<F>,
    body2: &FactSet<F>,
    stable: bool,
    arity: usize,
    projections: &[&[Result<usize, String>]],
) -> Vec<FactLSM<F>>
{
    let mut lsms = vec![FactLSM::default(); projections.len()];

    if stable {
        for layer1 in body1.stable.contents() {
            let built = layer1.join_many(body2.stable.contents(), arity, projections);
            lsms.iter_mut().zip(built).for_each(|(lsm, mut built)| lsm.extend(&mut built));
        }
    }

    let built = body1.recent.join_many(body2.stable.contents().chain([&body2.recent]), arity, projections);
    lsms.iter_mut().zip(built).for_each(|(lsm, mut built)| lsm.extend(&mut built));

    for stable1 in body1.stable.contents() {
        let built = stable1.join(&body2.recent, arity, projections);
        lsms.iter_mut().zip(built).for_each(|(lsm, mut built)| lsm.extend(&mut built));
    }

    lsms
}

/// Increments `index` until just after the last element of `input` to satisfy `cmp`.
///
/// The method assumes that `cmp` is monotonic, never becoming true once it is false.
/// If an `upper` is supplied, it acts as a constraint on the interval of `input` explored.
#[inline(always)]
pub(crate) fn gallop<'a, C: Index>(input: C, lower: &mut usize, upper: usize, mut cmp: impl FnMut(<C as Index>::Ref) -> bool) {
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
