use columnar::{Container, Index, Len, Push};
use crate::facts::{Facts, FactBuilder, FactContainer, Sorted, Terms};

/// A sorted list of distinct facts.
#[derive(Clone, Default)]
pub struct FactList {
    ordered: Facts,
}

impl FactList {
    /// Borrows the underlying container.
    pub fn borrow(&self) -> <Facts as Container>::Borrowed<'_> { self.ordered.borrow() }
}

impl FactContainer for FactList {

    fn len(&self) -> usize { self.borrow().len() }
    fn is_empty(&self) -> bool { self.borrow().is_empty() }

    fn apply<'a>(&'a self, mut action: impl FnMut(&[<Terms as Container>::Ref<'a>])) {
        let mut attrs = Vec::new();
        for item in self.borrow().into_index_iter() {
            attrs.clear();
            Extend::extend(&mut attrs, item.into_index_iter());
            action(&attrs[..]);
        }
    }

    fn join<'a>(&'a self, other: &'a Self, arity: usize, projections: &[&[Result<usize, String>]], builders: &mut [FactBuilder<Self>]) {

        let mut action = |v1: <Facts as Container>::Ref<'_>, v2: <Facts as Container>::Ref<'_>| {
            for (projection, builder) in projections.iter().zip(builders.iter_mut()) {
                builder.push(projection.iter().map(|i| {
                    match i { Ok(col) => if *col < v1.len() { v1.get(*col).as_slice() } else { v2.get(*col - v1.len()).as_slice() },
                            Err(lit) => lit.as_bytes() }}));
            }
        };

        if arity == 1 {
            crate::join::join::<Facts>(self.borrow(), other.borrow(), |x,y| x.get(0).cmp(&y.get(0)), &mut action);
        }
        else {
            let order = |x: <Facts as Container>::Ref<'_>, y: <Facts as Container>::Ref<'_>| {
                (0 .. arity).map(|i| x.get(i)).cmp((0 .. arity).map(|i| y.get(i)))
            };
            crate::join::join::<Facts>(self.borrow(), other.borrow(), order, &mut action);
        }
    }

    fn except<'a>(self, others: impl Iterator<Item = &'a Self>) -> Self {
        let others = others.map(|x| x.borrow()).collect::<Vec<_>>();
        let mut starts = vec![0; others.len()];
        let mut ordered = Facts::default();
        let mut predicate = move |x| {
            starts.iter_mut().zip(others.iter()).all(|(start, other)| {
                crate::join::gallop::<Facts>(*other, start, other.len(), |y| y < x);
                *start >= other.len() || other.get(*start) != x
            })
        };
        ordered.extend(self.borrow().into_index_iter().filter(|x| predicate(*x)));
        Self { ordered }
    }

    fn merge(mut self, mut other: Self) -> Self {

        if self.is_empty() { return other; }
        if other.is_empty() { return self; }

        // TODO: Test for appendability.
        // if self.borrow().last() < Some(other.borrow().get(0)) { println!("prepend"); }
        // if other.borrow().last() < Some(self.borrow().get(0)) { println!("postpend"); }

        // Attempt to sniff out a known pattern of fact and term sizes.
        // Clearly needs to be generalized, or something.
        if let (Some(2), Some(4)) = (self.ordered.bounds.strided(), self.ordered.values.bounds.strided()) {
            if let (Some(2), Some(4)) = (other.ordered.bounds.strided(), other.ordered.values.bounds.strided()) {

                if self.len() < other.len() { std::mem::swap(&mut self, &mut other); }

                self.ordered.bounds.length += other.ordered.bounds.length;
                self.ordered.values.bounds.length += other.ordered.values.bounds.length;
                Extend::extend(&mut self.ordered.values.values, other.ordered.values.values);

                let (more, less) = self.ordered.values.values.as_chunks_mut::<8>();
                assert!(less.is_empty());
                more.sort();
                let mut finger = 0;
                for i in 1 .. more.len() {
                    if more[i] != more[finger] {
                        finger += 1;
                        more[finger] = more[i];
                    }
                }
                finger += 1;
                self.ordered.values.values.truncate(8 * finger);

                self.ordered.bounds.clear();
                self.ordered.bounds.stride = 2;
                self.ordered.bounds.length = finger as u64;
                self.ordered.values.bounds.clear();
                self.ordered.values.bounds.stride = 4;
                self.ordered.values.bounds.length = 2 * finger as u64;

                return self;
            }
        }

        let ordered = Facts::merge::<true>(self.borrow(), other.borrow());
        Self { ordered }
    }

    fn form(facts: &mut Facts) -> Self {

        // Attempt to sniff out a known pattern of fact and term sizes.
        // Clearly needs to be generalized, or something.
        if let (Some(2), Some(4)) = (facts.bounds.strided(), facts.values.bounds.strided()) {
            let (more, less) = facts.values.values.as_chunks_mut::<8>();
            assert!(less.is_empty());
            more.sort_unstable();
            let mut finger = 0;
            for i in 1 .. more.len() {
                if more[i] != more[finger] {
                    finger += 1;
                    more[finger] = more[i];
                }
            }
            finger += 1;
            facts.values.values.truncate(8 * finger);
            facts.bounds.length = finger as u64;
            facts.values.bounds.length = 2 * finger as u64;

            return Self { ordered: std::mem::take(facts) }
        }

        facts.sort::<true>();
        Self { ordered: std::mem::take(facts) }
    }
}
