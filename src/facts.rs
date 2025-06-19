//! Methods and types to support building and maintaining ordered sets of facts.

use std::collections::BTreeMap;
use columnar::{Columnar, Container, Index, Len, Push};

pub type Fact = Vec<Vec<u8>>;
pub type Facts = BTreeMap<String, FactSet>;

#[derive(Default)]
pub struct FactSet {
    pub stable: FactLSM,
    pub recent: FactContainer,
    pub to_add: FactLSM,
}

impl FactSet {

    pub fn len(&self) -> usize { self.stable.layers.iter().map(|x| x.len()).sum::<usize>() + self.recent.len() }

    pub fn active(&self) -> bool {
        !self.recent.is_empty() || !self.to_add.layers.is_empty()
    }

    pub fn add_set(&mut self, facts: FactBuilder) {
        let mut facts = facts.finish();
        if !facts.layers.is_empty() {
            self.to_add.extend(&mut facts);
        }
    }

    pub fn advance(&mut self) {
        // Move recent into stable
        if !self.recent.is_empty() {
            self.stable.push(std::mem::take(&mut self.recent));
        }

        if let Some(to_add) = self.to_add.flatten() {

            // Tidy stable by an amount proportional to the work we are about to do.
            self.stable.tidy_through(2 * to_add.len());

            // Remove from to_add any facts already in stable.
            let mut starts = vec![0; self.stable.layers.len()];
            let stable = &self.stable;
            self.recent = to_add.filter(move |x| {
                starts.iter_mut().zip(&stable.layers).all(|(start, layer)| {
                    crate::join::gallop::<Fact>(layer.borrow(), start, |y| y < x);
                    *start >= layer.borrow().len() || layer.borrow().get(*start) != x
                })
            });
        }
    }
}

/// A sorted list of distinct facts.
#[derive(Clone, Default)]
pub struct FactContainer {
    ordered: <Fact as Columnar>::Container,
}

impl FactContainer {
    pub fn borrow(&self) -> <<Fact as Columnar>::Container as Container<Fact>>::Borrowed<'_> {
        <<Fact as Columnar>::Container as Container<Fact>>::borrow(&self.ordered)
    }

    fn filter(mut self, mut p: impl FnMut(<Fact as Columnar>::Ref<'_>) -> bool) -> FactContainer {
        let mut ordered = <Fact as Columnar>::Container::default();
        ordered.extend(self.borrow().into_index_iter().filter(|x| p(*x)));
        use columnar::Clear;
        self.ordered.clear();
        Self { ordered }
    }

    /// Merges two sorted deduplicated lists into one sorted deduplicated list.
    fn merge(self, other: Self) -> Self {
    
        if self.is_empty() { return other; }
        if other.is_empty() { return self; }
    
        // TODO: Test for appendability.
        // if self.borrow().last() < Some(other.borrow().get(0)) { println!("prepend"); }
        // if other.borrow().last() < Some(self.borrow().get(0)) { println!("postpend"); }

        // TODO: Have columnar learn to extend from ranges of containers with memcpy.
    
        let mut ordered = <Fact as Columnar>::Container::default();

        let mut iter1 = self.borrow().into_index_iter().peekable();
        let mut iter2 = other.borrow().into_index_iter().peekable();
    
        while let (Some(fact1), Some(fact2)) = (iter1.peek(), iter2.peek()) {
            match fact1.cmp(fact2) {
                std::cmp::Ordering::Less => {
                    ordered.push(*fact1);
                    iter1.next();
                }
                std::cmp::Ordering::Equal => {
                    ordered.push(*fact1);
                    iter1.next();
                    iter2.next();
                }
                std::cmp::Ordering::Greater => {
                    ordered.push(*fact2);
                    iter2.next();
                }
            }
        }
        ordered.extend(iter1);
        ordered.extend(iter2);
    
        Self { ordered }
    }
    
    fn from(facts: &<Fact as Columnar>::Container) -> Self {
        let mut indexes = (0 .. facts.len()).collect::<Vec<_>>();
        let borrowed = <<Fact as Columnar>::Container as Container<Fact>>::borrow(facts);
        indexes.sort_by_key(|i| borrowed.get(*i));
        indexes.dedup_by_key(|i| borrowed.get(*i));
    
        let mut ordered = <Fact as Columnar>::Container::default();
        ordered.extend(indexes.into_iter().map(|i| borrowed.get(i)));
        Self { ordered }
    }
}

impl std::ops::Deref for FactContainer {
    type Target = <Fact as Columnar>::Container;
    fn deref(&self) -> &Self::Target {
        &self.ordered
    }
}

#[derive(Clone, Default)]
pub struct FactBuilder {
    active: <Fact as Columnar>::Container,
    layers: FactLSM,
}

impl FactBuilder {
    pub fn push<I>(&mut self, item: I) where <Fact as Columnar>::Container: Push<I> {
        self.active.push(item);
        if self.active.len() > 1_000_000 {
            use columnar::Clear;
            self.layers.push(FactContainer::from(&self.active));
            self.active.clear();
        }
    }
    fn finish(mut self) -> FactLSM {
        self.layers.push(FactContainer::from(&self.active));
        self.layers
    }
}

/// A list of fact lists that double in length, each sorted and distinct.
#[derive(Clone, Default)]
pub struct FactLSM {
    pub layers: Vec<FactContainer>,
}

impl FactLSM {
    fn push(&mut self, layer: FactContainer) {
        self.layers.push(layer);
        self.tidy();
    }
    
    fn extend(&mut self, other: &mut FactLSM) {
        Extend::extend(&mut self.layers, other.layers.drain(..));
        self.tidy();
    }

    /// Flattens the layers into one layer, and takes it.
    fn flatten(&mut self) -> Option<FactContainer> {
        self.layers.sort_by_key(|x| x.len());
        self.layers.reverse();
        while self.layers.len() > 1 {
            let x = self.layers.pop().unwrap();
            let y = self.layers.pop().unwrap();
            self.layers.push(x.merge(y));
            self.layers.sort_by_key(|x| x.len());
            self.layers.reverse();
        }
        self.layers.pop()
    }

    /// Ensures layers double in size.
    fn tidy(&mut self) {
        self.layers.sort_by_key(|x| x.len());
        self.layers.reverse();
        while let Some(pos) = (1..self.layers.len()).position(|i| self.layers[i-1].len() < 2 * self.layers[i].len()) {
            while self.layers.len() > pos + 1 {
                let x = self.layers.pop().unwrap();
                let y = self.layers.pop().unwrap();
                self.layers.push(x.merge(y));
                self.layers.sort_by_key(|x| x.len());
                self.layers.reverse();
            }
        }
    }

    /// Ensures layers double in size and at most one is less than `size`.
    fn tidy_through(&mut self, size: usize) {
        self.layers.sort_by_key(|x| x.len());
        self.layers.reverse();
        while self.layers.len() > 1 && self.layers[self.layers.len()-2].len() < size {
            let x = self.layers.pop().unwrap();
            let y = self.layers.pop().unwrap();
            self.layers.push(x.merge(y));
            self.layers.sort_by_key(|x| x.len());
            self.layers.reverse();
        }
        self.tidy();
    }
}
