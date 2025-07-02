//! Methods and types to support building and maintaining ordered sets of facts.

use std::collections::BTreeMap;
use columnar::{Columnar, Container, Index, Len, Push};

/// Use the `List` type to access an alternate columnar container.
pub type Fact = List<List<u8>>;
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
                    *start >= layer.len() || layer.borrow().get(*start) != x
                })
            });
        }
    }
}

pub type InternalContainer = Lists<Lists<Vec<u8>>>;

pub use lists::{List, Lists};
/// An internal container implementation that optimizes offsets when strided.
///
/// This module exists mostly because of limitations in `columnar`, and how
/// containers require an owned type that they are a container of. In this
/// case there is no good type that isn't already taken, or that seems to be.
mod lists {

    use std::ops::Deref;
    use columnar::{Columnar, Container, Index, Len, AsBytes, FromBytes};

    #[derive(Clone, Debug, Default)]
    pub struct List<T> { pub items: Vec<T> }
    impl<T> Deref for List<T> { type Target = Vec<T>; fn deref(&self) -> &Self::Target { &self.items } }

    impl<T: Columnar> Columnar for List<T> {
        type Ref<'a> = ListRef<<<T as Columnar>::Container as Container<T>>::Borrowed<'a>>;
        #[inline(always)]
        fn copy_from<'a>(&mut self, other: Self::Ref<'a>) {
            self.items.truncate(other.len());
            for i in 0 .. self.items.len() {
                T::copy_from(&mut self.items[i], other.get(i));
            }
            for i in self.items.len() .. other.len() {
                self.items.push(T::into_owned(other.get(i)));
            }
        }
        #[inline(always)]
        fn into_owned<'a>(other: Self::Ref<'a>) -> Self {
            let mut list = List { items: Vec::with_capacity(other.len()) };
            Self::copy_from(&mut list, other);
            list
        }
        type Container = Lists<T::Container>;
        #[inline(always)]
        fn reborrow<'b, 'a: 'b>(thing: Self::Ref<'a>) -> Self::Ref<'b> where Self: 'a {
            ListRef {
                lower: thing.lower,
                upper: thing.upper,
                items: <T::Container as Container<T>>::reborrow(thing.items),
            }
        }
    }

    #[derive(Copy, Clone, Default)]
    pub struct Lists<VC, BC = Vec<u64>> {
        pub bounds: Strides<BC>,
        pub values: VC,
    }

    impl<T: Columnar> Container<List<T>> for Lists<T::Container> {
        type Borrowed<'a> = Lists<<T::Container as Container<T>>::Borrowed<'a> , &'a [u64]>;
        #[inline(always)]
        fn borrow<'a>(&'a self) -> Self::Borrowed<'a> {
            Lists {
                bounds: Strides { bounds: &self.bounds.bounds[..] },
                values: self.values.borrow(),
            }
        }
        #[inline(always)]
        fn reborrow<'b, 'a: 'b>(thing: Self::Borrowed<'a>) -> Self::Borrowed<'b> {
            Lists {
                bounds: Strides { bounds: thing.bounds.bounds },
                values: T::Container::reborrow(thing.values),
            }
        }
    }

    impl<VC: Copy> Index for Lists<VC, &[u64]> {
        type Ref = ListRef<VC>;
        #[inline(always)]
        fn get(&self, index: usize) -> Self::Ref {
            let (lower, upper) = self.bounds.bounds(index);
            ListRef { lower, upper, items: self.values }
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct ListRef<VC> {
        lower: usize,
        upper: usize,
        items: VC,
    }

    impl<'a, T> ListRef<&'a [T]> {
        pub fn as_slice(&self) -> &'a [T] {
            &self.items[self.lower .. self.upper]
        }
    }

    impl<VC: Index> ListRef<VC> {
        #[inline(always)]
        pub fn len(&self) -> usize { self.upper - self.lower }
        #[inline(always)]
        pub fn get(&self, index: usize) -> <VC as Index>::Ref {
            self.items.get(index + self.lower)
        }
        #[inline(always)]
        pub fn iter(&self) -> impl Iterator<Item=<VC as Index>::Ref> {
            (0 .. self.len()).map(|i| self.get(i))
        }
    }

    impl<VC: Index<Ref: PartialEq>> PartialEq for ListRef<VC> {
        #[inline(always)]
        fn eq(&self, other: &Self) -> bool { self.iter().eq(other.iter()) }
    }
    impl<VC: Index<Ref: Eq>> Eq for ListRef<VC> { }
    impl<VC: Index<Ref: PartialOrd>> PartialOrd for ListRef<VC> {
        #[inline(always)]
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { self.iter().partial_cmp(other.iter()) }
    }
    impl<VC: Index<Ref: Ord>> Ord for ListRef<VC> {
        #[inline(always)]
        fn cmp(&self, other: &Self) -> std::cmp::Ordering { self.iter().cmp(other.iter()) }
    }

    /// The first two integers describe a stride pattern, [stride, length].
    ///
    /// If the length is zero the collection is empty. The first `item` pushed
    /// always becomes the first list element. The next element is the number of
    /// items at position `i` whose value is `item * (i+1)`. After this comes
    /// the remaining entries in the bounds container.
    #[derive(Copy, Clone, Default)]
    pub struct Strides<BC = Vec<u64>> { bounds: BC }

    impl<BC: Deref<Target=[u64]>> Strides<BC> {
        #[inline(always)]
        fn len(&self) -> usize { if self.bounds.len() < 2 { 0 } else { self.bounds[1] as usize + self.bounds[2..].len() } }
        #[inline(always)]
        pub fn bounds(&self, index: usize) -> (usize, usize) {
            let stride = self.bounds[0];
            let length = self.bounds[1];
            let index = index as u64;
            let lower = if index == 0 { 0 } else {
                let index = index - 1;
                if index < length { (index+1) * stride } else { self.bounds[(index - length + 2) as usize] }
            } as usize;
            let upper = if index < length { (index+1) * stride } else { self.bounds[(index - length + 2) as usize] } as usize;
            (lower, upper)
        }
    }

    impl Strides {
        #[inline(always)]
        pub fn push(&mut self, item: u64) {
            if self.bounds.len() < 2 { self.clear() }
            if self.bounds[..2] == [0,0] {
                self.bounds[0] = item;
                self.bounds[1] = 1;
            }
            else if self.bounds.len() > 2 {
                self.bounds.push(item);
            }
            else if item == self.bounds[0] * (self.bounds[1] + 1) {
                self.bounds[1] += 1;
            }
            else {
                self.bounds.push(item);
            }
        }
        #[inline(always)]
        fn clear(&mut self) {
            self.bounds.clear();
            self.bounds.push(0);
            self.bounds.push(0);
        }
    }

    use columnar::Push;
    impl<VC1: Index, VC2: Len + Push<<VC1 as Index>::Ref>> Push<ListRef<VC1>> for Lists<VC2> {
        #[inline(always)]
        fn push(&mut self, item: ListRef<VC1>) {
            for index in 0 .. item.len() {
                self.values.push(item.get(index));
            }
            self.bounds.push(self.values.len() as u64);
        }
    }
    impl<'a, T: Columnar, VC: Len + Push<&'a T>> Push<&'a List<T>> for Lists<VC> {
        #[inline(always)]
        fn push(&mut self, list: &'a List<T>) {
            self.values.extend(list.items.iter());
            self.bounds.push(self.values.len() as u64);
        }
    }
    impl<I: IntoIterator, VC: Len + Push<I::Item>> Push<I> for Lists<VC> {
        #[inline(always)]
        fn push(&mut self, item: I) {
            self.values.extend(item);
            self.bounds.push(self.values.len() as u64);
        }
    }

    impl<VC, BC: Deref<Target=[u64]>> Len for Lists<VC, BC> {
        #[inline(always)]
        fn len(&self) -> usize { self.bounds.len() }
    }

    use columnar::Clear;
    impl<VC: Clear> Clear for Lists<VC> {
        #[inline(always)]
        fn clear(&mut self) {
            self.bounds.clear();
            self.values.clear();
        }
    }

    impl<'a, VC: AsBytes<'a>, BC: AsBytes<'a>> AsBytes<'a> for Lists<VC, BC> {
        #[inline(always)]
        fn as_bytes(&self) -> impl Iterator<Item=(u64, &'a [u8])> {
            self.bounds.bounds.as_bytes().chain(self.values.as_bytes())
        }
    }

    impl<'a, VC: FromBytes<'a>, BC: FromBytes<'a>> FromBytes<'a> for Lists<VC, BC> {
        #[inline(always)]
        fn from_bytes(bytes: &mut impl Iterator<Item=&'a [u8]>) -> Self {
            Self {
                bounds: Strides { bounds: BC::from_bytes(bytes) },
                values: VC::from_bytes(bytes),
            }
        }
    }
}

/// A sorted list of distinct facts.
#[derive(Clone, Default)]
pub struct FactContainer {
    pub ordered: InternalContainer,
}

impl FactContainer {

    pub fn borrow(&self) -> <InternalContainer as Container<Fact>>::Borrowed<'_> {
        <InternalContainer as Container<Fact>>::borrow(&self.ordered)
    }

    pub fn len(&self) -> usize { self.borrow().len() }
    pub fn is_empty(&self) -> bool { self.borrow().is_empty() }

    fn filter(mut self, mut p: impl FnMut(<Fact as Columnar>::Ref<'_>) -> bool) -> FactContainer {
        let mut ordered = InternalContainer::default();
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
    
        let mut ordered = InternalContainer::default();

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

    /// Merges many sorted deduplicated lists into one sorted deduplicated list.
    fn _multiway_merge<const K: usize>(many: &[Self; K]) -> Self {
    
        let mut ordered = InternalContainer::default();

        let mut iters: [_; K] =
        many.iter()
            .map(|x| x.borrow().into_index_iter().peekable())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap_or_else(|_| panic!());

        while let Some((_min, idx)) = iters.iter_mut().enumerate().filter_map(|(i,x)| x.peek().map(|x| (x,i))).min() {
            let min = iters[idx].next().unwrap();
            ordered.push(min);
            for iter in iters.iter_mut() {
                if iter.peek() == Some(&min) {
                    iter.next();
                }
            }
        }

        Self { ordered }
    }

    fn from(facts: &InternalContainer) -> Self {
        let mut ordered = InternalContainer::default();
        let borrowed = <InternalContainer as Container<Fact>>::borrow(facts);

        let mut items = borrowed.into_index_iter().collect::<Vec<_>>();
        items.sort();
        items.dedup();
        ordered.extend(items);

        Self { ordered }
    }
}

#[derive(Clone, Default)]
pub struct FactBuilder {
    active: InternalContainer,
    layers: FactLSM,
}

impl FactBuilder {
    pub fn push<I>(&mut self, item: I) where InternalContainer: Push<I> {
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
    layers: Vec<FactContainer>,
}

impl FactLSM {
    fn push(&mut self, layer: FactContainer) {
        if !layer.is_empty() {
            self.layers.push(layer);
            self.tidy();
        }
    }
    
    fn extend(&mut self, other: &mut FactLSM) {
        Extend::extend(&mut self.layers, other.layers.drain(..));
        self.tidy();
    }

    pub fn contents(&self) -> impl Iterator<Item = &FactContainer> {
        self.layers.iter()
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

/// A layered trie representation in columns.
pub mod forests {

    use columnar::{Columnar, Index, Len, Push};
    use crate::facts::List;

    /// A sequence of `[T]` ordered lists, each acting as a map.
    ///
    /// For each integer input, corresponding to a path to a tree node,
    /// the node forks by way of the associated list of `T`, where each
    /// child has an index that can be used in a next layer (or not!).
    pub struct Layer<T: Columnar> { pub list: <List<T> as Columnar>::Container }

    /// A sequence of layers, where the outputs in one match the inputs in the next.
    ///
    /// Represents a layered trie, where each layer introduces a new "symbol".
    pub struct Forest<T: Columnar> { pub layers: Vec<Layer<T>> }

    /// A report we would expect to see in a sequence about two layers.
    ///
    /// A sequence of these reports reveal an ordered traversal of the keys
    /// of two layers, with ranges exclusive to one, ranges exclusive to the
    /// other, and individual elements (not ranges) common to both.
    #[derive(Copy, Clone)]
    pub enum Report {
        /// Range of indices in this input.
        This(usize, usize),
        /// Range of indices in that input.
        That(usize, usize),
        /// Matching indices in both inputs.
        Both(usize, usize),
    }

    impl<T: for<'a> Columnar<Ref<'a>: Ord>> Forest<T> {

        /// Create a forest from an ordered list of `[T]` of a common length.
        pub fn form(sorted: &<List<T> as Columnar>::Container) -> Self {
            use columnar::Container;
            let mut sorted = <<List<T> as Columnar>::Container as Container<List<T>>>::borrow(sorted).into_index_iter().peekable();
            if let Some(prev) = sorted.next() {
                let arity = prev.len();
                let mut layers = (0 .. arity).map(|_| Layer { list: <List<T> as Columnar>::Container::default() }).collect::<Vec<_>>();

                for (index, layer) in layers.iter_mut().enumerate() { layer.list.values.push(prev.get(index)); }

                // For each new item, we assess the first coordinate it diverges from the prior,
                // then seal subsequent lists and push all values from this coordinate onward.
                for item in sorted {
                    let mut differs = false;
                    for (index, layer) in layers.iter_mut().enumerate().take(arity) {
                        let len = layer.list.values.len();
                        if differs {  layer.list.bounds.push(len as u64); }
                        differs |= T::reborrow(item.get(index)) != layer.list.values.borrow().get(len-1);
                        if differs { layer.list.values.push(T::reborrow(item.get(index))); }
                    }
                }
                // Seal the last lists with their bounds.
                for layer in layers.iter_mut() { layer.list.bounds.push(layer.list.values.len() as u64); }

                Self { layers }
            }
            else {
                println!("Formed an empty forest");
                Self { layers: Vec::default() }
            }
        }
    }
}
