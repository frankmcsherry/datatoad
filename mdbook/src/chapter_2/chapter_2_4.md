# Execution abstractions

Each atom involved in join execution implements a trait with two key methods:

```
pub trait ExecAtom<T: Ord> {
    /// For each fact in `delta`, the number of distinct values for terms in `added`.
    fn count(&self, delta: &Facts, added: &BTreeSet<T>) -> Vec<u64>;
    /// Joins `self` with `delta`, introducing terms in `added`, and projected to `after`.
    fn join(&self, delta: &mut Facts, added: &BTreeSet<T>, after: &[T]);
}
```

These methods allow us to implement binary joins, semijoins, and worst-case optimal joins.

Importantly, these methods can be implemented not only by columnar tries of data.
Antijoins are implemented using this interface, but are only able to semijoin facts.
Logic relations are also implemented this way, providing counts and values for any terms they have advertised they can ground.

There is a contract between `PlanAtom` and `ExecAtom`.
If an atom advertises that it can ground a term as a function of other terms, then it must both propose a count and be able to enumerate the values of the terms.
Atoms like antijoins will not advertise grounding any term, and can error if asked to count or propose terms; they should correctly semijoin when asked.
