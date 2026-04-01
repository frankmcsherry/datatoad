# Planning

Datatoad plans a rule by forming independent plans for each atom.
Each of these plans is used when the atom presents with new facts.
Unioned together, the results of these plans produce all new values of the rule head.

Each individual atom plan is a sequence of pairs of terms and atoms.
Starting from the terms of the atom, each `(terms, atoms)` stage adds new `terms`, and restricts their values by `atoms`.

There are two common forms these take:
1. Single atom, multiple term (conventional binary join),
2. Single term, multiple atom (worst-case optimal join).

The only requirement on the plan is that by the end of it, each atom has participated while all of its terms were present.
This ensures that each binding of values to terms that we produce satisfies each atom in the rule.

When planning a path, all atoms present through a common trait:
```
pub trait PlanAtom<T: Ord> {
    /// Terms the atom references.
    fn terms(&self) -> BTreeSet<T>;
    /// For input terms, other terms the atom can ground.
    fn ground(&self, terms: &BTreeSet<T>) -> BTreeSet<T>;
}
```
This trait explains the set of terms, and helps the planner navigate the relationship among terms.

For most data-based atoms, the terms are those of the atom and every term can be ground.
These atoms can be used at any moment, as they can always just enumerate their contents.
Obviously we prefer to do something more clever with them than this.

For logic-based atoms, the story can be more complicated.
The operator `order(a, b, c) : a < b < c` could ground `b` given `(a, c)`, but cannot ground `c` given `(a, b)`.
Logic based atoms can have a "direction" to their planning hyper-edge.

The datatoad planner starts from the terms of the source atom, and repeatedly adds terms that can be ground from the present terms.
The planner has some heuristic preferences to involve terms that are constrained by multiple atoms, seeking the benefits of worst-case optimal joins early.
There is much room to improve the depth of thought here, and conversations are welcome.
