# Relations as Logic

In most Datalog engines, an atom in a rule body refers to a stored relation: a table of facts.
Datatoad generalizes this.
An atom can be backed by anything that supports two operations: *count* (how many extensions would you propose?) and *propose* (enumerate or validate those extensions).
A stored relation implements these by looking into its trie.
But so can a computation.

The relation `:plus(x, y, z)` represents the constraint `x + y = z`.
Given `x` and `y`, it can propose `z`.
Given `x` and `z`, it can propose `y`.
Given only `z`, it cannot propose anything (infinitely many decompositions), so it reports that and the planner knows not to start there.
This bidirectionality falls out of the `count`/`propose` interface — the planner asks each atom what it can contribute given the currently bound terms, and logic relations answer honestly.

There is no special case for logic relations in the join algorithm.
They are atoms, like any other.

This chapter covers how logic-backed relations are defined, how bidirectional computation works, and how they integrate with the join planner.
