# Datatoad

Datatoad is an interactive Datalog engine, written in Rust.

It is built around a few ideas that, taken together, produce something meaningfully different from other Datalog engines:

1.  **Columnar dispatch.**
    Data lives in columns rather than rows.
    Operations like permutation, filtering, and intersection are bulk transformations on contiguous arrays.
    This makes it cheap to rearrange data on the fly, which is what enables everything that follows.

2.  **Sorted columns as tries.**
    Once columns are sorted lexicographically, prefix-sharing emerges for free.
    A column of values plus a column of bounds *is* a trie level, with no separate index structure.

3.  **Joins as trie intersection.**
    Binary joins align two tries by shared prefix.
    Worst-case optimal joins generalize: for each fact, pick whichever trie offers the fewest extensions, propose from that, validate against the others.
    Both are instances of the same operation.

4.  **Relations as logic.**
    A relation doesn't have to be a stored table.
    Anything that can count extensions and propose values can participate in a join: arithmetic, ranges, constraints.
    These "logic relations" are bidirectional and first-class.

These ideas compose.
Columnar dispatch makes worst-case optimal joins practical (not just theoretical) by making per-fact adaptive atom selection a bulk operation.
Sorted columns give you tries without building them.
The join framework's generality lets logic relations slot in alongside stored data.

This book walks through each idea, how they are realized in datatoad, and what the consequences are.
