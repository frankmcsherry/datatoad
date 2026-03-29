# Columnar Orientation

The foundational choice in datatoad is to represent data in columns rather than rows.

A relation with three columns is not stored as a vector of 3-tuples.
Instead, it is three parallel vectors: one per column.
Operations act on columns in bulk: permuting, filtering, sorting, and intersecting columns are array operations, not per-row decisions.

These bulk operations matter for more than raw performance; they make it easier to adapt our behavior.
1.  Interpreted execution comes easily (and efficiently) to columnar models.
    The interpretation overhead is amortized over the bulk operations.
2.  Isolating each column conceals details, which makes it easier for each column to specialize their behavior.
    We can sort a column of any fixed-width integers faster than a sequence of mixed width integers.
3.  By abstracting the relations in joins they can be backed by different implementations.
    In addition to conventional joins, both antijoins and logic are applied as if columnar relations.

This chapter makes the columnar layout concrete.
We start with the trie representation — how sorted relations decompose into layers of values and bounds — and show how datatoad's core operations (union, antijoin, intersection) work layer by layer on this structure.
We then cover sorting, which is the main cost of getting data *into* this representation.
