# Columnar tries

The chapter introduction described how columnar layouts let us cheaply rearrange which columns the engine looks at.
This section makes the representation concrete: the actual data structures, how they compose, and how runtime specialization works.

## The representation

A relation with three columns, sorted and deduplicated, looks like this:
```
(A, 1, x),
(A, 1, y),
(A, 1, z),
(A, 2, x),
(A, 3, x),
(A, 3, y),
(B, 2, z),
(C, 1, x),
(C, 2, x).
```

A naive columnar layout stores three parallel arrays, one per column:
```
c0  c1  c2
--  --  --
A   1   x
A   1   y
A   1   z
A   2   x
A   3   x
A   3   y
B   2   z
C   1   x
C   2   x
```
This is already useful — each column can be stored in a type-appropriate container — but it doesn't exploit the sortedness.

### Prefix compression

Because the data are sorted, the first column has runs of identical values.
We can deduplicate it, but we need to remember where each value's entries begin and end in the next column.
Peeling off the last column and deduplicating the prefix gives:
```
c0  c1  bounds  c2
--  --  ------  --
A   1   [0, 3)  x
A   2   [3, 4)  y
A   3   [4, 6)  z
B   2   [6, 7)  x
C   1   [7, 8)  x
C   2   [8, 9)  y
                z
                x
                x
```
The bounds array translates from the second column into the third: each entry in `c1` owns a range of entries in `c2`.
Since bounds are always contiguous (one range's upper bound is the next's lower bound), we only need to store the upper bounds:
```
c0  c1  b2  c2
--  --  --  --
A   1   3   x
A   2   4   y
A   3   6   z
B   2   7   x
C   1   8   x
C   2   9   y
            z
            x
            x
```
Repeating this for the first two columns:
```
c0  b1  c1  b2  c2
--  --  --  --  --
A   3   1   3   x
B   4   2   4   y
C   6   3   6   z
        2   7   x
        1   8   x
        2   9   y
                z
                x
                x
```

Each column is now a sequence of sorted lists.
Column 0 has one list (`[A, B, C]`) — the distinct values extending the empty prefix.
Column 1 has three lists (`[1,2,3]`, `[2]`, `[1,2]`) — one per distinct value in column 0.
Column 2 has six lists — one per distinct value in column 1.

The bounds between columns describe which lists in the next column correspond to which values in the current one.
Importantly, the bounds belong to the *next* column, not the current one: they translate forward.
This keeps the representation clean when multiple independent extensions share the same prefix column, a pattern that shows up in [forward-looking join strategies](https://www.cs.ox.ac.uk/dan.olteanu/papers/os-sigrec16.pdf).

### Layers and forests

In code, each column becomes a `Layer`:
```rust
pub struct Layer<C> {
    pub list: Lists<C>,
}
```
where `Lists<C>` is a columnar container holding the values and bounds together — the sequence of sorted lists described above.

A complete trie is a `Forest`: a sequence of layers, one per column.
```rust
pub struct Forest<C> {
    layers: Vec<Rc<Layer<C>>>,
}
```
The number of layers equals the arity of the relation.
Each layer's values are typed (in datatoad's case, byte sequences whose widths can be introspected at runtime), and the bounds translate between adjacent layers.

The name is "forest" because there is no requirement there be a single root, and generally we will work with intermediate runs of layers that have multiple "roots".

## Runtime specialization

A key property of the layer representation is that the boundary between layers carries no type information — just index ranges (bounds) translating from one layer to the next.
This is what enables per-column specialization at runtime.

When datatoad encounters a layer whose byte sequences all have width 4 (or 8, or 12), it can upgrade to a fixed-width representation and dispatch to code that compares and copies fixed-size values.
When the widths vary, it falls back to variable-length byte comparison.
The choice is made per layer, per operation, at runtime — and because the interface between layers is type-erased, mixing specialized and generic layers in the same trie is free.

This is where the columnar trie representation pays off for an interpreter.
A row-oriented engine would need to specialize on the full row type (the product of all column types), which explodes combinatorially.
A columnar engine specializes each column independently, and the decisions compose without interference.
