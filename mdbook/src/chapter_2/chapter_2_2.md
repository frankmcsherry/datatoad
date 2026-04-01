# Binary joins

Datatoad's binary join stages occur when a plan has one atom and any number of terms.

Binary joins are relatively easy when the two inputs are arranged as tries each starting with the columns to equate, in order.
The first step is intersection: we find all pairs of indices corresponding to matching prefixes along the equated columns.
The second step is enumeration: for each pair of indices we enumerate all pairs of remaining values from each input.

Almost all of the complexity of datatoad's binary join implementation is in performing a fused enumeration and projection.
The projections, which lead to the trie layout of the next stage, are the main cost in joining.
They end up very analogous to trie formation, with columnar radix sorting to form the output layers.

The spirit here is very close to [factorized databases](https://www.cs.ox.ac.uk/dan.olteanu/papers/os-sigrec16.pdf), where aligning data is cheap, and one avoids materializing results until one is compelled (by a projection, for example).
