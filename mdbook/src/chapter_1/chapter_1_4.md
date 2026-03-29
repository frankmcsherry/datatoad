# Log-structured merge tries

Rather than maintain a single `Forest` per relation and modify it in place, datatoad wraps forests in a log-structured merge tree:
```rust
pub struct FactLSM<F> {
    layers: Vec<F>,
}
```
New facts arrive as small forests.

As soon as two forests have the same size, they are merged to keep the total count logarithmic — the invariant is that sizes should at least halve as you move through the list.
This keeps individual forests immutable: all mutation happens by appending new forests and merging.
Immutability plays well with large contiguous allocations, avoids the bookkeeping of in-place updates, and allows reference counted sharing.

The merge discipline, halving in size, keeps the memory footprint within 2x of what it could possibly be.
All tries together sum to at most twice the size of the largest, which itself contains only distinct facts.

## Products of sums

The LSM structure means that we'll need to adapt many of our algorithms to work on sums of tries.
This turns out to be not that hard; we do not need to flatten the LSM to one trie to union or intersect, for example.
The requirement paves the way for other moments we might want to sum relations but cannot, for example if they have different representations (data v logic).
