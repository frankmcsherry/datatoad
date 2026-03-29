# Operations: union, intersection, and join

The columnar trie supports column-by-column operation for standard relational operations.
The key observation, like with columnar sorting, is that each column can provide the information the next needs to continue, without revealing the details of the column itself.
In sorting this was the ordering and grouping information.
For these operators it will be *alignment* information.

## Reports

The alignment between two layers is a sequence of `Report` values:
```rust
enum Report {
    This(usize, usize), // values exclusive to the first input
    That(usize, usize), // values exclusive to the second input
    Both(usize, usize), // a matching value in both inputs
}
```
A `This(lower, upper)` says that values at indices `lower..upper` in the first input have no match in the second.
A `That(lower, upper)` says the same for the second input.
A `Both(i, j)` says that value `i` in the first input equals value `j` in the second.

The sequence of reports accounts for every value in both inputs and spells out their sorted order.
It tells the next layer exactly what to do: leave exclusive ranges as-is, and continue to resolve matching values by their values in the next layer.
This foundation is sufficient for us to implement union, intersection, and join.

## Union

Merging two tries proceeds layer by layer, starting from a single `Both(0, 0)` report (both inputs have one top-level list to merge).

At each layer, the merge consumes the current reports and produces new ones for the next layer:

- **`This(lower, upper)`**: Copy the lists from the first input. Emit `This` reports with expanded indices.
- **`That(lower, upper)`**: Copy the lists from the second input. Emit `That` reports with expanded indices.
- **`Both(i, j)`**: Merge the two lists (they're sorted, so this is a linear merge). Emit `This`, `That`, and `Both` reports for the elements within.

The per-layer merge is generic over the value type, so each layer dispatches to type-appropriate comparison and copy logic.
At the trie level, the code is compact — it walks the layers and, for each one, checks whether the data can be upgraded to a fixed-width type (e.g., 4-byte values) for a faster path:
```rust
pub fn union(&self, other: &Self) -> Self {
    let mut reports = VecDeque::default();
    reports.push_back(Report::Both(0, 0));
    for (layer0, layer1) in self.layers.iter().zip(other.layers.iter()) {
        // Merge this layer using the current reports,
        // producing new reports for the next layer.
        // Specialize by value width when possible.
    }
    ...
}
```

The `This` and `That` ranges are where the real throughput comes from: they identify contiguous runs of values and lists that can be bulk-copied rather than compared element by element.

## Intersection

Intersection reuses the same layer-by-layer walk, but only tracks the `Both` matches — the `This` and `That` ranges are irrelevant, since we only care about what overlaps.
At each layer, pairs of matching list indices are fed forward, and within those lists, a merge identifies matching values and records them for the next layer.
The merge uses galloping (exponential search) to skip past non-matching regions efficiently:
```rust
while lower0 < upper0 && lower1 < upper1 {
    match val0.cmp(&val1) {
        Less    => { lower0 += 1; gallop(list0, &mut lower0, upper0, |x| x < val1); },
        Equal   => { reports.push_back((lower0, lower1)); lower0 += 1; lower1 += 1; },
        Greater => { lower1 += 1; gallop(list1, &mut lower1, upper1, |x| x < val0); },
    }
}
```

Intersection shows us where two input tries line up, without spending time on intervals where they do not.
This ends up as the foundation for joins and antijoins.

## Join (and Antijoin)

To join two collections by some shared key columns, datatoad forms columnar tries whose first columns are the shared key columns.
An intersection not only finds the keys in common, but also returns with their offsets in each trie.
In each trie that offset is the root of a subtree of values that must be crossed with the values of the other trie.
Once intersected, a join is as easy as just reading all pairs of values out of the tails of the two tries (a "constant time enumerator").

Antijoins are similar, in that the intersection indicates which values to *avoid*, rather than keep.
The intersection report allows the trie to produce those elements that are exclusive to it.
This is a core action in Datalog, where we want to retain only the truly novel facts each iteration.
