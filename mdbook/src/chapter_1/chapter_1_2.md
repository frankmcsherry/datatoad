# Columnar sorting

Our data rarely starts out as a columnar trie, and we'll need to get it in to that shape.
Moreover, we'll often find we do have a columnar trie, but would like it in a different order.
This is the generally challenging problem of "columnar sorting", which we'll describe here.

The problem is "generally challenging" because it is usually slow.
Top sorting algorithms move data as they sort to localize the work, and columns smear that data across multiple locations.
We are not going to out-perform row-oriented sorting at what they do best, but we'll see there is a place for columnar sorting.

Columnar sorting starts from a sequence of columns (or even tries), and sorts each column in turn, each column passing notes to the next about how to continue the sort.
Each column sort takes as input a list of integers that order and group its rows, and it sorts them by `(group, value)`.
It produces an output list of integers that order and group its rows, to pass to the next column.

This sort respects the ordering requirement of the preceding columns, without introducing the complexity of the types of those columns.
In an interpreted setting this is paramount, because we cannot pre-compile the row sort for each of the column orders a user might create.
In datatoad each type is `[u8]`, but in each column sort we notice if it is exactly `[u8; K]` for some `K` and dispatch to an optimized `(usize, [u8;K])` sort in each case.

## Columnar trie sorting

One of datatoad's core actions is *reshaping* columnar tries, and it wants to take as much advantage as it can.

The columnar sorting story becomes stronger when we start from a columnar trie.
The layout is already columnar, but it is also helpfully *compressed*.
Imagine we want to re-sort a trie from the column order `(A, B, C)` to the order `(B, C, A)`.
1. The `B` column may be much shorter than the `C` column, and so there is less to sort.
2. When `B` is more complicated to sort, text for example, the reduction is especially well felt.
3. We can avoid ever materializing the uncompressed representation.

The columnar trie reveals structure that can make sorting substantially more efficient than flattening and re-forming.

## Paged radix sorting

Datatoad uses a paged radix sort that is worth discussing.
We use LSB radix sort because we often sort `(usize, [u8; K])` data, which are narrow and byte-ordered.
Radix sort excels at this sort of problem.

Rather than work with one large contiguous array, as LSB radix sort usually does, we'll work with a sequence of smaller "pages".
The pages are small enough that an extra 256 of them are not problematic, but large enough to spend time working through rather than working around.

One benefit of the paged approach is that we are rarely sorting in-place.
We have read the data from somewhere (a file, a trie) and want to write it back to somewhere else (a trie).
The paged approach acquires memory as we fill it (like demand paging), but also *releases* memory as we finish with it (unlike most allocators).
The pages allow us to maintain a smaller footprint as we sort.
