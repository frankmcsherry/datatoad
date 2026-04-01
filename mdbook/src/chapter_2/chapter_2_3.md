# Worst-case optimal joins

Datatoad's worst-case optimal (WCO) join stages happen when there is one term and multiple atoms.

The WCO stages will build on binary joins as a primitive.
In fact, these stages are just a few binary joins, with a careful switch put in to place.

When a stage has one term and multiple atoms, each atom involves the term and some other set of existing terms (perhaps none).
For each tentative partial fact, a list of term bindings, each atom is probed to ask "how many values of the new term would you introduce?".
Each atom is then joined with the set of tentative partial facts for which the atom proposes the fewest values of the term.
Finally, all newly extended facts are semijoined with all atoms, to confirm that each term that was added works for all atoms.

The operation of counting the values of the term, rather than producing the values, is the new addition.
A WCO join stage starts with the counting, and partitions the facts.
The parts are then joined with each of their respective atoms.
All parts are merged and semijoined with all of the atoms.

## Sequestration

When extending terms `(a, b, c)` to `d` through `body0(b, d)` and `body1(c, d)`, we will "sequester" column `a`.
We rotate the terms to be ordered `(b, c, a)` and then put the last layer to the side.
We then join `(b, c)` to get `(b, c, d)` and re-assemble with the independent `a` column.
Holding `a` to the side reduces the volume of data, potentially asymptotically.
