# What is Datalog?

Datalog is a declarative language for expressing recursive queries over relations.

A Datalog program consists of *facts* (things that are true) and *rules* (ways to derive new facts from existing ones).

For example, given edges in a graph:

```
edge(1, 2).
edge(2, 3).
edge(3, 4).
```

We can define reachability:

```
reach(x, y) :- edge(x, y).
reach(x, y) :- edge(x, z), reach(z, y).
```

The first rule says: if there is an edge from `x` to `y`, then `y` is reachable from `x`.
The second says: if there is an edge from `x` to `z`, and `y` is reachable from `z`, then `y` is reachable from `x`.

The engine computes the fixpoint: it repeatedly applies the rules until no new facts are derived.
The result is every `(x, y)` pair where `y` is reachable from `x`.

## Incremental Datalog

The core loop of (semi-naive, bottom-up) Datalog evaluation is
1. Starting from some novel facts,
2. Determine through rules candidate facts that may be novel,
3. Remove any pre-existing facts from the candidates, then call them novel,
4. Repeat as long as there are any novel facts.

This loop is very similar to the bones of streaming, incremental, relational computation.
Our connection to Datalog is through a shared interest in these properties.
