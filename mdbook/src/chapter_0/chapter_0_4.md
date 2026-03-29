# Showing off

The previous example was deliberately simple.
Let's look at some things that make datatoad interesting.

## Triangle queries

A triangle query finds all triples `(a, b, c)` that share all pairwise edges in a graph.
It's a standard benchmark because it is deceptively hard for conventional binary join engines.

First, let's build a graph with a million edges designed to make binary joins suffer:
```
arc(0, x) :- :range(1, x, 1000001).
arc(x, 0) :- :range(1, x, 1000001).
arc(x, y) :- :range(1, x, 1000001), :plus(x, 1, y).
```
This creates a star around node 0 (a million spokes in each direction) plus a long path from one to one million.
Any binary join plan for triangles on this graph must consider roughly a trillion intermediate results, because joining any two copies of `arc` produces every pair of edges through node 0: one million, squared.

The triangle query itself is one line:
```
tri(a, b, c) :- arc(a,b), arc(b,c), arc(c,a).
```

Datatoad handles this in about a second.
A worst-case optimal join avoids the intermediate blowup entirely: for each `(a,b)` it finds the `c` by intersecting values from `arc(b,c)` and `arc(c,a)` efficiently, and similarly for the other edge inputs.

For comparison, the equivalent SQL
```sql
select count(*)
from arc ab, arc bc, arc ca
where ab.y = bc.x
  and bc.y = ca.x
  and ca.y = ab.x;
```
will keep PostgreSQL busy for the better part of an hour (at least; I haven't waited long enough to find out).
Try it out!

## Logic relations

You may have noticed `:range` and `:plus` in the example above.
These are *logic relations*: relations whose contents are defined by logic rather than by stored data.

- `:range(a, x, b)` contains all triples where `a <= x < b`.
- `:plus(x, y, z)` contains all triples where `x + y = z`.

These relations are unbounded in size and are never stored explicitly.
Instead, they sit behind an abstraction that lets them participate directly in worst-case optimal joins — answering "which values extend this prefix?" on the fly.

Imagine a set of sensors `s` with integer readings `r`, and monitoring intervals `[lo, hi)` for each sensor:
```
hits(s, r) :- asks(s, lo, hi), data(s, r), :range(lo, r, hi).
```
The right join strategy depends on the sensor, and the relative sizes of `[lo, hi)` and its number of its readings.
Noisy sensors with many readings and a tight range should enumerate the range and intersect with the readings.
Quiet sensors with few readings and a wide range should enumerate their readings and validate each with the range.
Datatoad picks the right strategy sensor-by-sensor, rather than choosing one join plan for all sensors as in SQL.

Logic relations are also bidirectional: `:plus(x, y, z)` can compute `z` from bound `x` and `y`, or solve for `x` given `y` and `z`.
This means the join planner can use them flexibly, choosing whichever direction produces fewer candidates.
When presented with a query like
```
result(x, y, z) :- in1(x, y), in2(y, z), in3(x, z), :plus(x, y, z).
```
the introduction of a new tuple through any input can, via `:plus`, immediately form one candidate result, which then only needs to be validated with the other inputs.
If `:plus` could only convert `(x, y)` to `z`, and not other directions, then the rule would only be efficient for facts produced through `in1(x, y)`; the other inputs would need to join to propose `x` before the predicate could test it.

## Distributed execution

Datatoad can shard work across multiple workers and machines.
To run with four workers on one machine:
```
cargo run --release -- -w 4
```
Each worker maintains its own shard of the data, exchanging facts by hash as rules produce them.
The same REPL, the same rules — just more workers.

To run across multiple machines, provide a common hostfile listing their addresses (as `addr:port` on new lines) in order:
```
cargo run --release -- -n 4 -p 0 --hostfile hostfile.txt
```
where each machine runs with its own `-p` index, starting at zero.
This uses timely-communication's networking layer under the hood, so the coordination model is the same whether workers are local threads or remote processes.

## Planting face

The showing off notwithstanding, datatoad is very much a work in progress.
There are many things it should do that it doesn't yet do, for example not crashing in surprising ways.
Some of the best examples are cherry picked, to make a point more than convince you to use datatoad.

And yet, it is all meant to work.
Reach out when you encounter problems, and we can add them to the list.
