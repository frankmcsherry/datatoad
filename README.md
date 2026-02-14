# datatoad
An interactive, columnar, worst-case optimal Datalog

[Datalog](https://en.wikipedia.org/wiki/Datalog) is a logic programming language whose evaluation is most commonly based on repeated application of relational equijoins.
A Datalog program is a collection of rules, each of which describes conditions under which some facts being true leads to other facts being true.
When combined with a starting set of facts, rules lead to an iterative process in which more facts can be inferred, iteratively, until eventually no additional facts can be learned.

A classic Datalog example is the `Ancestor` relationship, which can be described from a `Parent` relationship as
```
Ancestor(X, Y) :- Parent(X, Y).
Ancestor(X, Z) :- Parent(X, Y), Ancestor(Y, Z).
```
The two rules here indicate respectively that any parent relationship implies an ancestor relationship, but also that the parent of an ancestor is also an ancestor.
The presence of `Y` twice in the second rule is a constraint that the two terms must be equal, and when this happens the "head" of the rule becomes true with the corresponding bindings of `X` and `Z`.
Having seeded the ancestor relationship with the parent relationship, the second rule enables the derivation of further facts, and then further facts, and so on until saturation.

This project is an exploration of some intersecting attributes a Datalog engine might have.
Many of these are fuzzy intentions, as much as crisp characteristics.

*   It is **interactive** in that the user supplies their logic program to our interpreter program, which evaluates it without additional compilation.
    Intellectually, we are trying to minimize the amount of work we do in reaction to the logic program itself, and in particular work done by other systems (e.g. an external compiler).
    We do think about the logic program and plan how to evaluate it, but do not generate any executable code to help with this.

*   It is **columnar** in that the evaluator is [column-oriented](https://en.wikipedia.org/wiki/Data_orientation) and avoids any row-at-a-time operation.
    This brings some performance benefits, and pitfalls, but importantly unlocks some algorithmic novelty.
    The join algorithm generalizes binary and worst-case optimal joins, supports bidirectional predicates as relations, and is relatively extensible.

*   It is **worst-case optimal** in the sense that its multi-way join implementations parallel an instance of the [Generic Join](https://en.wikipedia.org/wiki/Worst-case_optimal_join_algorithm) framework.
    This is a translation of [the same algorithm being worst-case optimal for insertion-only streaming workloads](https://www.vldb.org/pvldb/vol11/p691-ammar.pdf) to Datalog where facts are only ever inserted, but for non-streaming reasons.

Importantly, the project is an exploration, and so it is for now at least continually a bit of a mess.
You are more than welcome to take a peek, ask questions, that sort of thing, but I would not recommend on relying on it for any particular task.

## An example

If you have some time, you can type the following into PostgreSQL.

```sql
create table arc(x int, y int);
insert into arc select 0, generate_series(1, 1000000);
insert into arc select generate_series(1, 1000000), 0;
insert into arc select x, x+1 from generate_series(1, 1000000) as x;
select count(*)
from arc ab, arc bc, arc ca
where ab.y = bc.x
  and bc.y = ca.x
  and ca.y = ab.x;
```
Put a `\timing` before that and go grab a coffee.

This is a "triangle query", with an input meant to demonstrate why conventional binary joins can be arbitrarily bad.
There is no order to join any pair of `ab`, `ac`, and `bc` that does not transiently produce one trillion intermediate results.

The same fragment in `datatoad`'s Datalog would be written
```
arc(0, x) :- :range(1, x, 1000001).
arc(x, 0) :- :range(1, x, 1000001).
arc(x, y) :- :range(1, x, 1000001), :plus(x, 1, y).

tri(a, b, c) :- arc(a,b), arc(b,c), arc(c,a).
```
For me, this loads the data in ~100ms, and enumerates all triangles in an additional 1s.
Also for me, the PostgreSQL query is still running five minutes later, and has spun up two additional helper processes to help max out my CPUs.

### Predicates as Relations

You may have noticed the `:range` and `:plus` above, and wondered what they represent?
Both are simply relations, but whose contents are backed by logic rather than by data.

* `:range(a, b, c)` contains triples where `a <= b < c`.
* `:plus(a, b, c))` contains triples where `a + b = c`.

These two relations are unbounded in size, and we don't store them explicitly.
Instead, they fit behind a abstraction for relations that is sufficient to participate in worst-case optimal joins.

As another example, the following creates `data(s, r)` of sensors `s` whose readings `r` are either numerous or singular.
```
data(s, r) :- :range(0, s, 256), :range(0, r, 65536).
data(s, s) :- :range(256, s, 65536).
```
We follow this with `asks(s, l, u)` of queries for the readings of a sensor `s` that lie between a lower `l` and upper `u` bound.
Reasonably, we will use a narrow interval for sensors with many measurements, and a wide interval for the sensors with singular measurements.
```
asks(s, 0, 256) :- :range(0, s, 256).
asks(s, 0, 65536) :- :range(256, s, 65536).
```
The sensor readings we would like returned are those that lie between the bound of some ask.
```
back(s, r) :- asks(s, l, u), data(s, r), :range(l, r, u).
```

How might this unfold in a language like SQL?

In one implementation, we might join `asks` and `data`, and then apply the predicate `WHERE r IS BETWEEN l AND u`.
This has the potential to enumerate all of `data`, the majority of which will be from sensors with many measurements, the majority of which we will discard.

An alternate implementation might use `generate_series(l, u)` to produce for each `s` the specific values that we are looking for.
This has the potential to immediately find the one value for each sensor with many measurements and few target targets, but it would be incredibly inefficient for the many sensors with wide query ranges.

Datatoad's worst-case optimal join computes `back` by choosing for each `s` independently the approach above that produces fewer intermediate results.
It either enumerates the sensor's readings, or enumerates the ask's range, whichever are fewer.
The application of worst-case optimal algorithms to logical relations rather than relations defined by data is new to me, and beats having to write either of `BETWEEN` or `generate_series`, to say nothing of having to write both.

PostgreSQL is now at 30m on each of the three processes.

## Evaluation

Much of the exploration is based around the goals of **expressivity**, **performance**, and **robustness**.

Expressivity-wise, I wouldn't be at all surprised to see the project migrate in the direction of an [array language](https://en.wikipedia.org/wiki/Array_programming), or come to a halt as soon as I realize that one exists that accommodates logic programming as well.
Many of the day-to-day changes chase performance on a few reference benchmarks (in a moment), leaning primarily on learnings about columnar evaluation kernels and more thoughtful sequencing of relational work.
Historically, there have been several performance regressions accepted in pursuit of "robustness", a vague attempt to suggest that its benefits apply more uniformly than they used to.

There are several performance benchmarks I've used, and the set evolves a bit as we move to increasingly exotic problem spaces.
Initially the engine was only good on path-following queries, and used [Graspan](https://dl.acm.org/doi/10.1145/3093336.3037744) as a point of comparison.
More recently, the worst-case optimal execution opens the doors to more exotic queries, where I've been using the [GALEN](https://github.com/frankmcsherry/dynamic-datalog/tree/master/problems/galen) workload.
The current state-of-the-art (as I understand it) for GALEN looks like (from table 1 in [a preprint of the FlowLog paper](https://arxiv.org/pdf/2511.00865)):

|   system | cores |   time |
| --------:| -----:| ------:|
| FlowLog  |    64 |   8.7s |
| Soufflé  |    64 |  36.8s |
| RecStep  |    64 | 667.9s |
|   DDlog  |    64 |  64.6s |
| datatoad |     1 |  11.9s |

I've been staring at this particular problem for a while, so don't read too much into the numbers here, except that they seem to be at least competitive.
I should be a grown-up and produce corresponding numbers for the rest of the problems in the paper, including admitting that some of them do not yet run (antijoins, amirite).

## Roadmap

Nothing concrete planned at the moment.

What I'd really like to do is clean up the code a bit more, explain what is going on a bit more, and see if the tidiness presents any new opportunities.
This has worked out rather well in the past, where boiling away the complexity reveals some commonality, or some kernel of hard work to lean in to.
Identifying these, isolating them, and then thinking out loud about them is what I personally find the most interesting about all of this.

Several reasonable folks have asked for better testing and tooling, and that seems to be on the path towards making this more useful to others.
If nothing else, it's helpful to be kept honest about what actually works and just how well.
Me copy/pasting the most recent runtime for that one query I bother to check is no longer the pinnacle of software engineering.
