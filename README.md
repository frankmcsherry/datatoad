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
    Columns are stored separately, and all operations act on at most one column at a time.
    The specific types of each column are revealed only within these single-column operations, and the type that would be a row (a sequence of column values) is not present in the codebase.

*   It is **worst-case optimal** in the sense that its multi-way join implementations parallel an instance of the [Generic Join](https://en.wikipedia.org/wiki/Worst-case_optimal_join_algorithm) framework.
    The join algorithms provide an arguably stronger property, that I'm not certain I know how to state, that each invocation of the algorithm exhibits a proportionality to the number of new facts, rather than the sum of the sizes of the inputs.
    This requires thoughtful use and maintenance of indexes to avoid doing work linear in the input.
    It is conceivable, for example, that the iterative application of the rules takes no more time than a WCOJ algorithm would take to confirm the join results for the final set of facts.

Importantly, the project is an exploration, and so it is for now at least continually a bit of a mess.
You are more than welcome to take a peek, ask questions, that sort of thing, but I would not recommend on relying on it for any particular task.

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

I should probably make antijoins work.
It turns out all Datalog engines have antijoins in them, and `datatoad` is no exception (you need them to determe which facts are actually novel each iteration).
However, you can't type them in yet, and they need some care to stitch them in to query plans when you do type them (they suppress rather than propose facts).

It is very reasonable to think about a data-parallel implementation, but I'm not eager to race into doing that.
It seems like there might be a few different parallelization idioms to follow, and I could use the experience trying out a few of them before committing to anything.
I'm used to the "partition by join key" approach, and while I can imagine that works well enough, there are other options when one peers closer at the columnar operations, where you could partition each of the columns as well, introducing more shuffling but gaining some robustness.

What I'd really like to do is clean up the code a bit more, explain what is going on a bit more, and see if the tidiness presents any new opportunities.
This has worked out rather well in the past, where boiling away the complexity reveals some commonality, or some kernel of hard work to lean in to.
Identifying these, isolating them, and then thinking out loud about them is what I personally find the most interesting about all of this.

Several reasonable folks have asked for better testing and tooling, and that semes to be on the path towards making this more useful to others.
If nothing else, it's helpful to be kept honest about what actually works and just how well.
Me copy/pasting the most recent runtime for that one query I bother to check is no longer the pinnacle of software engineering.
