# What is Datatoad?

Datatoad is an interactive, interpreted Datalog engine written in Rust.

Datatoad exists to exercise a few "big ideas" in the context of streaming, incremental, relational computation.
No one of the ideas is fundamentally new, but they come together especially well in datatoad, and complement each other.
The foundation is datatoad's columnar data layout, which allows it to efficiently interpret and dispatch at runtime.
This flexibility unlocks a variety of independently developed concepts, which now compose in ways that were unclear (to me) before.

Some call-outs, each of which we will develop in greater detail:

-   **Columnar from the ground up.**
    Data is stored and processed in columns, not rows.
    All algorithms and primitives work natively on columns; they do not have the ability to form complete rows.
    This reduces the memory footprint, can simplify data alignment, and makes other features practical.

-   **Interpreted, not compiled.**
    You type rules at a REPL and get results immediately.
    There is no compilation step, no generated code, no JIT.
    The engine interprets your program directly.

-   **Lean multi-way join processing**
    Multi-way joins are handled using indexes on input relations, but do not maintain intermediate state.
    Updates flow through the join in multiple directions, using per-atom query update plans.

-   **Worst-case optimal.**
    Datatoad implements multi-way joins by an instance of the GenericJoin algorithm, which provides worst-case optimal guarantees.
    Following the work of [VLDB2018](http://www.vldb.org/pvldb/vol11/p691-ammar.pdf) this gives rise to a worst-case optimal bound for the whole iterative computation.
    Query patterns like triangle enumeration take asymptotically (and empirically) less time than in other systems.

-   **Logic relations.**
    Relations like `:plus`, `:range`, and `:times` participate in worst-case optimal joins as first-class atoms.
    They are bidirectional: `:plus(x, y, z)` can compute `z` from `x` and `y`, or `x` from `y` and `z`.
    The bidirectionality is especially important for multi-way join processing.

-   **Distributed execution.**
    Datatoad can shard data across multiple workers and even multiple machines.
    The columnar layout makes sharing and serialization easy and efficient.
