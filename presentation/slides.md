---
marp: true
theme: default
paginate: false
title: Worst-Case Optimal Datalog (++)
author: Frank McSherry
---

<style>
/* Fix titles at the top: top-align content slides (those whose first element
   is an h2) so the title stays put regardless of how much content follows. */
section:has(> h2:first-child) {
  display: flex;
  flex-direction: column;
  justify-content: flex-start;
}
</style>

# Worst-Case Optimal Datalog (++)

Frank McSherry
Minnowbrook Analytic Reasoning Seminar
June 2026

---

## Context: [`datatoad`](https://github.com/frankmcsherry/datatoad) framework

A { columnar, wco, ~directional, .. } Datalog (Z?)

- Columnar data layout and computation.
- Worst-case optimal incremental joins. ([Ammar et al., VLDB 2018](https://www.vldb.org/pvldb/vol11/p691-ammar.pdf))
- { bi / many / omni } - directional predicates.
- Interactive, Distributed, Low memory, ..

Came out of last year's version of this seminar.


---

<style scoped>section { padding: 28px; }</style>

<iframe src="http://localhost:8000/" width="1180" height="640"
        style="border:1px solid #d0d7de; border-radius:8px; display:block; margin:0 auto;"></iframe>

---

## Talk outline

1.  My favorite worst-case optimal join algorithm (columnar).

2.  WCO join bounds (can) extend to indexes, streaming, iteration.

3.  Columnar WCOJ is actually a nice **interface** to relations.

    - Disjunctive clauses (body only)
    - Directional predicates
    - FFI / Extensibility

4.  Comments, provocations, and future directions.

---

## Columnar WCO Joins (1/2)

An instance of GenericJoin (NPRR).

    Head(T0, T1, .. ) :- Body0(T1, ..), Body1(.., T0), .. BodyK(Tj) .

<div style="height: 0.6em"></div>

Develop assignments satisfying the body projected on increasing subsets of terms.
1.  Terms start `{ }`, trivial assignment satisfies the body (if all non-empty).
2.  Repeatedly add a new term, update satisfying assignments by that term.
3.  Project down to head terms (and as you go, if you like).

---

## Columnar WCO Joins (2/2)

An instance of GenericJoin (NPRR).

    Head(T0, T1, .. ) :- Body0(T1, ..), Body1(.., T0), .. BodyK(Tj) .

<div style="height: 0.6em"></div>

To extend an assignment `A` by a term `Ti`, each involved atom does three things
1. Each atom that mentions `Ti` **counts**
    1. for each `a` in `A` its distinct compatible `ti` values.
1. Each atom that mentions `Ti` **extends** by `ti \in Ti`
    1. each `a` in `A` for which it had the least count.
1. Each atom that mentions `Ti` **validates**
    1. each extended assignment `[a;Ti=ti]`.

---

## Streaming WCO Joins (1/2)

    Head(T0, T1, .. ) :- Body0(T1, ..), Body1(.., T0), .. BodyK(Tj) .

What actually happens is that the input atoms *change*: `dBody0`, `dBody1`, ... `dBodyK`.

<div style="height: 0.6em"></div>

Could restart from scratch, but can also determine `dHead`:

    dHead = dBody0, (Body1 + dBody1), .., (BodyK + dBodyK)
          + dBody1, (Body0 + dBody0), .., (BodyK + dBodyK)
          + ..
          + dBodyK, (Body0 + dBody0), (Body1 + dBody1), ..

A sequence of *seeded* WCO joins, against maintained indexes. Constrained term order.

---

## Streaming WCO Joins (2/2)

    Head(T0, T1, .. ) :- Body0(T1, ..), Body1(.., T0), .. BodyK(Tj) .

What actually happens is that the input atoms *change*: `dBody0`, `dBody1`, ... `dBodyK`.

<div style="height: 0.6em"></div>

**Theorem:** *For append-only changes, the WCO bound applies using the final atom sizes.*

For [Ammar et al]: "Streaming WCO Joins", but here "WCO Datalog".

**Corollary:** For each Datalog rule, the WCO bound applies using the final atom sizes.

---

## Columnar WCO Joins: An API

```rust
/// A type that can participate in WCO joins.
pub trait ExecAtom<T> {

    /// An initial set of facts, either the recent facts or all facts.
    fn facts(&self, recent: bool) -> Facts<T>;

    /// The number of values of `added` terms that extend each fact.
    fn count(&self, facts: &mut Facts<T>, added: &Set<T>);

    /// Join or semijoin `facts` with `self`, introducing `added`.
    fn join(&self, facts: &mut Facts<T>, added: &Set<T>);

}
```

---

## What implements `ExecAtom`?

1. Stored relations (the obvious one)
2.
3.
4.
5.

---

## What implements `ExecAtom`?

1. Stored relations (the obvious one)
2. Antijoins .. wait.
3.
4.
5.

---


## Columnar WCO Joins: Another API

```rust

/// A type that can be *planned* in WCO joins
pub trait PlanAtom<T> {

    /// Terms the atom references.
    fn terms(&self) -> Set<T>;

    /// Terms that can be made concrete from other concrete terms.
    ///
    /// The output are cardinality bounds, like Mercury's determinism levels.
    fn modes(&self, from: &Set<T>, onto: &Self<T>) -> (usize, Option<usize>);

}
```

---

## What implements `PlanAtom + ExecAtom`?

1. Stored relations (the obvious one)
2. Antijoins.
3. Disjunctions.
4.
5.

---

## What implements `PlanAtom + ExecAtom`?

1. Stored relations (the obvious one)
2. Antijoins.
3. Disjunctions.
4. Logic (Relations)
5.

---

## Logic Atoms

Consider:

```
:plus(a, b, c) : { (a, b, c) | a + b = c }
```

<div style="height: 0.6em"></div>

Is it a predicate, or a function, or a relation?

1. As a **predicate** it can map `(a, b, c)` to present or not.
2. As a **function** it can map `(a, b)` to `c`.
3. As a **relation** it can map any two of `{ a, b, c }` to the other.

This is enough for `PlanAtom + ExecAtom`.

---

## `:plus` in action

```
tri1(a, b, c) :- arc(a, b), arc(b, c), arc(c, a).
```
```
tri2(a, b, c) :- arc(a, b), arc(b, c), arc(c, a), :plus(a, b, c).
```

The secord query can have far fewer results, but do we notice in time?

|  N=1000       | `tri1` | `tri2` |
|---------------|-------:|-------:|
| Outputs       |     1B |  ~500K |
| Time          | 117.4s |  196ms |

---

## A more-WCO example

Sensors `s` with readings `r`; few are noisy, many are not.
```
data(s, r) :- :range(0, s, 256), :range(0, r, 65536).
data(s, s) :- :range(256, s, 65536).
```
Queries for sensors `s` have ranges `[l, u)`; narrow for noisy, wide for others.
```
asks(s, 0, 256) :- :range(0, s, 256).
asks(s, 0, 65536) :- :range(256, s, 65536).
```
Intersecting the query range with the sensor readings
```
query(s, r) :- asks(s, l, u), data(s, r), :range(l, r, u).
```

---

## Connecting to relational programming

Languages that have supported this for years:

- **CLP** (Prolog with `clpfd`, etc.) — via constraint solvers.
- **Mercury** — via compile-time mode declarations.
- **Kanren family** — via runtime unification + search.

Maybe new here: **the WCOJ count protocol as the mechanism**.
<!--
Generous to prior art. The "marriage of relational programming with WCOJ throughput"
is the framing that lands here. Hemann is in the room.
-->



---


## What implements `PlanAtom + ExecAtom`?

1. Stored relations (the obvious one)
2. Antijoins.
3. Disjunctions.
4. Logic (Relations)
5. Extensibility (FFI)

---

```
┌────────────────┬────────┬────────┬────────┬────────┬─────────┐
│    problem     │  1×1   │  1×4   │  4×1   │  4×4   │ 1×1→4×4 │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ galen          │  10.10 │   5.01 │   4.65 │   3.38 │    3.0× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ tc-10k         │  19.58 │   8.94 │   7.13 │   2.74 │    7.1× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ sg-10k         │  34.63 │  14.35 │  12.01 │   4.67 │    7.4× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ cspa           │  29.47 │  11.46 │  10.18 │   4.25 │    6.9× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ dyck           │   1.48 │   0.81 │   0.75 │   0.41 │    3.6× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ csda           │   1.48 │   0.70 │   0.73 │   0.43 │    3.4× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ andersen       │   1.86 │   1.33 │   1.26 │   0.68 │    2.7× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ cvc5           │  43.51 │  15.73 │  13.70 │   8.48 │    5.1× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ z3             │  55.87 │  27.95 │  28.40 │  22.58 │    2.5× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ reach          │  46.74 │  15.25 │  11.48 │   7.70 │    6.1× │
├────────────────┼────────┼────────┼────────┼────────┼─────────┤
│ batik          │ 254.59 │ 216.67 │ 184.80 │ 187.53 │    1.4× │
└────────────────┴────────┴────────┴────────┴────────┴─────────┘
```

---

## Closing

Worst-case optimal Datalog is neat and different from WCO Join.

But the **columnar orientation** also turns out to be a uniform interface:

- Stored relations
- Antijoins
- Sums and differences
- Directional predicates
- External data

Each adds capability without new engine machinery.
Columnar WCO Datalog ends up being a substrate, not just a faster engine.

---

## Hackathon

> "Bring your hard query, we'll run it on datatoad / <your system>."

We'll be kicking some tires — please come with your worst.

---

## Conversation starters

Things I'd like to argue for over coffee:

1. **Columnar WCOJ is the easiest version of WCOJ to explain.**
2. **Demand transform fights against worst-case-optimal joins.**
    WCOJ presuppose materialization; demand presupposes avoiding it.
3. **Free Join and datatoad converged on similar territory from different sides.**
    Both interpolate between binary and wco join plans. That's all I know.
4. **Relational programming + Datalog = a thing?**
    Kanren / Mercury / CLP traditions meet bottom-up Datalog.
5. **Factorized DBs narrowly avoided.** Same principles at play; less random access.
6. **Columnar WCOJ as an interface is worth it.** Compositionality often MIA.

---

## Language I'm working with now (DDIR)

<style scoped>
section { padding: 28px; }
pre.code { max-height: 656px; overflow: auto; margin: 0; padding: 14px 16px;
  font-size: 23px; line-height: 1.35; white-space: pre;
  background: #f6f8fa; border: 1px solid #d0d7de; border-radius: 6px; }
</style>

<pre class="code">
let edges = input 0 | key($0[0] ; $0[1]);
let trans = edges | key($1 ; $0);

outer: {
    let scc = edges + trim;

    fwd: {
        let nodes = edges | key($1 ; $1) | enter_at($1[0]);
        let labels = proposals + nodes | min;
        var proposals = labels | join(scc, ($2 ; $1));
    }

    let trim_fwd = edges
        | join(fwd::labels, ($1 ; $0, $2))
        | join(fwd::labels, ($0 ; $1, $2))
        | filter($1[1] == $1[2])
        | key($0 ; $1[0]);

    bwd: {
        let nodes = trans | key($1 ; $1) | enter_at($1[0]);
        let labels = proposals + nodes | min;
        var proposals = labels | join(trim_fwd, ($2 ; $1));
    }

    let trim_bwd = trans
        | join(bwd::labels, ($1 ; $0, $2))
        | join(bwd::labels, ($0 ; $1, $2))
        | filter($1[1] == $1[2])
        | key($0 ; $1[0]);

    var trim = trim_bwd - edges;
}

result outer::scc | map(;) | arrange | inspect(total);</pre>

---

# Thanks

Questions?
