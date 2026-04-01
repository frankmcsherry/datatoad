# Joins

In Datalog each rule is translated to a multi-way equijoin.
The rule
```
head(a, b, c) :- body0(a, x, y), body1(b, x, z), body2(c, y, z).
```
is a three-way join between `body0`, `body1`, and `body2`, with equality constraints imposed by the re-use of terms.
The third field of `body0` must equal the second field of `body2`, for example.

Not only do we need to perform joins in Datalog, we often perform *incremental* joins.
These are joins that start from some pre-existing facts, and need to update in response to new facts.
For example, we might have additions to `body0`, written `d_body0`, and need to produce `d_head` in response.
We would like to perform this efficiently, proportional only to the new facts we are producing.

In this section we discuss how datatoad plans and executes joins.
