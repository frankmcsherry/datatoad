# Joins

A binary equijoin on shared columns is a trie intersection: walk the shared prefix levels in lockstep, keeping only values that appear in both tries.
For each surviving prefix, the unshared columns from each side are paired up.

Worst-case optimal joins (GenericJoin) generalize this.
Given multiple atoms sharing some terms, instead of picking a fixed pair to join first, the engine asks each atom: "for this prefix, how many extensions would you propose?"
The atom with the fewest proposals wins, proposes its values, and the others validate by semijoin.
This is a per-fact decision — different facts may route to different atoms, depending on which is cheapest for that particular prefix.

In datatoad, both binary joins and worst-case optimal joins are implemented as trie operations on sorted columns.
A single-atom step is a binary join; a multi-atom step is the full count/propose/validate cycle.
The same columnar machinery handles both.

This chapter covers how datatoad evaluates joins: the binary join path, the worst-case optimal join path, how they are unified under a single framework, and how the planner decides which to use.
