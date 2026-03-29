# Introduction

This chapter introduces Datalog, datatoad, and gets you running a first example.

Datalog is a declarative logic programming language: you state rules about what should be true, and the engine figures out everything that follows.
Datatoad is an interactive runtime for evaluating Datalog programs, with a focus on robust performance.
It has a few "big ideas", revolving around unlocks from columnar data layouts, which are discussed in the next chapter.

Although a lot of what follows is in the framing of Datalog, relatively little of datatoad is specific to Datalog.
It just happens that Datalog is also a minimal shell of requirements for streaming, incremental, relational joins.
Don't get attached to the logic programming part of the language on my account, at least.
