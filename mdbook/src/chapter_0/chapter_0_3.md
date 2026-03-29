# A first example

Running datatoad (`cargo run`), you are dropped into a REPL.
If you would like it to go faster, you can use cargo's `--release` flag.

Let's compute transitive closure of a small graph:

```
> edge(1, 2) :- .
> edge(2, 3) :- .
> edge(3, 1) :- .

> reach(x, y) :- edge(x, y).
> reach(x, y) :- edge(x, z), reach(z, y).
```

Datatoad evaluates the rules to a fixpoint, and then returns a prompt.

The `.list` command prints all relations and their sizes.
You should see something like
```
> .list
         3 edge  [forms: Identity, Permute-1-0]
         9 reach [forms: Identity]
```

To inspect the results you'll want to use the built-in `:print` relation:
```
> temp(x,y) :- reach(x,y), :print(x,y).
```

This prompts a query that consults the `:print` relation, which contains all facts but prints each fact it is queried about.
```
> temp(x,y) :- reach(x,y), :print(x,y).
0x00000001      0x00000001
0x00000001      0x00000002
0x00000001      0x00000003
0x00000002      0x00000001
0x00000002      0x00000002
0x00000002      0x00000003
0x00000003      0x00000001
0x00000003      0x00000002
0x00000003      0x00000003
```

The output is hexadecimal, because the underlying data model is `[u8]`, and integer literals are parsed as 32 bit integers.
