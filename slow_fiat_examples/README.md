# Slow `Defined`, slow `End Section`, `cbv` that runs out of memory

To build in Coq 8.4, run
```
cp _CoqProject{.v84,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SlowEndSection.vo src/Parsers/Grammars/ExpressionNumPlusParen.vo -j
```

To build in Coq 8.5, run
```
cp _CoqProject{.v85,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SharpenedJSONDependencies.vo src/Parsers/Grammars/ExpressionNumPlusParen.vo -j && make TIMED=1 OTHERFLAGS="-compat 8.4" src/Parsers/Refinement/SlowEndSection.vo src/Parsers/Refinement/SlowEndSectionNative.vo -j
```

N.B. Your system will run out of memory (mine did with 64 GB of RAM)
if you try to compile `src/Parsers/Refinement/SharpenedJSON` to native
code.  This is why there are two invocations of `make` for Coq 8.5.

The relevant issues are:

- `Defined.` sometimes takes 2 minutes ([bug
  #4643](https://coq.inria.fr/bugs/show_bug.cgi?id=4643))

  . This is the `Time Definition ComputationalSplitter' ...` in
    [`src/Parsers/Refinement/SlowEndSection.v`](./src/Parsers/Refinement/SlowEndSection.v).
    (Actually, for unknown reasons, although the `Defined` only takes
    2 minutes, this `Definition` takes 581 seconds in 8.5, and a
    whopping 1266 seconds in 8.4.)

  . To see it as a `Defined`, look at the first `Time Defined.` in
    [`src/Parsers/Refinement/SharpenedJSON.v`](./src/Parsers/Refinement/SharpenedJSON.v).
    The `SlowEndSection.v` file is to be able to skip over the 7-15
    minute-long proof script, if you want to compile the script in
    advance.

  . Look at
    [`src/Parsers/Refinement/SlowEndSectionNative.v`](./src/Parsers/Refinement/SlowEndSectionNative.v)
    in Coq 8.5 to see the effect of using `native_compute` rather than
    `vm_compute`

- `End Section` can take 30 seconds, even though there are no section
  variables, no tactics, no notations, no `Let`s, and only one or two
  `Definition`s ([bug
  #4640](https://coq.inria.fr/bugs/show_bug.cgi?id=4640))

  . This is `Time End IndexedImpl.` in
    [`src/Parsers/Refinement/SlowEndSection.v`](./src/Parsers/Refinement/SlowEndSection.v)
    (or
    [`src/Parsers/Refinement/SlowEndSectionNative.v`](./src/Parsers/Refinement/SlowEndSectionNative.v)
    to see the impact of `native_compute` in 8.5)

  . Alterntively, to see the original example, look at `Time End
    IndexedImpl.` in
    [`src/Parsers/Refinement/SharpenedJSON.v`](./src/Parsers/Refinement/SharpenedJSON.v).
    This is actually faster in 8.4 than looking at
    [`src/Parsers/Refinement/SlowEndSection.v`](./src/Parsers/Refinement/SlowEndSection.v),
    because retypechecking the proof apparently takes a bit longer
    than the entire proof script and the `Defined` combined.

- `cbv [some identifiers]` can run through 64 GB of RAM in 15 minutes
  ([bug #4642](https://coq.inria.fr/bugs/show_bug.cgi?id=4642))

  . This is `let term := (eval parser_red5 in term) in` in
    [`src/Parsers/Refinement/SharpenedJSONDebug.v`](./src/Parsers/Refinement/SharpenedJSONDebug.v)

- `pose y as x; change y with x in H` can take 1300x longer than `set
  (x := y) in H`.  See `Time refine_binop_table.` in
  [`src/Parsers/Refinement/SharpenedExpressionPlusParen.v`](./src/Parsers/Refinement/SharpenedExpressionPlusParen.v).
  If we made the same replacement in `SharpenedJSON`, `change` blows
  through 64 GB of RAM before crashing Coq, in about 10-20 minutes.
  (By contrast, `set` takes 0.2 s.)

For convenience, the log of times in `SharpenedJSON`:

In Coq 8.4pl6:
```
Finished transaction in 0. secs (0.u,0.s)              Time start sharpening ADT.
Finished transaction in 5. secs (5.88u,0.036s)         Time start honing parser using indexed representation.
Finished transaction in 2. secs (1.328u,0.s)           Time hone method "splits".
Finished transaction in 27. secs (27.672u,0.008s)      Time simplify parser splitter.
Finished transaction in 226. secs (225.596u,0.052s)    Time rewrite_disjoint_search_for.
Finished transaction in 16. secs (15.628u,0.008s)      Time rewrite_disjoint_rev_search_for.
Finished transaction in 56. secs (56.588u,0.s)         Time progress repeat refine_binop_table.
Finished transaction in 28. secs (27.8u,0.012s)        Time simplify parser splitter.
Finished transaction in 2. secs (1.832u,0.s)           Time finish honing parser method.
Finished transaction in 0. secs (0.084u,0.s)           Time finish_Sharpening_SplitterADT.
Finished transaction in 141. secs (140.48u,0.092s)     Time Defined.
Finished transaction in 17. secs (16.668u,0.364s)      Time make_simplified_splitter ComputationalSplitter'.
Finished transaction in 0. secs (0.0799999999999u,0.s) Time Defined.
Finished transaction in 31. secs (30.956u,0.16s)       Time End IndexedImpl.
```

In Coq 8.5pl1:
```
Finished transaction in 0. secs (0.u,0.s) (successful)              Time start sharpening ADT.
Finished transaction in 4.875 secs (4.876u,0.s) (successful)        Time start honing parser using indexed representation.
Finished transaction in 1.949 secs (1.944u,0.004s) (successful)     Time hone method "splits".
Finished transaction in 114.862 secs (114.812u,0.04s) (successful)  Time simplify parser splitter.
Finished transaction in 668.654 secs (668.544u,0.06s) (successful)  Time rewrite_disjoint_search_for.
Finished transaction in 39.3 secs (39.296u,0.s) (successful)        Time rewrite_disjoint_rev_search_for.
Finished transaction in 135.619 secs (135.591u,0.016s) (successful) Time progress repeat refine_binop_table.
Finished transaction in 41.421 secs (41.415u,0.004s) (successful)   Time simplify parser splitter.
Finished transaction in 9.147 secs (9.148u,0.s) (successful)        Time finish honing parser method.
Finished transaction in 0.503 secs (0.504u,0.s) (successful)        Time finish_Sharpening_SplitterADT.
Finished transaction in 94.052 secs (93.952u,0.095s) (successful)   Time Defined.
Finished transaction in 5.157 secs (5.051u,0.104s) (successful)     Time make_simplified_splitter ComputationalSplitter'.
Finished transaction in 0.054 secs (0.051u,0.s) (successful)        Time Defined.
Finished transaction in 15.279 secs (15.072u,0.208s) (successful)   Time End IndexedImpl.
src/Parsers/Refinement/SharpenedJSON (user: 1133.46 mem: 4608684 ko)
```

In Coq 8.5pl1 using `native_compute`:
```
Finished transaction in 0. secs (0.u,0.s) (successful)               Time start sharpening ADT.
Finished transaction in 5.056 secs (4.864u,0.035s) (successful)      Time start honing parser using indexed representation.
Finished transaction in 1.982 secs (1.976u,0.008s) (successful)      Time hone method "splits".
Finished transaction in 115.609 secs (115.556u,0.043s) (successful)  Time simplify parser splitter.
Finished transaction in 608.772 secs (601.812u,1.636s) (successful)  Time rewrite_disjoint_search_for.
Finished transaction in 35.037 secs (34.543u,0.104s) (successful)    Time rewrite_disjoint_rev_search_for.
Finished transaction in 122.969 secs (122.764u,0.076s) (successful)  Time progress repeat refine_binop_table.
Finished transaction in 41.725 secs (41.716u,0.008s) (successful)    Time simplify parser splitter.
Finished transaction in 9.226 secs (9.223u,0.s) (successful)         Time finish honing parser method.
Finished transaction in 0.503 secs (0.504u,0.s) (successful)         Time finish_Sharpening_SplitterADT.
Finished transaction in 1037.209 secs (818.476u,1.396s) (successful) Time Defined.
Finished transaction in 5.083 secs (5.028u,0.056s) (successful)      Time make_simplified_splitter ComputationalSplitter'.
Finished transaction in 0.054 secs (0.052u,0.s) (successful)         Time Defined.
Finished transaction in 14.39 secs (14.283u,0.108s) (successful)     Time End IndexedImpl.
```

In Coq 8.4pl6 using `lazy`:
```
Finished transaction in 0. secs (0.u,0.s)                  Time start sharpening ADT.
Finished transaction in 11. secs (10.388u,0.012s)          Time start honing parser using indexed representation.
Finished transaction in 1. secs (1.296u,0.012s)            Time hone method "splits".
Finished transaction in 28. secs (28.156u,0.016s)          Time simplify parser splitter.
Finished transaction in 677. secs (676.072u,0.22s)         Time rewrite_disjoint_search_for.
Finished transaction in 158. secs (158.248u,0.048s)        Time rewrite_disjoint_rev_search_for.
Finished transaction in 926. secs (925.812u,0.236s)        Time progress repeat refine_binop_table.
Finished transaction in 29. secs (28.532u,0.s)             Time simplify parser splitter.
Finished transaction in 1. secs (1.836u,0.s)               Time finish honing parser method.
Finished transaction in 1. secs (0.0840000000001u,0.s)     Time finish_Sharpening_SplitterADT.
Finished transaction in 1242. secs (1241.476u,0.356s)      Time Defined.
Finished transaction in 17. secs (17.072u,0.088s)          Time make_simplified_splitter ComputationalSplitter'.
Finished transaction in 0. secs (0.0719999999997u,0.004s)  Time Defined.
Finished transaction in 31. secs (31.164u,0.028s)          Time End IndexedImpl.
```

So something performance-tuned for Coq 8.4 can be much slower in Coq
8.5.  (I suspect part of it is that `set (x := y)` is about 50x slower
than it needs to be in Coq 8.4, but is about 4x faster than the
alternatives in 8.5.  See [bug
#3280](https://coq.inria.fr/bugs/show_bug.cgi?id=3280) ([comment
13](https://coq.inria.fr/bugs/show_bug.cgi?id=3280#c13)) for more
details.)


Note: To rebuild the `_CoqProject` files, use:
```bash
(echo "-R src Fiat"; echo '-arg "-compat 8.4"'; echo '-arg "-native-compiler"'; find src -name "*.v" -a ! -name "*#*") > _CoqProject.v85
(echo "-R src Fiat"; find . -name "*.v" -a ! -name "*Native.v" -a ! -name "*#*") > _CoqProject.v84
```
