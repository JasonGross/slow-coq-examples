# Slow `Defined`, slow `End Section`, `cbv` that runs out of memory

To build in Coq 8.4, run
```
cp _CoqProject{.v84,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SlowEndSection.vo -j
```

To build in Coq 8.5, run
```
cp _CoqProject{.v85,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SlowEndSection.vo src/Parsers/Refinement/SlowEndSectionNative.vo -j
```

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

- `End Section` can take 30 seconds, even though there are no section variables, no tactics, no notations, no `Let`s, and only one or two `Definition`s ([bug #4640](https://coq.inria.fr/bugs/show_bug.cgi?id=4640))

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


For convenience, the log of times in `SharpenedJSON`:

In Coq 8.5:
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

In Coq 8.4:
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
