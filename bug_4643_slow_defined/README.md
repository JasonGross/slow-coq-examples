# Slow `Defined`, slow `End Section`, `cbv` that runs out of memory

To build in Coq 8.4, run
```
cp _CoqProject{.v84,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SharpenedJSON.vo -j
```

To build in Coq 8.5, run
```
cp _CoqProject{.v85,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SharpenedJSON.vo -j
```

The relevant issues are:

- `Defined.` sometimes takes 2 minutes ([bug #4643](https://coq.inria.fr/bugs/show_bug.cgi?id=4643))



Finished transaction in 0. secs (0.u,0.s) (successful)
Finished transaction in 4.875 secs (4.876u,0.s) (successful)
Finished transaction in 1.949 secs (1.944u,0.004s) (successful)
Finished transaction in 114.862 secs (114.812u,0.04s) (successful)
Finished transaction in 668.654 secs (668.544u,0.06s) (successful)
Finished transaction in 39.3 secs (39.296u,0.s) (successful)
Finished transaction in 135.619 secs (135.591u,0.016s) (successful)
Finished transaction in 41.421 secs (41.415u,0.004s) (successful)
Finished transaction in 9.147 secs (9.148u,0.s) (successful)
Finished transaction in 0.503 secs (0.504u,0.s) (successful)
Finished transaction in 94.052 secs (93.952u,0.095s) (successful)
Finished transaction in 5.157 secs (5.051u,0.104s) (successful)
Finished transaction in 0.054 secs (0.051u,0.s) (successful)
Finished transaction in 15.279 secs (15.072u,0.208s) (successful)
src/Parsers/Refinement/SharpenedJSON (user: 1133.46 mem: 4608684 ko)
