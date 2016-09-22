# Slow `vm_compute`

To build in 8.5, 8.5pl1, 8.5pl2, or v8.6, run
```
make
```

To build in 8.4pl1-pl6, comment out the `Fail Timeout 5 Eval
native_compute in ...` line in
[`src/Specific/FancyMachine256/Barrett.v`](./src/Specific/FancyMachine256/Barrett.v),
and run
```
make
```

In
[`src/Specific/FancyMachine256/Barrett.v`](./src/Specific/FancyMachine256/Barrett.v),
there is a `vm_compute` that I estimate will take about 2-5 hours to
run, while `native_compute`, `lazy`, and `compute` all run in under
0.1 seconds.  The subsequent proof shows a `do` statement that
partially reduces one of the subterms; telling it to go around 21
times makes the `vm_compute` take about 0.4 seconds.  It takes
multiple seconds starting at around 16.
