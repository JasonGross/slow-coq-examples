# Slow `vm_compute` and `native_compute` no-ops

To build in 8.5, 8.5pl1, 8.5pl2, or 8.6, run
```
make
```

In
[`src/Specific/GF25519Reflective/Reified/AddCoordinates.v`](./src/Specific/GF25519Reflective/Reified/AddCoordinates.v)
and
[`src/Specific/GF25519Reflective/Reified/LadderStep.v`](./src/Specific/GF25519Reflective/Reified/LadderStep.v),
there is a `vm_compute` and a `native_compute` on the last two lines
of each file that take a long time (around 20 seconds), despite there
not being any computation to do.  The `native_compute` line takes
significantly longer (a few hundred seconds).
