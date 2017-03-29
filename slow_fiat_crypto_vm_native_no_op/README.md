# Slow `vm_compute` and `native_compute` no-ops

To build in 8.5, 8.5pl1, 8.5pl2, or 8.6, run
```
make
```

In
[`src/Specific/GF25519Reflective/Reified/AddCoordinatesSlowExample.v`](./src/Specific/GF25519Reflective/Reified/AddCoordinatesSlowExample.v)
and
[`src/Specific/GF25519Reflective/Reified/LadderStepSlowExample.v`](./src/Specific/GF25519Reflective/Reified/LadderStepSlowExample.v),
there is a `vm_compute` and a `native_compute` in each file that take
a long time (around 20 seconds for `vm_compute`, a few hundred seconds
for `native_compute`), despite there not being any computation to do.
