# Very Slow `Defined`

To build in 8.6, run
```
make
```

In
[`src/Specific/IntegrationTest.v`](./src/Specific/IntegrationTest.v)
the final `Defined` takes over 30 hours and uses over 10 GB of RAM.
If you replace the final `refine` in the proof with `idtac`, the
`Defined` goes through in under 5 seconds.
