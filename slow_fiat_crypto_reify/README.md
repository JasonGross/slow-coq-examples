# Slow Ltac Reification

To build in 8.4pl1-6, 8.5, 8.5pl1, 8.5pl2, or v8.6, run
```
make
```

In
[`src/Specific/X86/Exponent25519.v`](./src/Specific/X86/Exponent25519.v),
there is an execution of an Ltac reification procedure that can run
for over 90 hours without finishing.
