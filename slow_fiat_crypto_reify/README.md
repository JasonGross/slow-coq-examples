# Slow Ltac Reification

To build in 8.4pl1-6, 8.5, 8.5pl1, 8.5pl2, or v8.6, run
```
make
```

In
[`src/Specific/X86/Exponent25519.v`](./src/Specific/X86/Exponent25519.v),
there is an execution of an Ltac reification procedure that can run
for over 90 hours without finishing.

I suspect the issue is that Coq is extremely slow at typechecking bare
`match` statements.  For example, if I execute the following emacs
commands to fold a subset of the `fst` and `snd` matches, the time to
evaluate the `Definition` goes from 3.3 s to about 2.6 s:
```
M-x replace-regexp RET let (\([^,_]*\), _) := \([^ ]*\) in \1 RET fst \2 RET
M-x replace-regexp RET let (_, \([^,_]*\)) := \([^ ]*\) in \1 RET snd \2 RET
```
