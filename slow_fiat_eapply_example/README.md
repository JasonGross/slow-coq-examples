# Slow `eapply`, slow `simple eapply`

To build in Coq 8.4, run
```
cp _CoqProject{.v84,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SharpenedJavaScriptAssignmentExpression.vo src/Parsers/Refinement/SharpenedJSON.vo -kj
```

To build in Coq 8.5, run
```
cp _CoqProject{.v85,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SharpenedJavaScriptAssignmentExpression.vo src/Parsers/Refinement/SharpenedJSON.vo -kj
```

The relevant issues are:

- `simple eapply` can take 2 hours
  [`src/Parsers/Refinement/SharpenedJavaScriptAssignmentExpression.v`](./src/Parsers/Refinement/SharpenedJavaScriptAssignmentExpression.v)
  and
  [`src/Parsers/Refinement/SharpenedJSON.v`](./src/Parsers/Refinement/SharpenedJSON.v)
  ([bug #4821](https://coq.inria.fr/bugs/show_bug.cgi?id=4821))



Note: To rebuild the `_CoqProject` files, use:
```bash
(echo "-R src Fiat"; echo '-arg "-compat 8.4"'; find src -name "*.v" -a ! -name "*#*") > _CoqProject.v85
(echo "-R src Fiat"; find . -name "*.v" -a ! -name "*Native.v" -a ! -name "*#*") > _CoqProject.v84
```
