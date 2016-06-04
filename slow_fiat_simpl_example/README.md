# Slow `simpl @fst`

To build dependencies in Coq 8.4, run
```
cp _CoqProject{.v84,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SharpenedJSON.vo -j
```

To build dependencies in Coq 8.5, run
```
cp _CoqProject{.v85,} && coq_makefile -f _CoqProject -o Makefile && make TIMED=1 src/Parsers/Refinement/SharpenedJSON.vo -j
```

Then look at the times for `simpl @fst` and `simpl @snd` in
[`src/Parsers/Refinement/SharpenedJSONDebug.v`](./src/Parsers/Refinement/SharpenedJSONDebug.v).
While `simpl @fst` is essentially instantaneous, `simpl @snd` does not
finish in the first hour of execution (though doesn't use more than 2
GB of RAM).

Note: To rebuild the `_CoqProject` files, use:
```bash
(echo "-R src Fiat"; echo '-arg "-compat 8.4"'; find src -name "*.v" -a ! -name "*#*") > _CoqProject.v85
(echo "-R src Fiat"; find . -name "*.v" -a ! -name "*Native.v" -a ! -name "*#*") > _CoqProject.v84
```
