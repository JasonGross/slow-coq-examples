# slow-coq-examples
Some examples of Coq being really slow:

- [Bug #4636](https://coq.inria.fr/bugs/show_bug.cgi?id=4636) - `set
  (x := y)` can be 100x slower than `pose y as x; change y with x` -
  see [slow_set.v](./slow_set.v)

- [Bug #4625](https://coq.inria.fr/bugs/show_bug.cgi?id=4625) -
  checking `Defined`/`Qed` causes coqtop to drop the most recent proof
  state.  This makes it a pain to debug things like:
```coq
Definition foo : bar.
Proof.
  some_slow_tactic.
  some_tactic_that_makes_Defined_slow.
Defined.
```
