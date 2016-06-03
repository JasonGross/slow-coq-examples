# slow-coq-examples
Some examples of Coq being really slow:

- [Bug #4636](https://coq.inria.fr/bugs/show_bug.cgi?id=4636) - `set
  (x := y)` can be 100x slower than `pose y as x; change y with x` -
  see [slow_set.v](./slow_set.v)

- [Bug #4776](https://coq.inria.fr/bugs/show_bug.cgi?id=4776) - there
  should be a way to terminate typeclass resolution early - see
  [slow_failing_setoid_rewrite.v](./slow_failing_setoid_rewrite.v)

- [Bug #4669](https://coq.inria.fr/bugs/show_bug.cgi?id=4669) -
  printing of dependent evars in ProofGeneral can slow emacs
  interaction to a crawl (because printing of dependent evars in the
  goal does not respect `Set Printing Width`) - see
  [slow_dependent_evars_in_pg.v](./slow_dependent_evars_in_pg.v), and
  make sure to let it set `coq-end-goals-regexp-show-subgoals` to
  `nil` appropriately.

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
