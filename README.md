# slow-coq-examples
Some examples of Coq being really slow:

- [Bug #4636](https://coq.inria.fr/bugs/show_bug.cgi?id=4636) - `set
  (x := y)` can be 100x slower than `pose y as x; change y with x` -
  see [slow_set.v](./slow_set.v)

- [Bug #3280](https://coq.inria.fr/bugs/show_bug.cgi?id=3280) `match
  goal with |- ?f ?x = ?g ?y => idtac end` can be arbitrarily slow -
  see
  [`evar-normalization-slowness/very_silly_slow_tactic.v`](./evar-normalization-slowness/very_silly_slow_tactic.v)
  and
  [`evar-normalization-slowness/exercise-tactics/exercise-tactics.sh`](./evar-normalization-slowness/exercise-tactics/exercise-tactics.sh).  Also, see this [graph of the time of tactics vs the size of goal](./evar-normalization-slowness/graph.svg)

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

- Bugs [#4643](https://coq.inria.fr/bugs/show_bug.cgi?id=4643)
  [#4640](https://coq.inria.fr/bugs/show_bug.cgi?id=4640), and
  [#4642](https://coq.inria.fr/bugs/show_bug.cgi?id=4642): `Defined.`
  sometimes takes 2 minutes; `End Section` can take 30 seconds, even
  though there are no section variables, no tactics, no notations, no
  `Let`s, and only one or two `Definition`s; and `cbv [some
  identifiers]` can run through 64 GB of RAM in 15 minutes;
  respectively.  See
  [`slow_fiat_examples/README.md`](./slow_fiat_examples/README.md) for
  more details and instructions on running.  (Be warned, some of the
  examples of slowness themselves take 20 minutes to compile.)

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
