# slow-coq-examples

## Preface

My experience with slowness is that slowness is most often caused by
Coq doing work it doesn't need to do.  Usually, this work comes in the
form of retypechecking terms it shouldn't need to retypecheck, and
occasionally it comes in the form of (re)doing typeclass search that
can be known to be useless.  I don't want to have to micro-optimize my
tactic scripts to get 1000x speed-ups.  In general, I have the sense
that I can't trust Coq to be fast, and I can't trust scripts that are
fast to remain fast in future versions of Coq unless I'm proactive
about reporting bugs and performance regressions.

## Specifics

The "Assessment" tags below were created after discussion with the Coq INRIA
team.

Some examples of Coq being really slow:

- [`vm_native_slower_extraction.v`](./vm_native_slower_extraction.v) -
  `native_compute` is about 14x-16x slower than `ocamlopt` extraction,
  `vm_compute` is another 2x-3x slower.

- [Bug #5148](https://coq.inria.fr/bugs/show_bug.cgi?id=5148) - Ltac
  reification of moderate sized terms can take over 90 hours - see
  [`slow_fiat_crypto_reify/README.md`](./slow_fiat_crypto_reify/README.md)
  for more details.

  **Assessment**: Ltac is inherently slow here, low priority to fix

- [Bug #5146](https://coq.inria.fr/bugs/show_bug.cgi?id=5146) -
  `nsatz` can sometimes spend 10 minutes or more in reification - see
  [`slow_nsatz.v`](./slow_nsatz.v).

  **Assessment**: The code is in ML, rather than Ltac, it may be
  possible to improve, but still this is a low priority issue

- [Bug #3441](https://coq.inria.fr/bugs/show_bug.cgi?id=3441) - `pose
  proof H as k` is sometimes an order of magnitude slower than `pose H
  as k; clearbody k` - see [`slow_pose_proof.v`](./slow_pose_proof.v)
  for an example of a 4x slowdown.

  **Assessment**: Unification here uses matching instead of
  let-binding; pose proof uses a different code path than vanilla
  pose, which disallows patterns; shares code with [set]; needs
  further study

- [Bug #3280](https://coq.inria.fr/bugs/show_bug.cgi?id=3280) `match
  goal with |- ?f ?x = ?g ?y => idtac end` can be arbitrarily slow -
  see
  [`evar-normalization-slowness/very_silly_slow_tactic.v`](./evar-normalization-slowness/very_silly_slow_tactic.v)
  and
  [`evar-normalization-slowness/exercise-tactics/exercise-tactics.sh`](./evar-normalization-slowness/exercise-tactics/exercise-tactics.sh).
  Also, see this [graph of the time of tactics vs the size of
  goal](./evar-normalization-slowness/graph.svg)

  **Assessment**: This is a normalization issue, can't get rid of it;
  won't be fixed for 8.6, in any case; maybe for 8.7

- [Bug #4819](https://coq.inria.fr/bugs/show_bug.cgi?id=4819) -
  interactive time is impacted by large terms that don't exist anymore
  in the goal -
  [`interactive_proof_state_slowness.v`](./interactive_proof_state_slowness.v)
  ([`interactive_proof_state_slowness.sh`](./interactive_proof_state_slowness.sh)
  for Coq 8.5, unless you want to use `coqtop -emacs -time <
  interactive_proof_state_slowness.v`)

  **Assessment**: The issue is specific to the -emacs flag to coqtop
  and to ProofTree, which will be broken in 8.6; need to make a
  decision about printing dependent evars

- [Bug #4662](https://coq.inria.fr/bugs/show_bug.cgi?id=4662) -
  `unfold ... in ...` should insert a cast annotation, else `Defined`
  can take over 6 minutes when it doesn't need to - see
  [`slow_unfold.v`](./slow_unfold.v)

- [Bug #4637](https://coq.inria.fr/bugs/show_bug.cgi?id=4637) -
  `vm_compute in ...` should insert vm_casts - see
  [`missing_vm_casts.v`](./missing_vm_casts.v)

  **Assessment**: these two cast issues are known problems; need to run
  experiments to know what's the best resolution

- [Bug #4776](https://coq.inria.fr/bugs/show_bug.cgi?id=4776) - there
  should be a way to terminate typeclass resolution early - see
  [`slow_failing_setoid_rewrite.v`](./slow_failing_setoid_rewrite.v)

  **Assessment**: Ltac2 will allow such termination via a non-backtracking
  exception mechanism, tentatively named "panic"

- [Bug #4636](https://coq.inria.fr/bugs/show_bug.cgi?id=4636) - `set
  (x := y)` can be 100x slower than `pose y as x; change y with x` -
  see [`slow_set.v`](./slow_set.v).  (The reverse can also happen,
  where `change` is orders of magnitude slower than `set`.  See also
  [bug #4779](https://coq.inria.fr/bugs/show_bug.cgi?id=4779), below.

  **Assessment**: we now have SSReflect's search algorithm, but need
  to study whether it's in fact better; a redesign is needed to
  share the search algorithm among tactics

- [Bug #4639](https://coq.inria.fr/bugs/show_bug.cgi?id=4639) -
  running `simpl @snd` can take over 158 hours - see
  [`slow_fiat_simpl_example/README.md`](./slow_fiat_simpl_example/README.md)

  **Assessment**: the solution is not to use [cbn], there are
  inefficiencies in [simpl] that might be fixed; in the longer term,
  a grander scheme is to uses something like [rewrite_strat], which
  takes a strategy as a parameter

- [Bug #4657](https://coq.inria.fr/bugs/show_bug.cgi?id=4657) -
  `omega` is slow on `x - y - (x - y - x) = x - y` (takes about 1 s,
  when it solves an equivalent equation in 0.06 s) - see
  [`slow_omega.v`](./slow_omega.v)

  **Assessment**: the [omega] code is a mess, it needs to be reviewed

- [Bug #4810](https://coq.inria.fr/bugs/show_bug.cgi?id=4810) - if the
  type of the field is a projection from a record, then the
  performance of `field_simplify_eq` is linear in the *number of
  record fields of that record*, which is absurd, given that the
  fields of the record shouldn't matter.

  **Assessment**: one solution is to use primitive projections, which
  is not difficult, but that raises another issue, because it breaks
  the naming of functions

- [Bug #3448](https://coq.inria.fr/bugs/show_bug.cgi?id=3448) - `Hint
  Extern (foo _) => ...` is significantly slower than `Hint Extern foo
  => ...`; typeclass resolution is slow at `intro` - see
  [`slow_typeclasses_intro.v`](./slow_typeclasses_intro.v)

  **Assessment**: the slowness here is due to repeated unification of
  function types; we'll postpone looking at this

- [Bug #5038](https://coq.inria.fr/bugs/show_bug.cgi?id=5038) -
  `Definition` does head-zeta-reduction.  See
  [`slow_lets.v`](./slow_lets.v) for an example of exponential
  behavior.

  **Assessment**: maybe the let-unfolding could be done lazily, or
  maybe it's not really a bug; or maybe the fix is just to remove the
  code

  [Bug #4642](https://coq.inria.fr/bugs/show_bug.cgi?id=4642) -
  `cbv [some identifiers]` can run through 64 GB of RAM in 15 minutes;
  see slow_fiat_examples/README.md for more details and instructions on running.
  (Be warned, some of the examples of slowness themselves take 20 minutes to compile.)

  **Assessment**: NOT DONE

  [Bug #4779](https://coq.inria.fr/bugs/show_bug.cgi?id=4779) -
  `pose y as x; change y with x in H` can be 1300x slower than `set (x := y) in H`;
  see slow_fiat_examples/README.md for more details and instructions on running.
  (Be warned, some of the examples of slowness themselves take 20 minutes to compile.)

  **Assessment**: NOT DONE

## Partially fixed:

- [Bug #4187](https://coq.inria.fr/bugs/show_bug.cgi?id=4187) -
  `admit` is slow on a goal of the form `G' -> Prop` when it's fast on
  a goal of the form `G'` - see [`slow_admit.v`](./slow_admit.v)

  **Assessment**: could be better

- [Bug #4777](https://coq.inria.fr/bugs/show_bug.cgi?id=4777) - unless
  `Set Silent` is on, the printing time is impacted by large terms
  that don't print - see
  [`interactive_hidden_slowness.v`](./interactive_hidden_slowness.v)
  ([`interactive_hidden_slowness.sh`](./interactive_hidden_slowness.sh)
  for Coq 8.5, unless you want to use `coqtop -emacs -time <
  interactive_hidden_slowness.v`)

- [Bug #3447](https://coq.inria.fr/bugs/show_bug.cgi?id=3447) - Some
  `Defined`s are 30x slower in trunk - most of the time was spent
  hashconsing universes.

  **Assessment**: need to run experiments

## Fixed:

- [Bug #3425](https://coq.inria.fr/bugs/show_bug.cgi?id=3425) -
  unification can be very slow - see
  [`slow_unification.v`](./slow_unification.v).  (Matthieu's
  explanation in the file.)

- [Bug #5096](https://coq.inria.fr/bugs/show_bug.cgi?id=5096) -
  `vm_compute` is exponentially slower than `native_compute`, `lazy`,
  and `compute`.  See
  [`slow_fiat_crypto_vm_compute/README.md`](./slow_fiat_crypto_vm_compute/README.md)
  for more details and instructions on running.

- [Bug #3450](https://coq.inria.fr/bugs/show_bug.cgi?id=3450) - `End
  foo.` is slower in trunk in some cases; it's also slower in batch
  mode than in interactive mode.  The original slowdown was due to
  hashconsing of universes (then to substituting universes) on leaving
  a section.  But now the example has gotten orders of magnitude
  slower, in earlier places.  See
  [`super_slow_end_section_and_record.v`](./super_slow_end_section_and_record.v)
  (Coq 8.5 only).  The `Pseudofunctor` record takes 999 s to be
  defined, and you can watch the `<projection> is definted` messages
  appear one by one, very slowly.

- [Bug #4821](https://coq.inria.fr/bugs/show_bug.cgi?id=4821) -
  `simple eapply` can take 2 hours - see
  [`slow_fiat_eapply_example/src/Parsers/Refinement/SharpenedJavaScriptAssignmentExpression.v`](./slow_fiat_eapply_example/src/Parsers/Refinement/SharpenedJavaScriptAssignmentExpression.v)

- [Bug #4537](https://coq.inria.fr/bugs/show_bug.cgi?id=4537) - Coq
  8.5 is slower (sometimes by as much as 5x-6x) than Coq 8.5beta2 in
  typeclass resolution with identical traces.   Pierre-Marie Pédrot said:

> All right, I think I'm the responsible here. This is probably
> because of commit a895b2c0ca that introduced a performance
> enhancement of auto hints *in the non-polymorphic case*. The
> polymorphic case has a nice comment
```ocaml
(** FIXME: We're being inefficient here because we substitute the whole
          evar map instead of just its metas, which are the only ones
          mentioning the old universes. *)
```
> which is exactly the hotspot I'm seeing right there. I'll write a quick fix.

  and then, after fixing that, said:

> Note that there is still a hotspot that looks suspicious to
> me. Indeed, the code for Evarsolve.noccur_evar whose goal is
> essentially to ensure that an evar does not appear in a term
> repeatedly calls the following snippet of code
```ocaml
    let c =
      try Retyping.expand_projection env evd p c []
      with Retyping.RetypeError _ ->
	(* Can happen when called from w_unify which doesn't assign evars/metas
	   eagerly enough *) c
    in occur_rec acc c
```
> which is responsible for ~50% of the time passed in one of your
> tactics for no good reason.

## Issues related to Proof General slowness (not Coq slowness per se):

- [Bug #4669](https://coq.inria.fr/bugs/show_bug.cgi?id=4669) -
  printing of dependent evars in ProofGeneral can slow emacs
  interaction to a crawl (because printing of dependent evars in the
  goal does not respect `Set Printing Width`) - see
  [`slow_dependent_evars_in_pg.v`](./slow_dependent_evars_in_pg.v), and
  make sure to let it set `coq-end-goals-regexp-show-subgoals` to
  `nil` appropriately.

## Issues marked WONTFIX:

  [#4640](https://coq.inria.fr/bugs/show_bug.cgi?id=4640),
  Has to do with slow [End Section] in special case of no section variables.

## Issues marked MOVED:

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

## Issues marked INVALID:

- [Bug #4643](https://coq.inria.fr/bugs/show_bug.cgi?id=4643) -
 `Defined.` sometimes takes 2 minutes; see
  [`slow_fiat_examples/README.md`](./slow_fiat_examples/README.md) for
  more details and instructions on running. (Be warned, some of the examples
  of slowness themselves take 20 minutes to compile.)


## Misc

There are some unminimized examples in [`unminimized/`](./unminimized).
See the latest commit in each submodule for more details.
