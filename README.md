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

Some examples of Coq being really slow:

- [Bug #3441](https://coq.inria.fr/bugs/show_bug.cgi?id=3441) - `pose
  proof H as k` is sometimes an order of magnitude slower than `pose H
  as k; clearbody k` - see [`slow_pose_proof.v`](./slow_pose_proof.v)
  for an example of a 4x slowdown.

- [Bug #3280](https://coq.inria.fr/bugs/show_bug.cgi?id=3280) `match
  goal with |- ?f ?x = ?g ?y => idtac end` can be arbitrarily slow -
  see
  [`evar-normalization-slowness/very_silly_slow_tactic.v`](./evar-normalization-slowness/very_silly_slow_tactic.v)
  and
  [`evar-normalization-slowness/exercise-tactics/exercise-tactics.sh`](./evar-normalization-slowness/exercise-tactics/exercise-tactics.sh).
  Also, see this [graph of the time of tactics vs the size of
  goal](./evar-normalization-slowness/graph.svg)

- [Bug #4777](https://coq.inria.fr/bugs/show_bug.cgi?id=4777) - unless
  `Set Silent` is on, the printing time is impacted by large terms
  that don't print - see
  [`interactive_hidden_slowness.v`](./interactive_hidden_slowness.v)
  ([`interactive_hidden_slowness.sh`](./interactive_hidden_slowness.sh)
  for Coq 8.5, unless you want to use `coqtop -emacs -time <
  interactive_hidden_slowness.v`)

- [Bug #4662](https://coq.inria.fr/bugs/show_bug.cgi?id=4662) -
  `unfold ... in ...` should insert a cast annotation, else `Defined`
  can take over 6 minutes when it doesn't need to - see
  [`slow_unfold.v`](./slow_unfold.v)

- [Bug #4637](https://coq.inria.fr/bugs/show_bug.cgi?id=4637) -
  `vm_compute in ...` should insert vm_casts - see
  [`missing_vm_casts.v`](./missing_vm_casts.v)

- [Bug #4776](https://coq.inria.fr/bugs/show_bug.cgi?id=4776) - there
  should be a way to terminate typeclass resolution early - see
  [`slow_failing_setoid_rewrite.v`](./slow_failing_setoid_rewrite.v)

- [Bug #4669](https://coq.inria.fr/bugs/show_bug.cgi?id=4669) -
  printing of dependent evars in ProofGeneral can slow emacs
  interaction to a crawl (because printing of dependent evars in the
  goal does not respect `Set Printing Width`) - see
  [`slow_dependent_evars_in_pg.v`](./slow_dependent_evars_in_pg.v), and
  make sure to let it set `coq-end-goals-regexp-show-subgoals` to
  `nil` appropriately.

- [Bug #4636](https://coq.inria.fr/bugs/show_bug.cgi?id=4636) - `set
  (x := y)` can be 100x slower than `pose y as x; change y with x` -
  see [`slow_set.v`](./slow_set.v).  (The reverse can also happen,
  where `change` is orders of magnitude slower than `set`.  See
  [bug #4779](https://coq.inria.fr/bugs/show_bug.cgi?id=4779) in the next
  bullet.)

- Bugs [#4643](https://coq.inria.fr/bugs/show_bug.cgi?id=4643)
  [#4640](https://coq.inria.fr/bugs/show_bug.cgi?id=4640),
  [#4642](https://coq.inria.fr/bugs/show_bug.cgi?id=4642), and
  [#4779](https://coq.inria.fr/bugs/show_bug.cgi?id=4779): `Defined.`
  sometimes takes 2 minutes; `End Section` can take 30 seconds, even
  though there are no section variables, no tactics, no notations, no
  `Let`s, and only one or two `Definition`s; `cbv [some identifiers]`
  can run through 64 GB of RAM in 15 minutes; and `pose y as x; change
  y with x in H` can be 1300x slower than `set (x := y) in H`;
  respectively.  See
  [`slow_fiat_examples/README.md`](./slow_fiat_examples/README.md) for
  more details and instructions on running.  (Be warned, some of the
  examples of slowness themselves take 20 minutes to compile.)

- [Bug #4657](https://coq.inria.fr/bugs/show_bug.cgi?id=4657) -
  `omega` is slow on `x - y - (x - y - x) = x - y` (takes about 1 s,
  when it solves an equivalent equation in 0.06 s) - see
  [`slow_omega.v`](./slow_omega.v)

- [Bug #4187](https://coq.inria.fr/bugs/show_bug.cgi?id=4187) -
  `admit` is slow on a goal of the form `G' -> Prop` when it's fast on
  a goal of the form `G'` - see [`slow_admit.v`](./slow_admit.v)

- [Bug #3448](https://coq.inria.fr/bugs/show_bug.cgi?id=3448) - `Hint
  Extern (foo _) => ...` is significantly slower than `Hint Extern foo
  => ...`; typeclass resolution is slow at `intro` - see
  [`slow_typeclasses_intro.v`](./slow_typeclasses_intro.v)

- [Bug #3425](https://coq.inria.fr/bugs/show_bug.cgi?id=3425) -
  unification can be very slow - see
  [`slow_unification.v`](./slow_unification.v).  (Matthieu's
  explanation in the file.)

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


## Already fixed or partially fixed issues:

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

- [Bug #3447](https://coq.inria.fr/bugs/show_bug.cgi?id=3447) - Some
  `Defined`s are 30x slower in trunk - most of the time was spent
  hashconsing universes.
