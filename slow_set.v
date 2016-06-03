(** Lifted from bug #4636, slow in 8.4 and 8.5 *)
(** Hugo explains:

Yes, experimenting the compatibility of ssreflect's algorithm for set
(and, ideally, provide at the same time an "in pattern" alternative to
"at occurrences" to select occurrences, with a syntax to be invented)
would be interesting, assuming that this is ok to others too. No
objection from my side.

Otherwise, to answer Jason's question, I could not resist to look at
why it is slow and the answer is that there are two causes for a time
polynomial in the size of the goal expression.

The first one is the occur_meta_or_undefined_evar test in unify_0 in
unification.ml which is done on 40320, 40319, 40318, etc. Computing it
in advance would solve this inefficiency with all uses of unify_0
taking advantage of it (including maybe ssreflect).

The second one is a call to closed0 in
Find_subterm.replace_term_occ_gen_modulo (commit dbdff037af1 from
Matthieu). I don't know if it was supposed to improve efficiency or to
prevent incorrect solutions, but its effect on very large expression
is bad.

In particular, as far as I could see, the matching strategy in itself
is not concerned, and once these two causes of polynomial time are
removed, one gets back a linear time. *)

Fixpoint fact n := match n with 0 => 1 | S n' => n * fact n' end.

Definition foo := Eval compute in fact 8.
Goal fact 8 * 10 = foo * 10.
Proof.
  unfold foo.
  Time set (x := fact 8). (* Finished transaction in 14.363 secs (14.359u,0.004s) (successful) *)
  Time pose (fact 8) as x'; change (fact 8) with x. (* Finished transaction in 0.169 secs (0.167u,0.s) (successful) *)
