(** Coq is slow, interactively, even if there is nothing big being displayed, if there are big hidden things *)
(** Use interactive_hidden_slowness.sh if you're using 8.5, since [Time] doesn't work *)

Definition dhidden {T} {x : T} := x.
Definition nhidden {T} (x : T) := x.
Notation Nhidden := (nhidden _).

Axiom iter2 : bool -> bool -> bool.
Fixpoint do2 (n : nat) (A : bool) :=
  match n with
    | 0 => A
    | S n' => do2 n' (iter2 A A)
  end.
Axiom x : bool.

Goal True.
  Time idtac. (* 0.0s *)
  let x := constr:(do2 19 x) in
  let x := (eval vm_compute in x) in
  pose (@dhidden _ x).
  Unset Silent.
  Time idtac. (* 3.7 s in 8.4; still slow (about 1.5 s) in 8.5, but not displayed with [Time] *)
  Time idtac.
  Time idtac.
  Set Silent. Time idtac. Set Silent. (* 0.084 s in 8.4, which is still slow, but not insanely slow *)
  Set Silent. Time idtac. Set Silent.
  Set Silent. Time idtac. Set Silent.
Abort.


Goal True.
  Time idtac. (* 0.0s *)
  let x := constr:(do2 19 x) in
  let x := (eval vm_compute in x) in
  pose (@nhidden _ x).
  Unset Silent.
  Time idtac. (* 1.0 s in 8.4; still slow (about 0.5 s) in 8.5, but not displayed with [Time] *)
  Time idtac.
  Time idtac.
  Set Silent. Time idtac. Set Silent. (* 0.084 s in 8.4, which is still slow, but not insanely slow *)
  Set Silent. Time idtac. Set Silent.
  Set Silent. Time idtac. Set Silent.
Abort.
