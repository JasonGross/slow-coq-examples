(** Coq is slow, interactively, even if there is nothing big being displayed, if there are big cleared things *)
(** Use interactive_hidden_slowness.sh if you're using 8.5, since [Time] doesn't work *)

Axiom iter2 : bool -> bool -> bool.
Fixpoint do2 (n : nat) (A : bool) :=
  match n with
    | 0 => A
    | S n' => do2 n' (iter2 A A)
  end.
Ltac display2 := hnf; unfold do2; cbv beta.
Axiom x : bool.
Notation hidden := (_ = _).
Goal let n := 20 in do2 n x = do2 n x.
  display2.
  Time let G := match goal with |- ?G => G end in set (H := G). (* 1 s *)
  Time clearbody H. (* 0.134 *)
  Time evar (e : Set). (* 0.4 s *)
  Time clear e. (* 0.4 *)
Admitted.
