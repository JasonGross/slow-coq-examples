Axiom iter2 : bool -> bool -> bool.
Fixpoint do2 (n : nat) (A : bool) :=
  match n with
    | 0 => A
    | S n' => do2 n' (iter2 A A)
  end.
Ltac display2 := match goal with |- let n := ?k in _ => idtac "[2][" k "] :=" end; hnf; unfold do2; cbv beta.
Axiom x : bool.
Notation hidden := (_ = _).
Goal let n := 20 in do2 n x = do2 n x. display2. Time (match goal with |- ?f ?x = ?g ?y => idtac end). (* 2.6 s *) Admitted.
