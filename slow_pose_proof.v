(** Lifted from https://coq.inria.fr/bugs/show_bug.cgi?id=3441 *)

(* Pierre-Marie Pédrot say: The assert & pose proof tactics do the
   same thing actually. The cost seems related to a retyping of the
   term. *)

Axiom f : nat -> nat -> nat.
Fixpoint do_n (n : nat) (k : nat) :=
  match n with
    | 0 => k
    | S n' => do_n n' (f k k)
  end.

Notation big := (_ = _).
Axiom k : nat.
Goal True.
Time let H := fresh "H" in
     let x := constr:(let n := 17 in do_n n = do_n n) in
     let y := (eval lazy in x) in
     pose proof y as H. (* Finished transaction in 0.408 secs (0.407u,0.s) (successful) *)
Time let H := fresh "H" in
     let x := constr:(let n := 17 in do_n n = do_n n) in
     let y := (eval lazy in x) in
     pose y as H; clearbody H. (* Finished transaction in 0.092 secs (0.092u,0.s) (successful) *)
Time let H := fresh "H" in
     let x := constr:(let n := 17 in do_n n = do_n n) in
     let y := (eval lazy in x) in
     assert (H := y). (* Finished transaction in 0.394 secs (0.387u,0.008s) (successful) *)
