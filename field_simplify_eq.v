(** Lifted from https://coq.inria.fr/bugs/show_bug.cgi?id=4810, if the type of the field is a projection from a record, then the performance of [field_simplify_eq] is linear in the *number of record fields of that record*.  This number is completely irrelevant to the intended behavior of [field_simplify_eq].  Fixing this would remove the need for the variant of [field_simplify_eq] mentioned in bug #4809.  (The constant coefficient in trunk is around 1.3 s rather than 5 s, which is better, but still entirely unacceptable, given that we need records with 11 fields.) *)

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require Coq.nsatz.Nsatz.
Import Coq.ZArith.BinInt.
Import Coq.ZArith.Znumtheory.

Definition F (modulus : BinInt.Z) : Set.
exact { z : BinInt.Z | z = z mod modulus }.
Defined.
Export Coq.setoid_ring.Field_tac.
Export Coq.ZArith.ZArith.
Axiom pow : forall {m}, F m -> BinNums.N -> F m.
Axiom add : forall {p}, F p -> F p -> F p.
Axiom mul : forall {p}, F p -> F p -> F p.
Axiom sub : forall {p}, F p -> F p -> F p.
Axiom div : forall {p}, F p -> F p -> F p.
Axiom opp : forall {p}, F p -> F p.
Axiom inv : forall {p}, F p -> F p.
Axiom ZToField : forall {p}, BinInt.Z -> F p.

Axiom FieldTheory : forall p, @field_theory (F p) (ZToField 0%Z) (ZToField 1%Z) add mul sub opp div inv eq.

Module Type params.
  Parameter TwistedEdwardsParams : Set.
  Parameter q : forall {_ : TwistedEdwardsParams}, BinInt.Z.
End params.
Module gen (Import P : params).
  Existing Class TwistedEdwardsParams.

  Context {prm:TwistedEdwardsParams}.

  Add Field Ffield_notConstant : (FieldTheory q).

  Notation qq := (@q prm).

  Infix "*" := (@mul qq).
  Infix "+" := (@add qq).
  Infix "-" := (@sub qq).
  Infix "/" := (@div qq).
  Notation "1" := (@ZToField qq 1%Z).
  Infix "^" := (@pow qq).

  Axiom d : F qq.
  Axiom a : F qq.

  Definition GT := forall xA yA : F qq,
   a * xA ^ 2%N + yA ^ 2%N = 1 + d * xA ^ 2%N * yA ^ 2%N ->
   forall xB yB : F qq,
   a * xB ^ 2%N + yB ^ 2%N = 1 + d * xB ^ 2%N * yB ^ 2%N ->
   forall xC yC : F qq,
   a * xC ^ 2%N + yC ^ 2%N = 1 + d * xC ^ 2%N * yC ^ 2%N ->
   (xA * ((yB * yC - a * xB * xC) / (1 - d * xB * xC * yB * yC)) + yA * ((xB * yC + yB * xC) / (1 + d * xB * xC * yB * yC))) /
   (1 + d * xA * ((xB * yC + yB * xC) / (1 + d * xB * xC * yB * yC)) * yA * ((yB * yC - a * xB * xC) / (1 - d * xB * xC * yB * yC))) =
   ((xA * yB + yA * xB) / (1 + d * xA * xB * yA * yB) * yC + (yA * yB - a * xA * xB) / (1 - d * xA * xB * yA * yB) * xC) /
   (1 + d * ((xA * yB + yA * xB) / (1 + d * xA * xB * yA * yB)) * xC * ((yA * yB - a * xA * xB) / (1 - d * xA * xB * yA * yB)) * yC).

  Ltac t0 := unfold GT; intros.
End gen.

Record TwistedEdwardsParams0 := { q0 : BinInt.Z }.
Module P0 <: params. Definition TwistedEdwardsParams := TwistedEdwardsParams0. Definition q := @q0. End P0.
Module Import Show0 := gen P0.
Goal GT. t0. Time field_simplify_eq. (* Finished transaction in 0. secs (0.324u,0.004s) *) Admitted.

Record TwistedEdwardsParams1 := { q1 : BinInt.Z ; a1 : F q1 }.
Module P1 <: params. Definition TwistedEdwardsParams := TwistedEdwardsParams1. Definition q := @q1. End P1.
Module Import Show1 := gen P1.
Goal GT. t0. Time field_simplify_eq. (* Finished transaction in 5. secs (4.76u,0.028s) *) Admitted.

Record TwistedEdwardsParams2 := { q2 : BinInt.Z ; a2 : F q2 ; b2 : F q2 }.
Module P2 <: params. Definition TwistedEdwardsParams := TwistedEdwardsParams2. Definition q := @q2. End P2.
Module Import Show2 := gen P2.
Goal GT. t0. Time field_simplify_eq. (* Finished transaction in 11. secs (10.12u,0.096s) *) Admitted.

(* And our actual example *)
Class TwistedEdwardsParams7 := {
  q : BinInt.Z;
  a : F q;
  d : F q;
  prime_q : Znumtheory.prime q;
  two_lt_q : BinInt.Z.lt 2 q;
  nonzero_a : a <> (ZToField 0);
  square_a : exists sqrt_a, pow sqrt_a 2 = a;
  nonsquare_d : forall x, pow x 2 <> d
}.
Module P7 <: params. Definition TwistedEdwardsParams := TwistedEdwardsParams7. Definition q := @q. End P7.
Module Import Show7 := gen P7.
Goal GT. t0. Time field_simplify_eq. Admitted.
