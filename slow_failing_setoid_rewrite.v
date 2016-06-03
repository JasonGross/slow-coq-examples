(** We would like to be able to abort typeclass search early.  But we can't do that, and slowness ensues. *)

Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive Coq.MSets.MSetInterface Coq.MSets.MSetProperties.
Require Import Coq.MSets.MSetFacts Coq.MSets.MSetDecide.

Set Implicit Arguments.

Local Coercion is_true : bool >-> Sortclass.

Instance pointwise_Proper {A B} R (f : A -> B) `{H : forall x, Proper R (f x)}
  : Proper (pointwise_relation A R) f
  := H.

Global Instance or_iff_impl_morphism : Proper (iff ==> iff ==> impl) or.
Admitted.

Module MSetExtensionsOn (E: DecidableType) (Import M: WSetsOn E).
  Module Export BasicProperties := WPropertiesOn E M.
  Module Export BasicFacts := WFactsOn E M.
  Module Export BasicDec := WDecideOn E M.

  Global Instance Equal_Equivalence : Equivalence Equal.
  Admitted.
  Axiom union_subset_1b : forall s s', subset s (union s s').
  Axiom union_subset_2b : forall s s', subset s' (union s s').
  Create HintDb setsb discriminated.
  Hint Rewrite union_subset_1b union_subset_2b : setsb.
End MSetExtensionsOn.

Module MSetExtensions (M: Sets) := MSetExtensionsOn M.E M.

Module PositiveSetExtensions0 := MSetExtensions PositiveSet.
Module PositiveSetExtensions1 := MSetExtensions PositiveSet.
Module PositiveSetExtensions2 := MSetExtensions PositiveSet.
Module PositiveSetExtensions3 := MSetExtensions PositiveSet.
Module Import PositiveSetExtensions := MSetExtensions PositiveSet.

Goal forall s s', PositiveSet.subset s (PositiveSet.union s s').
Proof.
  intros.
  (*Typeclasses eauto := debug.*)
  Time rewrite union_subset_1b. (* 9069 lines of tc resolution before success, 0.75 s *)
  Undo.
  Time progress autorewrite with setsb. (* 18142 lines of tc resolution before success, 1.4 s *)
  exact (eq_refl : is_true true).
Qed.

Goal forall t t0 : PositiveSet.t,
    PositiveSet.Equal t0 t \/ PositiveSet.Subset t0 t /\ ~ PositiveSet.Equal t0 t -> False.
Proof.
  intros ?? H.
  (*Typeclasses eauto := debug.*)
  Time try rewrite union_subset_1b in H. (* 2584 lines of tc resolution, 0.12 s *)
  Time autorewrite with setsb in H. (* 25885 lines of tc resolution before failure, 1.48 s *)
  (** Suppose we allow these contradictory lemmas. *)
  assert (forall R1 R2, Proper (PositiveSet.subset ==> R1 ==> R2) PositiveSet.Equal) by admit.
  assert (forall R1 R2, Proper (PositiveSet.subset ==> R1 ==> R2) PositiveSet.Subset) by admit.
  Time rewrite union_subset_1b in H. (* 0.008 s *)
  (** autorewrite will, unsurprisingly, loop *)
Abort.
