Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.NewBaseSystemTest.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Import ListNotations.

Require Import Crypto.Reflection.Z.Bounds.Pipeline.

Require Import AdmitAxiom.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 10)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := 2^exp + 2^(exp-3) |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
  (* The definition [bounds_exp] is a tuple-version of the
     limb-widths, which are the [exp] argument in [b_of] above, i.e.,
     the approximate base-2 exponent of the bounds on the limb in that
     position. *)
  Let bounds_exp : Tuple.tuple Z length_lw
    := Eval compute in
        Tuple.from_list length_lw limb_widths eq_refl.
  Let bounds : Tuple.tuple zrange length_lw
    := Eval compute in
        Tuple.map (fun e => b_of e) bounds_exp.

  Let feZ : Type := tuple Z 10.
  Let feW : Type := tuple word32 10.
  Let feBW : Type := BoundedWord 10 32 bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

  (* TODO : change this to field once field isomorphism happens *)
  Definition add :
    { add : feBW -> feBW -> feBW
    | forall a b, phi (add a b) = F.add (phi a) (phi b) }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a b, ?phi (f a b) = @?rhs a b } ]
      => apply lift2_sig with (P:=fun a b f => phi f = rhs a b)
    end.
    intros. eexists ?[add]. cbv [phi].
    rewrite <- (proj2_sig add_sig).
    symmetry; rewrite <- (proj2_sig carry_sig); symmetry.
    set (carry_addZ := fun a b => proj1_sig carry_sig (proj1_sig add_sig a b)).
    change (proj1_sig carry_sig (proj1_sig add_sig ?a ?b)) with (carry_addZ a b).
    cbv beta iota delta [proj1_sig add_sig carry_sig runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz] in carry_addZ.
    cbn beta iota delta [fst snd] in carry_addZ.
    apply f_equal.
    (* jgross start here! *)
    Set Ltac Profiling.
    Require Import Glue AdmitAxiom.
    do_curry.
    check_split_BoundedWordToZ_precondition;
      (** first revert the context definition which is an evar named [f]
      in the docs above, so that it becomes evar 1 (for
      [instantiate]), and so that [make_evar_for_first_projection]
      works *)
      lazymatch goal with
      | [ |- BoundedWordToZ _ _ _ ?f = _ ]
        => revert f
      end;
      repeat match goal with
             | [ |- context[BoundedWordToZ _ _ _ ?x] ]
               => is_var x;
                    first [ clearbody x; fail 1
                          | (** we want to keep the same context variable in
                          the evar that we reverted above, and in the
                          current goal; hence the instantiate trick *)
                          instantiate (1:=ltac:(destruct x)); destruct x ]
             end;
      cbv beta iota; intro; (* put [f] back in the context so that [cbn] doesn't remove this let-in *)
        unfold BoundedWordToZ; cbn [proj1_sig].

      Require Import Coq.ZArith.ZArith.
      Require Import Crypto.Util.LetIn.
      lazymatch goal with
  | [ |- ?map (@proj1_sig _ ?P ?f) = _ ]
    => let f1 := fresh f in
       let f2 := fresh f in
       let pf := fresh in
       revert f; refine (_ : let f := exist P _ _ in _);
         intro f;
         pose (proj1_sig f) as f1;
         pose (proj2_sig f : P f1) as f2;
         change f with (exist P f1 f2);
         subst f; cbn [proj1_sig proj2_sig] in f1, f2 |- *; revert f2;
           (** Now we rely on the behavior of Coq's unifier to transform
           the goal for us; we a goal like [let f' : A := ?f_evar in
           B], and we want a goal like [A /\ B].  So we refine with a
           hole named [pf] which is proof of [A /\ B], and then assert
           that the second projection of the proof (which has type
           [B]) actually has type [let f' : A := proj1 pf in B].  If
           done naïvely, this would give a circlular type, which Coq
           disallows.  However, Coq is happy to zeta-reduce away the
           circlularity; happily, this is done after Coq unifies [let
           f' : A := proj1 pf in B] with [let f' : A := ?f_evar in B],
           hence filling [?f_evar] with the first projection of the
           proof.  Since Coq instantiates the two existing evars
           ([?f_evar] and the current goal, which is represented by an
           evar under the hood) with projections of the new evar
           (which becomes the new goal)---and let us hope that Coq
           devs never decide both to turn on judgmental η (currently
           controlled by primitive projections) for [and], and to
           prefer η-expansion of evars before dropping context
           variables (we might also be in trouble if someone adds a
           [Canonical Structure] for [and])---we get the desired
           behavior--for now. *)
           lazymatch goal with
           | [ |- let f' := _ in ?B ]
             => refine (let pf := _ in ((proj2 pf : B) : let f' := proj1 pf in B))
           end
  end.

        exfalso; clear; admit. Grab Existential Variables. all:exfalso; clear; admit.  Time Defined.
