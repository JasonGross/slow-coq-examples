Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Syntax.Equality.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Z.BoundsInterpretations.
Require Import Crypto.Reflection.Z.BoundsInterpretationsLemmas.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.Reflection.MapCastByDeBruijn.
Require Import Crypto.Reflection.MapCastByDeBruijnInterp.
Require Import Crypto.Reflection.MapCastByDeBruijnWf.
Require Import Crypto.Reflection.Z.MapBounds.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.Head.

Local Notation pick_typeb := Bounds.bounds_to_base_type (only parsing).
Local Notation pick_type v := (SmartFlatTypeMap (fun _ => pick_typeb) v).

Local Ltac my_fold t :=
  let h := head t in
  let t' := (eval cbv [h] in t) in
  change t' with t in *.
Local Ltac fold_SmartFlatTypeMap :=
  repeat match goal with
         | [ |- context[@smart_interp_flat_map ?btc ?var' _ _ _ _ _ ?v] ]
           => my_fold (@SmartFlatTypeMap btc _ (fun _ => pick_typeb) _ v)
         end.
Lemma MapBoundsSigCorrect {t}
      (e : Expr base_type op t)
      (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
      (Hwf : Wf e)
      {b e'} (He : MapBoundsSig e input_bounds = Some (existT _ b e'))
      (v : interp_flat_type Syntax.interp_base_type (domain t))
      (v' : interp_flat_type Syntax.interp_base_type (pick_type input_bounds))
      (Hv : Bounds.is_bounded_by input_bounds v /\ cast_back_flat_const v' = v)
  : Interp (@Bounds.interp_op) e input_bounds = b
    /\ Bounds.is_bounded_by b (Interp interp_op e v)
    /\ cast_back_flat_const (Interp interp_op e' v') = Interp interp_op e v.
Proof.
  rewrite unfold_MapBoundsSig in He; unfold option_map in *.
  break_match_hyps; inversion_option; inversion_sigma; subst; unfold eq_rect.
  fold_SmartFlatTypeMap.
  rewrite InterpExprEta_arrow, InterpInlineConst by eauto using internal_base_type_dec_lb with wf.
  refine (@MapCastCorrect
           _ _ _ _ internal_base_type_dec_lb
           _
           _ Syntax.interp_op
           _ (@Bounds.interp_op)
           _ _ (fun _ _ => cast_const)
           (@Bounds.is_bounded_by')
           is_bounded_by_interp_op
           pull_cast_genericize_op
           t _ Hwf input_bounds _ _ _ v v' Hv).
  eassumption.
Qed.

Lemma MapBoundsPackagedCorrect {t}
      (e : Expr base_type op t)
      (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
      (Hwf : Wf e)
      {b e'} (He : MapBoundsPackaged e input_bounds
                   = Some {| input_expr := e ; input_bounds := input_bounds ; output_bounds := b ; output_expr := e' |})
      (v : interp_flat_type Syntax.interp_base_type (domain t))
      (v' : interp_flat_type Syntax.interp_base_type (pick_type input_bounds))
      (Hv : Bounds.is_bounded_by input_bounds v /\ cast_back_flat_const v' = v)
  : Interp (@Bounds.interp_op) e input_bounds = b
    /\ Bounds.is_bounded_by b (Interp interp_op e v)
    /\ cast_back_flat_const (Interp interp_op e' v') = Interp interp_op e v.
Proof.
  eapply MapBoundsSigCorrect; try eassumption.
  unfold MapBoundsPackaged, option_map in *; break_match_hyps; inversion_option.
  apply f_equal.
  lazymatch goal with
  | [ H : _ = _ :> MapBoundsPackage |- _ = _ :> sigT ?P ]
    => lazymatch eval pattern t, input_bounds in P with
       | ?P' _ _
         => apply (f_equal (fun x : MapBoundsPackage
                            => let (t, e, input_bounds, a, b) := x in
                               existT (fun t => { ib : _ & sigT (P' t ib) }) t (existT _ input_bounds (existT _ a b))))
           in H
       end
  end.
  repeat (inversion_sigma || subst || simpl in * || eliminate_hprop_eq).
  reflexivity.
Qed.
