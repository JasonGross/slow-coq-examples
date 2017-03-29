Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.BoundsInterpretations.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.

Local Notation pick_typeb := Bounds.bounds_to_base_type (only parsing).
Local Notation pick_type v := (SmartFlatTypeMap (fun _ => pick_typeb) v).

Local Ltac break_t_step :=
  first [ progress destruct_head'_and
        | progress destruct_head'_or
        | progress destruct_head'_prod
        | break_innermost_match_step ].

Local Ltac fin_t :=
  first [ reflexivity
        | assumption
        | match goal with
          | [ |- and _ _ ]
            => first [ split; [ | solve [ fin_t ] ]
                     | split; [ solve [ fin_t ] | ] ];
               try solve [ fin_t ]
          end
        | omega ].

Local Ltac specializer_t_step :=
  first [ progress specialize_by_assumption
        | progress specialize_by fin_t ].

Local Ltac Zarith_t_step :=
  first [ match goal with
          | [ H : (?x <= ?y)%Z, H' : (?y <= ?x)%Z |- _ ]
            => assert (x = y) by omega; clear H H'
          end
        | progress Z.ltb_to_lt_in_context ].

Local Ltac split_min_max :=
  repeat match goal with
         | [ H : (?a <= ?b)%Z |- context[Z.max ?a ?b] ]
           => rewrite (Z.max_r a b) by omega
         | [ H : (?b <= ?a)%Z |- context[Z.max ?a ?b] ]
           => rewrite (Z.max_l a b) by omega
         | [ H : (?a <= ?b)%Z |- context[Z.min ?a ?b] ]
           => rewrite (Z.min_l a b) by omega
         | [ H : (?b <= ?a)%Z |- context[Z.min ?a ?b] ]
           => rewrite (Z.min_r a b) by omega
         | [ |- context[Z.max ?a ?b] ]
           => first [ rewrite (Z.max_l a b) by omega
                    | rewrite (Z.max_r a b) by omega ]
         | [ |- context[Z.min ?a ?b] ]
           => first [ rewrite (Z.min_l a b) by omega
                    | rewrite (Z.min_r a b) by omega ]
         | _ => progress repeat apply Z.min_case_strong; intros
         | _ => progress repeat apply Z.max_case_strong; intros
         end.

Local Ltac rewriter_t :=
  first [ rewrite !Bool.andb_true_iff
        | rewrite !Bool.andb_false_iff
        | rewrite wordToZ_ZToWord by (autorewrite with push_Zof_nat zsimplify_const; omega)
        | match goal with
          | [ H : _ |- _ ]
            => first [ rewrite !Bool.andb_true_iff in H
                     | rewrite !Bool.andb_false_iff in H ]
          end ].

Local Arguments Bounds.is_bounded_by' !_ _ _ / .
Local Arguments Bounds.is_bounded_byb !_ _ _ / .

Section is_bounded_by_interp_op.
  Local Notation is_bounded_by_interp_opT opc
    := (forall (bs : interp_flat_type Bounds.interp_base_type _)
               (v : interp_flat_type interp_base_type _)
               (H : Bounds.is_bounded_by bs v),
           Bounds.is_bounded_by (Bounds.interp_op opc bs) (Syntax.interp_op _ _ opc v))
         (only parsing).

  Local Ltac t_step :=
    first [ fin_t
          | progress intros
          | progress subst
          | progress simpl in *
          | progress split_andb
          | progress Zarith_t_step
          | specializer_t_step
          | rewriter_t
          | progress break_t_step
          | progress split_min_max
          | progress cbv [Bounds.neg' Bounds.cmovne' Bounds.cmovle' ModularBaseSystemListZOperations.neg ModularBaseSystemListZOperations.cmovne ModularBaseSystemListZOperations.cmovl] ].
  Local Ltac t := repeat t_step.

  Lemma is_bounded_by_interp_op t tR (opc : op t tR)
    : is_bounded_by_interp_opT opc.
  Proof. Admitted.
End is_bounded_by_interp_op.

Local Arguments lift_op : simpl never.
Local Arguments cast_back_flat_const : simpl never.
Local Arguments unzify_op : simpl never.
Local Arguments Z.pow : simpl never.
Local Arguments Z.add !_ !_.
Local Existing Instance Z.pow_Zpos_le_Proper.
Lemma pull_cast_genericize_op t tR (opc : op t tR)
      (bs : interp_flat_type Bounds.interp_base_type t)
      (v : interp_flat_type interp_base_type (pick_type bs))
      (H : Bounds.is_bounded_by bs
                                (SmartFlatTypeMapUnInterp
                                   (fun (t1 : base_type) (b0 : Bounds.interp_base_type t1) => cast_const) v))
  : interp_op t tR opc (cast_back_flat_const v)
    = cast_back_flat_const (interp_op (pick_type bs) (pick_type (Bounds.interp_op opc bs)) (genericize_op opc) v).
Proof.
Admitted.
