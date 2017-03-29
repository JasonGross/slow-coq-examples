Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Export Crypto.Specific.GF25519.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.Tuple.
Require Import Crypto.Reflection.RenameBinders.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.Z.BoundsInterpretations.
Require Import Crypto.Reflection.Z.MapBounds.
Require Import Crypto.Reflection.Z.MapBoundsInterp.
Require Import Crypto.Reflection.Z.Reify.
Require Export Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Equality.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.FoldTypes.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Util.Curry.
Require Import Crypto.Util.Tower.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Notations.

(* BEGIN common curve-specific definitions *)
Definition bit_width : nat := Eval compute in Z.to_nat (GF25519.int_width).
Local Notation b_of exp := (0, 2^exp + 2^(exp-3))%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
Definition bounds_exp : Tuple.tuple Z length_fe25519
  := Eval compute in
      Tuple.from_list length_fe25519 limb_widths eq_refl.
Definition bounds : Tuple.tuple (Z * Z) length_fe25519
  := Eval compute in
      Tuple.map (fun e => b_of e) bounds_exp.
Definition wire_digit_bounds_exp : Tuple.tuple Z (List.length wire_widths)
  := Eval compute in Tuple.from_list _ wire_widths eq_refl.
Definition wire_digit_bounds : Tuple.tuple (Z * Z) (List.length wire_widths)
  := Eval compute in Tuple.map (fun e => (0,2^e-1)%Z) wire_digit_bounds_exp.
(* END common curve-specific definitions *)

Notation Expr := (Expr base_type op).

Local Ltac make_type_from' T :=
  let T := (eval compute in T) in
  let rT := reify_type T in
  exact rT.
Local Ltac make_type_from uncurried_op :=
  let T := (type of uncurried_op) in
  make_type_from' T.

Definition fe25519T : flat_type base_type.
Proof.
  let T := (eval compute in GF25519.fe25519) in
  let T := reify_flat_type T in
  exact T.
Defined.
Definition Expr_n_OpT (count_out : nat) : flat_type base_type
  := Eval cbv [Syntax.tuple Syntax.tuple' fe25519T] in
      Syntax.tuple fe25519T count_out.
Definition Expr_nm_OpT (count_in count_out : nat) : type base_type
  := Eval cbv [Syntax.tuple Syntax.tuple' fe25519T Expr_n_OpT] in
      Arrow (Syntax.tuple fe25519T count_in) (Expr_n_OpT count_out).
Definition ExprBinOpT : type base_type := Eval compute in Expr_nm_OpT 2 1.
Definition ExprUnOpT : type base_type := Eval compute in Expr_nm_OpT 1 1.
Definition ExprUnOpFEToZT : type base_type.
Proof. make_type_from ge_modulus. Defined.
Definition ExprUnOpWireToFET : type base_type.
Proof. make_type_from unpack. Defined.
Definition ExprUnOpFEToWireT : type base_type.
Proof. make_type_from pack. Defined.

Definition make_bound (x : Z * Z) : Bounds.t
  := {| lower := fst x ; upper := snd x |}.

Fixpoint Expr_nm_Op_bounds count_in count_out {struct count_in} : interp_flat_type Bounds.interp_base_type (domain (Expr_nm_OpT count_in count_out))
  := match count_in return interp_flat_type _ (domain (Expr_nm_OpT count_in count_out)) with
     | 0 => tt
     | S n
       => let b := (Tuple.map make_bound bounds) in
          let bs := Expr_nm_Op_bounds n count_out in
          match n return interp_flat_type _ (domain (Expr_nm_OpT n _)) -> interp_flat_type _ (domain (Expr_nm_OpT (S n) _)) with
          | 0 => fun _ => b
          | S n' => fun bs => (bs, b)
          end bs
     end.
Definition ExprBinOp_bounds : interp_flat_type Bounds.interp_base_type (domain ExprBinOpT)
  := Eval compute in Expr_nm_Op_bounds 2 1.
Definition ExprUnOp_bounds : interp_flat_type Bounds.interp_base_type (domain ExprUnOpT)
  := Eval compute in Expr_nm_Op_bounds 1 1.
Definition ExprUnOpFEToZ_bounds : interp_flat_type Bounds.interp_base_type (domain ExprUnOpFEToZT)
  := Eval compute in Expr_nm_Op_bounds 1 1.
Definition ExprUnOpFEToWire_bounds : interp_flat_type Bounds.interp_base_type (domain ExprUnOpFEToWireT)
  := Eval compute in Expr_nm_Op_bounds 1 1.
Definition ExprUnOpWireToFE_bounds : interp_flat_type Bounds.interp_base_type (domain ExprUnOpWireToFET)
  := Tuple.map make_bound wire_digit_bounds.


Ltac rexpr_cbv :=
  lazymatch goal with
  | [ |- { rexpr | forall x, Interp _ (t:=?T) rexpr x = ?uncurry ?oper x } ]
    => let operf := head oper in
       let uncurryf := head uncurry in
       try cbv delta [T]; try cbv delta [oper];
       try cbv beta iota delta [uncurryf]
  | [ |- { rexpr | forall x, Interp _ (t:=?T) rexpr x = ?oper x } ]
    => let operf := head oper in
       try cbv delta [T]; try cbv delta [oper]
  end;
  cbv beta iota delta [interp_flat_type interp_base_type zero_ GF25519.fe25519 GF25519.wire_digits].

Ltac reify_sig :=
  rexpr_cbv; eexists; Reify_rhs; reflexivity.

Local Notation rexpr_sig T uncurried_op :=
  { rexprZ
  | forall x, Interp interp_op (t:=T) rexprZ x = uncurried_op x }
    (only parsing).

Notation rexpr_binop_sig op := (rexpr_sig ExprBinOpT (curry2 op)) (only parsing).
Notation rexpr_unop_sig op := (rexpr_sig ExprUnOpT op) (only parsing).
Notation rexpr_unop_FEToZ_sig op := (rexpr_sig ExprUnOpFEToZT op) (only parsing).
Notation rexpr_unop_FEToWire_sig op := (rexpr_sig ExprUnOpFEToWireT op) (only parsing).
Notation rexpr_unop_WireToFE_sig op := (rexpr_sig ExprUnOpWireToFET op) (only parsing).

Ltac rexpr_correct :=
  let ropW' := fresh in
  let ropZ_sig := fresh in
  intros ropW' ropZ_sig;
  let wf_ropW := fresh "wf_ropW" in
  assert (wf_ropW : Wf ropW') by (subst ropW' ropZ_sig; reflect_Wf base_type_eq_semidec_is_dec op_beq_bl);
  cbv zeta; repeat apply conj;
  [ vm_compute; reflexivity
  | apply @InterpWf;
    [ | apply wf_ropW ].. ];
  auto with interp_related.

Notation rword_of_Z rexprZ_sig := (proj1_sig rexprZ_sig) (only parsing).

Notation rexpr_wfT e := (Wf.Wf e) (only parsing).

Ltac prove_rexpr_wfT
  := reflect_Wf Equality.base_type_eq_semidec_is_dec Equality.op_beq_bl.

Notation rexpr_select_word_sizes_option rexprZ rexpr_bounds
  := (Z.MapBounds.MapBoundsPackaged rexprZ rexpr_bounds)
       (only parsing).
Notation rexpr_select_word_sizes_postprocess1 v
  := (invert_Some v)
       (only parsing).
Notation get_output_type v := (MapBoundsOutputType v) (only parsing).
Notation get_bounds v := (@output_bounds v) (only parsing).
Notation get_output_expr v := (@output_expr v) (only parsing).
Notation rexpr_select_word_sizes_postprocess2 v
  := (renamify v)
       (only parsing).

Local Notation pick_typeb := Bounds.bounds_to_base_type (only parsing).
Local Notation pick_type v := (SmartFlatTypeMap (fun _ => pick_typeb) v).

Notation rexpr_correct_and_boundedT rexprZ rexprW input_bounds output_bounds
  := (let t := _ in
      let e : Expr t := rexprZ in
      let input_bounds : interp_flat_type Bounds.interp_base_type (domain t)
          := input_bounds in
      let output_bounds : interp_flat_type Bounds.interp_base_type (codomain t)
          := output_bounds in
      forall (v : interp_flat_type Syntax.interp_base_type (domain t))
             (v' : interp_flat_type Syntax.interp_base_type (pick_type input_bounds)),
         (Bounds.is_bounded_by input_bounds v /\ cast_back_flat_const v' = v)
         -> Bounds.is_bounded_by output_bounds (Interp interp_op e v)
            /\ cast_back_flat_const (Interp interp_op rexprW v') = Interp interp_op e v)
       (only parsing).

Notation rexpr_correct_and_bounded rexprZ rexprW input_bounds output_bounds rexprZ_Wf
  := (fun v v' Hv
      => proj2
           (@MapBoundsPackagedCorrect
              _ rexprZ input_bounds rexprZ_Wf
              output_bounds rexprW
              _
              v v' Hv))
       (only parsing).

Ltac rexpr_correct_and_bounded_obligation_tac :=
  intros;
  lazymatch goal with
  | [ |- ?x = Some ?y ]
    => abstract vm_cast_no_check (eq_refl (Some y))
  | _ => vm_compute; constructor
  end.

Module Export PrettyPrinting.
  Export Bounds.Notations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Open Scope bounds_scope.

  Inductive result := yes | no (max_bitwidth : Z) (dummy : unit).
  Arguments no [max_bitwidth] dummy. (* get it to print as [no (max_bitwidth := _)] *)

  Definition max_allowable_bitwidth := Eval compute in Z.of_nat bit_width.
  Definition max_allowable_type := TWord (Z.to_nat (Z.log2 max_allowable_bitwidth)).

  Definition does_it_overflow {t} (e : Expr t) : unit -> result
    := match MaxTypeUsed e with
       | TZ => fun _ => yes
       | TWord v => let bitwidth := 2^Z.of_nat v in
                    if (bitwidth <=? max_allowable_bitwidth)%bool
                    then @no bitwidth
                    else fun _ => yes
       end.
  Definition does_not_overflow_type {t} (e : Expr t) : Prop
    := let v := match MaxTypeUsed e with
                | TZ => 0
                | TWord v => 2^Z.of_nat v
                end in
       @no v = @no v.

  (** This allows us to give a slightly easier to read version of the
      bounds, even when we change their format *)
  Notation compute_bounds_for_display op_pkg
    := (get_bounds op_pkg) (only parsing).
  Notation sanity_compute op_pkg
    := (does_it_overflow (get_output_expr op_pkg)) (only parsing).
  Notation sanity_check op_pkg
    := (eq_refl (sanity_compute op_pkg) <: (does_not_overflow_type (get_output_expr op_pkg)))
         (only parsing).
End PrettyPrinting.
