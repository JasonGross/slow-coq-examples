(** * An x86 Machine *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Decidable.
Require Export Crypto.BoundedArithmetic.Interface.
Require Export Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.Inline.
Require Export Crypto.Reflection.Reify.
Require Export Crypto.Util.Notations.

Open Scope Z_scope.
Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta3' x := (fst x, eta (snd x)).

(** ** Reflective Assembly Syntax *)
Section reflection.
  Context {n} (ops : x86.instructions n).
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Inductive base_type := TZ | Tbool | TW.
  Global Instance dec_base_type : DecidableRel (@eq base_type)
    := base_type_eq_dec.
  Definition interp_base_type (v : base_type) : Type :=
    match v with
    | TZ => Z
    | Tbool => bool
    | TW => x86.W
    end.
  Local Notation tZ := (Tbase TZ).
  Local Notation tbool := (Tbase Tbool).
  Local Notation tW := (Tbase TW).
  Local Open Scope ctype_scope.
  Inductive op : flat_type base_type -> flat_type base_type -> Type :=
  | OPldi     : op tZ tW
  | OPshrd    : op (tW * tW * tZ) (tbool * tW)
  | OPshl     : op (tW * tZ) (tbool * tW)
  | OPshr     : op (tW * tZ) (tbool * tW)
  | OPadc     : op (tW * tW * tbool) (tbool * tW)
  | OPsubc    : op (tW * tW * tbool) (tbool * tW)
  | OPmuldw   : op (tW * tW) (tbool * (tW * tW))
  | OPselc    : op (tbool * tW * tW) tW
  | OPor      : op (tW * tW) (tbool * tW).

  Definition interp_op src dst (f : op src dst)
    : interp_flat_type_gen interp_base_type src -> interp_flat_type_gen interp_base_type dst
    := match f in op s d return interp_flat_type_gen _ s -> interp_flat_type_gen _ d with
       | OPldi     => ldi
       | OPshrd    => fun xyz => let '(x, y, z) := eta3 xyz in shrdf x y z
       | OPshl     => fun xy => let '(x, y) := eta xy in shlf x y
       | OPshr     => fun xy => let '(x, y) := eta xy in shrf x y
       | OPadc     => fun xyz => let '(x, y, z) := eta3 xyz in adc x y z
       | OPsubc    => fun xyz => let '(x, y, z) := eta3 xyz in subc x y z
       | OPmuldw   => fun xy => let '(x, y) := eta xy in muldwf x y
       | OPselc    => fun xyz => let '(x, y, z) := eta3 xyz in selc x y z
       | OPor      => fun xy => let '(x, y) := eta xy in orf x y
       end.

  Definition Inline {t} e := @InlineConst base_type interp_base_type op t e.
End reflection.

Ltac base_reify_op op op_head ::=
     lazymatch op_head with
     | @Interface.ldi => constr:(reify_op op op_head 1 OPldi)
     | @Interface.shrdf => constr:(reify_op op op_head 3 OPshrd)
     | @Interface.shlf => constr:(reify_op op op_head 2 OPshl)
     | @Interface.shrf => constr:(reify_op op op_head 2 OPshr)
     | @Interface.adc => constr:(reify_op op op_head 3 OPadc)
     | @Interface.subc => constr:(reify_op op op_head 3 OPsubc)
     | @Interface.muldwf => constr:(reify_op op op_head 2 OPmuldw)
     | @Interface.selc => constr:(reify_op op op_head 3 OPselc)
     | @Interface.orf => constr:(reify_op op op_head 3 OPor)
     end.
Ltac base_reify_type T ::=
     match T with
     | Z => TZ
     | bool => Tbool
     | x86.W => TW
     end.

Ltac Reify' e := Reify.Reify' base_type (interp_base_type _) op e.
Ltac Reify e :=
  let v := Reify.Reify base_type (interp_base_type _) op e in
  constr:(Inline _ ((*CSE _*) (InlineConst (Linearize v)))).
(*Ltac Reify_rhs := Reify.Reify_rhs base_type (interp_base_type _) op (interp_op _).*)
