Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.PositiveContext.
Require Import Crypto.Reflection.CountLets.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Definition default_names_forf {var} (dummy : forall t, var t) {t} (e : exprf base_type_code op (var:=var) t) : list positive
    := map BinPos.Pos.of_succ_nat (seq 0 (count_let_bindersf dummy e)).
  Definition default_names_for {var} (dummy : forall t, var t) {t} (e : expr base_type_code op (var:=var) t) : list positive
    := map BinPos.Pos.of_succ_nat (seq 0 (count_binders dummy e)).
  Definition DefaultNamesFor {t} (e : Expr base_type_code op t) : list positive
    := map BinPos.Pos.of_succ_nat (seq 0 (CountBinders e)).
End language.
