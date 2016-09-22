(** * Counts how many binders there are *)
Require Import Crypto.Reflection.Syntax.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).

  Fixpoint count_pairs (t : flat_type) : nat
    := match t with
       | Tbase _ => 1
       | Prod A B => count_pairs A + count_pairs B
       end%nat.

  Section with_var.
    Context {var : base_type_code -> Type}
            (mkVar : forall t, var t).

    Local Notation exprf := (@exprf base_type_code interp_base_type op var).
    Local Notation expr := (@expr base_type_code interp_base_type op var).

    Section gen.
      Context (count_type_let : flat_type -> nat).
      Context (count_type_abs : base_type_code -> nat).

      Fixpoint count_lets_genf {t} (e : exprf t) : nat
        := match e with
           | LetIn tx _ _ eC
             => count_type_let tx + @count_lets_genf _ (eC (SmartVal var mkVar tx))
           | _ => 0
           end.
      Fixpoint count_lets_gen {t} (e : expr t) : nat
        := match e with
           | Return _ x
             => count_lets_genf x
           | Abs tx _ f => count_type_abs tx + @count_lets_gen _ (f (mkVar tx))
           end.
    End gen.

    Definition count_let_bindersf {t} (e : exprf t) : nat
      := count_lets_genf count_pairs e.
    Definition count_letsf {t} (e : exprf t) : nat
      := count_lets_genf (fun _ => 1) e.
    Definition count_let_binders {t} (e : expr t) : nat
      := count_lets_gen count_pairs (fun _ => 0) e.
    Definition count_lets {t} (e : expr t) : nat
      := count_lets_gen (fun _ => 1) (fun _ => 0) e.
    Definition count_binders {t} (e : expr t) : nat
      := count_lets_gen count_pairs (fun _ => 1) e.
  End with_var.

  Definition CountLetsGen (count_type_let : flat_type -> nat) (count_type_abs : base_type_code -> nat) {t} (e : Expr t) : nat
    := count_lets_gen (fun _ => tt) count_type_let count_type_abs (e _).
  Definition CountLetBinders {t} (e : Expr t) : nat
    := count_let_binders (fun _ => tt) (e _).
  Definition CountLets {t} (e : Expr t) : nat
    := count_lets (fun _ => tt) (e _).
  Definition CountBinders {t} (e : Expr t) : nat
    := count_binders (fun _ => tt) (e _).
End language.
