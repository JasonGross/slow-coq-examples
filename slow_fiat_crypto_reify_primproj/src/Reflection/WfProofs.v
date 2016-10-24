Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type_gen interp_base_type.
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  Local Notation wff := (@wff base_type_code interp_base_type op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.
    Local Hint Constructors Syntax.wff.
    Lemma wff_in_impl_Proper G0 G1 {t} e1 e2
      : @wff var1 var2 G0 t e1 e2
        -> (forall x, List.In x G0 -> List.In x G1)
        -> @wff var1 var2 G1 t e1 e2.
    Proof.
      intro wf; revert G1; induction wf;
        repeat match goal with
               | _ => setoid_rewrite List.in_app_iff
               | _ => progress intros
               | _ => progress simpl in *
               | [ |- wff _ _ _ ] => constructor
               | [ H : _ |- _ ] => apply H
               | _ => solve [ intuition eauto ]
               end.
    Qed.

    Local Hint Resolve List.in_app_or List.in_or_app.
    Local Hint Extern 1 => progress unfold List.In in *.
    Local Hint Resolve wff_in_impl_Proper.

    Lemma wff_SmartVar {t} x1 x2
      : @wff var1 var2 (flatten_binding_list base_type_code x1 x2) t (SmartVar x1) (SmartVar x2).
    Proof.
      unfold SmartVar.
      induction t; simpl; constructor; eauto.
    Qed.

    Local Hint Resolve wff_SmartVar.

    Lemma wff_Const_eta G {A B} v1 v2
      : @wff var1 var2 G (Prod A B) (Const v1) (Const v2)
        -> (@wff var1 var2 G A (Const (fst v1)) (Const (fst v2))
           /\ @wff var1 var2 G B (Const (snd v1)) (Const (snd v2))).
    Proof.
      intro wf.
      assert (H : Some v1 = Some v2).
      { refine match wf in @Syntax.wff _ _ _ _ _ G t e1 e2 return invert_Const e1 = invert_Const e2 with
               | WfConst _ _ _ => eq_refl
               | _ => eq_refl
               end. }
      inversion H; subst; repeat constructor.
    Qed.

    Definition wff_Const_eta_fst G {A B} v1 v2 H
      := proj1 (@wff_Const_eta G A B v1 v2 H).
    Definition wff_Const_eta_snd G {A B} v1 v2 H
      := proj2 (@wff_Const_eta G A B v1 v2 H).

    Local Hint Resolve wff_Const_eta_fst wff_Const_eta_snd.

    Lemma wff_SmartConst G {t t'} v1 v2 x1 x2
          (Hin : List.In (existT (fun t : base_type_code => (@exprf var1 t * @exprf var2 t)%type) t (x1, x2))
                         (flatten_binding_list base_type_code (SmartConst v1) (SmartConst v2)))
          (Hwf : @wff var1 var2 G t' (Const v1) (Const v2))
      : @wff var1 var2 G t x1 x2.
    Proof.
      induction t'. simpl in *.
      { intuition (inversion_sigma; inversion_prod; subst; eauto). }
      { unfold SmartConst in *; simpl in *.
        apply List.in_app_iff in Hin.
        intuition (inversion_sigma; inversion_prod; subst; eauto). }
    Qed.

    Local Hint Resolve wff_SmartConst.
  End with_var.
End language.
