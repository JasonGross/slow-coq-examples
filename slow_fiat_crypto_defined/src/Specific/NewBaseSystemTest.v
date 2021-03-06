Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.NewBaseSystem. Import B.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tactics Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.
Require Crypto.Util.Tuple.
Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

(*** 
Modulus : 2^255-19
Base: 25.5
***)
Section Ops25p5.
  Local Infix "^" := tuple : type_scope.

  (* These definitions will need to be passed as Ltac arguments (or
  cleverly inferred) when things are eventually automated *)
  Definition wt := fun i : nat => 2^(25 * (i / 2) + 26 * ((i + 1) / 2)).
  Definition sz := 10%nat.
  Definition s : Z := 2^255.
  Definition c : list B.limb := [(1, 19)].
  Definition coef_div_modulus := 2. (* add 2*modulus before subtracting *)
  Definition carry_chain1 := Eval vm_compute in (seq 0 (pred sz)).
  Definition carry_chain2 := ([0;1])%nat.

  (* These definitions are inferred from those above *)
  Definition m := Eval vm_compute in Z.to_pos (s - Associational.eval c). (* modulus *)
  Definition sz2 := Eval vm_compute in ((sz * 2) - 1)%nat.
  Definition coef := Eval vm_compute in (@Positional.encode wt modulo div sz (coef_div_modulus * (s-Associational.eval c))). (* subtraction coefficient *)
  Definition coef_mod : mod_eq m (Positional.eval (n:=sz) wt coef) 0 := eq_refl.

  Lemma sz_nonzero : sz <> 0%nat. Proof. vm_decide. Qed.
  Lemma wt_nonzero i : wt i <> 0.
  Proof. apply Z.pow_nonzero; zero_bounds. Qed.
  Lemma wt_divides_chain1 i (H:In i carry_chain1) : wt (S i) / wt i <> 0.
  Proof.
    cbv [In carry_chain1] in H.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try (exfalso; assumption); subst; try vm_decide.
  Qed.
  Lemma wt_divides_chain2 i (H:In i carry_chain2) : wt (S i) / wt i <> 0.
  Proof.
    cbv [In carry_chain2] in H.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try (exfalso; assumption); subst; try vm_decide.
  Qed.
  Lemma wt_divides_full i : wt (S i) / wt i <> 0.
  Proof.
    cbv [wt].
    match goal with |- _ ^ ?x / _ ^ ?y <> _ => assert (0 <= y <= x) end.
    { rewrite Nat2Z.inj_succ. split; [zero_bounds|].
    apply Z.add_le_mono;
      (apply Z.mul_le_mono_nonneg_l; [zero_bounds|]);
      apply Z.div_le_mono; omega. }
    rewrite <-Z.pow_sub_r by omega.
    apply Z.pow_nonzero; omega.
  Qed.

  Definition zero_sig :
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}.
  Proof.
    let t := eval vm_compute in
    (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt 0) in
        exists t; vm_decide.
  Defined.

  Definition one_sig :
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}.
  Proof.
    let t := eval vm_compute in
    (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt 1) in
        exists t; vm_decide.
  Defined.

  Definition add_sig :
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (add a b) = (eval a  + eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero.
    let x := constr:(
        Positional.add_cps (n := sz) wt a b id) in
    solve_op_F wt x. reflexivity.
  Defined.

  Definition sub_sig :
    {sub : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (sub a b) = (eval a - eval b)%F}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
    solve_op_F wt x. reflexivity.
  Defined.

  Definition opp_sig :
    {opp : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (opp a) = F.opp (eval a)}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
    solve_op_F wt x. reflexivity.
  Defined.
  
  Definition mul_sig :
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (mul a b) = (eval a  * eval b)%F}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.mul_cps (n:=sz) (m:=sz2) wt a b
           (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    solve_op_F wt x. reflexivity.

    (* rough breakdown of synthesis time *)
    (* 1.2s for side conditions -- should improve significantly when [chained_carries] gets a correctness lemma *)
    (* basesystem_partial_evaluation_RHS (primarily vm_compute): 1.8s, which gets re-computed during defined *)

    (* doing [cbv -[Let_In runtime_add runtime_mul]] took 37s *)

  Defined. (* 3s *)

  (* Performs a full carry loop (as specified by carry_chain) *)
  Definition carry_sig :
    {carry : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (carry a) = eval a}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero. pose proof wt_divides_chain1.
    pose proof div_mod. pose proof wt_divides_chain2.
    let x := constr:(
               Positional.chained_carries_cps (n:=sz) (div:=div)(modulo:=modulo) wt a carry_chain1
                  (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
                  (fun rrr => Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt rrr carry_chain2 id
             ))) in
    solve_op_F wt x. reflexivity.
  Defined.
  
  Definition ring_25p5 :=
    (Ring.ring_by_isomorphism
         (F := F m)
         (H := Z^sz)
         (phi := Positional.Fencode wt)
         (phi' := Positional.Fdecode wt)
         (zero := proj1_sig zero_sig)
         (one := proj1_sig one_sig)
         (opp := proj1_sig opp_sig)
         (add := proj1_sig add_sig)
         (sub := proj1_sig sub_sig)
         (mul := proj1_sig mul_sig)
         (phi'_zero := proj2_sig zero_sig)
         (phi'_one := proj2_sig one_sig)
         (phi'_opp := proj2_sig opp_sig)
         (Positional.Fdecode_Fencode_id
            (sz_nonzero := sz_nonzero)
            (div_mod := div_mod)
            wt eq_refl wt_nonzero wt_divides_full)
         (Positional.eq_Feq_iff wt)
         (proj2_sig add_sig)
         (proj2_sig sub_sig)
         (proj2_sig mul_sig)
      ).

(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
*)

End Ops25p5.