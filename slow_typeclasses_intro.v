(* Lifted from https://coq.inria.fr/bugs/show_bug.cgi?id=3448 *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require Program.Tactics.
Generalizable All Variables.

Class ILogicOps Frm := {
                        lentails: Frm -> Frm -> Prop;
                        lforall: forall {T}, (T -> Frm) -> Frm;
                        lexists: forall {T}, (T -> Frm) -> Frm
                      }.

Infix "|--"  := lentails (at level 79, no associativity).
Notation "'Forall' x .. y , p" :=
  (lforall (fun x => .. (lforall (fun y => p)) .. )) (at level 78, x binder, y binder, right associativity).
Notation "'Exists' x .. y , p" :=
  (lexists (fun x => .. (lexists (fun y => p)) .. )) (at level 78, x binder, y binder, right associativity).

Section ILogic_Pre.
  Context (T : Type) .
  Context `{ILOps: ILogicOps Frm}.

  Record ILPreFrm := mkILPreFrm {
                         ILPreFrm_pred :> T -> Frm;
                         ILPreFrm_closed: forall t t': T,
                                                          ILPreFrm_pred t |-- ILPreFrm_pred t'
                       }.

  Notation "'mk'" := @mkILPreFrm.

  Program Definition ILPre_Ops : ILogicOps ILPreFrm := {|
                                                        lentails P Q := forall t:T, P t |-- Q t;
                                                        lforall  A P := mk (fun t => Forall a, P a t) _;
                                                        lexists  A P := mk (fun t => Exists a, P a t) _
                                                      |}.
  Admit Obligations.

End ILogic_Pre.

Implicit Arguments ILPreFrm [T [ILOps]].
Implicit Arguments mkILPreFrm [T Frm ILOps].

Section ILogic_Fun.
  Context (T: Type).
  Context `{ILOps: ILogicOps Frm}.

  Definition ILFunFrm := T -> Frm .

  Program Definition ILFun_Ops : ILogicOps ILFunFrm := {|
                                                        lentails P Q := forall t:T, P t |-- Q t;
                                                        lforall  A P := (fun t => Forall a, P a t);
                                                        lexists  A P := (fun t => Exists a, P a t)
                                                      |}.

End ILogic_Fun.

Set Implicit Arguments.

Axiom PState : Type.
Definition SPred := @ILFunFrm PState Prop.
Axiom sepSP : SPred -> SPred -> SPred.
Axiom eq_pred : PState -> SPred.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILPre_Ops.

Instance ILogicOps_Prop : ILogicOps Prop | 2 := {
                                                 lentails := fun (P : Prop) (Q : Prop) => P -> Q;
                                                 lforall  T F := forall x:T, F x;
                                                 lexists  T F := exists x:T, F x
                                               }.

Definition spec := @ILPreFrm nat (@ILPreFrm SPred Prop _) _.

Definition mkspec (f: nat -> SPred -> Prop)
           (HSPred: forall k P P', f k P -> f k P') : spec.
Proof.
  refine (mkILPreFrm (fun k => mkILPreFrm (f k) _) _).
  repeat intro.
  simpl in *.
  admit.
  Grab Existential Variables.
  admit.
Defined.

Definition spec_fun (S: spec) := fun k P => S k P.
Coercion spec_fun: spec >-> Funclass.

Definition spec_at (S: spec) (R: SPred) : spec.
Proof.
  refine (mkspec (fun k P => S k (sepSP R P)) _); admit.
Defined.

Infix "@" := spec_at (at level 44, left associativity).

Class AtEx S := at_ex: forall A f, Forall x:A, S @ f x |-- S @ lexists f.

Module slow.
  Axiom AtEx_at : forall S R {HS: AtEx S}, AtEx (S @ R).
  Local Hint Extern 1 (AtEx _) => apply AtEx_at : typeclass_instances.
  Typeclasses eauto := debug.
  Goal forall S R (HS : AtEx S) a, eq_pred a |-- R -> AtEx (S @ eq_pred a).
  Proof.
    Time typeclasses eauto. (* 0.247 s *)
    Undo.
    Time intros; typeclasses eauto. (* 0 s *)
  Admitted.
End slow.

Module fast.
  Axiom AtEx_at : forall S R {HS: AtEx S}, AtEx (S @ R).
  Local Hint Extern 1 AtEx => apply AtEx_at : typeclass_instances.
  Typeclasses eauto := debug.
  Goal forall S R (HS : AtEx S) a, eq_pred a |-- R -> AtEx (S @ eq_pred a).
  Proof.
    Time typeclasses eauto. (* 0.004 s *)
  Defined.
End fast.
