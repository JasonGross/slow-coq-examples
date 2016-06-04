Require Import Coq.Lists.List
        Coq.Strings.String
        Fiat.Common
        Fiat.Common.ilist
        Fiat.Common.BoundedLookup
        Fiat.ADT.Core Fiat.ADT.ComputationalADT
        Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.SetoidMorphisms.

(* To derive an ADT interactively from a specification [spec], we can
   build a dependent product [ {adt : _ & refineADT spec adt} ]. The
   derivation flow has the form:

   1. Apply a refinement.
   2. Discharge any side conditions.
   3. Repeat steps 1-2 until adt is completely specialized.

   My current thought is that to make this as pleasant as
   possible, the refinements used in the first step should be
   implemented using tactics which present the user with 'nice' side
   conditions. (In particular, this lets us be careful about not
   having any dangling existential variables at the end of a
   derivation).

   Aside on notation:
   When naming these tactics, I wanted one which
   wasn't already used by a tactic- refine, specialize, and replace
   were taken. The thesaurus suggested 'hone'.  This kind of agrees
   with 'Bedrock' (in as much as a Whetstone is used to sharpen
   knives), so I'm carrying on the naming convention with a
   'Sharpened' notation for the dependent products. *)

Definition FullySharpened {Sig} spec := {adt : cADT Sig & refineADT spec (LiftcADT adt)}.

Record NamedADTSig :=
  { ADTSigname : string;
    namedADTSig : ADTSig }.

Record SharpenedUnderDelegates (Sig : ADTSig)
  : Type
  := Build_SharpenedUnderDelegates
       { Sharpened_DelegateIDs : nat;
         Sharpened_DelegateSigs : Fin.t Sharpened_DelegateIDs -> ADTSig;
         Sharpened_Implementation :
           forall (DelegateReps : Fin.t Sharpened_DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                      pcADT (Sharpened_DelegateSigs idx) (DelegateReps idx)),
             cADT Sig;
         Sharpened_DelegateSpecs : forall idx, ADT (Sharpened_DelegateSigs idx) }.

Definition FullySharpenedUnderDelegates
           (Sig : ADTSig)
           (spec : ADT Sig)
           (adt : SharpenedUnderDelegates Sig)
  := forall (DelegateReps : Fin.t (Sharpened_DelegateIDs adt) -> Type)
            (DelegateImpls : forall idx,
                pcADT (Sharpened_DelegateSigs adt idx) (DelegateReps idx))
            (ValidImpls
             : forall idx : Fin.t (Sharpened_DelegateIDs adt),
                refineADT (Sharpened_DelegateSpecs adt idx)
                          (LiftcADT (existT _ _ (DelegateImpls idx)))),
    refineADT spec
              (LiftcADT (Sharpened_Implementation adt DelegateReps DelegateImpls)).

(* Old Deprecated Sharpened Definition *)
(* Notation Sharpened spec := {adt : _ & refineADT spec adt}. *)

(* Shiny New Sharpened Definition includes proof that the
   ADT produced is sharpened modulo a set of 'Delegated ADTs'. *)

Notation Sharpened spec := (@refineADT _ spec _).

Definition MostlySharpened {Sig} spec :=
  {adt : _ & prod (refineADT spec (fst adt)) (@FullySharpenedUnderDelegates Sig (fst adt) (snd adt))}.

Lemma FullySharpened_Start
  : forall {Sig} (spec : ADT Sig) cadt,
    refineADT spec (LiftcADT cadt)
    -> FullySharpened spec.
Proof.
  intros; exists cadt; eassumption.
Defined.

Lemma FullySharpened_Finish
  : forall {Sig} (spec : ADT Sig) adt
           (cadt : ComputationalADT.cADT Sig),
    @FullySharpenedUnderDelegates _ spec adt
    -> forall (DelegateReps : Fin.t (Sharpened_DelegateIDs adt) -> Type)
              (DelegateImpls :
                 forall idx,
                   ComputationalADT.pcADT (Sharpened_DelegateSigs adt idx) (DelegateReps idx))
              (ValidImpls
               : forall idx : Fin.t (Sharpened_DelegateIDs adt),
                  refineADT (Sharpened_DelegateSpecs adt idx)
                            (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
      refineADT
        (ComputationalADT.LiftcADT (Sharpened_Implementation adt DelegateReps DelegateImpls))
        (ComputationalADT.LiftcADT cadt)
      -> refineADT spec (ComputationalADT.LiftcADT cadt).
Proof.
  intros.
  eapply transitivityT; eauto.
Qed.

Lemma MostlySharpened_Start
  : forall {Sig} (spec : ADT Sig) adt cadt,
    (@refineADT _ spec adt)
    -> (@FullySharpenedUnderDelegates _ adt cadt)
    -> MostlySharpened spec.
Proof.
  intros; exists (adt, cadt); eauto.
Defined.

(* The proof componentn of a single refinement step. *)
Definition SharpenStep Sig adt :
  forall adt' adt''
         (refine_adt' : refineADT (Sig := Sig) adt adt'),
    refineADT adt' adt''
    -> refineADT adt adt''.
Proof.
  intros; eapply transitivityT.
  eassumption.
  apply X; eauto.
Qed.

Definition FullySharpenStep Sig adt :
  forall adt' adt''
         (refine_adt' : refineADT (Sig := Sig) adt adt'),
    FullySharpenedUnderDelegates adt' adt''
    -> FullySharpenedUnderDelegates adt adt''.
Proof.
  unfold FullySharpenedUnderDelegates in *.
  intros; eapply transitivityT.
  eassumption.
  apply X; eauto.
Qed.

Ltac start_sharpening_ADT :=
  match goal with
  | |- MostlySharpened ?spec => repeat unfold spec; eapply MostlySharpened_Start
  | |- FullySharpened ?spec => repeat unfold spec; eapply FullySharpened_Start
  end.

Tactic Notation "start" "sharpening" "ADT" := start_sharpening_ADT.

(* A single refinement step.
Definition SharpenStep Sig adt adt' adt''
           (refine_adt' : refineADT (Sig := Sig) adt adt')
           FullySharpenedUnderDelegates adt' adt''
: FullySharpenedUnderDelegates adt' adt'' :=
  existT _ (projT1 adt'') (SharpenStep_Proof refine_adt' adt'').

Lemma projT1_SharpenStep
: forall Sig adt adt' refine_adt_adt' Sharpened_adt',
    projT1 (@SharpenStep Sig adt adt' refine_adt_adt' Sharpened_adt') =
    projT1 Sharpened_adt'.
Proof.
  reflexivity.
Qed. *)

(* Definition for constructing an easily extractible ADT implementation. *)

Definition BuildMostlySharpenedcADT
           Sig
           (DelegateIDs : nat)
           (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
           (rep : (Fin.t DelegateIDs -> Type) -> Type)
           (cConstructors :
              forall
                (DelegateReps : Fin.t DelegateIDs -> Type)
                (DelegateImpls : forall idx,
                    pcADT (DelegateSigs idx) (DelegateReps idx)) idx,
                cConstructorType
                  (rep DelegateReps)
                  (ConstructorDom Sig idx))
           (cMethods :
              forall
                (DelegateReps : Fin.t DelegateIDs -> Type)
                (DelegateImpls : forall idx,
                    pcADT (DelegateSigs idx) (DelegateReps idx)) idx,
                cMethodType
                  (rep DelegateReps)
                  (fst (MethodDomCod Sig idx))
                  (snd (MethodDomCod Sig idx)))
           (DelegateReps : Fin.t DelegateIDs -> Type)
           (DelegateImpls : forall idx,
               pcADT (DelegateSigs idx) (DelegateReps idx))
  : cADT Sig :=
  existT _ (rep DelegateReps)
         {| pcConstructors := cConstructors DelegateReps DelegateImpls;
            pcMethods      := cMethods DelegateReps DelegateImpls |}.

(* Proof component of the ADT is Qed-ed. *)
Definition SharpenFully {Sig}
  : forall
    (spec : ADT Sig)
    (DelegateIDs : nat)
    (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
    (rep : (Fin.t DelegateIDs -> Type) -> Type)
    (cConstructors :
       forall
         (DelegateReps : Fin.t DelegateIDs -> Type)
         (DelegateImpls : forall idx,
             pcADT (DelegateSigs idx) (DelegateReps idx)) idx,
         cConstructorType
           (rep DelegateReps)
           (ConstructorDom Sig idx))
    (cMethods :
       forall
         (DelegateReps : Fin.t DelegateIDs -> Type)
         (DelegateImpls : forall idx,
             pcADT (DelegateSigs idx) (DelegateReps idx)) idx,
         cMethodType
           (rep DelegateReps)
           (fst (MethodDomCod Sig idx))
           (snd (MethodDomCod Sig idx)))
    (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
    (cAbsR :
       forall
         (DelegateReps : Fin.t DelegateIDs -> Type)
         (DelegateImpls : forall idx,
             pcADT (DelegateSigs idx) (DelegateReps idx))
         (ValidImpls
          : forall idx : Fin.t DelegateIDs,
             refineADT (DelegateSpecs idx)
                       (LiftcADT (existT _ _ (DelegateImpls idx)))),
         Rep spec -> rep DelegateReps -> Prop),
    (forall
        (DelegateReps : Fin.t DelegateIDs -> Type)
        (DelegateImpls : forall idx,
            pcADT (DelegateSigs idx) (DelegateReps idx))
        (ValidImpls
         : forall idx : Fin.t DelegateIDs,
            refineADT (DelegateSpecs idx)
                      (LiftcADT (existT _ _ (DelegateImpls idx)))),
        forall idx : ConstructorIndex Sig,
          @refineConstructor
            (Rep spec) (rep DelegateReps) (cAbsR _ _ ValidImpls)
            (ConstructorDom Sig idx)
            (Constructors spec idx)
            (LiftcConstructor _ _ (cConstructors DelegateReps DelegateImpls idx)))
    -> (forall
           (DelegateReps : Fin.t DelegateIDs -> Type)
           (DelegateImpls : forall idx,
               pcADT (DelegateSigs idx) (DelegateReps idx))
           (ValidImpls
            : forall idx : Fin.t DelegateIDs,
               refineADT (DelegateSpecs idx)
                         (LiftcADT (existT _ _ (DelegateImpls idx)))),
           forall idx,
             @refineMethod
               (Rep spec) (rep DelegateReps) (cAbsR _ _ ValidImpls)
               (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx))
               (Methods spec idx)
               (LiftcMethod (cMethods DelegateReps DelegateImpls idx)))
    -> FullySharpenedUnderDelegates
         spec
         {| Sharpened_DelegateSigs := DelegateSigs;
            Sharpened_Implementation := BuildMostlySharpenedcADT Sig DelegateSigs rep cConstructors
                                                                 cMethods;
            Sharpened_DelegateSpecs := DelegateSpecs |}.
Proof.
  intros * cConstructorsRefinesSpec cMethodsRefinesSpec DelegateReps DelegateImpls DelegateImplRefinesSpec.
  eapply (@refinesADT Sig spec (LiftcADT (existT _ (rep DelegateReps)
                                                 {| pcConstructors := _;
                                                    pcMethods := _|}))
                      (cAbsR DelegateReps DelegateImpls DelegateImplRefinesSpec)).
  - simpl; intros;
    eapply (cConstructorsRefinesSpec _ _ DelegateImplRefinesSpec idx).
  - simpl; intros.
    eapply (cMethodsRefinesSpec _ _ DelegateImplRefinesSpec); eauto.
Qed.

Fixpoint Lift_Constructor1P RepType (dom : list Type)
         (P : constructorType RepType [] -> Prop)
  : constructorType RepType dom -> Prop :=
  match dom with
  | nil => fun c => P c
  | d :: dom' => fun c => forall (t : d), Lift_Constructor1P dom' P (c t)
  end.

Fixpoint Lift_Constructor2P RepType RepType' (dom : list Type)
         (P : constructorType RepType []
              -> cConstructorType RepType' []
              -> Prop)
  : constructorType RepType dom
    -> cConstructorType RepType' dom
    -> Prop :=
  match dom with
  | nil => fun c c' => P c c'
  | d :: dom' => fun c c' => forall (t : d), Lift_Constructor2P dom' P (c t) (c' t)
  end.

Definition Lift_Constructor2P_ind RepType RepType'
           (dom : list Type)
           (P : constructorType RepType []
               -> cConstructorType RepType' []
               -> Prop)
           (P' : forall dom,
               constructorType RepType dom
               -> cConstructorType RepType' dom
               -> Prop)
           con cCon
           (H : forall con' cCon',
               P' _ con' cCon'
               -> Lift_Constructor2P [] P con' cCon')
           (IH : forall d d' con' cCon',
               (forall t, P' d' (con' t) (cCon' t)
                          -> Lift_Constructor2P d' P (con' t) (cCon' t))
               -> P' (d :: d') con' cCon'
               -> Lift_Constructor2P (d :: d') P con' cCon')
  : P' _ con cCon
    -> Lift_Constructor2P dom P con cCon.
Proof.
  induction dom; simpl in *; eauto.
Qed.

Lemma cConstructors_AbsR {Sig} {spec : ADT Sig}
      (impl : FullySharpened spec)
      midx
  :
    @Lift_Constructor2P _ _ _
                   (fun Cons cCons =>
                      exists r_o',
                        computes_to Cons (r_o')
                        /\ AbsR (projT2 impl) r_o' cCons)
                   (Constructors spec midx)
                   (cConstructors (projT1 impl) midx).
Proof.
  simpl in *.
  generalize  (ADTRefinementPreservesConstructors (projT2 impl) midx).
  intro.
  eapply Lift_Constructor2P_ind with
  (P' := fun dom meth (cCons : cConstructorType _ dom) => refineConstructor (AbsR (projT2 impl)) meth (LiftcConstructor _ dom cCons)) ; simpl; intros; eauto.
  - revert H0; clear -midx;  destruct (ConstructorDom Sig midx) as [|];
    simpl; intros;
    specialize (H0 _ (ReturnComputes _)); computes_to_inv; subst;
    eexists; split; simpl; try destruct v; simpl; eauto.
Qed.

Fixpoint Lift_Method1P RepType
         (dom : list Type)
         (cod : option Type)
         (P : forall cod,
             methodType' RepType [] (Some cod)
             -> Prop)
         (P' : methodType' RepType [] None
               -> Prop)
  : methodType' RepType dom cod
    -> Prop :=
  match dom with
  | nil => match cod with
           | Some cod' => fun c => P cod' c
           | None => fun c => P' c
           end
  | d :: dom' => fun c => forall (t : d), Lift_Method1P dom' cod P P' (c t)
  end.

Fixpoint Lift_Method2P RepType RepType'
         (dom : list Type)
         (cod : option Type)
         (P : forall cod,
             methodType' RepType [] (Some cod)
             -> cMethodType' RepType' [] (Some cod)
             -> Prop)
         (P' : methodType' RepType [] None
               -> cMethodType' RepType' [] None
               -> Prop)
  : methodType' RepType dom cod
    -> cMethodType' RepType' dom cod
    -> Prop :=
  match dom with
  | nil => match cod with
           | Some cod' => fun c c' => P cod' c c'
           | None => fun c c' => P' c c'
           end
  | d :: dom' => fun c c' => forall (t : d), Lift_Method2P dom' cod P P' (c t) (c' t)
  end.

Fixpoint Lift_cMethodP RepType
         (dom : list Type)
         (cod : option Type)
         (P : forall cod,
             cMethodType' RepType [] (Some cod)
             -> Prop)
         (P' : cMethodType' RepType [] None
               -> Prop)
  : cMethodType' RepType dom cod
    -> Prop :=
  match dom with
  | nil => match cod with
           | Some cod' => fun c => P cod' c
           | None => fun c => P' c
           end
  | d :: dom' => fun c => forall (t : d), Lift_cMethodP dom' cod P P' (c t)
  end.

Definition Lift_Method2P_ind RepType RepType'
           (dom : list Type)
           (cod : option Type)
           (P : forall cod,
               methodType' RepType [] (Some cod)
               -> cMethodType' RepType' [] (Some cod)
               -> Prop)
           (P' : methodType' RepType [] None
                 -> cMethodType' RepType' [] None
                 -> Prop)
           (P'' : forall dom cod,
               methodType' RepType dom cod
               -> cMethodType' RepType' dom cod
               -> Prop)
           meth cMeth
           (H : forall meth' cMeth',
               P'' _ _ meth' cMeth'
               -> Lift_Method2P [] cod P P' meth' cMeth')
           (IH : forall d d' meth' cMeth',
               (forall t, P'' d' cod (meth' t) (cMeth' t)
                          -> Lift_Method2P d' cod P P' (meth' t) (cMeth' t))
               -> P'' (d :: d') cod meth' cMeth'
               -> Lift_Method2P (d :: d') cod P P' meth' cMeth')
  : P'' _ _ meth cMeth
    -> Lift_Method2P dom cod P P' meth cMeth.
Proof.
  induction dom; simpl in *; eauto.
  destruct cod; eauto.
Qed.

Lemma cMethods_AbsR {Sig} {spec : ADT Sig}
      (impl : FullySharpened spec)
      midx
      (r_o : Rep spec)
      (r_n : cRep (projT1 impl))
      (Abs : AbsR (projT2 impl) r_o r_n)
  :
    @Lift_Method2P _ _ _ _
                   (fun _ Meth cMeth =>
                      exists r_o',
                        computes_to Meth (r_o', (snd cMeth))
                        /\ AbsR (projT2 impl) r_o' (fst cMeth))
                   (fun Meth cMeth =>
                      exists r_o',
                        computes_to Meth (r_o')
                        /\ AbsR (projT2 impl) r_o' cMeth)
                   (Methods spec midx r_o)
                   (cMethods (projT1 impl) midx r_n).
Proof.
  simpl in *.
  generalize  (ADTRefinementPreservesMethods (projT2 impl) midx _ _ Abs).
  intro.
  eapply Lift_Method2P_ind with
  (P'' := fun dom cod meth (cMeth : cMethodType' _ dom cod) => refineMethod' (AbsR (projT2 impl)) meth (LiftcMethod' _ dom cod cMeth)) ; simpl; intros; eauto.
  - revert H0; clear;  destruct (MethodDomCod Sig midx) as [? [? |] ];
    simpl; intros;
    specialize (H0 _ (ReturnComputes _)); computes_to_inv; subst;
    eexists; split; simpl; try destruct v; simpl; eauto.
    simpl; eauto.
Qed.

(*Definition SharpenFully {Sig}
    (spec : ADT Sig)
    (DelegateIDs : list string)
    (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
    (rep : (Fin.t DelegateIDs -> Type) -> Type)
    (cConstructors :
       forall
         (DelegateReps : Fin.t DelegateIDs -> Type)
         (DelegateImpls : forall idx,
                            pcADT (DelegateSigs idx) (DelegateReps idx)) idx,
         cConstructorType
           (rep DelegateReps)
           (ConstructorDom Sig idx))
    (cMethods :
       forall
         (DelegateReps : Fin.t DelegateIDs -> Type)
         (DelegateImpls : forall idx,
                            pcADT (DelegateSigs idx) (DelegateReps idx)) idx,
         cMethodType
           (rep DelegateReps)
           (fst (MethodDomCod Sig idx))
           (snd (MethodDomCod Sig idx)))
    (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
    (cAbsR :
       forall
         (DelegateReps : Fin.t DelegateIDs -> Type)
         (DelegateImpls : forall idx,
                            pcADT (DelegateSigs idx) (DelegateReps idx))
         (ValidImpls
          : forall idx : Fin.t DelegateIDs,
              refineADT (DelegateSpecs idx)
                        (LiftcADT (existT _ _ (DelegateImpls idx)))),
         Rep spec -> rep DelegateReps -> Prop)
    (cConstructorsRefinesSpec : forall
        (DelegateReps : Fin.t DelegateIDs -> Type)
        (DelegateImpls : forall idx,
                           pcADT (DelegateSigs idx) (DelegateReps idx))
        (ValidImpls
         : forall idx : Fin.t DelegateIDs,
             refineADT (DelegateSpecs idx)
                       (LiftcADT (existT _ _ (DelegateImpls idx)))),
      forall idx : ConstructorIndex Sig,
        @refineConstructor
          (Rep spec) (rep DelegateReps) (cAbsR _ _ ValidImpls)
          (ConstructorDom Sig idx)
          (Constructors spec idx)
         (fun d => ret (cConstructors DelegateReps DelegateImpls idx d)))
    (cMethodsRefinesSpec : forall
           (DelegateReps : Fin.t DelegateIDs -> Type)
           (DelegateImpls : forall idx,
                              pcADT (DelegateSigs idx) (DelegateReps idx))
           (ValidImpls
            : forall idx : Fin.t DelegateIDs,
                refineADT (DelegateSpecs idx)
                          (LiftcADT (existT _ _ (DelegateImpls idx)))),
        forall idx,
          @refineMethod
            (Rep spec) (rep DelegateReps) (cAbsR _ _ ValidImpls)
            (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx))
            (Methods spec idx)
            (fun r_n d => ret (cMethods DelegateReps DelegateImpls idx r_n d)))
    : Sharpened spec :=
  existT _ _ (FullySharpened_BuildMostlySharpenedcADT spec _ rep cConstructors
                                                      cMethods DelegateSpecs cAbsR
                                                      cConstructorsRefinesSpec cMethodsRefinesSpec). *)

(* Honing tactic for refining the observer method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)

Tactic Notation "hone'" "method" constr(obsIdx) "using" constr(obsBody) :=
  let A :=
      match goal with
        |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                ADT ?Sig => Sig
              end in
  let mutIdx_eq' := fresh in
  let Rep' := eval simpl in (Rep A) in
      let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
          let MethodIndex' := eval simpl in (MethodIndex ASig) in
              let Methods' := eval simpl in (Methods A) in
                  assert (forall idx idx' : MethodIndex', {idx = idx'} + {idx <> idx'})
                as obsIdx_eq' by (decide equality);
                eapply SharpenStep;
                [eapply (@refineADT_Build_ADT_Method
                           Rep' _ _ _
                           (fun idx : MethodIndex ASig => if (obsIdx_eq' idx ()) then
                                                            obsBody
                                                          else
                                                            Methods' idx))
                | idtac]; cbv beta in *; simpl in *.

(* Honing tactic for refining the constructor method with the specified index.
   This version of the tactic takes the new implementation as an argument. *)
Tactic Notation "hone'" "constructor" constr(mutIdx) "using" constr(mutBody) :=
  let A :=
      match goal with
        |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                ADT ?Sig => Sig
              end in
  let mutIdx_eq' := fresh in
  let Rep' := eval simpl in (Rep A) in
      let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
          let MethodIndex' := eval simpl in (MethodIndex ASig) in
              let Constructors' := eval simpl in (Constructors A) in
                  assert (forall idx idx' : ConstructorIndex', {idx = idx'} + {idx <> idx'})
                as mutIdx_eq' by (decide equality);
                eapply SharpenStep;
                [eapply (@refineADT_Build_ADT_Constructors Rep'
                                                           _
                                                           _
                                                           _
                                                           (fun idx : ConstructorIndex ASig => if (mutIdx_eq' idx mutIdx) then
                                                                                                 mutBody
                                                                                               else
                                                                                                 Constructors' idx))
                | idtac]; cbv beta in *; simpl in *.
