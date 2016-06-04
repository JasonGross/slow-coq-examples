(* -*- mode: coq; coq-prog-args: ("-emacs" "-indices-matter") -*- *)
(* File reduced by coq-bug-finder from original input, then from 17950 lines to 11826 lines, then from 10956 lines to 10214 lines, then from 10225 lines to 6285 lines, then from 6300 lines to 901 lines, then from 833 lines to 552 lines, then from 529 lines to 478 lines *)
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Axiom admit : forall {T}, T.
Reserved Infix "o" (at level 40, left associativity).
Definition relation (A : Type) := A -> A -> Type.
Class Symmetric {A} (R : relation A) := symmetry : forall x y, R x y -> R y x.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Delimit Scope path_scope with path.
Local Open Scope path_scope.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x := match p with idpath => idpath end.
Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.
Notation "1" := idpath : path_scope.
Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) := forall x:A, f x = g x.
Hint Unfold pointwise_paths : typeclass_instances.
Class Contr_internal (A : Type) := { center : A ; contr : (forall y : A, center = y) }.
Inductive trunc_index : Type := minus_two | trunc_S (x : trunc_index).
Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0 => trunc_S (trunc_S minus_two)
       | S n' => trunc_S (nat_to_trunc_index n')
     end.
Coercion nat_to_trunc_index : nat >-> trunc_index.
Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.
Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.
Notation IsHSet := (IsTrunc 0).
Axiom dummy_funext_type : Type.
Class Funext := { dummy_funext_value_for_speed : dummy_funext_type }.
Global Instance trunc_forall `{P : A -> Type} `{forall a, IsTrunc n (P a)} : IsTrunc n (forall a, P a) | 100.
admit.
Defined.
Definition path_prod_uncurried {A B : Type} (z z' : A * B)
           (pq : (fst z = fst z') * (snd z = snd z'))
: (z = z')
  := match pq with (p,q) =>
                   match z, z' return
                         (fst z = fst z') -> (snd z = snd z') -> (z = z') with
                     | (a,b), (a',b') => fun p q =>
                                           match p, q with
                                               idpath, idpath => 1
                                           end
                   end p q
     end.
Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).
Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
: (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (x,y) (x',y') p q.
Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
Global Existing Instance iss.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Record PreCategory :=
  Build_PreCategory' {
      object :> Type;
      morphism : object -> object -> Type;

      identity : forall x, morphism x x;
      compose : forall s d d',
                  morphism d d'
                  -> morphism s d
                  -> morphism s d'
                              where "f 'o' g" := (compose f g);

      associativity : forall x1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
                        (m3 o m2) o m1 = m3 o (m2 o m1);

      associativity_sym : forall x1 x2 x3 x4
                                 (m1 : morphism x1 x2)
                                 (m2 : morphism x2 x3)
                                 (m3 : morphism x3 x4),
                            m3 o (m2 o m1) = (m3 o m2) o m1;

      left_identity : forall a b (f : morphism a b), identity b o f = f;
      right_identity : forall a b (f : morphism a b), f o identity a = f;

      identity_identity : forall x, identity x o identity x = identity x;

      trunc_morphism : forall s d, IsHSet (morphism s d)
    }.

Bind Scope category_scope with PreCategory.
Arguments identity [!C%category] x%object : rename.
Arguments compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Definition Build_PreCategory
           object morphism compose identity
           associativity left_identity right_identity
  := @Build_PreCategory'
       object
       morphism
       compose
       identity
       associativity
       (fun _ _ _ _ _ _ _ => symmetry _ _ (associativity _ _ _ _ _ _ _))
       left_identity
       right_identity
       (fun _ => left_identity _ _ _).

Existing Instance trunc_morphism.
Infix "o" := compose : morphism_scope.
Notation "1" := (identity _) : morphism_scope.

Delimit Scope functor_scope with functor.

Local Open Scope morphism_scope.

Section Functor.

  Record Functor (C D : PreCategory) :=
    {
      object_of :> C -> D;
      morphism_of : forall s d, morphism C s d
                                -> morphism D (object_of s) (object_of d);
      composition_of : forall s d d'
                              (m1 : morphism C s d) (m2: morphism C d d'),
                         morphism_of _ _ (m2 o m1)
                         = (morphism_of _ _ m2) o (morphism_of _ _ m1);
      identity_of : forall x, morphism_of _ _ (identity x)
                              = identity (object_of x)
    }.
End Functor.

Bind Scope functor_scope with Functor.
Arguments morphism_of [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.
Notation "F '_1' m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.

Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) := { morphism_inverse : morphism C d s ;
                                                                      foo : morphism_inverse = morphism_inverse }.

Section opposite.
  Definition opposite (C : PreCategory) : PreCategory
    := @Build_PreCategory'
         C
         (fun s d => morphism C d s)
         (identity (C := C))
         (fun _ _ _ m1 m2 => m2 o m1)
         (fun _ _ _ _ _ _ _ => @associativity_sym _ _ _ _ _ _ _ _)
         (fun _ _ _ _ _ _ _ => @associativity _ _ _ _ _ _ _ _)
         (fun _ _ => @right_identity _ _ _)
         (fun _ _ => @left_identity _ _ _)
         (@identity_identity C)
         _.
End opposite.
Notation "C ^op" := (opposite C) (at level 3) : category_scope.

Section prod.

  Definition prod (C D : PreCategory) : PreCategory.
    refine (@Build_PreCategory
              (C * D)%type
              (fun s d => (morphism C (fst s) (fst d)
                           * morphism D (snd s) (snd d))%type)
              (fun x => (identity (fst x), identity (snd x)))
              (fun s d d' m2 m1 => (fst m2 o fst m1, snd m2 o snd m1))
              _
              _
              _
              _); admit.
  Defined.
End prod.
Infix "*" := prod : category_scope.

Section composition.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  Definition composeF : Functor C E
    := Build_Functor
         C E
         (fun c => G (F c))
         (fun _ _ m => morphism_of G (morphism_of F m))
         admit
         admit.
End composition.
Infix "o" := composeF : functor_scope.

Module Export HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.

  Section NaturalTransformation.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variables F G : Functor C D.

    Record NaturalTransformation :=
      Build_NaturalTransformation' {
          components_of :> forall c, morphism D (F c) (G c);
          commutes : forall s d (m : morphism C s d),
                       components_of d o F _1 m = G _1 m o components_of s;

          commutes_sym : forall s d (m : C.(morphism) s d),
                           G _1 m o components_of s = components_of d o F _1 m
        }.
  End NaturalTransformation.

  Section composition.

    Section compose.
      Variable C : PreCategory.
      Variable D : PreCategory.
      Variables F F' F'' : Functor C D.

      Variable T' : NaturalTransformation F' F''.
      Variable T : NaturalTransformation F F'.

      Local Notation CO c := (T' c o T c).

      Definition composeT
      : NaturalTransformation F F''
        := Build_NaturalTransformation' F F''
                                        (fun c => CO c)
                                        admit
                                        admit.
    End compose.

  End composition.
  Infix "o" := composeT : natural_transformation_scope.

  Section path_natural_transformation.

    Global Instance trunc_natural_transformation C D (F G : Functor C D)
    : IsHSet (NaturalTransformation F G).
    admit.
    Defined.

  End path_natural_transformation.
  Local Open Scope natural_transformation_scope.

  Section associativity.

    Section nt.

      Definition associativityT `{H0 : Funext}
                 C D F G H I
                 (V : @NaturalTransformation C D F G)
                 (U : @NaturalTransformation C D G H)
                 (T : @NaturalTransformation C D H I)
      : (T o U) o V = T o (U o V).
        admit.
      Defined.
    End nt.
  End associativity.

  Section functor_category.

    Definition functor_category `{Funext} (C D : PreCategory) : PreCategory
      := @Build_PreCategory (Functor C D)
                            (@NaturalTransformation C D)
                            admit
                            (@composeT C D)
                            (@associativityT _ C D)
                            admit
                            admit
                            _.
  End functor_category.

  Local Notation "C -> D" := (functor_category C D) : category_scope.
  Module Export ExponentialLaws.
    Module Export Law4.
      Module Export Functors.

        Section law4.
          Context `{Funext}.
          Variable C1 : PreCategory.
          Variable C2 : PreCategory.
          Variable D : PreCategory.

          Section inverse.

            Section object_of.
              Variable F : Functor (C1 * C2) D.

              Definition inverse_object_of_object_of
              : C1 -> (C2 -> D)%category.
              Proof.
                intro c1.
                refine (Build_Functor
                          C2 D
                          (fun c2 => F (c1, c2))
                          (fun s2 d2 m2 => morphism_of
                                             F
                                             (s := (c1, s2))
                                             (d := (c1, d2))
                                             (identity c1, m2))
                          _
                          _);
                  admit.
              Defined.

              Definition inverse_object_of_morphism_of
                         s d (m : morphism C1 s d)
              : morphism (C2 -> D)
                         (inverse_object_of_object_of s)
                         (inverse_object_of_object_of d).
                admit.
              Defined.

              Definition inverse_object_of
              : (C1 -> (C2 -> D))%category.
              Proof.
                refine (Build_Functor
                          C1 (C2 -> D)
                          inverse_object_of_object_of
                          inverse_object_of_morphism_of
                          _
                          _); admit.
              Defined.
            End object_of.

            Section morphism_of.

              Definition inverse_morphism_of
                         s d (m : morphism (C1 * C2 -> D) s d)
              : morphism (C1 -> (C2 -> D))
                         (inverse_object_of s)
                         (inverse_object_of d).
                admit.
              Defined.
            End morphism_of.

            Definition inverse
            : Functor (C1 * C2 -> D) (C1 -> (C2 -> D)).
            Proof.
              refine (Build_Functor
                        (C1 * C2 -> D) (C1 -> (C2 -> D))
                        inverse_object_of
                        inverse_morphism_of
                        _
                        _);
              admit.
            Defined.
          End inverse.
        End law4.

        Section opposite.

          Definition opposite C D (F : Functor C D) : Functor C^op D^op
            := Build_Functor (C^op) (D^op)
                             (object_of F)
                             (fun s d => morphism_of F (s := d) (d := s))
                             (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                             (identity_of F).
        End opposite.
        Notation "F ^op" := (opposite F) : functor_scope.

        Module ProdF.

          Section proj.

            Definition fst {C D} : Functor (C * D) C
              := Build_Functor (C * D) C
                               (@fst _ _)
                               (fun _ _ => @fst _ _)
                               (fun _ _ _ _ _ => idpath)
                               (fun _ => idpath).

            Definition snd {C D} : Functor (C * D) D
              := Build_Functor (C * D) D
                               (@snd _ _)
                               (fun _ _ => @snd _ _)
                               (fun _ _ _ _ _ => idpath)
                               (fun _ => idpath).
          End proj.

          Section prod.

            Definition prod C D D' (F : Functor C D) (F' : Functor C D')
            : Functor C (D * D')
              := Build_Functor
                   C (D * D')
                   (fun c => (F c, F' c))
                   (fun s d m => (F _1 m, F' _1 m))
                   (fun _ _ _ _ _ => path_prod' (composition_of F _ _ _ _ _)
                                                (composition_of F' _ _ _ _ _))
                   (fun _ => path_prod' (identity_of F _) (identity_of F' _)).
          End prod.

          Local Infix "*" := prod : functor_scope.

          Section pair.
            Definition pair C D C' D' (F : Functor C D) (F' : Functor C' D') : Functor (C * C') (D * D')
              := (F o fst) * (F' o snd).
          End pair.

          Module Export FunctorProdNotations.
            Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : functor_scope.
          End FunctorProdNotations.

        End ProdF.

        Notation cat_of obj :=
          (@Build_PreCategory obj
                              (fun x y => x -> y)
                              (fun _ x => x)
                              (fun _ _ _ f g => fun x => f (g x))
                              (fun _ _ _ _ _ _ _ => idpath)
                              (fun _ _ _ => idpath)
                              (fun _ _ _ => idpath)
                              _).
        Definition set_cat `{Funext} : PreCategory := cat_of hSet.

        Section hom_functor.
          Context `{Funext}.
          Variable C : PreCategory.

          Local Notation obj_of c'c :=
            (@BuildhSet
               (morphism
                  C
                  (fst (c'c : object (C^op * C)))
                  (snd (c'c : object (C^op * C))))
               _).

          Definition hom_functor : Functor (C^op * C) set_cat.
            refine (Build_Functor (C^op * C) set_cat
                                  (fun c'c => obj_of c'c)
                                  admit
                                  admit
                                  admit).
          Defined.
        End hom_functor.
        Import ProdF.

        Section full_faithful.
          Context `{Funext}.
          Variable C : PreCategory.
          Variable D : PreCategory.
          Variable F : Functor C D.

          Definition induced_hom_natural_transformation
          : NaturalTransformation (hom_functor C) (hom_functor D o (F^op, F)).
            admit.
          Defined.

          Class IsFullyFaithful
            := is_fully_faithful
               : forall x y : C,
                   IsIsomorphism (induced_hom_natural_transformation (x, y)).
        End full_faithful.

        Definition coyoneda `{Funext} A : Functor A^op (A -> set_cat)
          := ExponentialLaws.Law4.Functors.inverse _ _ _ (hom_functor A).

        Definition coyoneda_lemma_morphism `{Funext} A (F : object (A -> set_cat)) (a : A)
        : morphism set_cat
                   (@BuildhSet
                      (morphism (A -> set_cat) (coyoneda A a) F)
                      _)
                   (F a)
          := fun phi => phi a 1%morphism.
        Context `{Funext}.
        Variable A : PreCategory.

        Definition coyoneda_embedding : IsFullyFaithful (coyoneda A).
        Proof.
          intros a b.
          pose (coyoneda_lemma_morphism (F := coyoneda A b) (a := a)) as X.
          exists X.
          Undo.
          Typeclasses eauto := debug.
          Time exists (@coyoneda_lemma_morphism _ A (@coyoneda _ A b) a).
(** Matthieu says:

This is an unfortunate situation indeed. What happens currently is
that the exists tries to unify the type of the coyoneda application
with the hnf of the [morphism _ _ _ ] argument of Build_IsIsomorphism,
which is:

  (let
   (object, morphism, identity, compose, _, _, _, _, _, _) as p
   return (p -> p -> Type) := ?M216 in
   morphism) ?M218 ?M217

This fails. The typeclass resolution is launched during unification
([Typeclass Resolution for Conversion] is on), figuring out the funext
instances, but again the unification fails and we forget about these
instantiations. Then the goal is unified with
[IsIsomorphism ?M216 ?M217 ?M218] and that sets the metavariables to
the right terms. We try again the coercion of the coyoneda application
with the refined (let (objec... ) term which now unfolds and unifies
correctly, but as the existentials for the typeclass instances are not
filled, we must resort to doing the unfolding in unification and the
(unsound) first-order approximation rule of w_unify fires, which tries
to compare two terms of different types, namely Buildhset and:
Eval compute in @object_of
               (Top.prod (Top.opposite (Top.opposite A)) (Top.opposite A))
               (@set_cat H).
Forcing unification to compute a normal form of the latter, which
expands to a very large term. This explains the slowdown. In the case
of the pose, no unification is needed, only conversion, which does not
try this first-order unification, because no metavariables appear
anymore in the type of the coyoneda application.

I'm surprised by the remark of PMP though, I couldn't reproduce a
noticeable speedup by deactivating universe hconsing, how did you do
it? *)
