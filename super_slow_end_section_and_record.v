(* -*- mode: coq; coq-prog-args: ("-emacs" "-indices-matter") -*-  *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Open Scope type_scope.
Open Scope core_scope.
Arguments projT1 {_ _} _.
Arguments projT2 {_ _} _.
Definition iff (A B : Type) := prod (A -> B) (B -> A).
Notation "A <-> B" := (iff A B) : type_scope.
Notation "{ x | P }" := (sigT (fun x => P)) : type_scope.
Notation "{ x | P & Q }" := (sigT2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A | P }" := (sigT (fun x:A => P)) : type_scope.
Notation "{ x : A | P & Q }" := (sigT2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Module HoTT_DOT_Overture.
Module HoTT.
Module Overture.
(* -*- mode: coq; mode: visual-line -*-  *)

(** * Basic definitions of homotopy type theory, particularly the groupoid structure of identity types. *)

(** ** Type classes *)
Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

(** A [PreOrder] is both Reflexive and Transitive. *)
Class PreOrder {A} (R : relation A) :=
  { PreOrder_Reflexive :> Reflexive R | 2 ;
    PreOrder_Transitive :> Transitive R | 2 }.

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  refine (@transitivity _ R _ x y z _ _).

Tactic Notation "etransitivity" := etransitivity _.

(** We would like to redefine [symmetry], which is too smart for its own good, as follows:

<<
Ltac symmetry := refine (@symmetry _ _ _ _ _ _).
>>

But this gives "Error: in Tacinterp.add_tacdef: Reserved Ltac name symmetry.".  This might be fixed with https://coq.inria.fr/bugs/show_bug.cgi?id=3113.  For now, you can [apply symmetry] or [eapply symmetry].  (Note that we can get around this error message by using [Tactic Notation "symmetry"], but, confusingly, this tactic notation never gets called. *)

(** ** Basic definitions *)

(** Define an alias for [Set], which is really [Type₀]. *)
Notation Type0 := Set.
(** Define [Type₁] (really, [Type_i] for any [i > 0]) so that we can enforce having universes that are not [Set].  In trunk, universes will not be unified with [Set] in most places, so we want to never use [Set] at all. *)
Definition Type1 := Eval hnf in let U := Type in let gt := (Set : U) in U.
Arguments Type1 / .
Identity Coercion unfold_Type1 : Type1 >-> Sortclass.

(** We make the identity map a notation so we do not have to unfold it,
    or complicate matters with its type. *)
Notation idmap := (fun x => x).

(** We define notation for dependent pairs because it is too annoying to write and see [existT P x y] all the time.  However, we put it in its own scope, because sometimes it is necessary to give the particular dependent type, so we'd like to be able to turn off this notation selectively. *)
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.

(** We have unified [sig] and [sigT] of the standard Coq, and so we introduce a new notation to not annoy newcomers with the [T] in [projT1] and [projT2] nor the [_sig] in [proj1_sig] and [proj2_sig], and to not confuse Coq veterans by stealing [proj1] and [proj2], which Coq uses for [and]. *)
Notation pr1 := projT1.
Notation pr2 := projT2.

(** The following notation is very convenient, although it unfortunately clashes with Proof General's "electric period". *)
Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Notation "x .2" := (projT2 x) (at level 3) : fibration_scope.

(** Composition of functions. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

Hint Unfold compose.

(** We put the following notation in a scope because leaving it unscoped causes it to override identical notations in other scopes.  It's convenient to use the same notation for, e.g., function composition, morphism composition in a category, and functor composition, and let Coq automatically infer which one we mean by scopes.  We can't do this if this notation isn't scoped.  Unfortunately, Coq doesn't have a built-in [function_scope] like [type_scope]; [type_scope] is automatically opened wherever Coq is expecting a [Sort], and it would be nice if [function_scope] were automatically opened whenever Coq expects a thing of type [forall _, _] or [_ -> _].  To work around this, we open [function_scope] globally. *)
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.

(** ** The groupoid structure of identity types. *)

(** The results in this file are used everywhere else, so we need to be extra careful about how we define and prove things.  We prefer hand-written terms, or at least tactics that allow us to retain clear control over the proof-term produced. *)

(** We define our own identity type, rather than using the one in the Coq standard library, so as to have more control over transitivity, symmetry and inverse.  It seems impossible to change these for the standard eq/identity type (or its Type-valued version) because it breaks various other standard things.  Merely changing notations also doesn't seem to quite work. *)
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Arguments paths_ind [A] a P f y p.
Arguments paths_rec [A] a P f y p.
Arguments paths_rect [A] a P f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Instance reflexive_paths {A} : Reflexive (@paths A) | 0 := @idpath A.

(** We declare a scope in which we shall place path notations. This way they can be turned on and off by the user. *)

Delimit Scope path_scope with path.
Local Open Scope path_scope.

(** We define equality concatenation by destructing on both its arguments, so that it only computes when both arguments are [idpath].  This makes proofs more robust and symmetrical.  Compare with the definition of [identity_trans].  *)

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments concat {A x y z} p q : simpl nomatch.

Instance transitive_paths {A} : Transitive (@paths A) | 0 := @concat A.

(** The inverse of a path. *)
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

(** Declaring this as [simpl nomatch] prevents the tactic [simpl] from expanding it out into [match] statements.  We only want [inverse] to simplify when applied to an identity path. *)
Arguments inverse {A x y} p : simpl nomatch.

Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.


(** Note that you can use the built-in Coq tactics [reflexivity] and [transitivity] when working with paths, but not [symmetry], because it is too smart for its own good.  Instead, you can write [apply symmetry] or [eapply symmetry]. *)

(** The identity path. *)
Notation "1" := idpath : path_scope.

(** The composition of two paths. *)
Notation "p @ q" := (concat p q) (at level 20) : path_scope.

(** The inverse of a path. *)
Notation "p ^" := (inverse p) (at level 3) : path_scope.

(** An alternative notation which puts each path on its own line.  Useful as a temporary device during proofs of equalities between very long composites; to turn it on inside a section, say [Open Scope long_path_scope]. *)
Notation "p @' q" := (concat p q) (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'") : long_path_scope.


(** An important instance of [paths_rect] is that given any dependent type, one can _transport_ elements of instances of the type along equalities in the base.

   [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments transport {A} P {x y} p%path_scope u : simpl nomatch.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression.*)
Delimit Scope fib_scope with fib.
Local Open Scope fib_scope.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

(** Having defined transport, we can use it to talk about what a homotopy theorist might see as "paths in a fibration over paths in the base"; and what a type theorist might see as "heterogeneous eqality in a dependent type".

We will first see this appearing in the type of [apD]. *)

(** Functions act on paths: if [f : A -> B] and [p : x = y] is a path in [A], then [ap f p : f x = f y].

   We typically pronounce [ap] as a single syllable, short for "application"; but it may also be considered as an acronym, "action on paths". *)

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

(** We introduce the convention that [apKN] denotes the application of a K-path between
   functions to an N-path between elements, where a 0-path is simply a function or an
   element. Thus, [ap] is a shorthand for [ap01]. *)

Notation ap01 := ap (only parsing).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with idpath => 1 end.

Definition ap10 {A B} {f g:A->B} (h:f=g) : f == g
  := apD10 h.

Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
Proof.
  case h, p; reflexivity.
Defined.

(** See above for the meaning of [simpl nomatch]. *)
Arguments ap {A B} f {x y} p : simpl nomatch.

(** Similarly, dependent functions act on paths; but the type is a bit more subtle. If [f : forall a:A, B a] and [p : x = y] is a path in [A], then [apD f p] should somehow be a path between [f x : B x] and [f y : B y]. Since these live in different types, we use transport along [p] to make them comparable: [apD f p : p # f x = f y].

  The type [p # f x = f y] can profitably be considered as a heterogeneous or dependent equality type, of "paths from [f x] to [f y] over [p]". *)

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments apD {A B} f {x y} p : simpl nomatch.

(** ** Equivalences *)

(** Homotopy equivalences are a central concept in homotopy type theory. Before we define equivalences, let us consider when two types [A] and [B] should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are inverses of each other, up to homotopy.  Homotopically speaking, we should also require a certain condition on these homotopies, which is one of the triangle identities for adjunctions in category theory.  Thus, we call this notion an *adjoint equivalence*.

  The other triangle identity is provable from the first one, along with all the higher coherences, so it is reasonable to only assume one of them.  Moreover, as we will see, if we have maps which are inverses up to homotopy, it is always possible to make the triangle identity hold by modifying one of the homotopies.

   The second option is to use Vladimir Voevodsky's definition of an equivalence as a map whose homotopy fibers are contractible.  We call this notion a *homotopy bijection*.

   An interesting third option was suggested by André Joyal: a map [f] which has separate left and right homotopy inverses.  We call this notion a *homotopy isomorphism*.

   While the second option was the one used originally, and it is the most concise one, it makes more sense to use the first one in a formalized development, since it exposes most directly equivalence as a structure.  In particular, it is easier to extract directly from it the data of a homotopy inverse to [f], which is what we care about having most in practice.  Thus, adjoint equivalences are what we will refer to merely as *equivalences*. *)

(** Naming convention: we use [equiv] and [Equiv] systematically to denote types of equivalences, and [isequiv] and [IsEquiv] systematically to denote the assertion that a given map is an equivalence. *)

(** The fact that [r] is a left inverse of [s]. As a mnemonic, note that the partially applied type [Sect s] is the type of proofs that [s] is a section. *)
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

Existing Instance equiv_isequiv.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

(** A notation for the inverse of an equivalence.  We can apply this to a function as long as there is a typeclass instance asserting it to be an equivalence.  We can also apply it to an element of [A <~> B], since there is an implicit coercion to [A -> B] and also an existing instance of [IsEquiv]. *)

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

(** ** Contractibility and truncation levels *)

(** Truncation measures how complicated a type is.  In this library, a witness that a type is n-truncated is formalized by the [IsTrunc n] typeclass.  In many cases, the typeclass machinery of Coq can automatically infer a witness for a type being n-truncated.  Because [IsTrunc n A] itself has no computational content (that is, all witnesses of n-truncation of a type are provably equal), it does not matter much which witness Coq infers.  Therefore, the primary concerns in making use of the typeclass machinery are coverage (how many goals can be automatically solved) and speed (how long does it take to solve a goal, and how long does it take to error on a goal we cannot automatically solve).  Careful use of typeclass instances and priorities, which determine the order of typeclass resolution, can be used to effectively increase both the coverage and the speed in cases where the goal is solvable.  Unfortunately, typeclass resolution tends to spin for a while before failing unless you're very, very, very careful.  We currently aim to achieve moderate coverage and fast speed in solvable cases.  How long it takes to fail typeclass resolution is not currently considered, though it would be nice someday to be even more careful about things.

In order to achieve moderate coverage and speedy resolution, we currently follow the following principles.  They set up a kind of directed flow of information, intended to prevent cycles and potentially infinite chains, which are often the ways that typeclass resolution gets stuck.

- We prefer to reason about [IsTrunc (S n) A] rather than [IsTrunc n (@paths A a b)].  Whenever we see a statement (or goal) about truncation of paths, we try to turn it into a statement (or goal) about truncation of a (non-[paths]) type.  We do not allow typeclass resolution to go in the reverse direction from [IsTrunc (S n) A] to [forall a b : A, IsTrunc n (a = b)].

- We prefer to reason about syntactically smaller types.  That is, typeclass instances should turn goals of type [IsTrunc n (forall a : A, P a)] into goals of type [forall a : A, IsTrunc n (P a)]; and goals of type [IsTrunc n (A * B)] into the pair of goals of type [IsTrunc n A] and [IsTrunc n B]; rather than the other way around.  Ideally, we would add similar rules to transform hypotheses in the cases where we can do so.  This rule is not always the one we want, but it seems to heuristically capture the shape of most cases that we want the typeclass machinery to automatically infer.  That is, we often want to infer [IsTrunc n (A * B)] from [IsTrunc n A] and [IsTrunc n B], but we (probably) don't often need to do other simple things with [IsTrunc n (A * B)] which are broken by that reduction.
*)

(** *** Contractibility *)

(** A space [A] is contractible if there is a point [x : A] and a (pointwise) homotopy connecting the identity on [A] to the constant map at [x].  Thus an element of [contr A] is a pair whose first component is a point [x] and the second component is a pointwise retraction of [A] to [x]. *)

(** We use the [Contr_internal] record so as not to pollute typeclass search; we only do truncation typeclass search on the [IsTrunc] datatype, usually.  We will define a notation [Contr] which is equivalent to [Contr_internal], but picked up by typeclass search.  However, we must make [Contr_internal] a class so that we pick up typeclasses on [center] and [contr].  However, the only typeclass rule we register is the one that turns it into a [Contr]/[IsTrunc].  Unfortunately, this means that declaring an instance like [Instance contr_foo : Contr foo := { center := bar }.] will fail with mismatched instances/contexts.  Instead, we must iota expand such definitions to get around Coq's deficiencies, and write [Instance contr_foo : Contr foo := let x := {| center := bar |} in x.] *)
Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_}.

(** *** Truncation levels *)

(** Truncation measures how complicated a type is in terms of higher path spaces. The (-2)-truncated types are the contractible ones, whose homotopy is completely trivial. The (n+1)-truncated types are those whose path spaces are n-truncated.

   Thus, (-1)-truncated means "the space of paths between any two points is contactible". Such a space is necessarily a sub-singleton: any two points are connected by a path which is unique up to homotopy. In other words, (-1)-truncated spaces are truth values (we call them "propositions").

   Next, 0-truncated means "the space of paths between any two points is a sub-singleton". Thus, two points might not have any paths between them, or they have a unique path. Such a space may have many points but it is discrete in the sense that all paths are trivial. We call such spaces "sets".
*)

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

(** We will use [Notation] for [trunc_index]es, so define a scope for them here. *)
Delimit Scope trunc_scope with trunc.
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%trunc_scope.

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

Notation minus_one:=(trunc_S minus_two).
(** Include the basic numerals, so we don't need to go through the coercion from [nat], and so that we get the right binding with [trunc_scope]. *)
Notation "0" := (trunc_S minus_one) : trunc_scope.
Notation "1" := (trunc_S 0) : trunc_scope.
Notation "2" := (trunc_S 1) : trunc_scope.

Arguments IsTrunc_internal n A : simpl nomatch.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

(** We use the priciple that we should always be doing typeclass resolution on truncation of non-equality types.  We try to change the hypotheses and goals so that they never mention something like [IsTrunc n (_ = _)] and instead say [IsTrunc (S n) _].  If you're evil enough that some of your paths [a = b] are n-truncated, but others are not, then you'll have to either reason manually or add some (local) hints with higher priority than the hint below, or generalize your equality type so that it's not a path anymore. *)

Typeclasses Opaque IsTrunc. (* don't auto-unfold [IsTrunc] in typeclass search *)

Arguments IsTrunc : simpl never. (* don't auto-unfold [IsTrunc] with [simpl] *)

Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A)
: IsTrunc n (x = y)
  := H x y. (* but do fold [IsTrunc] *)

Hint Extern 0 => progress change IsTrunc_internal with IsTrunc in * : typeclass_instances. (* Also fold [IsTrunc_internal] *)

(** Picking up the [forall x y, IsTrunc n (x = y)] instances in the hypotheses is much tricker.  We could do something evil where we declare an empty typeclass like [IsTruncSimplification] and use the typeclass as a proxy for allowing typeclass machinery to factor nested [forall]s into the [IsTrunc] via backward reasoning on the type of the hypothesis... but, that's rather complicated, so we instead explicitly list out a few common cases.  It should be clear how to extend the pattern. *)
Hint Extern 10 =>
progress match goal with
           | [ H : forall x y : ?T, IsTrunc ?n (x = y) |- _ ]
             => change (IsTrunc (trunc_S n) T) in H
           | [ H : forall (a : ?A) (x y : @?T a), IsTrunc ?n (x = y) |- _ ]
             => change (forall a : A, IsTrunc (trunc_S n) (T a)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (x y : @?T a b), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a), IsTrunc (trunc_S n) (T a b)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (x y : @?T a b c), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b), IsTrunc (trunc_S n) (T a b c)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (d : @?D a b c) (x y : @?T a b c d), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b) (d : D a b c), IsTrunc (trunc_S n) (T a b c d)) in H; cbv beta in H
         end.

Notation Contr := (IsTrunc minus_two).
Notation IsHProp := (IsTrunc minus_one).
Notation IsHSet := (IsTrunc 0).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

(** *** Function extensionality *)

(** The function extensionality axiom is formulated as a class. To use it in a theorem, just assume it with [`{Funext}], and then you can use [path_forall], defined below.  If you need function extensionality for a whole development, you can assume it for an entire Section with [Context `{Funext}].  *)
(** We use a dummy class and an axiom to get universe polymorphism of [Funext] while still tracking its uses. *)
Axiom dummy_funext_type : Type.
Class Funext := { dummy_funext_value_for_speed : dummy_funext_type }.
Axiom isequiv_apD10 : forall `{Funext} (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).
Global Existing Instance isequiv_apD10.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^-1.

Definition path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y) :
  (forall x y, f x y = g x y) -> f = g
  :=
  (fun E => path_forall f g (fun x => path_forall (f x) (g x) (E x))).


(** *** Tactics *)

(** We declare some more [Hint Resolve] hints, now in the "hint database" [path_hints].  In general various hints (resolve, rewrite, unfold hints) can be grouped into "databases". This is necessary as sometimes different kinds of hints cannot be mixed, for example because they would cause a combinatorial explosion or rewriting cycles.

   A specific [Hint Resolve] database [db] can be used with [auto with db].

   The hints in [path_hints] are designed to push concatenation *outwards*, eliminate identities and inverses, and associate to the left as far as  possible. *)

(** TODO: think more carefully about this.  Perhaps associating to the right would be more convenient? *)
Hint Resolve
  @idpath @inverse
 : path_hints.

Hint Resolve @idpath : core.

Ltac path_via mid :=
  apply @concat with (y := mid); auto with path_hints.

(** We put [Empty] here, instead of in [Empty.v], because [Ltac done] uses it. *)
(** HoTT/coq is broken and somehow interprets [Type1] as [Prop] with regard to elimination schemes. *)
Unset Elimination Schemes.
Inductive Empty : Type1 := .
Scheme Empty_rect := Induction for Empty Sort Type.
Scheme Empty_rec := Induction for Empty Sort Set.
Scheme Empty_ind := Induction for Empty Sort Prop.
Set Elimination Schemes.

Definition not (A:Type) : Type := A -> Empty.
Notation "~ x" := (not x) : type_scope.
Hint Unfold not: core.

(** *** Pointed types *)

(** A space is pointed if that space has a point. *)
Class IsPointed (A : Type) := point : A.
Definition pointedType := { u : Type & IsPointed u }.
Arguments point A {_}.

(** Ssreflect tactics, adapted by Robbert Krebbers *)
Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [eapply symmetry; trivial]
      | reflexivity
      (* Discriminate should be here, but it doesn't work yet *)
      (* | discriminate *)
      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].
Tactic Notation "by" tactic(tac) :=
  tac; done.

(** A convenient tactic for using function extensionality. *)
Ltac by_extensionality x :=
  intros; unfold compose;
  match goal with
  | [ |- ?f = ?g ] => eapply path_forall; intro x;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl; auto with path_hints
  end.

(** Removed auto. We can write "by (path_induction;auto with path_hints)"
 if we want to.*)
Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : _ = _  |- _ ] => induction p
      | _ => idtac
    end
  ).

(** The tactic [f_ap] is a replacement for the previously existing standard library tactic [f_equal].  This tactic works by repeatedly applying the fact that [f = g -> x = y -> f x = g y] to turn, e.g., [f x y = f z w] first into [f x = f z] and [y = w], and then turns the first of these into [f = f] and [x = z].  The [done] tactic is used to detect the [f = f] case and finish, and the [trivial] is used to solve, e.g., [x = x] when using [f_ap] on [f y x = f z x].  This tactic only works for non-dependently-typed functions; we cannot express [y = w] in the first example if [y] and [w] have different types.  If and when Arnaud's new-tacticals branch lands, and we can have a goal which depends on the term used to discharge another goal, then this tactic should probably be generalized to deal with dependent functions. *)
Ltac f_ap :=
  idtac;
  lazymatch goal with
    | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g);
                             try (done || f_ap)
    | _ => apply ap11;
          [ done || f_ap
          | trivial ]
  end.

(** [expand] replaces both terms of an equality (either [paths] or [pointwise_paths] in the goal with their head normal forms *)
Ltac expand :=
  idtac;
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

(** [atomic x] is the same as [idtac] if [x] is a variable or hypothesis, but is [fail 0] if [x] has internal structure. *)
Ltac atomic x :=
  idtac;
  match x with
    | ?f _ => fail 1 x "is not atomic"
    | (fun _ => _) => fail 1 x "is not atomic"
    | forall _, _ => fail 1 x "is not atomic"
    | _ => idtac
  end.

End Overture.

End HoTT.

End HoTT_DOT_Overture.

Module HoTT_DOT_PathGroupoids.
Module HoTT.
Module PathGroupoids.
Import HoTT_DOT_Overture.
Import HoTT_DOT_Overture.HoTT.
(** * The groupid structure of paths *)
Import HoTT_DOT_Overture.HoTT.Overture.

Local Open Scope path_scope.

(** ** Naming conventions

   We need good naming conventions that allow us to name theorems without looking them up. The names should indicate the structure of the theorem, but they may sometimes be ambiguous, in which case you just have to know what is going on.    We shall adopt the following principles:

   - we are not afraid of long names
   - we are not afraid of short names when they are used frequently
   - we use underscores
   - name of theorems and lemmas are lower-case
   - records and other types may be upper or lower case

   Theorems about concatenation of paths are called [concat_XXX] where [XXX] tells us what is on the left-hand side of the equation. You have to guess the right-hand side. We use the following symbols in [XXX]:

   - [1] means the identity path
   - [p] means 'the path'
   - [V] means 'the inverse path'
   - [A] means '[ap]'
   - [M] means the thing we are moving across equality
   - [x] means 'the point' which is not a path, e.g. in [transport p x]
   - [2] means relating to 2-dimensional paths
   - [3] means relating to 3-dimensional paths, and so on

   Associativity is indicated with an underscore. Here are some examples of how the name gives hints about the left-hand side of the equation.

   - [concat_1p] means [1 * p]
   - [concat_Vp] means [p^ * p]
   - [concat_p_pp] means [p * (q * r)]
   - [concat_pp_p] means [(p * q) * r]
   - [concat_V_pp] means [p^ * (p * q)]
   - [concat_pV_p] means [(q * p^) * p] or [(p * p^) * q], but probably the former because for the latter you could just use [concat_pV].

   Laws about inverse of something are of the form [inv_XXX], and those about [ap] are of the form [ap_XXX], and so on. For example:

   - [inv_pp] is about [(p @ q)^]
   - [inv_V] is about [(p^)^]
   - [inv_A] is about [(ap f p)^]
   - [ap_V] is about [ap f (p^)]
   - [ap_pp] is about [ap f (p @ q)]
   - [ap_idmap] is about [ap idmap p]
   - [ap_1] is about [ap f 1]
   - [ap02_p2p] is about [ap02 f (p @@ q)]

   Then we have laws which move things around in an equation. The naming scheme here is [moveD_XXX]. The direction [D] indicates where to move to: [L] means that we move something to the left-hand side, whereas [R] means we are moving something to the right-hand side. The part [XXX] describes the shape of the side _from_ which we are moving where the thing that is getting moves is called [M].  The presence of 1 next to an [M] generally indicates an *implied* identity path which is inserted automatically after the movement.  Examples:

   - [moveL_pM] means that we transform [p = q @ r] to [p @ r^ = q]
     because we are moving something to the left-hand side, and we are
     moving the right argument of concat.

   - [moveR_Mp] means that we transform [p @ q = r] to [q = p^ @ r]
     because we move to the right-hand side, and we are moving the left
     argument of concat.

   - [moveR_1M] means that we transform [p = q] (rather than [p = 1 @ q]) to [p * q^ = 1].

   There are also cancellation laws called [cancelR] and [cancelL], which are inverse to the 2-dimensional 'whiskering' operations [whiskerR] and [whiskerL].

   We may now proceed with the groupoid structure proper.
*)

(** ** The 1-dimensional groupoid structure. *)

(** The identity path is a right unit. *)
Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p
  :=
  match p with idpath => 1 end.

(** The identity is a left unit. *)
Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p
  :=
  match p with idpath => 1 end.

(** Concatenation is associative. *)
Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r) :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

(** The left inverse law. *)
Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p^ = 1
  :=
  match p with idpath => 1 end.

(** The right inverse law. *)
Definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  p^ @ p = 1
  :=
  match p with idpath => 1 end.

(** Several auxiliary theorems about canceling inverses across associativity.  These are somewhat redundant, following from earlier theorems.  *)

Definition concat_V_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  p^ @ (p @ q) = q
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @ (p^ @ q) = q
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q) @ q^ = p
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ q^) @ q = p
  :=
  (match q as i return forall p, (p @ i^) @ i = p with
    idpath =>
    fun p =>
      match p with idpath => 1 end
  end) p.

(** Inverse distributes over concatenation *)
Definition inv_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition inv_Vp {A : Type} {x y z : A} (p : y = x) (q : y = z) :
  (p^ @ q)^ = q^ @ p
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition inv_pV {A : Type} {x y z : A} (p : x = y) (q : z = y) :
  (p @ q^)^ = q @ p^.
Proof.
  destruct p. destruct q. reflexivity.
Defined.

Definition inv_VV {A : Type} {x y z : A} (p : y = x) (q : z = y) :
  (p^ @ q^)^ = q @ p.
Proof.
  destruct p. destruct q. reflexivity.
Defined.

(** Inverse is an involution. *)
Definition inv_V {A : Type} {x y : A} (p : x = y) :
  p^^ = p
  :=
  match p with idpath => 1 end.


(* *** Theorems for moving things around in equations. *)

Definition moveR_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  p = r^ @ q -> r @ p = q.
Proof.
  destruct r.
  intro h. exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q @ p^ -> r @ p = q.
Proof.
  destruct p.
  intro h. exact (concat_p1 _ @ h @ concat_p1 _).
Defined.

Definition moveR_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r @ q -> r^ @ p = q.
Proof.
  destruct r.
  intro h. exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveR_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  r = q @ p -> r @ p^ = q.
Proof.
  destruct p.
  intro h. exact (concat_p1 _ @ h @ concat_p1 _).
Defined.

Definition moveL_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r^ @ q = p -> q = r @ p.
Proof.
  destruct r.
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveL_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r -> q = r @ p.
Proof.
  destruct p.
  intro h. exact ((concat_p1 _)^ @ h @ (concat_p1 _)^).
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
Proof.
  destruct r.
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveL_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  q @ p = r -> q = r @ p^.
Proof.
  destruct p.
  intro h. exact ((concat_p1 _)^ @ h @ (concat_p1 _)^).
Defined.

Definition moveL_1M {A : Type} {x y : A} (p q : x = y) :
  p @ q^ = 1 -> p = q.
Proof.
  destruct q.
  intro h. exact ((concat_p1 _)^ @ h).
Defined.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = 1 -> p = q.
Proof.
  destruct q.
  intro h. exact ((concat_1p _)^ @ h).
Defined.

Definition moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1 -> p = q^.
Proof.
  destruct q.
  intro h. exact ((concat_p1 _)^ @ h).
Defined.

Definition moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  q @ p = 1 -> p = q^.
Proof.
  destruct q.
  intro h. exact ((concat_1p _)^ @ h).
Defined.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_1p _)).
Defined.

Definition moveR_1M {A : Type} {x y : A} (p q : x = y) :
  1 = q @ p^ -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_p1 _)).
Defined.

Definition moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = q @ p -> p^ = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_p1 _)).
Defined.

Definition moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = p @ q -> p^ = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_1p _)).
Defined.

Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = p^ # v -> p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> p^ # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : p # u = v -> u = p^ # v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : p^ # u = v -> u = p # v.
Proof.
  destruct p.
  exact idmap.
Defined.

(** *** Functoriality of functions *)

(** Here we prove that functions behave like functors between groupoids, and that [ap] itself is functorial. *)

(** Functions take identity paths to identity paths. *)
Definition ap_1 {A B : Type} (x : A) (f : A -> B) :
  ap f 1 = 1 :> (f x = f x)
  :=
  1.

Definition apD_1 {A B} (x : A) (f : forall x : A, B x) :
  apD f 1 = 1 :> (f x = f x)
  :=
  1.

(** Functions commute with concatenation. *)
Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q)
  :=
  match q with
    idpath =>
    match p with idpath => 1 end
  end.

Definition ap_p_pp {A B : Type} (f : A -> B) {w x y z : A}
  (r : f w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q).
Proof.
  destruct p, q. simpl. exact (concat_p_pp r 1 1).
Defined.

Definition ap_pp_p {A B : Type} (f : A -> B) {w x y z : A}
  (p : x = y) (q : y = z) (r : f z = f w) :
  (ap f (p @ q)) @ r = (ap f p) @ (ap f q @ r).
Proof.
  destruct p, q. simpl. exact (concat_pp_p 1 1 r).
Defined.

(** Functions commute with path inverses. *)
Definition inverse_ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  (ap f p)^ = ap f (p^)
  :=
  match p with idpath => 1 end.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^
  :=
  match p with idpath => 1 end.

(** [ap] itself is functorial in the first argument. *)

Definition ap_idmap {A : Type} {x y : A} (p : x = y) :
  ap idmap p = p
  :=
  match p with idpath => 1 end.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g o f) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.

(* Sometimes we don't have the actual function [compose]. *)
Definition ap_compose' {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun a => g (f a)) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.

(** The action of constant maps. *)
Definition ap_const {A B : Type} {x y : A} (p : x = y) (z : B) :
  ap (fun _ => z) p = 1
  :=
  match p with idpath => idpath end.

(** Naturality of [ap]. *)
Definition concat_Ap {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ (ap g q)
  :=
  match q with
    | idpath => concat_1p _ @ ((concat_p1 _) ^)
  end.

(** Naturality of [ap] at identity. *)
Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q
  :=
  match q with
    | idpath => concat_1p _ @ ((concat_p1 _) ^)
  end.

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y)
  :=
  match q as i in (_ = y) return (p x @ ap f i = i @ p y) with
    | idpath => concat_p1 _ @ (concat_1p _)^
  end.

(** Naturality with other paths hanging around. *)
Definition concat_pA_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w z : B} (r : w = f x) (s : g y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (ap g q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pA_p {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w : B} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ ap g q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_A_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {z : B} (s : g y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (ap g q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Definition concat_pA1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = f x) (s : y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pp_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = x) (s : g y = z)
  :
  (r @ p x) @ (ap g q @ s) = (r @ q) @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_A1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {z : A} (s : y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Definition concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
  (r @ p x) @ ap g q = (r @ q) @ p y.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_p_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {z : A} (s : g y = z)
  :
  p x @ (ap g q @ s) = q @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

(** *** Action of [apD10] and [ap10] on paths. *)

(** Application of paths between functions preserves the groupoid structure *)

Definition apD10_1 {A} {B:A->Type} (f : forall x, B x) (x:A)
  : apD10 (idpath f) x = 1
:= 1.

Definition apD10_pp {A} {B:A->Type} {f f' f'' : forall x, B x}
  (h:f=f') (h':f'=f'') (x:A)
: apD10 (h @ h') x = apD10 h x @ apD10 h' x.
Proof.
  case h, h'; reflexivity.
Defined.

Definition apD10_V {A} {B:A->Type} {f g : forall x, B x} (h:f=g) (x:A)
  : apD10 (h^) x = (apD10 h x)^
:= match h with idpath => 1 end.

Definition ap10_1 {A B} {f:A->B} (x:A) : ap10 (idpath f) x = 1
  := 1.

Definition ap10_pp {A B} {f f' f'':A->B} (h:f=f') (h':f'=f'') (x:A)
  : ap10 (h @ h') x = ap10 h x @ ap10 h' x
:= apD10_pp h h' x.

Definition ap10_V {A B} {f g : A->B} (h : f = g) (x:A)
  : ap10 (h^) x = (ap10 h x)^
:= apD10_V h x.

(** [ap10] also behaves nicely on paths produced by [ap] *)
Lemma ap_ap10 {A B C} (f g : A -> B) (h : B -> C)
  (p : f = g) (a : A) :
  ap h (ap10 p a) = ap10 (ap (fun f' => h o f') p) a.
Proof.
  destruct p. exact 1.
Defined.

(** *** Transport and the groupoid structure of paths *)

Definition transport_1 {A : Type} (P : A -> Type) {x : A} (u : P x)
  : 1 # u = u
:= 1.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # p^ # z = z
  := (transport_pp P p^ p z)^
  @ ap (fun r => transport P r z) (concat_Vp p).

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P x)
  : p^ # p # z = z
  := (transport_pp P p p^ z)^
  @ ap (fun r => transport P r z) (concat_pV p).

(** In the future, we may expect to need some higher coherence for transport:
  for instance, that transport acting on the associator is trivial. *)
Definition transport_p_pp {A : Type} (P : A -> Type)
  {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
  (u : P x)
  : ap (fun e => e # u) (concat_p_pp p q r)
    @ (transport_pp P (p@q) r u) @ ap (transport P r) (transport_pp P p q u)
  = (transport_pp P p (q@r) u) @ (transport_pp P q r (p#u))
  :> ((p @ (q @ r)) # u = r # q # p # u) .
Proof.
  destruct p, q, r.  simpl.  exact 1.
Defined.

(* Here is another coherence lemma for transport. *)
Definition transport_pVp {A} (P : A -> Type) {x y:A} (p:x=y) (z:P x)
  : transport_pV P p (transport P p z)
  = ap (transport P p) (transport_Vp P p z).
Proof.
  destruct p; reflexivity.
Defined.

(** Dependent transport in a doubly dependent type. *)

Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with idpath => z end.

(** Transporting along higher-dimensional paths *)

Definition transport2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : P x)
  : p # z = q # z
  := ap (fun p' => p' # z) r.

(** An alternative definition. *)
Definition transport2_is_ap10 {A : Type} (Q : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q r z = ap10 (ap (transport Q) r) z
  := match r with idpath => 1 end.

Definition transport2_p2p {A : Type} (P : A -> Type) {x y : A} {p1 p2 p3 : x = y}
  (r1 : p1 = p2) (r2 : p2 = p3) (z : P x)
  : transport2 P (r1 @ r2) z = transport2 P r1 z @ transport2 P r2 z.
Proof.
  destruct r1, r2; reflexivity.
Defined.

Definition transport2_V {A : Type} (Q : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q (r^) z = (transport2 Q r z)^
  := match r with idpath => 1 end.

Definition concat_AT {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  {z w : P x} (r : p = q) (s : z = w)
  : ap (transport P p) s  @  transport2 P r w
    = transport2 P r z  @  ap (transport P q) s
  := match r with idpath => (concat_p1 _ @ (concat_1p _)^) end.

(* TODO: What should this be called? *)
Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
Proof.
  by induction p.
Defined.


(** *** Transporting in particular fibrations. *)

(** One frequently needs lemmas showing that transport in a certain dependent type is equal to some more explicitly defined operation, defined according to the structure of that dependent type.  For most dependent types, we prove these lemmas in the appropriate file in the types/ subdirectory.  Here we consider only the most basic cases. *)

(** Transporting in a constant fibration. *)
Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  destruct p.  exact 1.
Defined.

Definition transport2_const {A B : Type} {x1 x2 : A} {p q : x1 = x2}
  (r : p = q) (y : B)
  : transport_const p y = transport2 (fun _ => B) r y @ transport_const q y
  := match r with idpath => (concat_1p _)^ end.

(** Transporting in a pulled back fibration. *)
Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
Proof.
  destruct p; reflexivity.
Defined.

(** A special case of [transport_compose] which seems to come up a lot. *)
Definition transport_idmap_ap A (P : A -> Type) x y (p : x = y) (u : P x)
: transport P p u = transport idmap (ap P p) u
  := match p with idpath => idpath end.

(** *** The behavior of [ap] and [apD]. *)

(** In a constant fibration, [apD] reduces to [ap], modulo [transport_const]. *)
Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) :
  apD f p = transport_const p (f x) @ ap f p.
Proof.
  destruct p; reflexivity.
Defined.

(** ** The 2-dimensional groupoid structure *)

(** Horizontal composition of 2-dimensional paths. *)
Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p @ q = p' @ q'
:= match h, h' with idpath, idpath => 1 end.

Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.

(** 2-dimensional path inversion *)
Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
  : p^ = q^
:= match h with idpath => 1 end.

(** *** Whiskering *)

Definition whiskerL {A : Type} {x y z : A} (p : x = y)
  {q r : y = z} (h : q = r) : p @ q = p @ r
:= 1 @@ h.

Definition whiskerR {A : Type} {x y z : A} {p q : x = y}
  (h : p = q) (r : y = z) : p @ r = q @ r
:= h @@ 1.

(** *** Unwhiskering, a.k.a. cancelling. *)

Lemma cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : (p @ q = p @ r) -> (q = r).
Proof.
  destruct p, r.
  intro a.
  exact ((concat_1p q)^ @ a).
Defined.

Lemma cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : (p @ r = q @ r) -> (p = q).
Proof.
  destruct r, p.
  intro a.
  exact (a @ concat_p1 q).
Defined.

(** Whiskering and identity paths. *)

Definition whiskerR_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_p1 p) ^ @ whiskerR h 1 @ concat_p1 q = h
  :=
  match h with idpath =>
    match p with idpath =>
      1
    end end.

Definition whiskerR_1p {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerR 1 q = 1 :> (p @ q = p @ q)
  :=
  match q with idpath => 1 end.

Definition whiskerL_p1 {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerL p 1 = 1 :> (p @ q = p @ q)
  :=
  match q with idpath => 1 end.

Definition whiskerL_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_1p p) ^ @ whiskerL 1 h @ concat_1p q = h
  :=
  match h with idpath =>
    match p with idpath =>
      1
    end end.

Definition concat2_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  h @@ 1 = whiskerR h 1 :> (p @ 1 = q @ 1)
  :=
  match h with idpath => 1 end.

Definition concat2_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  1 @@ h = whiskerL 1 h :> (1 @ p = 1 @ q)
  :=
  match h with idpath => 1 end.


(** The interchange law for concatenation. *)
Definition concat_concat2 {A : Type} {x y z : A} {p p' p'' : x = y} {q q' q'' : y = z}
  (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q'') :
  (a @@ c) @ (b @@ d) = (a @ b) @@ (c @ d).
Proof.
  case d.
  case c.
  case b.
  case a.
  reflexivity.
Defined.

(** The interchange law for whiskering.  Special case of [concat_concat2]. *)
Definition concat_whisker {A} {x y z : A} (p p' : x = y) (q q' : y = z) (a : p = p') (b : q = q') :
  (whiskerR a q) @ (whiskerL p' b) = (whiskerL p b) @ (whiskerR a q')
  :=
  match b with
    idpath =>
    match a with idpath =>
      (concat_1p _)^
    end
  end.

(** Structure corresponding to the coherence equations of a bicategory. *)

(** The "pentagonator": the 3-cell witnessing the associativity pentagon. *)
Definition pentagon {A : Type} {v w x y z : A} (p : v = w) (q : w = x) (r : x = y) (s : y = z)
  : whiskerL p (concat_p_pp q r s)
      @ concat_p_pp p (q@r) s
      @ whiskerR (concat_p_pp p q r) s
  = concat_p_pp p q (r@s) @ concat_p_pp (p@q) r s.
Proof.
  case p, q, r, s.  reflexivity.
Defined.

(** The 3-cell witnessing the left unit triangle. *)
Definition triangulator {A : Type} {x y z : A} (p : x = y) (q : y = z)
  : concat_p_pp p 1 q @ whiskerR (concat_p1 p) q
  = whiskerL p (concat_1p q).
Proof.
  case p, q.  reflexivity.
Defined.

(** The Eckmann-Hilton argument *)
Definition eckmann_hilton {A : Type} {x:A} (p q : 1 = 1 :> (x = x)) : p @ q = q @ p :=
  (whiskerR_p1 p @@ whiskerL_1p q)^
  @ (concat_p1 _ @@ concat_p1 _)
  @ (concat_1p _ @@ concat_1p _)
  @ (concat_whisker _ _ _ _ p q)
  @ (concat_1p _ @@ concat_1p _)^
  @ (concat_p1 _ @@ concat_p1 _)^
  @ (whiskerL_1p q @@ whiskerR_p1 p).

(** The action of functions on 2-dimensional paths *)

Definition ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q
  := match r with idpath => 1 end.

Definition ap02_pp {A B} (f:A->B) {x y:A} {p p' p'':x=y} (r:p=p') (r':p'=p'')
  : ap02 f (r @ r') = ap02 f r @ ap02 f r'.
Proof.
  case r, r'; reflexivity.
Defined.

Definition ap02_p2p {A B} (f:A->B) {x y z:A} {p p':x=y} {q q':y=z} (r:p=p') (s:q=q')
  : ap02 f (r @@ s) =   ap_pp f p q
                      @ (ap02 f r  @@  ap02 f s)
                      @ (ap_pp f p' q')^.
Proof.
  case r, s, p, q. reflexivity.
Defined.

Definition apD02 {A : Type} {B : A -> Type} {x y : A} {p q : x = y}
  (f : forall x, B x) (r : p = q)
  : apD f p = transport2 B r (f x) @ apD f q
  := match r with idpath => (concat_1p _)^ end.

(* And now for a lemma whose statement is much longer than its proof. *)
Definition apD02_pp {A} (B : A -> Type) (f : forall x:A, B x) {x y : A}
  {p1 p2 p3 : x = y} (r1 : p1 = p2) (r2 : p2 = p3)
  : apD02 f (r1 @ r2)
  = apD02 f r1
  @ whiskerL (transport2 B r1 (f x)) (apD02 f r2)
  @ concat_p_pp _ _ _
  @ (whiskerR (transport2_p2p B r1 r2 (f x))^ (apD f p3)).
Proof.
  destruct r1, r2. destruct p1. reflexivity.
Defined.

(** ** Tactics, hints, and aliases *)

(** [concat], with arguments flipped. Useful mainly in the idiom [apply (concatR (expression))]. Given as a notation not a definition so that the resultant terms are literally instances of [concat], with no unfolding required. *)
Notation concatR := (fun p q => concat q p).

Hint Resolve
  concat_1p concat_p1 concat_p_pp
  inv_pp inv_V
 : path_hints.

(* First try at a paths db
We want the RHS of the equation to become strictly simpler *)
Hint Rewrite
@concat_p1
@concat_1p
@concat_p_pp (* there is a choice here !*)
@concat_pV
@concat_Vp
@concat_V_pp
@concat_p_Vp
@concat_pp_V
@concat_pV_p
(*@inv_pp*) (* I am not sure about this one *)
@inv_V
@moveR_Mp
@moveR_pM
@moveL_Mp
@moveL_pM
@moveL_1M
@moveL_M1
@moveR_M1
@moveR_1M
@ap_1
(* @ap_pp
@ap_p_pp ?*)
@inverse_ap
@ap_idmap
(* @ap_compose
@ap_compose'*)
@ap_const
(* Unsure about naturality of [ap], was absent in the old implementation*)
@apD10_1
:paths.

Ltac hott_simpl :=
  autorewrite with paths in * |- * ; auto with path_hints.

End PathGroupoids.

End HoTT.

End HoTT_DOT_PathGroupoids.

Module HoTT_DOT_Contractible.
Module HoTT.
Module Contractible.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** Contractibility *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_PathGroupoids.HoTT.PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** Naming convention: we consistently abbreviate "contractible" as "contr".  A theorem about a space [X] being contractible (which will usually be an instance of the typeclass [Contr]) is called [contr_X]. *)

(** Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. *)
Generalizable Variables A B f.

(** If a space is contractible, then any two points in it are connected by a path in a canonical way. *)
Definition path_contr `{Contr A} (x y : A) : x = y
  := (contr x)^ @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. *)
Definition path2_contr `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    intro r; destruct r; apply symmetry; now apply concat_Vp.
  path_via (path_contr x y).
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)
(** Because [Contr] is a notation, and [Contr_internal] is the record, we need to iota expand to fool Coq's typeclass machinery into accepting supposedly "mismatched" contexts. *)
Instance contr_paths_contr `{Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := (contr x)^ @ contr y;
  contr := path2_contr ((contr x)^ @ contr y)
|} in c.

(** Also, the total space of any based path space is contractible. *)
Instance contr_basedpaths {X : Type} (x : X) : Contr {y : X & x = y} | 100.
  exists (x ; 1).
  intros [y []]; reflexivity.
Defined.

Instance contr_basedpaths' {X : Type} (x : X) : Contr {y : X & y = x} | 100.
  exists (existT (fun y => y = x) x 1).
  intros [y []]; reflexivity.
Defined.

End Contractible.

End HoTT.

End HoTT_DOT_Contractible.

Module HoTT_DOT_Equivalences.
Module HoTT.
Module Equivalences.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Equivalences *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_PathGroupoids.HoTT.PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** We now give many ways to construct equivalences.  In each case, we define an instance of the typeclass [IsEquiv] named [isequiv_X], followed by an element of the record type [Equiv] named [equiv_X].

   Whenever we need to assume, as a hypothesis, that a certain function is an equivalence, we do it by assuming separately a function and a proof of [IsEquiv].  This is more general than assuming an inhabitant of [Equiv], since the latter has an implicit coercion and an existing instance to give us the former automatically.  Moreover, implicit generalization makes it easy to assume a function and a proof of [IsEquiv]. *)

Generalizable Variables A B C f g.

(** The identity map is an equivalence. *)
Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  BuildIsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition equiv_idmap (A : Type) : A <~> A := BuildEquiv A A idmap _.

Instance reflexive_equiv : Reflexive Equiv | 0 := equiv_idmap.

(** The composition of equivalences is an equivalence. *)
Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (compose g f) | 1000
  := BuildIsEquiv A C (compose g f)
    (compose f^-1 g^-1)
    (fun c => ap g (eisretr f (g^-1 c)) @ eisretr g c)
    (fun a => ap (f^-1) (eissect g (f a)) @ eissect f a)
    (fun a =>
      (whiskerL _ (eisadj g (f a))) @
      (ap_pp g _ _)^ @
      ap02 g
      ( (concat_A1p (eisretr f) (eissect g (f a)))^ @
        (ap_compose f^-1 f _ @@ eisadj f a) @
        (ap_pp f _ _)^
      ) @
      (ap_compose f g _)^
    ).

(* An alias of [isequiv_compose], with some arguments explicit; often convenient when type class search fails. *)
Definition isequiv_compose'
  {A B : Type} (f : A -> B) (_ : IsEquiv f)
  {C : Type} (g : B -> C) (_ : IsEquiv g)
  : IsEquiv (g o f)
  := isequiv_compose.

Definition equiv_compose {A B C : Type} (g : B -> C) (f : A -> B)
  `{IsEquiv B C g} `{IsEquiv A B f}
  : A <~> C
  := BuildEquiv A C (compose g f) _.

Definition equiv_compose' {A B C : Type} (g : B <~> C) (f : A <~> B)
  : A <~> C
  := equiv_compose g f.

(* The TypeClass [Transitive] has a different order of parameters than [equiv_compose].  Thus in declaring the instance we have to switch the order of arguments. *)
Instance transitive_equiv : Transitive Equiv | 0 :=
  fun _ _ _ f g => equiv_compose g f.


(** Anything homotopic to an equivalence is an equivalence. *)
Section IsEquivHomotopic.

  Context `(f : A -> B) `(g : A -> B).
  Context `{IsEquiv A B f}.
  Hypothesis h : f == g.

  Let sect := (fun b:B => (h (f^-1 b))^ @ eisretr f b).
  Let retr := (fun a:A => (ap f^-1 (h a))^ @ eissect f a).

  (* We prove the triangle identity with rewrite tactics.  Since we lose control over the proof term that way, we make the result opaque with "Qed". *)
  Let adj (a : A) : sect (g a) = ap g (retr a).
  Proof.
    unfold sect, retr.
    rewrite ap_pp. apply moveR_Vp.
    rewrite concat_p_pp, <- concat_Ap, concat_pp_p, <- concat_Ap.
    rewrite ap_V; apply moveL_Vp.
    rewrite <- ap_compose; unfold compose; rewrite (concat_A1p (eisretr f) (h a)).
    apply whiskerR, eisadj.
  Qed.

  (* It's unclear to me whether this should be a declared instance.  Will it cause the unifier to spin forever searching for homotopies?  For now, we give it a very large priority number, which means that other instances will be preferred over this one. *)
  Global Instance isequiv_homotopic : IsEquiv g | 10000
    := BuildIsEquiv _ _ g (f ^-1) sect retr adj.

  Definition equiv_homotopic : A <~> B
    := BuildEquiv _ _ g isequiv_homotopic.

End IsEquivHomotopic.


(** The inverse of an equivalence is an equivalence. *)
Section EquivInverse.

  Context `{IsEquiv A B f}.
  Open Scope long_path_scope.

  Theorem other_adj (b : B) : eissect f (f^-1 b) = ap f^-1 (eisretr f b).
  Proof.
    (* First we set up the mess. *)
    rewrite <- (concat_1p (eissect _ _)).
    rewrite <- (concat_Vp (ap f^-1 (eisretr f (f (f^-1 b))))).
    rewrite (whiskerR (inverse2 (ap02 f^-1 (eisadj f (f^-1 b)))) _).
    refine (whiskerL _ (concat_1p (eissect _ _))^ @ _).
    rewrite <- (concat_Vp (eissect f (f^-1 (f (f^-1 b))))).
    rewrite <- (whiskerL _ (concat_1p (eissect f (f^-1 (f (f^-1 b)))))).
    rewrite <- (concat_pV (ap f^-1 (eisretr f (f (f^-1 b))))).
    apply moveL_M1.
    repeat rewrite concat_p_pp.
    (* Now we apply lots of naturality and cancel things. *)
    rewrite <- (concat_pp_A1 (fun a => (eissect f a)^) _ _).
    rewrite (ap_compose' f f^-1).
    rewrite <- (ap_p_pp _ _ (ap f (ap f^-1 (eisretr f (f (f^-1 b))))) _).
    rewrite <- (ap_compose f^-1 f); unfold compose.
    rewrite (concat_A1p (eisretr f) _).
    rewrite ap_pp, concat_p_pp.
    rewrite (concat_pp_V _ (ap f^-1 (eisretr f (f (f^-1 b))))).
    repeat rewrite <- ap_V; rewrite <- ap_pp.
    rewrite <- (concat_pA1 (fun y => (eissect f y)^) _).
    rewrite ap_compose', <- (ap_compose f^-1 f); unfold compose.
    rewrite <- ap_p_pp.
    rewrite (concat_A1p (eisretr f) _).
    rewrite concat_p_Vp.
    rewrite <- ap_compose; unfold compose.
    rewrite (concat_pA1_p (eissect f) _).
    rewrite concat_pV_p; apply concat_Vp.
  Qed.

  Global Instance isequiv_inverse : IsEquiv f^-1 | 10000
    := BuildIsEquiv B A f^-1 f (eissect f) (eisretr f) other_adj.
End EquivInverse.

(** If the goal is [IsEquiv _^-1], then use [isequiv_inverse]; otherwise, don't pretend worry about if the goal is an evar and we want to add a [^-1]. *)
Hint Extern 0 (IsEquiv _^-1) => apply @isequiv_inverse : typeclass_instances.

(** [Equiv A B] is a symmetric relation. *)
Theorem equiv_inverse {A B : Type} : (A <~> B) -> (B <~> A).
Proof.
  intro e.
  exists (e^-1).
  apply isequiv_inverse.
Defined.

Instance symmetric_equiv : Symmetric Equiv | 0 := @equiv_inverse.

(** If [g \o f] and [f] are equivalences, so is [g]. *)
Instance cancelR_isequiv `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : IsEquiv g | 10000
:= isequiv_homotopic (compose (compose g f) f^-1) g
       (fun b => ap g (eisretr f b)).

Arguments cancelR_isequiv {_ _ _ _ _} g {_}.

Definition cancelR_equiv `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : B <~> C
:= BuildEquiv _ _ g (cancelR_isequiv g).

(** If [g \o f] and [g] are equivalences, so is [f]. *)
Instance cancelL_isequiv `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : IsEquiv f | 10000
:= isequiv_homotopic (compose g^-1 (compose g f)) f
       (fun a => eissect g (f a)).

Arguments cancelL_isequiv {_ _ _ _ _} f {_}.

Definition cancelL_equiv `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : A <~> B
:= BuildEquiv _ _ f (cancelL_isequiv f).

(** Transporting is an equivalence. *)
Section EquivTransport.

  Context {A : Type} (P : A -> Type) (x y : A) (p : x = y).

  Global Instance isequiv_transport : IsEquiv (transport P p) | 0
    := BuildIsEquiv (P x) (P y) (transport P p) (transport P p^)
    (transport_pV P p) (transport_Vp P p) (transport_pVp P p).

  Definition equiv_transport : P x <~> P y
    := BuildEquiv _ _ (transport P p) _.

End EquivTransport.

(** In all the above cases, we were able to directly construct all the structure of an equivalence.  However, as is evident, sometimes it is quite difficult to prove the adjoint law.

   The following adjointification theorem allows us to be lazy about this if we wish.  It says that if we have all the data of an (adjoint) equivalence except the triangle identity, then we can always obtain the triangle identity by modifying the datum [equiv_is_section] (or [equiv_is_retraction]).  The proof is the same as the standard categorical argument that any equivalence can be improved to an adjoint equivalence.

   As a stylistic matter, we try to avoid using adjointification in the library whenever possible, to preserve the homotopies specified by the user.  *)

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).

  (* This is the modified [eissect]. *)
  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
  Proof.
    unfold issect'.
    apply moveR_M1.
    repeat rewrite ap_pp, concat_p_pp; rewrite <- ap_compose; unfold compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)^)).
    repeat rewrite concat_pp_p; rewrite ap_V; apply moveL_Vp; rewrite concat_p1.
    rewrite concat_p_pp, <- ap_compose; unfold compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
    rewrite concat_pV, concat_1p; reflexivity.
  Qed.

  (** We don't make this a typeclass instance, because we want to control when we are applying it. *)
  Definition isequiv_adjointify : IsEquiv f
    := BuildIsEquiv A B f g isretr issect' is_adjoint'.

  Definition equiv_adjointify : A <~> B
    := BuildEquiv A B f isequiv_adjointify.

End Adjointify.

(** Several lemmas useful for rewriting. *)
Definition moveR_E `{IsEquiv A B f} (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y)
  := ap f p @ eisretr f y.

Definition moveL_E `{IsEquiv A B f} (x : A) (y : B) (p : f^-1 y = x)
  : (y = f x)
  := (eisretr f y)^ @ ap f p.

(** Equivalence preserves contractibility (which of course is trivial under univalence). *)
Lemma contr_equiv `(f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (center A)).
  intro y.
  apply moveR_E.
  apply contr.
Qed.

Definition contr_equiv' `(f : A <~> B) `{Contr A}
  : Contr B
  := contr_equiv f.

(** Assuming function extensionality, composing with an equivalence is itself an equivalence *)

Instance isequiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : IsEquiv (fun g => @compose A B C g f) | 1000
  := isequiv_adjointify (fun g => @compose A B C g f)
    (fun h => @compose B A C h f^-1)
    (fun h => path_forall _ _ (fun x => ap h (eissect f x)))
    (fun g => path_forall _ _ (fun y => ap g (eisretr f y))).

Definition equiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : (B -> C) <~> (A -> C)
  := BuildEquiv _ _ (fun g => @compose A B C g f) _.

Definition equiv_precompose' `{Funext} {A B C : Type} (f : A <~> B)
  : (B -> C) <~> (A -> C)
  := BuildEquiv _ _ (fun g => @compose A B C g f) _.

Instance isequiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : IsEquiv (fun g => @compose A B C f g) | 1000
  := isequiv_adjointify (fun g => @compose A B C f g)
    (fun h => @compose A C B f^-1 h)
    (fun h => path_forall _ _ (fun x => eisretr f (h x)))
    (fun g => path_forall _ _ (fun y => eissect f (g y))).

Definition equiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : (A -> B) <~> (A -> C)
  := BuildEquiv _ _ (fun g => @compose A B C f g) _.

Definition equiv_postcompose' `{Funext} {A B C : Type} (f : B <~> C)
  : (A -> B) <~> (A -> C)
  := BuildEquiv _ _ (fun g => @compose A B C f g) _.


(** The function [equiv_rect] says that given an equivalence [f : A <~> B], and a hypothesis from [B], one may always assume that the hypothesis is in the image of [e].

In fibrational terms, if we have a fibration over [B] which has a section once pulled back along an equivalence [f : A <~> B], then it has a section over all of [B].  *)

Definition equiv_rect `{IsEquiv A B f} (P : B -> Type)
  : (forall x:A, P (f x)) -> forall y:B, P y
  := fun g y => transport P (eisretr f y) (g (f^-1 y)).

Arguments equiv_rect {A B} f {_} P _ _.

(** Using [equiv_rect], we define a handy little tactic which introduces a variable and simultaneously substitutes it along an equivalence. *)

Ltac equiv_intro E x :=
  match goal with
    | |- forall y, @?Q y =>
      refine (equiv_rect E Q _); intros x
  end.

(** [equiv_composeR'], a flipped version of [equiv_compose'], is (like [concatR]) most often useful partially applied, to give the “first half” of an equivalence one is constructing and leave the rest as a subgoal. One could similarly define [equiv_composeR] as a flip of [equiv_compose], but it doesn’t seem so useful since it doesn’t leave the remaining equivalence as a subgoal. *)
Definition equiv_composeR' {A B C} (f : A <~> B) (g : B <~> C)
  := equiv_compose' g f.

Ltac equiv_via mid :=
  apply @equiv_composeR' with (B := mid).

End Equivalences.

End HoTT.

End HoTT_DOT_Equivalences.

Module HoTT_DOT_types_DOT_Paths.
Module HoTT.
Module types.
Module Paths.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about path spaces *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_PathGroupoids.HoTT.PathGroupoids HoTT_DOT_Equivalences.HoTT.Equivalences.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f x y z.

(** ** Path spaces *)

(** The path spaces of a path space are not, of course, determined; they are just the
    higher-dimensional structure of the original space. *)

(** ** Transporting in path spaces.

   There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

   - `l` means the left endpoint varies
   - `r` means the right endpoint varies
   - `F` means application of a function to that (varying) endpoint.
*)

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = p^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  : transport (fun x => x = x) p q = p^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (fun x => f x = y) p q = (ap f p)^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport (fun y => x = g y) p q = q @ (ap g p).
Proof.
  destruct p. apply symmetry, concat_p1.
Defined.

Definition transport_paths_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transport (fun x => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FlFr_D {A : Type} {B : A -> Type}
  {f g : forall a, B a} {x1 x2 : A} (p : x1 = x2) (q : f x1 = g x1)
: transport (fun x => f x = g x) p q
  = (apD f p)^ @ ap (transport B p) q @ (apD g p).
Proof.
  destruct p; simpl.
  exact ((ap_idmap _)^ @ (concat_1p _)^ @ (concat_p1 _)^).
Defined.

Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  : transport (fun x => g (f x) = x) p q = (ap g (ap f p))^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_lFFr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = g (f x1))
  : transport (fun x => x = g (f x)) p q = p^ @ q @ (ap g (ap f p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.


(** ** Functorial action *)

(** 'functor_path' is called [ap]. *)

(** ** Equivalences between path spaces *)

(** If [f] is an equivalence, then so is [ap f].  We are lazy and use [adjointify]. *)
Instance isequiv_ap `{IsEquiv A B f} (x y : A)
  : IsEquiv (@ap A B f x y) | 1000
  := isequiv_adjointify (ap f)
  (fun q => (eissect f x)^  @  ap f^-1 q  @  eissect f y)
  (fun q =>
    ap_pp f _ _
    @ whiskerR (ap_pp f _ _) _
    @ ((ap_V f _ @ inverse2 (eisadj f _)^)
      @@ (ap_compose f^-1 f _)^
      @@ (eisadj f _)^)
    @ concat_pA1_p (eisretr f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _)
  (fun p =>
    whiskerR (whiskerL _ (ap_compose f f^-1 _)^) _
    @ concat_pA1_p (eissect f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _).

Definition equiv_ap `(f : A -> B) `{IsEquiv A B f} (x y : A)
  : (x = y) <~> (f x = f y)
  := BuildEquiv _ _ (ap f) _.

(* TODO: Is this really necessary? *)
Definition equiv_inj `{IsEquiv A B f} {x y : A}
  : (f x = f y) -> (x = y)
  := (ap f)^-1.

(** ** Path operations are equivalences *)

Instance isequiv_path_inverse {A : Type} (x y : A)
  : IsEquiv (@inverse A x y) | 0
  := BuildIsEquiv _ _ _ (@inverse A y x) (@inv_V A y x) (@inv_V A x y) _.
Proof.
  intros p; destruct p; reflexivity.
Defined.

Definition equiv_path_inverse {A : Type} (x y : A)
  : (x = y) <~> (y = x)
  := BuildEquiv _ _ (@inverse A x y) _.

Instance isequiv_concat_l {A : Type} `(p : x = y) (z : A)
  : IsEquiv (@concat A x y z p) | 0
  := BuildIsEquiv _ _ _ (@concat A y x z p^)
     (concat_p_Vp p) (concat_V_pp p) _.
Proof.
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_l {A : Type} `(p : x = y) (z : A)
  : (y = z) <~> (x = z)
  := BuildEquiv _ _ (concat p) _.

Instance isequiv_concat_r {A : Type} `(p : y = z) (x : A)
  : IsEquiv (fun q:x=y => q @ p) | 0
  := BuildIsEquiv _ _ (fun q => q @ p) (fun q => q @ p^)
     (fun q => concat_pV_p q p) (fun q => concat_pp_V q p) _.
Proof.
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_r {A : Type} `(p : y = z) (x : A)
  : (x = y) <~> (x = z)
  := BuildEquiv _ _ (fun q => q @ p) _.

Instance isequiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : IsEquiv (fun r:x=y => p @ r @ q) | 0
  := @isequiv_compose _ _ (fun r => p @ r) _ _ (fun r => r @ q) _.

Definition equiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : (x = y) <~> (x' = y')
  := BuildEquiv _ _ (fun r:x=y => p @ r @ q) _.

(** We can use these to build up more complicated equivalences.

In particular, all of the [move] family are equivalences.

(Note: currently, some but not all of these [isequiv_] lemmas have corresponding [equiv_] lemmas.  Also, they do *not* currently contain the computational content that e.g. the inverse of [moveR_Mp] is [moveL_Vp]; perhaps it would be useful if they did? *)

Definition isequiv_moveR_Mp
 {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_Mp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition isequiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_pM p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition isequiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveR_Vp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: (p = r @ q) <~> (r^ @ p = q)
:= BuildEquiv _ _ _ (isequiv_moveR_Vp p q r).

Definition isequiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveR_pV p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition isequiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_Mp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition isequiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_pM p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r <~> q = r @ p
  := BuildEquiv _ _ _ (isequiv_moveL_pM p q r).

Definition isequiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveL_Vp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition isequiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveL_pV p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition isequiv_moveL_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_1M p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_M1 p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_1V p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_V1 p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_M1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_1M p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_1V p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_V1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveR_transport_p P p u v).
Proof.
  destruct p. apply isequiv_idmap.
Defined.

Definition isequiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveR_transport_V P p u v).
Proof.
  destruct p. apply isequiv_idmap.
Defined.

Definition isequiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveL_transport_V P p u v).
Proof.
  destruct p. apply isequiv_idmap.
Defined.

Definition isequiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveL_transport_p P p u v).
Proof.
  destruct p. apply isequiv_idmap.
Defined.

Definition isequiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : IsEquiv (cancelL p q r).
Proof.
  destruct r, p; simpl. apply isequiv_concat_l.
Defined.

Definition isequiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : IsEquiv (cancelR p q r).
Proof.
  destruct r, p; simpl. apply isequiv_concat_r.
Defined.

Definition equiv_ap_l `(f : A -> B) `{IsEquiv A B f} (x : A) (z : B)
  : (f x = z) <~> (x = f^-1 z).
Proof.
  apply transitivity with (f x = f (f^-1 z)).
  apply equiv_concat_r.
  apply symmetry.
  apply (eisretr f).
  apply symmetry.
  apply equiv_ap.
  assumption.
Defined.

(** *** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a path space, these dependent paths have a more convenient description: rather than transporting the left side both forwards and backwards, we transport both sides of the equation forwards, forming a sort of "naturality square".

   We use the same naming scheme as for the transport lemmas. *)

Definition dpath_path_l {A : Type} {x1 x2 y : A}
  (p : x1 = x2) (q : x1 = y) (r : x2 = y)
  : q = p @ r
  <~>
  transport (fun x => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_r {A : Type} {x y1 y2 : A}
  (p : y1 = y2) (q : x = y1) (r : x = y2)
  : q @ p = r
  <~>
  transport (fun y => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_lr {A : Type} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = x1) (r : x2 = x2)
  : q @ p = p @ r
  <~>
  transport (fun x => x = x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y) (r : f x2 = y)
  : q = ap f p @ r
  <~>
  transport (fun x => f x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_Fr {A B : Type} {g : A -> B} {x : B} {y1 y2 : A}
  (p : y1 = y2) (q : x = g y1) (r : x = g y2)
  : q @ ap g p = r
  <~>
  transport (fun y => x = g y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1) (r : f x2 = g x2)
  : q @ ap g p = ap f p @ r
  <~>
  transport (fun x => f x = g x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_FFlr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  : q @ p = ap g (ap f p) @ r
  <~>
  transport (fun x => g (f x) = x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_lFFr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : x1 = g (f x1)) (r : x2 = g (f x2))
  : q @ ap g (ap f p) = p @ r
  <~>
  transport (fun x => x = g (f x)) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.


(** ** Universal mapping property *)

Instance isequiv_paths_rect `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : IsEquiv (paths_rect a P) | 0
  := isequiv_adjointify (paths_rect a P) (fun f => f a 1) _ _.
Proof.
  - intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  - intros u. reflexivity.
Defined.

Definition equiv_paths_rect `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : P a 1 <~> forall x p, P x p
  := BuildEquiv _ _ (paths_rect a P) _.

(** ** Truncation *)

(** Paths reduce truncation level by one.  This is essentially the definition of [IsTrunc_internal]. *)

End Paths.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Paths.

Module HoTT_DOT_types_DOT_Unit.
Module HoTT.
Module types.
Module Unit.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the unit type *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_PathGroupoids.HoTT.PathGroupoids HoTT_DOT_Equivalences.HoTT.Equivalences.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A.

(** coq calls it "unit", we call it "Unit" *)
(** HoTT/coq is broken and somehow interprets [Type1] as [Prop] with regard to elimination schemes. *)
Unset Elimination Schemes.
Inductive Unit : Type1 :=
    tt : Unit.
Scheme Unit_rect := Induction for Unit Sort Type.
Scheme Unit_rec := Induction for Unit Sort Set.
Scheme Unit_ind := Induction for Unit Sort Prop.
Set Elimination Schemes.

(** ** Eta conversion *)

Definition eta_unit (z : Unit) : tt = z
  := match z with tt => 1 end.

(** ** Paths *)

(* This is all kind of ridiculous, but it fits the pattern. *)

Definition path_unit_uncurried (z z' : Unit) : Unit -> z = z'
  := fun _ => match z, z' with tt, tt => 1 end.

Definition path_unit (z z' : Unit) : z = z'
  := path_unit_uncurried z z' tt.

Definition eta_path_unit {z z' : Unit} (p : z = z') :
  path_unit z z' = p.
Proof.
  destruct p. destruct z. reflexivity.
Defined.

Instance isequiv_path_unit (z z' : Unit) : IsEquiv (path_unit_uncurried z z') | 0.
  refine (BuildIsEquiv _ _ (path_unit_uncurried z z') (fun _ => tt)
    (fun p:z=z' =>
      match p in (_ = z') return (path_unit_uncurried z z' tt = p) with
        | idpath => match z as z return (path_unit_uncurried z z tt = 1) with
                    | tt => 1
                  end
      end)
    (fun x => match x with tt => 1 end) _).
  intros []; destruct z, z'; reflexivity.
Defined.

Definition equiv_path_unit (z z' : Unit) : Unit <~> (z = z')
  := BuildEquiv _ _ (path_unit_uncurried z z') _.

(** ** Transport *)

(** Is a special case of transporting in a constant fibration. *)

(** ** Universal mapping properties *)

(* The positive universal property *)
Arguments Unit_rect [A] a u : rename.

Instance isequiv_unit_rect `{Funext} (A : Type) : IsEquiv (@Unit_rect (fun _ => A)) | 0
  := isequiv_adjointify _
  (fun f : Unit -> A => f tt)
  (fun f : Unit -> A => path_forall (@Unit_rect (fun _ => A) (f tt)) f
                                    (fun x => match x with tt => 1 end))
  (fun _ => 1).

(* For various reasons, it is typically more convenient to define functions out of the unit as constant maps, rather than [Unit_rect]. *)
Notation unit_name x := (fun (_ : Unit) => x).

(* The negative universal property *)
Definition unit_corect {A : Type} : Unit -> (A -> Unit)
  := fun _ _ => tt.

Instance isequiv_unit_corect `{Funext} (A : Type) : IsEquiv (@unit_corect A) | 0
  := isequiv_adjointify _
  (fun f => tt)
  _ _.
Proof.
  - intro f. apply path_forall; intros x; apply path_unit.
  - intro x; destruct x; reflexivity.
Defined.

Definition equiv_unit_corect `{Funext} (A : Type)
  : Unit <~> (A -> Unit)
  := BuildEquiv _ _ (@unit_corect A) _.

(** ** Truncation *)

(* The Unit type is contractible *)
(** Because [Contr] is a notation, and [Contr_internal] is the record, we need to iota expand to fool Coq's typeclass machinery into accepting supposedly "mismatched" contexts. *)
Instance contr_unit : Contr Unit | 0 := let x := {|
  center := tt;
  contr := fun t : Unit => match t with tt => 1 end
|} in x.

(** ** Equivalences *)

(** A contractible type is equivalent to [Unit]. *)
Definition equiv_contr_unit `{Contr A} : A <~> Unit.
Proof.
  refine (BuildEquiv _ _
    (fun (_ : A) => tt)
    (BuildIsEquiv _ _ _
      (fun (_ : Unit) => center A)
      (fun t : Unit => match t with tt => 1 end)
      (fun x : A => contr x) _)).
  intro x. apply symmetry, ap_const.
Defined.

(* Conversely, a type equivalent to [Unit] is contractible. *)
Instance contr_equiv_unit (A : Type) (f : A <~> Unit) : Contr A | 10000
  := BuildContr A (f^-1 tt)
  (fun a => ap f^-1 (contr (f a)) @ eissect f a).

End Unit.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Unit.

Module HoTT_DOT_Trunc.
Module HoTT.
Module Trunc.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*-  *)
(** * Truncatedness *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_Contractible.HoTT.Contractible HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_types_DOT_Paths.HoTT.types.Paths HoTT_DOT_types_DOT_Unit.HoTT.types.Unit.
Local Open Scope equiv_scope.
Local Open Scope trunc_scope.

Generalizable Variables A B m n f.

(** ** Arithmetic on truncation-levels. *)
Fixpoint trunc_index_add (m n : trunc_index) : trunc_index
  := match m with
       | minus_two => n
       | trunc_S m' => trunc_S (trunc_index_add m' n)
     end.

Notation "m -2+ n" := (trunc_index_add m n) (at level 50, left associativity) : trunc_scope.

Fixpoint trunc_index_leq (m n : trunc_index) : Type
  := match m, n with
       | minus_two, _ => Unit
       | trunc_S m', minus_two => Empty
       | trunc_S m', trunc_S n' => trunc_index_leq m' n'
     end.

Notation "m <= n" := (trunc_index_leq m n) (at level 70, no associativity) : trunc_scope.

(** ** Truncatedness proper. *)

(** A contractible space is (-2)-truncated, by definition. *)
Definition contr_trunc_minus_two `{H : IsTrunc minus_two A} : Contr A
  := H.

(** Truncation levels are cumulative. *)
Instance trunc_succ `{IsTrunc n A} : IsTrunc (trunc_S n) A | 1000.
Proof.
  generalize dependent A.
  induction n as [| n I]; simpl; intros A H x y.
  - apply contr_paths_contr.
  - apply I, H.
Qed.

Instance trunc_leq {m n} (Hmn : m <= n) `{IsTrunc m A} : IsTrunc n A | 1000.
Proof.
  generalize dependent A; generalize dependent m.
  induction n as [ | n' IH];
    intros [ | m'] Hmn A ? .
  - (* -2, -2 *) assumption.
  - (* S m', -2 *) destruct Hmn.
  - (* -2, S n' *) apply @trunc_succ, (IH minus_two); auto.
  - (* S m', S n' *) intros x y; apply (IH m');
                     auto with typeclass_instances.
Qed.

(** Equivalence preserves truncation (this is, of course, trivial with univalence).
   This is not an [Instance] because it causes infinite loops.
   *)
Definition trunc_equiv `(f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent f; revert B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B f ?.
  - refine (contr_equiv f).
  - intros x y.
    pose proof (fun X Y => I (f^-1 x = f^-1 y) X (x = y) ((ap (f^-1))^-1) Y).
    clear I.
    typeclasses eauto.
Qed.

Definition trunc_equiv' `(f : A <~> B) `{IsTrunc n A}
  : IsTrunc n B
  := trunc_equiv f.

End Trunc.

End HoTT.

End HoTT_DOT_Trunc.

Module HoTT_DOT_types_DOT_Forall.
Module HoTT.
Module types.
Module Forall.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about dependent products *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_PathGroupoids.HoTT.PathGroupoids HoTT_DOT_Contractible.HoTT.Contractible HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_Trunc.HoTT.Trunc.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.Paths.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f g e n.

Section AssumeFunext.
Context `{Funext}.

(** ** Paths *)

(** Paths [p : f = g] in a function type [forall x:X, P x] are equivalent to functions taking values in path types, [H : forall x:X, f x = g x], or concisely, [H : f == g].

This equivalence, however, is just the combination of [apD10] and function extensionality [funext], and as such, [path_forall], et seq. are given in the [Overture]:  *)

(** Now we show how these things compute. *)

Definition apD10_path_forall `{P : A -> Type}
  (f g : forall x, P x) (h : f == g)
  : apD10 (path_forall _ _ h) == h
  := apD10 (eisretr apD10 h).

Definition eta_path_forall `{P : A -> Type}
  (f g : forall x, P x) (p : f = g)
  : path_forall _ _ (apD10 p) = p
  := eissect apD10 p.

Definition path_forall_1 `{P : A -> Type} (f : forall x, P x)
  : (path_forall f f (fun x => 1)) = 1
  := eta_path_forall f f 1.

(** The identification of the path space of a dependent function space, up to equivalence, is of course just funext. *)

Global Instance isequiv_path_forall `{P : A -> Type} (f g : forall x, P x)
  : IsEquiv (path_forall f g) | 0
  := @isequiv_inverse _ _ (@apD10 A P f g) _.

Definition equiv_path_forall `{P : A -> Type} (f g : forall x, P x)
  : (f == g)  <~>  (f = g)
  := BuildEquiv _ _ (path_forall f g) _.

(** ** Transport *)

(** The concrete description of transport in sigmas and pis is rather trickier than in the other types. In particular, these cannot be described just in terms of transport in simpler types; they require the full Id-elim rule by way of "dependent transport" [transportD].

  In particular this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory). A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)
Definition transport_forall
  {A : Type} {P : A -> Type} {C : forall x, P x -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y)
  : (transport (fun x => forall y : P x, C x y) p f)
    == (fun y =>
       transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (p^ # y))))
  := match p with idpath => fun _ => 1 end.

(** A special case of [transport_forall] where the type [P] does not depend on [A],
    and so it is just a fixed type [B]. *)
Definition transport_forall_constant
  {A B : Type} {C : A -> B -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B, C x1 y)
  : (transport (fun x => forall y : B, C x y) p f)
    == (fun y => transport (fun x => C x y) p (f y))
  := match p with idpath => fun _ => 1 end.

(** ** Maps on paths *)

(** The action of maps given by lambda. *)
Definition ap_lambdaD {A B : Type} {C : B -> Type} {x y : A} (p : x = y) (M : forall a b, C b) :
  ap (fun a b => M a b) p =
  path_forall _ _ (fun b => ap (fun a => M a b) p).
Proof.
  destruct p;
  symmetry;
  simpl; apply path_forall_1.
Defined.

(** ** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a function space, these dependent paths have a more convenient description: rather than transporting the argument of [y1] forwards and backwards, we transport only forwards but on both sides of the equation, yielding a "naturality square". *)

Definition dpath_forall `{Funext}
  {A:Type} (B:A -> Type) (C:forall a, B a -> Type) (x1 x2:A) (p:x1=x2)
  (f:forall y1:B x1, C x1 y1) (g:forall (y2:B x2), C x2 y2)
  : (forall (y1:B x1), transportD B C p y1 (f y1) = g (transport B p y1))
  <~>
  (transport (fun x => forall y:B x, C x y) p f = g).
Proof.
  destruct p.
  apply equiv_path_forall.
Defined.

(** ** Functorial action *)

(** The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. *)
Definition functor_forall `{P : A -> Type} `{Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b)
  := (fun g b => f1 _ (g (f0 b))).

Definition ap_functor_forall `{P : A -> Type} `{Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
    (g g' : forall a:A, P a) (h : g == g')
  : ap (functor_forall f0 f1) (path_forall _ _ h)
    = path_forall _ _ (fun b:B => (ap (f1 b) (h (f0 b)))).
Proof.
  revert h.  equiv_intro (@apD10 A P g g') h.
  destruct h.  simpl.
  path_via (idpath (functor_forall f0 f1 g)).
  - exact (ap (ap (functor_forall f0 f1)) (path_forall_1 g)).
  - symmetry.  apply path_forall_1.
Defined.

(** ** Equivalences *)

Global Instance isequiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv B A f} `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : IsEquiv (functor_forall f g) | 1000.
Proof.
  refine (isequiv_adjointify (functor_forall f g)
    (functor_forall (f^-1)
      (fun (x:A) (y:Q (f^-1 x)) => eisretr f x # (g (f^-1 x))^-1 y
      )) _ _);
  intros h.
  - abstract (
        apply path_forall; intros b; unfold functor_forall;
        rewrite eisadj;
        rewrite <- transport_compose;
        rewrite ap_transport;
        rewrite eisretr;
        apply apD
      ).
  - abstract (
        apply path_forall; intros a; unfold functor_forall;
        rewrite eissect;
        apply apD
      ).
Defined.

Definition equiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
  (f : B -> A) `{IsEquiv B A f}
  (g : forall b, P (f b) -> Q b)
  `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : (forall a, P a) <~> (forall b, Q b)
  := BuildEquiv _ _ (functor_forall f g) _.

Definition equiv_functor_forall' `{P : A -> Type} `{Q : B -> Type}
  (f : B <~> A) (g : forall b, P (f b) <~> Q b)
  : (forall a, P a) <~> (forall b, Q b)
  := equiv_functor_forall f g.

Definition equiv_functor_forall_id `{P : A -> Type} `{Q : A -> Type}
  (g : forall a, P a <~> Q a)
  : (forall a, P a) <~> (forall a, Q a)
  := equiv_functor_forall (equiv_idmap A) g.

(** ** Truncatedness: any dependent product of n-types is an n-type *)

Global Instance contr_forall `{P : A -> Type} `{forall a, Contr (P a)}
  : Contr (forall a, P a) | 100.
Proof.
  exists (fun a => center (P a)).
  intro f.  apply path_forall.  intro a.  apply contr.
Defined.

Global Instance trunc_forall `{P : A -> Type} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (forall a, P a) | 100.
Proof.
  generalize dependent P.
  induction n as [ | n' IH]; simpl; intros P ?.
  (* case [n = -2], i.e. contractibility *)
  - exact _.
  (* case n = trunc_S n' *)
  - intros f g; apply (trunc_equiv (apD10 ^-1)).
Defined.


(** ** Symmetry of curried arguments *)

(** Using the standard Haskell name for this, as it’s a handy utility function.

Note: not sure if [P] will usually be deducible, or whether it would be better explicit. *)
Definition flip `{P : A -> B -> Type}
  : (forall a b, P a b) -> (forall b a, P a b)
  := fun f b a => f a b.

Global Instance isequiv_flip `{P : A -> B -> Type}
  : IsEquiv (@flip _ _ P) | 0.
Proof.
  set (flip_P := @flip _ _ P).
  set (flip_P_inv := @flip _ _ (flip P)).
  set (flip_P_is_sect := (fun f => 1) : Sect flip_P flip_P_inv).
  set (flip_P_is_retr := (fun g => 1) : Sect flip_P_inv flip_P).
  exists flip_P_inv flip_P_is_retr flip_P_is_sect.
  intro g.  exact 1.
Defined.

Definition equiv_flip `(P : A -> B -> Type)
  : (forall a b, P a b) <~> (forall b a, P a b)
  := BuildEquiv _ _ (@flip _ _ P) _.

End AssumeFunext.

End Forall.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Forall.

Module HoTT_DOT_types_DOT_Prod.
Module HoTT.
Module types.
Module Prod.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about cartesian products *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_PathGroupoids.HoTT.PathGroupoids HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_Trunc.HoTT.Trunc.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(** ** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : A * B] by writing [u] as a pair [(fst u ; snd u)]. This is accomplished by [unpack_prod]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_prod `{P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u
  :=
  let (x, y) as u return (P (fst u, snd u) -> P u) := u in idmap.

(** Now we write down the reverse. *)
Definition pack_prod `{P : A * B -> Type} (u : A * B) :
  P u -> P (fst u, snd u)
  :=
  let (x, y) as u return (P u -> P (fst u, snd u)) := u in idmap.

(** ** Eta conversion *)

Definition eta_prod `(z : A * B) : (fst z, snd z) = z
  := match z with (x,y) => 1 end.

(** ** Paths *)

(** With this version of the function, we often have to give [z] and [z'] explicitly, so we make them explicit arguments. *)
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

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).

(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of product types.  But it has the advantage that the components of those pairs can more often be inferred. *)
Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (x,y) (x',y') p q.

(** Now we show how these things compute. *)

Definition ap_fst_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap fst (path_prod _ _ p q) = p.
Proof.
  revert p q; destruct z, z'; simpl; intros [] []; reflexivity.
Defined.

Definition ap_snd_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap snd (path_prod _ _ p q) = q.
Proof.
  revert p q; destruct z, z'; simpl; intros [] []; reflexivity.
Defined.

Definition eta_path_prod {A B : Type} {z z' : A * B} (p : z = z') :
  path_prod _ _(ap fst p) (ap snd p) = p.
Proof.
  destruct p. destruct z. reflexivity.
Defined.

(** Now we show how these compute with transport. *)

Lemma transport_path_prod_uncurried A B (P : A * B -> Type) (x y : A * B)
      (H : (fst x = fst y) * (snd x = snd y))
      Px
: transport P (path_prod_uncurried _ _ H) Px
  = unpack_prod
      y
      (transport (fun x => P (x, snd y))
                 (fst H)
                 (transport (fun y => P (fst x, y))
                            (snd H)
                            (pack_prod x Px))).
Proof.
  destruct x, y, H; simpl in *.
  path_induction.
  reflexivity.
Defined.

Definition transport_path_prod A B (P : A * B -> Type) (x y : A * B)
           (HA : fst x = fst y)
           (HB : snd x = snd y)
           Px
: transport P (path_prod _ _ HA HB) Px
  = unpack_prod
      y
      (transport (fun x => P (x, snd y))
                 HA
                 (transport (fun y => P (fst x, y))
                            HB
                            (pack_prod x Px)))
  := transport_path_prod_uncurried _ _ P x y (HA, HB) Px.

Definition transport_path_prod'
           A B (P : A * B -> Type)
           (x y : A)
           (x' y' : B)
           (HA : x = y)
           (HB : x' = y')
           Px
: transport P (path_prod' HA HB) Px
  = transport (fun x => P (x, y'))
              HA
              (transport (fun y => P (x, y))
                         HB
                         Px)
  := transport_path_prod _ _ P (x, x') (y, y') HA HB Px.

(** This lets us identify the path space of a product type, up to equivalence. *)

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
  : IsEquiv (path_prod_uncurried z z') | 0.
  refine (BuildIsEquiv _ _ _
    (fun r => (ap fst r, ap snd r))
    eta_path_prod
    (fun pq => match pq with
                 | (p,q) => path_prod'
                   (ap_fst_path_prod p q) (ap_snd_path_prod p q)
               end) _).
  destruct z as [x y], z' as [x' y'].
  intros [p q]; simpl in p, q.
  destruct p, q; reflexivity.
Defined.

Definition equiv_path_prod {A B : Type} (z z' : A * B)
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z')
  := BuildEquiv _ _ (path_prod_uncurried z z') _.

(** ** Transport *)

Definition transport_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport (fun a => P a * Q a) p z  =  (p # (fst z), p # (snd z))
  := match p with idpath => match z with (x,y) => 1 end end.

(** ** Functorial action *)

Definition functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  : A * B -> A' * B'
  := fun z => (f (fst z), g (snd z)).

Definition ap_functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  (z z' : A * B) (p : fst z = fst z') (q : snd z = snd z')
  : ap (functor_prod f g) (path_prod _ _ p q)
  = path_prod (functor_prod f g z) (functor_prod f g z') (ap f p) (ap g q).
Proof.
  destruct z as [a b]; destruct z' as [a' b'].
  simpl in p, q. destruct p, q. reflexivity.
Defined.

(** ** Equivalences *)

Instance isequiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : IsEquiv (functor_prod f g) | 1000.
  refine (BuildIsEquiv _ _ (functor_prod f g) (functor_prod f^-1 g^-1)
    (fun z => path_prod' (eisretr f (fst z)) (eisretr g (snd z)) @ eta_prod z)
    (fun w => path_prod' (eissect f (fst w)) (eissect g (snd w)) @ eta_prod w)
    _).
  intros [a b]; simpl.
  unfold path_prod'.
  repeat rewrite concat_p1.
  rewrite ap_functor_prod.
  repeat rewrite eisadj.
  reflexivity.
Defined.

Definition equiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _.    (* i.e., search the context for instances *)
Defined.

Definition equiv_functor_prod' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _.    (* i.e., search the context for instances *)
Defined.

Definition equiv_functor_prod_l {A B B' : Type} (g : B <~> B')
  : A * B <~> A * B'.
Proof.
  exists (functor_prod idmap g).
  exact _.    (* i.e., search the context for instances *)
Defined.

Definition equiv_functor_prod_r {A A' B : Type} (f : A <~> A')
  : A * B <~> A' * B.
Proof.
  exists (functor_prod f idmap).
  exact _.    (* i.e., search the context for instances *)
Defined.

(** ** Symmetry *)

(* This is a special property of [prod], of course, not an instance of a general family of facts about types. *)

Definition equiv_prod_symm (A B : Type) : A * B <~> B * A.
Proof.
  refine (BuildEquiv (A*B) (B*A)
    (fun ab => let (a,b) := ab in (b,a))
    (BuildIsEquiv (A*B) (B*A) _
      (fun ba => let (b,a) := ba in (a,b))
      (fun ba => let (b,a) as ba return
            ((let (a,b) := (let (b,a) := ba in (a,b)) in (b,a)) = ba)
                 := ba in 1)
    (fun ab => let (a,b) as ab return
            ((let (b,a) := (let (a,b) := ab in (b,a)) in (a,b)) = ab)
                 := ab in 1)
    _)).
  intros [a b]. reflexivity.
Defined.

(** ** Universal mapping properties *)

(** Ordinary universal mapping properties are expressed as equivalences of sets or spaces of functions.  In type theory, we can go beyond this and express an equivalence of types of *dependent* functions.  Moreover, because the product type can expressed both positively and negatively, it has both a left universal property and a right one. *)

(* First the positive universal property.
   Doing this sort of thing without adjointifying will require very careful use of funext. *)
Instance isequiv_prod_rect `{Funext} `(P : A * B -> Type)
  : IsEquiv (prod_rect P) | 0
  := isequiv_adjointify _
  (fun f x y => f (x,y))
  (fun f => path_forall
    (fun z => prod_rect P (fun x y => f (x,y)) z)
    f (fun z => match z with (a,b) => 1 end))
  (fun f => path_forall2
    (fun x y => prod_rect P f (x,y))
    f (fun a b => 1)).

Definition equiv_prod_rect `{Funext} `(P : A * B -> Type)
  : (forall (a : A) (b : B), P (a, b)) <~> (forall p : A * B, P p)
  := BuildEquiv _ _ (prod_rect P) _.

(* The non-dependent version, which is a special case, is the currying equivalence. *)
Definition equiv_uncurry `{Funext} (A B C : Type)
  : (A -> B -> C) <~> (A * B -> C)
  := equiv_prod_rect (fun _ => C).

(* Now the negative universal property. *)
Definition prod_corect_uncurried `{A : X -> Type} `{B : X -> Type}
  : (forall x, A x) * (forall x, B x) -> (forall x, A x * B x)
  := fun fg x => let (f,g):=fg in (f x, g x).

Definition prod_corect `(f : forall x:X, A x) `(g : forall x:X, B x)
  : forall x, A x * B x
  := prod_corect_uncurried (f,g).

Instance isequiv_prod_corect `{Funext} `(A : X -> Type) (B : X -> Type)
  : IsEquiv (@prod_corect_uncurried X A B) | 0
  := isequiv_adjointify _
  (fun h => (fun x => fst (h x), fun x => snd (h x)))
  _ _.
Proof.
  - intros h.
    apply path_forall; intros x.
    apply path_prod; simpl; reflexivity.
  - intros [f g].
    apply path_prod; simpl; reflexivity.
Defined.

Definition equiv_prod_corect `{Funext} `(A : X -> Type) (B : X -> Type)
  : ((forall x, A x) * (forall x, B x)) <~> (forall x, A x * B x)
  := BuildEquiv _ _ (@prod_corect_uncurried X A B) _.

(** ** Products preserve truncation *)

Instance trunc_prod `{IsTrunc n A} `{IsTrunc n B} : IsTrunc n (A * B) | 100.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B ?.
  exists (center A, center B).
    intros z; apply path_prod; apply contr.
  intros x y.
    exact (trunc_equiv (equiv_path_prod x y)).
Defined.

Instance contr_prod `{CA : Contr A} `{CB : Contr B} : Contr (A * B) | 100
  := @trunc_prod minus_two A CA B CB.

End Prod.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Prod.

Module HoTT_DOT_Tactics.
Module HoTT.
Module Tactics.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*-  *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_types_DOT_Prod.HoTT.types.Prod HoTT_DOT_types_DOT_Forall.HoTT.types.Forall HoTT_DOT_PathGroupoids.HoTT.PathGroupoids HoTT_DOT_Contractible.HoTT.Contractible HoTT_DOT_types_DOT_Paths.HoTT.types.Paths.

Set Implicit Arguments.

(** * Extra tactics for homotopy type theory. *)

(** ** Tactics for dealing with [Funext] *)
(** *** Tactics about [transport]ing with [path_forall] *)

(** Given using the variable names from [transport : forall {A : Type} (P : A -> Type) {x y : A}, x = y -> P x -> P y] and [path_forall : {Funext} -> forall {A B} (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g]:

The high-level idea is that we don't really need functional extensionality if we end up just applying the functions to arguments anyway.  That is, if we have that [forall x, f x = g x], and we only talk about [f y] and [f z], then we don't actually need to transport across [f = g], just [f y = g y] and [f z = g z].

In a bit more detail, if we are transporting across [path_forall f g H], and in the function [P], all instances of [f] are applied to some expressions, say we only see [f x], [f y], ..., [f z], then we can eliminate the [path_forall] by explicitly transporting across [H x], [H y], ..., [H z].  The lemma [path_forall_1_beta] expresses this fact in the case that we see [f] applied to only a single argument in [P], and the tactic [transport_path_forall_hammer] is some fancy Ltac to auto-infer what [P] is and what the argument to [f] is.

The way the tactic does this is by creating an evar for [P] and an evar for the argument to [f], and then using a combination of [assert], [pattern], etc to figure out what each should be.  If you want to see how it works, you can step through each step of [transport_path_forall_hammer] when trying to prove [path_forall_2_beta]. *)

(** First, we prove some helpful lemmas about [path_forall] and [transport] *)
Local Ltac path_forall_beta_t :=
  lazymatch goal with
    | [ |- appcontext[@path_forall ?H ?A ?B ?f ?g ?e] ]
      => let X := fresh in
         pose proof (eissect (@path_forall H A B f g) e) as X;
           case X;
           generalize (@path_forall H A B f g e);
           clear X; clear e;
           intro X; destruct X;
           simpl;
           unfold apD10;
           rewrite !(path_forall_1 f)
  end;
  reflexivity.

(** The basic idea is expressed in the type of this lemma. *)
Lemma path_forall_1_beta `{Funext} A B x P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x)) f g (@path_forall _ _ _ _ _ e) Px
  = @transport (B x) P (f x) (g x) (e x) Px.
Proof.
  path_forall_beta_t.
Defined.

(** The powerful recursive case *)
Lemma path_forall_recr_beta' `{Funext} A B x0 P f g e Px
: @transport (forall a : A, B a)
             (fun f => P f (f x0))
             f
             g
             (@path_forall _ _ _ _ _ e)
             Px
  = @transport ((forall a, B a) * B x0)%type
               (fun x => P (fst x) (snd x))
               (f, f x0)
               (g, g x0)
               (path_prod' (@path_forall _ _ _ _ _ e) (e x0))
               Px.
Proof.
  path_forall_beta_t.
Defined.

(** Two lemmas about [transport]ing across [path_prod'], used for cleanup *)
Definition transport_path_prod'_beta A B P (x x' : A) (y y' : B) (HA : x = x') (HB : y = y') (Px : P (x, y))
: @transport (A * B) P (x, y) (x', y') (@path_prod' A B x x' y y' HA HB) Px
  = @transport A (fun x => P (x, y')) x x' HA
               (@transport B (fun y => P (x, y)) y y' HB Px).
Proof.
  path_induction.
  reflexivity.
Defined.

Definition transport_path_prod'_beta' A B P (x x' : A) (y y' : B) (HA : x = x') (HB : y = y') (Px : P x y)
: @transport (A * B) (fun xy => P (fst xy) (snd xy)) (x, y) (x', y') (@path_prod' A B x x' y y' HA HB) Px
  = @transport A (fun x => P x y') x x' HA
               (@transport B (fun y => P x y) y y' HB Px).
Proof.
  path_induction.
  reflexivity.
Defined.

(** Rewrite the recursive case after clean-up *)
Lemma path_forall_recr_beta `{Funext} A B x0 P f g e Px
: @transport (forall a : A, B a)
             (fun f => P f (f x0))
             f
             g
             (@path_forall _ _ _ _ _ e)
             Px
  = @transport (forall x : A, B x)
               (fun x => P x (g x0))
               f
               g
               (@path_forall H A B f g e)
               (@transport (B x0)
                           (fun y => P f y)
                           (f x0)
                           (g x0)
                           (e x0)
                           Px).
Proof.
  etransitivity.
  - apply path_forall_recr_beta'.
  - apply transport_path_prod'_beta'.
Defined.


(** The sledge-hammer for computing with [transport]ing across a [path_forall].  Note that it uses [rewrite], and so should only be used in opaque proofs. *)

(** We separate the inference part and the rewrite part to avoid 'Anomaly: Uncaught exception Invalid_argument("to_constraints: non-trivial algebraic constraint between universes", _).
Please report.' on rewrite *)

Ltac transport_path_forall_hammer_helper :=
  (* pull out the parts of the goal to use [path_forall_recr_beta] *)
  let F := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(F) end in
  let H := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(H) end in
  let X := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(X) end in
  let T := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(T) end in
  let t0 := fresh "t0" in
  let t1 := fresh "t1" in
  let T1 := lazymatch type of F with (?T -> _) -> _ => constr:(T) end in
      evar (t1 : T1);
    let T0 := lazymatch type of F with (forall a : ?A, @?B a) -> ?C => constr:((forall a : A, B a) -> B t1 -> C) end in
        evar (t0 : T0);
      (* make a dummy goal to figure out the functional form of [P] in [@transport _ P] *)
      let dummy := fresh in
      assert (dummy : forall x0, F x0 = t0 x0 (x0 t1));
        [ let x0 := fresh in
          intro x0;
            simpl in *;
            let GL0 := lazymatch goal with |- ?GL0 = _ => constr:(GL0) end in
                let GL0' := fresh in
                let GL1' := fresh in
                set (GL0' := GL0);
                  (* find [x0] applied to some argument, and note the argument *)
                  let arg := match GL0 with appcontext[x0 ?arg] => constr:(arg) end in
                  assert (t1 = arg) by (subst t1; reflexivity); subst t1;
                  pattern (x0 arg) in GL0';
                  match goal with
                    | [ GL0'' := ?GR _ |- _ ] => constr_eq GL0' GL0'';
                                                pose GR as GL1'
                  end;
                  (* remove the other instances of [x0], and figure out the shape *)
                  pattern x0 in GL1';
                  match goal with
                    | [ GL1'' := ?GR _ |- _ ] => constr_eq GL1' GL1'';
                                                assert (t0 = GR)
                  end;
                  subst t0; [ reflexivity | reflexivity ]
              | clear dummy ];
        let p := fresh in
        pose (@path_forall_recr_beta H X T t1 t0) as p;
          simpl in *;
          rewrite p;
          subst t0 t1 p.

Ltac transport_path_forall_hammer :=
  progress
    repeat (
      transport_path_forall_hammer_helper;
      cbv beta;
      rewrite ?transport_const
    ).

(** An example showing that it works *)
Lemma path_forall_2_beta' `{Funext} A B x0 x1 P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x0) (f x1)) f g (@path_forall _ _ _ _ _ e) Px
  = @transport (B x0 * B x1)%type (fun x => P (fst x) (snd x)) (f x0, f x1) (g x0, g x1) (path_prod' (e x0) (e x1)) Px.
Proof.
  transport_path_forall_hammer.
  repeat match goal with
           | [ |- appcontext[e ?x] ] => induction (e x)
         end;
    simpl.
  reflexivity.
Qed.

Lemma path_forall_2_beta `{Funext} A B x0 x1 P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x0) (f x1)) f g (@path_forall _ _ _ _ _ e) Px
  = transport (fun y : B x1 => P (g x0) y) (e x1)
     (transport (fun y : B x0 => P y (f x1)) (e x0) Px).
Proof.
  transport_path_forall_hammer.
  reflexivity.
Qed.

(** ** A more powerful variant of [path_induction] *)
(** We first define some helper tactics, and then define [path_induction_hammer], which has poor computational behavior, but is vastly more powerful than [path_induction], and removes paths which are discoverably contractible, and paths which only appear in the goal, etc. *)

(** A variant of [induction] which also tries [destruct] and [case], and may be extended to using other [destruct]-like tactics. *)
Ltac induction_hammer H :=
  destruct H || induction H || (case H; clear H).

(** Takes a term of type [_ = _], and tries to replace it by [idpath] by trying to prove that it's an hProp.  The ordering of attempts is tuned for speed. *)
Ltac clear_contr_path p :=
  let H := fresh in
  let T := type of p in
  progress (
      first [ assert (H : idpath = p) by exact (center _)
            | assert (H : idpath = p)
              by (
                  let a := match goal with |- @paths (?x = ?y) ?a ?b => constr:(a) end in
                  let b := match goal with |- @paths (?x = ?y) ?a ?b => constr:(b) end in
                  let x := match goal with |- @paths (?x = ?y) ?a ?b => constr:(x) end in
                  let y := match goal with |- @paths (?x = ?y) ?a ?b => constr:(y) end in
                  apply (@equiv_inv _ _ _ (@equiv_ap _ _ _ (@isequiv_apD10 _ _ _ x y) a b));
                  exact (center _)
                )
            | pose proof (@path_contr T _ idpath p) as H ];
      destruct H;
      (* now reduce any matches on [idpath] (and on other things too) *)
      cbv iota in *
    ).

(** Use both [induction_hammer] and [clear_contr_path] on a path, to try to get rid of it *)
Ltac clear_path_no_check p :=
  induction_hammer p || clear_contr_path p.
Ltac clear_path p :=
  let t := type of p in
  lazymatch eval hnf in t with
    | @paths _ _ _ => clear_path_no_check p || fail 1 "cannot clear path" p
    | _ => fail 0 "clear_path only works on paths;" p "is not a path"
  end.

(** Run [clear_path] on hypotheses *)
(** We don't match only on things of type [_ = _], because maybe that's the head normal form, but it's hiding behind something else; [clear_path] will make sure it's of the right type.  We include some redundant cases at the top, for speed; it is faster to try to destruct everything first, and then do the full battery of tactics, than to just run the hammer. *)
Ltac step_clear_paths :=
  idtac;
  match goal with
    | [ p : _ = _ |- _ ] => destruct p
    | [ p : _ = _ |- _ ] => clear_path_no_check p
    | [ p : _ |- _ ] => clear_path p
  end.
Ltac clear_paths := progress repeat step_clear_paths.

(** Run [clear_path] on anything inside a [match] *)
Ltac step_clear_paths_in_match :=
  idtac;
  match goal with
    | [ |- appcontext[match ?p with idpath => _ end] ] => progress destruct p
    | [ |- appcontext[match ?p with idpath => _ end] ] => clear_path_no_check p
  end.
Ltac clear_paths_in_match := progress repeat step_clear_paths_in_match.

(** Now some lemmas about trivial [match]es *)
Definition match_eta T (x y : T) (H0 : x = y)
: (H0 = match H0 in (_ = y) return (x = y) with
          | idpath => idpath
        end)
  := match H0 with idpath => idpath end.

Definition match_eta1 T (x : T) (E : x = x)
: (match E in (_ = y) return (x = y) with
     | idpath => idpath
   end = idpath)
  -> idpath = E
  := fun H => ((H # match_eta E) ^)%path.

Definition match_eta2 T (x : T) (E : x = x)
: (idpath
   = match E in (_ = y) return (x = y) with
       | idpath => idpath
     end)
  -> idpath = E
  := fun H => match_eta1 E (H ^)%path.

(** And now the actual tactic.  Note that the order of the cases in the [match goal with ... end] is somewhat finely tuned for speed. *)
Ltac step_path_induction_hammer :=
  idtac;
  match goal with
    | _ => reflexivity
    | _ => intro
    | _ => progress simpl in *
    | _ => exact (contr _)
    | [ p : _ = _ |- _ ]
      => progress destruct p (* placed up here for speed *)
    | [ H : _ |- _ ]
      => let H' := fresh in assert (H' := match_eta1 _ H); destruct H'
    | [ H : _ |- _ ]
      => let H' := fresh in assert (H' := match_eta2 _ H); destruct H'
    | _ => step_clear_paths
    | _ => expand; step_clear_paths_in_match
    | _ => progress auto with path_hints
    | _ => done
    | _ => exact (center _)
  end.

Ltac path_induction_hammer := progress repeat step_path_induction_hammer.

(** * Miscellaneous tactics *)

(** Substitute all hypotheses with bodies, i.e., of the form [H := _]. *)
Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.

(** Some tactics to do things with some arbitrary hypothesis in the context.  These tactics are similar to, e.g., [assumption]. *)

Ltac do_with_hyp tac :=
  idtac;
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

Ltac apply_hyp' := do_with_hyp ltac:(fun H => apply H).
Ltac apply_hyp := repeat apply_hyp'.
Ltac eapply_hyp' := do_with_hyp ltac:(fun H => eapply H).
Ltac eapply_hyp := repeat eapply_hyp'.

(** Run [simpl] on a hypothesis before rewriting with it. *)
Ltac simpl_do_clear tac term :=
  let H := fresh in
  assert (H := term);
    simpl in H |- *;
    tac H;
    clear H.

Tactic Notation "simpl" "rewrite"      constr(term) := simpl_do_clear ltac:(fun H => rewrite    H) term.
Tactic Notation "simpl" "rewrite" "->" constr(term) := simpl_do_clear ltac:(fun H => rewrite -> H) term.
Tactic Notation "simpl" "rewrite" "<-" constr(term) := simpl_do_clear ltac:(fun H => rewrite <- H) term.

Tactic Notation "simpl" "rewrite"      constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite    H in hyp) term.
Tactic Notation "simpl" "rewrite" "->" constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite -> H in hyp) term.
Tactic Notation "simpl" "rewrite" "<-" constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite <- H in hyp) term.

Tactic Notation "simpl" "rewrite"      constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite    H in * ) term.
Tactic Notation "simpl" "rewrite" "->" constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite -> H in * ) term.
Tactic Notation "simpl" "rewrite" "<-" constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite <- H in * ) term.

Tactic Notation "simpl" "rewrite"      constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite    H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "->" constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite -> H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "<-" constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite <- H in hyp |- * ) term.

Tactic Notation "simpl" "rewrite"      constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite    H in * |- ) term.
Tactic Notation "simpl" "rewrite" "->" constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite -> H in * |- ) term.
Tactic Notation "simpl" "rewrite" "<-" constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite <- H in * |- ) term.


Tactic Notation "simpl" "rewrite"      "!" constr(term) := simpl_do_clear ltac:(fun H => rewrite    !H) term.
Tactic Notation "simpl" "rewrite" "->" "!" constr(term) := simpl_do_clear ltac:(fun H => rewrite -> !H) term.
Tactic Notation "simpl" "rewrite" "<-" "!" constr(term) := simpl_do_clear ltac:(fun H => rewrite <- !H) term.

Tactic Notation "simpl" "rewrite"      "!" constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite    !H in hyp) term.
Tactic Notation "simpl" "rewrite" "->" "!" constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite -> !H in hyp) term.
Tactic Notation "simpl" "rewrite" "<-" "!" constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite <- !H in hyp) term.

Tactic Notation "simpl" "rewrite"      "!" constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite    !H in * ) term.
Tactic Notation "simpl" "rewrite" "->" "!" constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite -> !H in * ) term.
Tactic Notation "simpl" "rewrite" "<-" "!" constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite <- !H in * ) term.

Tactic Notation "simpl" "rewrite"      "!" constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite    !H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "->" "!" constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite -> !H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "<-" "!" constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite <- !H in hyp |- * ) term.

Tactic Notation "simpl" "rewrite"      "!" constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite    !H in * |- ) term.
Tactic Notation "simpl" "rewrite" "->" "!" constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite -> !H in * |- ) term.
Tactic Notation "simpl" "rewrite" "<-" "!" constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite <- !H in * |- ) term.


Tactic Notation "simpl" "rewrite"      "?" constr(term) := simpl_do_clear ltac:(fun H => rewrite    ?H) term.
Tactic Notation "simpl" "rewrite" "->" "?" constr(term) := simpl_do_clear ltac:(fun H => rewrite -> ?H) term.
Tactic Notation "simpl" "rewrite" "<-" "?" constr(term) := simpl_do_clear ltac:(fun H => rewrite <- ?H) term.

Tactic Notation "simpl" "rewrite"      "?" constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite    ?H in hyp) term.
Tactic Notation "simpl" "rewrite" "->" "?" constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite -> ?H in hyp) term.
Tactic Notation "simpl" "rewrite" "<-" "?" constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite <- ?H in hyp) term.

Tactic Notation "simpl" "rewrite"      "?" constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite    ?H in * ) term.
Tactic Notation "simpl" "rewrite" "->" "?" constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite -> ?H in * ) term.
Tactic Notation "simpl" "rewrite" "<-" "?" constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite <- ?H in * ) term.

Tactic Notation "simpl" "rewrite"      "?" constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite    ?H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "->" "?" constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite -> ?H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "<-" "?" constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite <- ?H in hyp |- * ) term.

Tactic Notation "simpl" "rewrite"      "?" constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite    ?H in * |- ) term.
Tactic Notation "simpl" "rewrite" "->" "?" constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite -> ?H in * |- ) term.
Tactic Notation "simpl" "rewrite" "<-" "?" constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite <- ?H in * |- ) term.

(** find the head of the given expression *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(* given a [matcher] that succeeds on some hypotheses and fails on
   others, destruct any matching hypotheses, and then execute [tac]
   after each [destruct].

   The [tac] part exists so that you can, e.g., [simpl in *], to
   speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in *).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(** matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

End Tactics.

End HoTT.

End HoTT_DOT_Tactics.

Module HoTT_DOT_categories_DOT_Category_DOT_Core.
Module HoTT.
Module categories.
Module Category.
Module Core.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Definition of a [PreCategory] *)
Export HoTT_DOT_Overture.HoTT.Overture.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Local Open Scope morphism_scope.

(** Quoting the HoTT Book: *)
(** Definition 9.1.1. A precategory [A] consists of the following.

    (i) A type [A₀] of objects. We write [a : A] for [a : A₀].

    (ii) For each [a, b : A], a set [hom_A(a, b)] of arrows or morphisms.

    (iii) For each [a : A], a morphism [1ₐ : hom_A(a, a)].

    (iv) For each [a, b, c : A], a function

         [hom_A(b, c) → hom_A(a, b) → hom_A(a, c)]

         denoted infix by [g ↦ f ↦ g ∘ f] , or sometimes simply by [g f].

    (v) For each [a, b : A] and [f : hom_A(a, b)], we have [f = 1_b ∘
        f] and [f = f ∘ 1ₐ].

    (vi) For each [a, b, c, d : A] and [f : hom_A(a, b)], [g :
         hom_A(b, c)], [h : hom_A(c,d)], we have [h ∘ (g ∘ f) = (h ∘
         g) ∘ f]. *)
(** In addition to these laws, we ask for a few redundant laws to give
    us more judgmental equalities.  For example, since [(p^)^ ≢ p] for
    paths [p], we ask for the symmetrized version of the associativity
    law, so we can swap them when we take the dual. *)

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
      (** Ask for the symmetrized version of [associativity], so that [(Cᵒᵖ)ᵒᵖ] and [C] are equal without [Funext] *)
      associativity_sym : forall x1 x2 x3 x4
                                 (m1 : morphism x1 x2)
                                 (m2 : morphism x2 x3)
                                 (m3 : morphism x3 x4),
                            m3 o (m2 o m1) = (m3 o m2) o m1;

      left_identity : forall a b (f : morphism a b), identity b o f = f;
      right_identity : forall a b (f : morphism a b), f o identity a = f;
      (** Ask for the double-identity version so that [InitialTerminalCategory.Functors.from_terminal Cᵒᵖ X] and [(InitialTerminalCategory.Functors.from_terminal C X)ᵒᵖ] are convertible. *)
      identity_identity : forall x, identity x o identity x = identity x;

      trunc_morphism : forall s d, IsHSet (morphism s d)
    }.

Bind Scope category_scope with PreCategory.
Bind Scope object_scope with object.
Bind Scope morphism_scope with morphism.

Arguments object C%category : rename.
Arguments morphism !C%category s d : rename.
Arguments identity [!C%category] x%object : rename.
Arguments compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Local Infix "o" := compose : morphism_scope.
(** Perhaps we should consider making this notation more global. *)
(** Perhaps we should pre-reserve all of the notations. *)
Local Notation "x --> y" := (@morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Local Notation "1" := (identity _) : morphism_scope.

(** Define a convenience wrapper for building a precategory without
    specifying the redundant proofs. *)
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

(** create a hint db for all category theory things *)
Create HintDb category discriminated.
(** create a hint db for morphisms in categories *)
Create HintDb morphism discriminated.

Hint Resolve @left_identity @right_identity @associativity : category morphism.
Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : morphism.

(** ** Simple laws about the identity morphism *)
Section identity_unique.
  Variable C : PreCategory.

  (** The identity morphism is unique. *)
  Lemma identity_unique (id0 id1 : forall x, morphism C x x)
        (id1_left : forall s d (m : morphism C s d), id1 _ o m = m)
        (id0_right : forall s d (m : morphism C s d), m o id0 _ = m)
  : id0 == id1.
  Proof.
    intro.
    etransitivity;
      [ symmetry; apply id1_left
      | apply id0_right ].
  Qed.

  (** Anything equal to the identity acts like it.  This is obvious,
      but useful as a helper lemma for automation. *)
  Definition concat_left_identity s d (m : morphism C s d) i
  : i = 1 -> i o m = m
    := fun H => (ap10 (ap _ H) _ @ left_identity _ _ _ m)%path.

  Definition concat_right_identity s d (m : morphism C s d) i
  : i = 1 -> m o i = m
    := fun H => (ap _ H @ right_identity _ _ _ m)%path.
End identity_unique.

(** Make a separate module for Notations, which can be exported/imported separately. *)
Module Export CategoryCoreNotations.
  Infix "o" := compose : morphism_scope.
  (** Perhaps we should consider making this notation more global. *)
  (** Perhaps we should pre-reserve all of the notations. *)
  Local Notation "x --> y" := (@morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Notation "1" := (identity _) : morphism_scope.
End CategoryCoreNotations.

(** We have a tactic for trying to run a tactic after associating morphisms either all the way to the left, or all the way to the right *)
Tactic Notation "try_associativity_quick" tactic(tac) :=
  first [ rewrite <- ?associativity; tac
        | rewrite -> ?associativity; tac ].

End Core.

End Category.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Category_DOT_Core.

Module HoTT_DOT_types_DOT_Empty.
Module HoTT.
Module types.
Module Empty.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the empty type *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_Contractible.HoTT.Contractible.
Local Open Scope path_scope.

(** ** Unpacking *)
(** ** Eta conversion *)
(** ** Paths *)
(** ** Transport *)
(** ** Functorial action *)
(** ** Equivalences *)
(** ** Universal mapping properties *)

(** We eta-expand [_] to [fun _ => _] to work around a bug in HoTT/coq: https://github.com/HoTT/coq/issues/117 *)
Instance contr_from_Empty {_ : Funext} (A : Type) :
  Contr (Empty -> A) :=
  BuildContr _
             (Empty_rect (fun _ => A))
             (fun f => path_forall _ f (fun x => Empty_rect (fun _ => _) x)).

(** ** Behavior with respect to truncation *)

Instance hprop_Empty : IsHProp Empty.
Proof. intro x. destruct x. Defined.

(** ** Paths *)

(** We could probably prove some theorems about non-existing paths in
   [Empty], but this is really quite useless. As soon as an element
   of [Empty] is hypothesized, we can prove whatever we like with
   a simple elimination. *)

End Empty.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Empty.

Module HoTT_DOT_types_DOT_Arrow.
Module HoTT.
Module types.
Module Arrow.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Non-dependent function types *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_PathGroupoids.HoTT.PathGroupoids HoTT_DOT_Contractible.HoTT.Contractible HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_Trunc.HoTT.Trunc.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.Paths HoTT_DOT_types_DOT_Forall.HoTT.types.Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B C D f g n.

Section AssumeFunext.
Context `{Funext}.

(** ** Paths *)

(** As for dependent functions, paths [p : f = g] in a function type [A -> B] are equivalent to functions taking values in path types, [H : forall x:A, f x = g x], or concisely [H : f == g].  These are all given in the [Overture], but we can give them separate names for clarity in the non-dependent case. *)

Definition path_arrow {A B : Type} (f g : A -> B)
  : (f == g) -> (f = g)
  := path_forall f g.

(** There are a number of combinations of dependent and non-dependent for [apD10_path_forall]; we list all of the combinations as helpful lemmas for rewriting. *)
Definition ap10_path_arrow {A B : Type} (f g : A -> B) (h : f == g)
  : ap10 (path_arrow f g h) == h
  := apD10_path_forall f g h.

Definition apD10_path_arrow {A B : Type} (f g : A -> B) (h : f == g)
  : apD10 (path_arrow f g h) == h
  := apD10_path_forall f g h.

Definition ap10_path_forall {A B : Type} (f g : A -> B) (h : f == g)
  : ap10 (path_forall f g h) == h
  := apD10_path_forall f g h.

Definition eta_path_arrow {A B : Type} (f g : A -> B) (p : f = g)
  : path_arrow f g (ap10 p) = p
  := eta_path_forall f g p.

Definition path_arrow_1 {A B : Type} (f : A -> B)
  : (path_arrow f f (fun x => 1)) = 1
  := eta_path_arrow f f 1.

Global Instance isequiv_path_arrow {A B : Type} (f g : A -> B)
  : IsEquiv (path_arrow f g) | 0
  := isequiv_path_forall f g.

Definition equiv_path_arrow {A B : Type} (f g : A -> B)
  : (f == g) <~> (f = g)
  := equiv_path_forall f g.

(** ** Transport *)

(** Transporting in non-dependent function types is somewhat simpler than in dependent ones. *)

Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2)
  : (transport (fun x => B x -> C x) p f) y  =  p # (f (p^ # y)).
Proof.
  destruct p; simpl; auto.
Defined.


(** ** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a function space, these dependent paths have a more convenient description: rather than transporting the argument of [y1] forwards and backwards, we transport only forwards but on both sides of the equation, yielding a "naturality square". *)

Definition dpath_arrow
  {A:Type} (B C : A -> Type) {x1 x2:A} (p:x1=x2)
  (f : B x1 -> C x1) (g : B x2 -> C x2)
  : (forall (y1:B x1), transport C p (f y1) = g (transport B p y1))
  <~>
  (transport (fun x => B x -> C x) p f = g).
Proof.
  destruct p.
  apply equiv_path_arrow.
Defined.

Definition ap10_dpath_arrow
  {A:Type} (B C : A -> Type) {x1 x2:A} (p:x1=x2)
  (f : B x1 -> C x1) (g : B x2 -> C x2)
  (h : forall (y1:B x1), transport C p (f y1) = g (transport B p y1))
  (u : B x1)
  : ap10 (dpath_arrow B C p f g h) (p # u)
  = transport_arrow p f (p # u)
  @ ap (fun x => p # (f x)) (transport_Vp B p u)
  @ h u.
Proof.
  destruct p; simpl; unfold ap10.
  exact (apD10_path_forall f g h u @ (concat_1p _)^).
Defined.

(** ** Maps on paths *)

(** The action of maps given by application. *)
Definition ap_apply_l {A B : Type} {x y : A -> B} (p : x = y) (z : A) :
  ap (fun f => f z) p = ap10 p z
:= 1.

Definition ap_apply_Fl {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) (z : B) :
  ap (fun a => (M a) z) p = ap10 (ap M p) z
:= match p with 1 => 1 end.

Definition ap_apply_Fr {A B C : Type} {x y : A} (p : x = y) (z : B -> C) (N : A -> B) :
  ap (fun a => z (N a)) p = ap01 z (ap N p)
:= (ap_compose N _ _).

Definition ap_apply_FlFr {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) (N : A -> B) :
  ap (fun a => (M a) (N a)) p = ap11 (ap M p) (ap N p)
:= match p with 1 => 1 end.

(** The action of maps given by lambda. *)
Definition ap_lambda {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) :
  ap (fun a b => M a b) p =
  path_arrow _ _ (fun b => ap (fun a => M a b) p).
Proof.
  destruct p;
  symmetry;
  simpl; apply path_arrow_1.
Defined.

(** ** Functorial action *)

Definition functor_arrow `(f : B -> A) `(g : C -> D)
  : (A -> C) -> (B -> D)
  := @functor_forall A (fun _ => C) B (fun _ => D) f (fun _ => g).

Definition ap_functor_arrow `(f : B -> A) `(g : C -> D)
  (h h' : A -> C) (p : h == h')
  : ap (functor_arrow f g) (path_arrow _ _ p)
  = path_arrow _ _ (fun b => ap g (p (f b)))
  := @ap_functor_forall _ A (fun _ => C) B (fun _ => D)
  f (fun _ => g) h h' p.

(** ** Truncatedness: functions into an n-type is an n-type *)

Global Instance contr_arrow {A B : Type} `{Contr B}
  : Contr (A -> B) | 100
:= contr_forall.

Global Instance trunc_arrow {A B : Type} `{IsTrunc n B}
  : IsTrunc n (A -> B) | 100
:= trunc_forall.

(** ** Equivalences *)

Global Instance isequiv_functor_arrow `{IsEquiv B A f} `{IsEquiv C D g}
  : IsEquiv (functor_arrow f g) | 1000
  := @isequiv_functor_forall _ A (fun _ => C) B (fun _ => D)
     _ _ _ _.

Definition equiv_functor_arrow `{IsEquiv B A f} `{IsEquiv C D g}
  : (A -> C) <~> (B -> D)
  := @equiv_functor_forall _ A (fun _ => C) B (fun _ => D)
  f _ (fun _ => g) _.

Definition equiv_functor_arrow' `(f : B <~> A) `(g : C <~> D)
  : (A -> C) <~> (B -> D)
  := @equiv_functor_forall' _ A (fun _ => C) B (fun _ => D)
  f (fun _ => g).

(** What remains is really identical to that in [Forall].  *)

End AssumeFunext.

End Arrow.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Arrow.

Module HoTT_DOT_types_DOT_Sigma.
Module HoTT.
Module types.
Module Sigma.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Sigma-types (dependent sums) *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_PathGroupoids.HoTT.PathGroupoids HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_Contractible.HoTT.Contractible HoTT_DOT_Trunc.HoTT.Trunc.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.Arrow.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables X A B C f g n.

(** In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sigT P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [existT P x y] in Coq, where [x : A] and [y : P x].  In [Common.v] we defined the notation [(x;y)] to mean [existT _ x y].

The base and fiber components of a point in the total space are extracted with the two projections [projT1] and [projT2]. *)

(** ** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : {x : A & P x}] by writing [u] as a pair [(projT1 u ; projT2 u)]. This is accomplished by [sigT_unpack]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_sigma `{P : A -> Type} (Q : sigT P -> Type) (u : sigT P) :
  Q (projT1 u; projT2 u) -> Q u
  :=
  fun H =>
    (let (x,p) as u return (Q (projT1 u; projT2 u) -> Q u) := u in idmap) H.

(** ** Eta conversion *)

Definition eta_sigma `{P : A -> Type} (u : sigT P)
  : (projT1 u; projT2 u) = u
  := match u with existT x y => 1 end.

Definition eta2_sigma `{P : forall (a : A) (b : B a), Type}
           (u : sigT (fun a => sigT (P a)))
  : (u.1; (u.2.1; u.2.2)) = u
  := match u with existT x (existT y z) => 1 end.

Definition eta3_sigma `{P : forall (a : A) (b : B a) (c : C a b), Type}
           (u : sigT (fun a => sigT (fun b => sigT (P a b))))
  : (u.1; (u.2.1; (u.2.2.1; u.2.2.2))) = u
  := match u with existT x (existT y (existT z w)) => 1 end.

(** ** Paths *)

(** A path in a total space is commonly shown component wise. Because we use this over and over, we write down the proofs by hand to make sure they are what we think they should be. *)

(** With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. *)
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (pq : {p : u.1 = v.1 &  p # u.2 = v.2})
  : u = v
  := match pq with
       | existT p q =>
         match u, v return (forall p0 : (u.1 = v.1), (p0 # u.2 = v.2) -> (u=v)) with
           | (x;y), (x';y') => fun p1 q1 =>
             match p1 in (_ = x'') return (forall y'', (p1 # y = y'') -> (x;y)=(x'';y'')) with
               | idpath => fun y' q2 =>
                 match q2 in (_ = y'') return (x;y) = (x;y'') with
                   | idpath => 1
                 end
             end y' q1
         end p q
     end.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : u = v
  := path_sigma_uncurried P u v (p;q).

(** A variant of [Forall.dpath_forall] from which uses dependent sums to package things. It cannot go into [Forall] because [Sigma] depends on [Forall]. *)

Definition dpath_forall'
  {A : Type } (P : A -> Type) (Q: sigT P -> Type) {x y : A} (h : x = y)
  (f : forall p, Q (x ; p)) (g : forall p, Q (y ; p))
 :
  (forall p, transport Q (path_sigma P (x ; p) (y; _) h 1) (f p) = g (h # p))
  <~>
  (forall p, transportD P (fun x => fun p => Q ( x ; p)) h p (f p) = g (transport P h p)).
Proof.
  destruct h.
  apply equiv_idmap.
Defined.


(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of dependent sum types.  But it has the advantage that the components of those pairs can more often be inferred, so we make them implicit arguments. *)
Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
  (p : x = x') (q : p # y = y')
  : (x;y) = (x';y')
  := path_sigma P (x;y) (x';y') p q.


(** Projections of paths from a total space. *)

Definition projT1_path `{P : A -> Type} {u v : sigT P} (p : u = v)
  : u.1 = v.1
  :=
  ap (@projT1 _ _) p.
  (* match p with idpath => 1 end. *)

Notation "p ..1" := (projT1_path p) (at level 3) : fibration_scope.

Definition projT2_path `{P : A -> Type} {u v : sigT P} (p : u = v)
  : p..1 # u.2 = v.2
  := (transport_compose P (@projT1 _ _) p u.2)^
     @ (@apD {x:A & P x} _ (@projT2 _ _) _ _ p).

Notation "p ..2" := (projT2_path p) (at level 3) : fibration_scope.

(** Now we show how these things compute. *)

Definition projT1_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
  (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
  : (path_sigma_uncurried _ _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition projT2_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
  (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
  : (path_sigma_uncurried _ _ _ pq)..2
    = ap (fun s => transport P s u.2) (projT1_path_sigma_uncurried pq) @ pq.2.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
  (p : u = v)
  : path_sigma_uncurried _ _ _ (p..1; p..2) = p.
Proof.
  destruct p. destruct u. reflexivity.
Defined.

Lemma transport_projT1_path_sigma_uncurried
      `{P : A -> Type} {u v : sigT P}
      (pq : { p : u.1 = v.1 & transport P p u.2 = v.2 })
      Q
: transport (fun x => Q x.1) (@path_sigma_uncurried A P u v pq)
  = transport _ pq.1.
Proof.
  destruct pq as [p q], u, v; simpl in *.
  destruct p, q; simpl in *.
  reflexivity.
Defined.

Definition projT1_path_sigma `{P : A -> Type} {u v : sigT P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : (path_sigma _ _ _ p q)..1 = p
  := projT1_path_sigma_uncurried (p; q).

Definition projT2_path_sigma `{P : A -> Type} {u v : sigT P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : (path_sigma _ _ _ p q)..2
    = ap (fun s => transport P s u.2) (projT1_path_sigma p q) @ q
  := projT2_path_sigma_uncurried (p; q).

Definition eta_path_sigma `{P : A -> Type} {u v : sigT P} (p : u = v)
  : path_sigma _ _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition transport_projT1_path_sigma
      `{P : A -> Type} {u v : sigT P}
      (p : u.1 = v.1) (q : p # u.2 = v.2)
      Q
: transport (fun x => Q x.1) (@path_sigma A P u v p q)
  = transport _ p
  := transport_projT1_path_sigma_uncurried (p; q) Q.

(** This lets us identify the path space of a sigma-type, up to equivalence. *)

Instance isequiv_path_sigma `{P : A -> Type} {u v : sigT P}
  : IsEquiv (path_sigma_uncurried P u v) | 0.
  refine (isequiv_adjointify _
    (fun r => (existT (fun p : u.1 = v.1 => p # u.2 = v.2) r..1 r..2))
    eta_path_sigma
    _).
  destruct u as [u1 u2]; destruct v as [v1 v2]; intros [p q].
  simpl in p, q.
  destruct p; simpl in q.
  destruct q; reflexivity.
Defined.

Definition equiv_path_sigma `(P : A -> Type) (u v : sigT P)
  : {p : u.1 = v.1 &  p # u.2 = v.2} <~> (u = v)
  := BuildEquiv _ _ (path_sigma_uncurried P u v) _.

(** This identification respects path concatenation. *)

Definition path_sigma_pp_pp {A : Type} (P : A -> Type) {u v w : sigT P}
  (p1 : u.1 = v.1) (q1 : p1 # u.2 = v.2)
  (p2 : v.1 = w.1) (q2 : p2 # v.2 = w.2)
  : path_sigma P u w (p1 @ p2)
      (transport_pp P p1 p2 u.2 @ ap (transport P p2) q1 @ q2)
  = path_sigma P u v p1 q1 @ path_sigma P v w p2 q2.
Proof.
  destruct u, v, w. simpl in *.
  destruct p1, p2, q1, q2.
  reflexivity.
Defined.

Definition path_sigma_pp_pp' {A : Type} (P : A -> Type)
  {u1 v1 w1 : A} {u2 : P u1} {v2 : P v1} {w2 : P w1}
  (p1 : u1 = v1) (q1 : p1 # u2 = v2)
  (p2 : v1 = w1) (q2 : p2 # v2 = w2)
  : path_sigma' P (p1 @ p2)
      (transport_pp P p1 p2 u2 @ ap (transport P p2) q1 @ q2)
  = path_sigma' P p1 q1 @ path_sigma' P p2 q2
  := @path_sigma_pp_pp A P (u1;u2) (v1;v2) (w1;w2) p1 q1 p2 q2.

Definition path_sigma_p1_1p' {A : Type} (P : A -> Type)
  {u1 v1 : A} {u2 : P u1} {v2 : P v1}
  (p : u1 = v1) (q : p # u2 = v2)
  : path_sigma' P p q
  = path_sigma' P p 1 @ path_sigma' P 1 q.
Proof.
  destruct p, q.
  reflexivity.
Defined.

(** [projT1_path] also commutes with the groupoid structure. *)

Definition projT1_path_1 {A : Type} {P : A -> Type} (u : sigT P)
: (idpath u) ..1 = idpath (u .1)
:= 1.

Definition projT1_path_pp {A : Type} {P : A -> Type} {u v w : sigT P}
  (p : u = v) (q : v = w)
: (p @ q) ..1 = (p ..1) @ (q ..1)
:= ap_pp _ _ _.

Definition projT1_path_V {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v)
: p^ ..1 = (p ..1)^
:= ap_V _ _.

(** Applying [existT] to one argument is the same as [path_sigma] with reflexivity in the first place. *)

Definition ap_existT {A : Type} (P : A -> Type) (x : A) (y1 y2 : P x)
  (q : y1 = y2)
  : ap (existT P x) q = path_sigma' P 1 q.
Proof.
  destruct q; reflexivity.
Defined.

(** Dependent transport is the same as transport along a [path_sigma]. *)

Definition transportD_is_transport
  {A:Type} (B:A->Type) (C:sigT B -> Type)
  (x1 x2:A) (p:x1=x2) (y:B x1) (z:C (x1;y))
  : transportD B (fun a b => C (a;b)) p y z
    = transport C (path_sigma' B p 1) z.
Proof.
  destruct p. reflexivity.
Defined.

(** Applying a function constructed with [sigT_rect] to a [path_sigma] can be computed.  Technically this computation should probably go by way of a 2-variable [ap], and should be done in the dependently typed case. *)

Definition ap_sigT_rectnd_path_sigma {A : Type} (P : A -> Type) {Q : Type}
  (x1 x2:A) (p:x1=x2) (y1:P x1) (y2:P x2) (q:p # y1 = y2)
  (d : forall a, P a -> Q)
  : ap (sigT_rect (fun _ => Q) d) (path_sigma' P p q)
  = (transport_const p _)^
  @ (ap ((transport (fun _ => Q) p) o (d x1)) (transport_Vp _ p y1))^

  @ (transport_arrow p _ _)^
  @ ap10 (apD d p) (p # y1)
  @ ap (d x2) q.
Proof.
  destruct p. destruct q. reflexivity.
Defined.


(** A path between paths in a total space is commonly shown component wise. *)

(** With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. *)
Definition path_path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (p q : u = v)
  (rs : {r : p..1 = q..1 & transport (fun x => transport P x u.2 = v.2) r p..2 = q..2})
  : p = q.
Proof.
  destruct rs, p, u.
  etransitivity; [ | apply eta_path_sigma ].
  simpl in *.
  generalize dependent (q..2); generalize dependent (q..1); clear q.
  simpl; intros.
  path_induction.
  reflexivity.
Defined.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (r : p..1 = q..1)
           (s : transport (fun x => transport P x u.2 = v.2) r p..2 = q..2)
: p = q
  := path_path_sigma_uncurried P u v p q (r; s).

(** ** Transport *)

(** The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)

Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y })
  : transport (fun x => { y : B x & C x y }) p yz
    = (p # yz.1 ; transportD _ _ p yz.1 yz.2).
Proof.
  destruct p.  destruct yz as [y z]. reflexivity.
Defined.

(** The special case when the second variable doesn't depend on the first is simpler. *)
Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
  : transport (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.

(** ** Functorial action *)

Definition functor_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) (g : forall a, P a -> Q (f a))
  : sigT P -> sigT Q
  := fun u => (f u.1 ; g u.1 u.2).

Definition ap_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) (g : forall a, P a -> Q (f a))
  (u v : sigT P) (p : u.1 = v.1) (q : p # u.2 = v.2)
  : ap (functor_sigma f g) (path_sigma P u v p q)
  = path_sigma Q (functor_sigma f g u) (functor_sigma f g v)
               (ap f p)
               ((transport_compose Q f p (g u.1 u.2))^
               @ (@ap_transport _ P (fun x => Q (f x)) _ _ p g u.2)^
               @ ap (g v.1) q).
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in p, q.
  destruct p; simpl in q.
  destruct q.
  reflexivity.
Defined.

(** ** Equivalences *)

Instance isequiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
  : IsEquiv (functor_sigma f g) | 1000.
Proof.
  refine (isequiv_adjointify (functor_sigma f g)
    (functor_sigma (f^-1)
      (fun x y => ((g (f^-1 x))^-1 ((eisretr f x)^ # y)))) _ _);
  intros [x y].
  - refine (path_sigma' _ (eisretr f x) _); simpl.
    rewrite (eisretr (g (f^-1 x))).
    apply transport_pV.
  - refine (path_sigma' _ (eissect f x) _); simpl.
    refine ((ap_transport (eissect f x) (fun x' => (g x') ^-1)
              (transport Q (eisretr f (f x)) ^ (g x y)))^ @ _).
    rewrite transport_compose, eisadj, transport_pV.
    apply eissect.
Qed.

Definition equiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) `{IsEquiv A B f}
  (g : forall a, P a -> Q (f a))
  `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
  : sigT P <~> sigT Q
  := BuildEquiv _ _ (functor_sigma f g) _.

Definition equiv_functor_sigma' `{P : A -> Type} `{Q : B -> Type}
  (f : A <~> B)
  (g : forall a, P a <~> Q (f a))
  : sigT P <~> sigT Q
  := equiv_functor_sigma f g.

Definition equiv_functor_sigma_id `{P : A -> Type} `{Q : A -> Type}
  (g : forall a, P a <~> Q a)
  : sigT P <~> sigT Q
  := equiv_functor_sigma (equiv_idmap A) g.

(** Summing up a contractible family of types does nothing. *)
Instance isequiv_pr1_contr {A} {P : A -> Type}
           `{forall a, Contr (P a)}
: IsEquiv (@pr1 A P) | 100.
Proof.
  refine (isequiv_adjointify (@projT1 A P)
    (fun a => (a ; center (P a))) _ _).
  intros a; reflexivity.
  intros [a p]. apply path_sigma' with 1, contr.
Defined.

Definition equiv_sigma_contr {A : Type} (P : A -> Type)
  `{forall a, Contr (P a)}
  : sigT P <~> A
  := BuildEquiv _ _ pr1 _.

(** ** Associativity *)

Definition equiv_sigma_assoc `(P : A -> Type) (Q : {a : A & P a} -> Type)
  : {a : A & {p : P a & Q (a;p)}} <~> sigT Q.
Proof.
  refine (@equiv_adjointify {a : A & {p : P a & Q (a;p)}} (sigT Q)
    (fun apq => let (a,pq):=apq in let (p,q):=pq in ((a;p);q))
    (fun apq => let (ap,q):=apq in
      (let (a,p) return (Q ap -> {a : A & {p : P a & Q (a;p)}})
        := ap in fun q => (a ; existT (fun p:P a => Q (a;p)) p q)) q)
    _ _).
  - intros [[a p] q]; reflexivity.
  - intros [a [p q]]; reflexivity.
Defined.

Definition equiv_sigma_prod `(Q : (A * B) -> Type)
  : {a : A & {b : B & Q (a,b)}} <~> sigT Q.
Proof.
  refine (@equiv_adjointify {a : A & {b : B & Q (a,b)}} (sigT Q)
    (fun abq => let (a,bq):=abq in let (b,q):=bq in ((a,b);q))
    (fun abq => let (ab,q):=abq in
      (let (a,b) return (Q ab -> {a : A & {b : B & Q (a,b)}})
        := ab in fun q => (a ; existT (fun b:B => Q (a,b)) b q)) q)
    _ _).
  - intros [[a b] q]; reflexivity.
  - intros [a [b q]]; reflexivity.
Defined.

(** ** Universal mapping properties *)

(* The positive universal property. *)
Instance isequiv_sigT_rect `{Funext} `{P : A -> Type}
  (Q : sigT P -> Type)
  : IsEquiv (sigT_rect Q) | 0
  := isequiv_adjointify (sigT_rect Q)
  (fun f x y => f (x;y))
  _ _.
Proof.
  - intros f; apply path_forall; intros [x y].
    reflexivity.
  - intros f; apply path_forall; intros x; apply path_forall; intros y.
    reflexivity.
Defined.

Definition equiv_sigT_rect `{Funext} `{P : A -> Type}
  (Q : sigT P -> Type)
  : (forall (x:A) (y:P x), Q (x;y)) <~> (forall xy, Q xy)
  := BuildEquiv _ _ (sigT_rect Q) _.

(* The negative universal property. *)

Definition sigT_corect_uncurried
  `{A : X -> Type} (P : forall x, A x -> Type)
  : { f : forall x, A x & forall x, P x (f x) }
     -> (forall x, sigT (P x))
  := fun fg => fun x => (fg.1 x ; fg.2 x).

Definition sigT_corect
  `{A : X -> Type} (P : forall x, A x -> Type)
  (f : forall x, A x) (g : forall x, P x (f x))
  : (forall x, sigT (P x))
  := sigT_corect_uncurried P (f;g).

Instance isequiv_sigT_corect `{Funext}
         `{A : X -> Type} {P : forall x, A x -> Type}
: IsEquiv (sigT_corect_uncurried P) | 0
  := BuildIsEquiv
       _ _
       (sigT_corect_uncurried P)
       (fun h => existT (fun f => forall x, P x (f x))
                        (fun x => (h x).1)
                        (fun x => (h x).2))
       (fun h => path_forall _ _ (fun a : X => @eta_sigma (A a) (P a) (h a)))
       (fun h => eta_sigma h)
       _.
Proof.
  intros [f g]; simpl.
  unfold sigT_corect_uncurried; simpl.
  exact (eissect apD10 1).
Defined.

Definition equiv_sigT_corect `{Funext}
  `(A : X -> Type) (P : forall x, A x -> Type)
  : { f : forall x, A x & forall x, P x (f x) }
     <~> (forall x, sigT (P x))
  := BuildEquiv _ _ (sigT_corect_uncurried P) _.

(** ** Sigmas preserve truncation *)

Instance trunc_sigma `{P : A -> Type}
  `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (sigT P) | 100.
Proof.
  generalize dependent A.
  induction n; simpl; intros A P ac Pc.
  - exists (center A; center (P (center A))).
    intros [a ?].
    refine (path_sigma' P (contr a) (path_contr _ _)).
  - intros u v.
    refine (trunc_equiv (path_sigma_uncurried P u v)).
Defined.

End Sigma.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Sigma.

Module HoTT_DOT_types_DOT_Record.
Module HoTT.
Module types.
Module Record.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(* -*- mode: coq; mode: visual-line -*- *)
(** * Techniques for applying theorems from [Sigma.v] to record types. *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_Contractible.HoTT.Contractible HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_types_DOT_Sigma.HoTT.types.Sigma HoTT_DOT_types_DOT_Forall.HoTT.types.Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** The following tactic proves automatically that a two-component record type is equivalent to a Sigma-type.  Specifically, it proves a goal that looks like
<<
   { x : A & B x } <~> Some_Record
>>
   You have to give it the record constructor and the two record projections as arguments (it has no way to guess what those might be). *)

Ltac issig1 build pr1 pr2 :=
  (** What follows is is a bit of Ltac black magic.  We want to give the explicit proof term except for the coherence cell and define that cell afterwards with tactics.  We could do this by calling the tactic [refine] and leaving a placeholder [_] in the term.  However, the following trick seems to be noticably faster, at least when we move on to the 3- and 4-variable versions below. *)
  let T := fresh in
  let t := fresh in
  (** We introduce a new existential variable [T:Type], assert an element [t:T], and substitute away the definition of [T] in the context. *)
  evar (T : Type); assert (t : T); subst T;
  (** At this point we have two subgoals.  The first is to construct [t] whose type is utterly unknown (an existential variable), and the second is to prove our desired equivalence under the additional assumption of [t] (with its unknown type).  We proceed to ignore the first subgoal and supply a term proving the second one, with [t] standing in for the coherence cell.  This enables Coq to infer what the type of [t] must be.  Since existential variables are the only way that Coq can communicate typing information between subgoals, this information then propagates over to the first subgoal. *)
  [ |
  (** Just in case the user supplied a goal which only *reduces* to one of the desired form. *)
  hnf;
  (** Extract the fibration of which our Sigma-type is the total space, as well as the record type. We pull the terms out of a [match], rather than leaving everything inside the [match] because this gives us better error messages. *)
  let fibration := match goal with |- sigT ?fibration <~> ?record => constr:(fibration) end in
  let record := match goal with |- sigT ?fibration <~> ?record => constr:(record) end in
  exact (BuildEquiv (sigT fibration) record (fun u => build u.1 u.2)
    (BuildIsEquiv (sigT fibration) record (fun u => build u.1 u.2)
      (fun v => existT fibration (pr1 v) (pr2 v))
      (fun v =>
        let (v1,v2) as v' return (build (pr1 v') (pr2 v') = v')
          := v in 1)
      (fun u =>
        match u return
          (existT fibration
            (pr1 (build (u.1) (u.2)))
            (pr2 (build (u.1) (u.2))))
          = u with
          existT x y => 1
        end)
      (** We *could* actually give an explicit proof term for the coherence cell.  Here it is:
<<
      (fun u => match u return
                  ((let (v1,v2) as v' return (build (pr1 v') (pr2 v') = v')
                      := (build u.1 u.2) in 1) =
                  ap (fun u => build u.1 u.2)
                    (match u return
                       (existT fibration
                         (pr1 (build (u.1) (u.2)))
                         (pr2 (build (u.1) (u.2))))
                       = u with
                       existT x y => 1
                     end)) with
                  existT x y => 1
                end)
>>
      However, for the 3- and 4-variable versions, giving the explicit proof term seems to actually *slow down* the tactic.  Perhaps it is because Coq has to infer more implicit arguments, or perhaps this is because there is no oppertunity to run [simpl]  Thus, we proceed instead by supplying the term [t] whose type is an existential variable. *)
      t)) ];
  (** Now we are left only with the one subgoal to prove [t], and at this point we know its type.  The proof basically amounts to destructing a pair.  First, though, we instruct Coq to incorporate learned values of all unification variables.  This speeds things up significantly (although again, the difference is really only noticable for the 3- and 4-variable versions below). *)
  instantiate;
  simpl;
  let x := fresh in intro x;
  destruct x as [? ?];
  exact 1.

(** This allows us to use the same notation for the tactics with varying numbers of variables. *)
Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) :=
  issig1 build pr1 pr2.

(** We show how the tactic works in a couple of examples. *)

Definition issig_contr (A : Type)
  : { x : A & forall y:A, x = y } <~> Contr A.
Proof.
  issig (BuildContr A) (@center A) (@contr A).
Defined.

Definition issig_equiv (A B : Type)
  : { f : A -> B & IsEquiv f } <~> Equiv A B.
Proof.
  issig (BuildEquiv A B) (equiv_fun A B) (equiv_isequiv A B).
Defined.

(** Here is a version of the [issig] tactic for three-component records, which proves goals that look like
<<
   { x : A & { y : B x & C x y } } <~> Some_Record.
>>
   It takes the record constructor and its three projections as arguments, as before. *)

(** First we build a version that doesn't go through adjointification.  By applying [symmetry] first, we can speed up the coherence proof by about two orders of magnitude (in the case of [issig3], from around 24 seconds to around 0.3 seconds, plus a reduction from 16 seconds to 0.8 seconds in the [Defined].  However, this still is too slow, so we will eventually adjointify first.  The speed boost comes from the fact that we are [destruct]ing a record rather than a sigma type; when primitive projections land in Coq, hopefully this won't make so much of a difference. *)

(** The harness takes a tactical to make the [IsEquiv] proof; when proving [A <~> B], the tactical is given [A] and [B], and should return a function that takes the coherence proof [eisadj] and gives back an [IsEquiv]. *)
Ltac issig_harness make_is_equiv_tac :=
  let T := fresh in
  let t := fresh in
  evar (T : Type); assert (t : T); subst T;
  [
  | hnf;
    apply symmetry;
    let A := match goal with |- ?A <~> ?B => constr:(A) end in
    let B := match goal with |- ?A <~> ?B => constr:(B) end in
    let isequiv_proof := make_is_equiv_tac A B in
    exact (@BuildEquiv
             _ _ _
             (isequiv_proof t)) ];
  instantiate;
  simpl;
  let x := fresh in
  intro x;
    destruct x;
    exact 1.

(** Now we actually build the non-adjointified version.  We use some notations to provide a cleaner-looking tactic.  We name it [_exact] because the section and retraction are not adjusted, as they are in adjointification. *)
Ltac issig2_transparent build pr1 pr2 pr3 :=
  issig_harness
    ltac:(fun A B =>
            constr:(@BuildIsEquiv
                      A B
                      (fun v => (pr1 v; (pr2 v; pr3 v)))
                      (fun u => build u.1 u.2.1 u.2.2)
                      eta2_sigma
                      (fun v =>
                         let (v1,v2,v3) as v' return (build (pr1 v') (pr2 v') (pr3 v') = v')
                             := v in 1))).

(** Now we build the adjointified version. *)
Ltac issig2 build pr1 pr2 pr3 :=
  exact (equiv_adjointify
           (fun u => build u.1 u.2.1 u.2.2)
           (fun v => (pr1 v; (pr2 v; pr3 v)))
           (fun v =>
              let (v1,v2,v3) as v' return (build (pr1 v') (pr2 v') (pr3 v') = v')
                  := v in 1)
           eta2_sigma).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) :=
  issig2 build pr1 pr2 pr3.

(** And a similar version for four-component records.  It should be clear how to extend the pattern indefinitely. *)
Ltac issig3_transparent build pr1 pr2 pr3 pr4 :=
  issig_harness
    ltac:(fun A B =>
            constr:(@BuildIsEquiv
                      A B
                      (fun v => (pr1 v; (pr2 v; (pr3 v; pr4 v))))
                      (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2)
                      eta3_sigma
                      (fun v =>
                         let (v1,v2,v3,v4) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v')
                             := v in 1))).

Ltac issig3 build pr1 pr2 pr3 pr4 :=
  exact (equiv_adjointify
           (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2)
           (fun v => (pr1 v; (pr2 v; (pr3 v; pr4 v))))
           (fun v =>
              let (v1,v2,v3,v4) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v')
                  := v in 1)
           eta3_sigma).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) :=
  issig3 build pr1 pr2 pr3 pr4.


(** The record [IsEquiv] has four components, so [issig3] can prove that it is equivalent to an iterated Sigma-type. *)

Definition issig_isequiv_transparent {A B : Type} (f : A -> B) :
  { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) = ap f (s x) }}}
  <~> IsEquiv f.
Proof.
  issig3_transparent (BuildIsEquiv A B f) (@equiv_inv A B f) (@eisretr A B f)
    (@eissect A B f) (@eisadj A B f).
Defined.

Definition issig_isequiv {A B : Type} (f : A -> B) :
  { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) = ap f (s x) }}}
  <~> IsEquiv f.
Proof.
  issig (BuildIsEquiv A B f) (@equiv_inv A B f) (@eisretr A B f)
    (@eissect A B f) (@eisadj A B f).
Defined.

End Record.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Record.

Module HoTT_DOT_HProp.
Module HoTT.
Module HProp.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * HPropositions *)
Import HoTT_DOT_Overture.HoTT.Overture HoTT_DOT_Contractible.HoTT.Contractible HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_Trunc.HoTT.Trunc.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.Forall HoTT_DOT_types_DOT_Sigma.HoTT.types.Sigma HoTT_DOT_types_DOT_Prod.HoTT.types.Prod HoTT_DOT_types_DOT_Record.HoTT.types.Record HoTT_DOT_types_DOT_Paths.HoTT.types.Paths HoTT_DOT_Equivalences.HoTT.Equivalences.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** ** Facts about [IsHProp] *)

(** Maybe this should go to a separate file? *)

Generalizable Variables A B.

(** An inhabited proposition is contractible.
   This is not an [Instance] because it causes infinite loops.
   *)
Lemma contr_inhabited_hprop (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
Proof.
  exists x.
  intro y.
  apply center, H.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition.  We probably won't often have a hypothesis of the form [A -> Contr A], so we make sure we give priority to other instances. *)
Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A | 10000.
Proof.
  intros H x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** If a type is contractible, then so is its type of contractions.
    Using [issig_contr] and the [equiv_intro] tactic, we can transfer this to the equivalent problem of contractibility of a certain Sigma-type, in which case we can apply the general path-construction functions. *)
Instance contr_contr `{Funext} (A : Type)
  : Contr A -> Contr (Contr A) | 100.
Proof.
  intros c; exists c; generalize c.
  equiv_intro (issig_contr A) c'.
  equiv_intro (issig_contr A) d'.
  refine (ap _ _).
  refine (path_sigma _ _ _ ((contr (c'.1))^ @ contr (d'.1)) _).
  refine (path_forall _ _ _); intros x.
  apply path2_contr.
Qed.

(** This provides the base case in a proof that truncatedness is a proposition. *)
Instance hprop_trunc `{Funext} (n : trunc_index) (A : Type)
  : IsHProp (IsTrunc n A) | 0.
Proof.
  apply hprop_inhabited_contr.
  revert A.
  induction n as [| n I]; unfold IsTrunc; simpl.
  - intros A ?.
    exact _.
  - intros A AH1.
    exists AH1.
    intro AH2.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply @path_contr.
    apply I, AH1.
Qed.

(** We can induct on the truncation index to get that [IsTrunc] is (n+1)-truncated for all [n]. *)
Lemma istrunc_s__ishprop `{IsHProp A} {n} : IsTrunc (trunc_S n) A.
Proof.
  induction n; typeclasses eauto.
Defined.

Global Instance trunc_trunc `{Funext} A m n : IsTrunc (trunc_S n) (IsTrunc m A) | 0
  := istrunc_s__ishprop.

(** Chracterization of [IsHProp] in terms of all points being connected by paths. *)

Theorem allpath_hprop `{H : IsHProp A} : forall x y : A, x = y.
Proof.
  apply H.
Defined.

Theorem hprop_allpath (A : Type) : (forall (x y : A), x = y) -> IsHProp A.
  intros H x y.
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr.
Defined.

Theorem equiv_hprop_allpath `{Funext} (A : Type)
  : IsHProp A <~> (forall (x y : A), x = y).
Proof.
  apply (equiv_adjointify (@allpath_hprop A) (@hprop_allpath A));
  (* The proofs of the two homotopies making up this equivalence are almost identical.  First we start with a thing [f]. *)
    intro f;
  (* Then we apply funext a couple of times *)
    apply path_forall; intro x;
    apply path_forall; intro y;
  (* Now we conclude that [A] is contractible *)
    try pose (C := BuildContr A x (f x));
    try pose (D := contr_inhabited_hprop A x);
  (* And conclude because we have a path in a contractible space. *)
    apply path_contr.
Defined.

(** Two propositions are equivalent as soon as there are maps in both
   directions. *)

Definition equiv_iff_hprop_uncurried `{IsHProp A} `{IsHProp B}
  : (A <-> B) -> (A <~> B).
Proof.
  intros [f g].
  apply (equiv_adjointify f g);
    intros ?; apply allpath_hprop.
Defined.

Definition equiv_iff_hprop `{IsHProp A} `{IsHProp B}
  : (A -> B) -> (B -> A) -> (A <~> B)
  := fun f g => equiv_iff_hprop_uncurried (f, g).

(** Being a contractible space is a proposition. *)

Instance hprop_contr `{Funext} (A : Type) : IsHProp (Contr A) | 0.
Proof.
  apply hprop_inhabited_contr.
  intro cA.
  exact _.
Defined.

(** Here is an alternate characterization of propositions. *)

Instance HProp_HProp `{Funext} A : IsHProp (IsHProp A) | 0
  := hprop_trunc minus_one A.

Theorem equiv_hprop_inhabited_contr `{Funext} {A}
  : IsHProp A <~> (A -> Contr A).
Proof.
  apply (equiv_adjointify (@contr_inhabited_hprop A) (@hprop_inhabited_contr A)).
  - intro ic. by_extensionality x.
    apply @path_contr. apply contr_contr. exact (ic x).
  - intro hp. by_extensionality x. by_extensionality y.
    apply @path_contr. apply contr_contr. exact (hp x y).
Defined.

(** Here are some alternate characterizations of contractibility. *)
Theorem equiv_contr_inhabited_hprop `{Funext} {A}
  : Contr A <~> A * IsHProp A.
Proof.
  assert (f : Contr A -> A * IsHProp A).
    intro P. split. exact (@center _ P). apply @trunc_succ. exact P.
  assert (g : A * IsHProp A -> Contr A).
    intros [a P]. apply (@contr_inhabited_hprop _ P a).
  refine (@equiv_iff_hprop _ _ _ _ f g).
  apply hprop_inhabited_contr; intro p.
  apply @contr_prod.
  exact (g p). apply (@contr_inhabited_hprop _ _ (snd p)).
Defined.

Theorem equiv_contr_inhabited_allpath `{Funext} {A}
  : Contr A <~> A * forall (x y : A), x = y.
Proof.
  apply transitivity with (y := A * IsHProp A).
  apply equiv_contr_inhabited_hprop.
  apply equiv_functor_prod'. apply equiv_idmap. apply equiv_hprop_allpath.
Defined.

(** If the second component of a sigma type is an hProp, then to prove equality, we only need equality of the first component. *)
Definition path_sigma_hprop {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)}
           (u v : sigT P)
: u.1 = v.1 -> u = v
  := path_sigma_uncurried P u v o pr1^-1.

Instance isequiv_path_sigma_hprop {A P} `{forall x : A, IsHProp (P x)} {u v : sigT P}
: IsEquiv (@path_sigma_hprop A P _ u v) | 100
  := isequiv_compose.

Hint Immediate isequiv_path_sigma_hprop : typeclass_instances.

(** The sigma of an hprop over a type can be viewed as a subtype. In particular, paths in the subtype are equivalent to paths in the original type. *)
Definition equiv_path_sigma_hprop {A : Type} {P : A -> Type}
           {HP : forall a, IsHProp (P a)} (u v : sigT P)
: (u.1 = v.1) <~> (u = v)
  := BuildEquiv _ _ (path_sigma_hprop _ _) _.

(** The type of Propositions *)
Record hProp := hp { hproptype :> Type ; isp : IsHProp hproptype}.
(** This one would allow us to turn the record type of contractible types
into an [hProp].
<<
Canonical Structure default_HProp:= fun T P => (@hp T P).
>>
*)
Existing Instance isp.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.Unit HoTT_DOT_types_DOT_Empty.HoTT.types.Empty.
Definition Unit_hp:hProp:=(hp Unit _).
Definition False_hp:hProp:=(hp Unit _).
(** We could continue with products etc *)

Definition issig_hProp: (sigT IsHProp) <~> hProp.
Proof.
  issig hp hproptype isp.
Defined.

(** Prove that [ap hproptype] is an equivalence. *)
Global Instance isequiv_ap_hproptype `{Funext} X Y : IsEquiv (@ap _ _ hproptype X Y).
Proof.
  (* TODO: This is a bit slow... can we speed it up? *)
  pose proof
       (isequiv_homotopic
          ((@path_sigma_hprop _ _ _ _ _)^-1 o (@ap _ _ issig_hProp^-1 X Y)))
    as H'.
  apply H'; clear H'.
  - apply @isequiv_compose.
    + typeclasses eauto.
    + apply @isequiv_inverse.
  - intros []; reflexivity.
Defined.

Definition path_hprop `{Funext} X Y := (@ap _ _ hproptype X Y)^-1%equiv.

End HProp.

End HoTT.

End HoTT_DOT_HProp.

Module HoTT_DOT_categories_DOT_Functor_DOT_Core.
Module HoTT.
Module categories.
Module Functor.
Module Core.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Definition of a functor *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Delimit Scope functor_scope with functor.

Local Open Scope morphism_scope.

Section Functor.
  Variable C : PreCategory.
  Variable D : PreCategory.

  (** Quoting from the lecture notes for MIT's 18.705, Commutative Algebra:

      A map of categories is known as a functor. Namely, given
      categories [C] and [C'], a (covariant) functor [F : C -> C'] is
      a rule that assigns to each object [A] of [C] an object [F A] of
      [C'] and to each map [m : A -> B] of [C] a map [F m : F A -> F
      B] of [C'] preserving composition and identity; that is,

     (1) [F (m' ∘ m) = (F m') ∘ (F m)] for maps [m : A -> B] and [m' :
         B -> C] of [C], and

     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A]
         is the identity morphism of [A]. **)

  Record Functor :=
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

Create HintDb functor discriminated.

Arguments Functor C D.
Arguments object_of {C%category D%category} F%functor c%object : rename, simpl nomatch.
Arguments morphism_of [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Arguments composition_of [C D] F _ _ _ _ _ : rename.
Arguments identity_of [C D] F _ : rename.

Module Export FunctorCoreNotations.
  (** Perhaps we should consider making this more global? *)
  Local Notation "C --> D" := (Functor C D) (at level 99, right associativity) : type_scope.
  Notation "F '_0' x" := (object_of F x) (at level 10, no associativity, only parsing) : object_scope.
  Notation "F '_1' m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.
End FunctorCoreNotations.

Hint Resolve @composition_of @identity_of : category functor.
Hint Rewrite @identity_of : category.
Hint Rewrite @identity_of : functor.

End Core.

End Functor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Functor_DOT_Core.

Module HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Module HoTT.
Module categories.
Module Category.
Module Morphisms.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Definitions and theorems about {iso,epi,mono,}morphisms in a precategory *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core.
Import HoTT_DOT_Tactics.HoTT.Tactics HoTT_DOT_types_DOT_Record.HoTT.types.Record HoTT_DOT_Trunc.HoTT.Trunc HoTT_DOT_HProp.HoTT.HProp HoTT_DOT_types_DOT_Sigma.HoTT.types.Sigma HoTT_DOT_Equivalences.HoTT.Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Definition of isomorphism *)
Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) :=
  {
    morphism_inverse : morphism C d s;
    left_inverse : morphism_inverse o m = identity _;
    right_inverse : m o morphism_inverse = identity _
  }.

Local Notation "m ^-1" := (morphism_inverse (m := m)) : morphism_scope.

Hint Resolve left_inverse right_inverse : category morphism.
Hint Rewrite @left_inverse @right_inverse : category.
Hint Rewrite @left_inverse @right_inverse : morphism.

Class Isomorphic {C : PreCategory} s d :=
  {
    morphism_isomorphic :> morphism C s d;
    isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic
  }.

(*Coercion Build_Isomorphic : IsIsomorphism >-> Isomorphic.*)
Coercion morphism_isomorphic : Isomorphic >-> morphism.
Coercion isisomorphism_isomorphic : Isomorphic >-> IsIsomorphism.

Local Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.

Existing Instance isisomorphism_isomorphic.

(** ** Theorems about isomorphisms *)
Section iso_contr.
  Variable C : PreCategory.

  Local Open Scope equiv_scope.

  Variables s d : C.

  Section IsIsomorphism.
    Variable m : morphism C s d.

    (** *** The inverse of a morphism is unique *)
    Lemma inverse_unique (m_inv0 m_inv1 : morphism C d s)
          (left_inverse_0 : m_inv0 o m = identity _)
          (right_inverse_1 : m o m_inv1 = identity _)
    : m_inv0 = m_inv1.
    Proof.
      transitivity (m_inv0 o m o m_inv1);
      try solve [ by (rewrite -> ?associativity; rewrite_hyp;
                      autorewrite with morphism)
                | by (rewrite <- ?associativity; rewrite_hyp;
                      autorewrite with morphism) ].
    Qed.

    Local Notation IsIsomorphism_sig_T :=
      { inverse : morphism C d s
      | { _ : inverse o m = identity _
        | m o inverse = identity _ } } (only parsing).

    (** *** Equivalence between the record and sigma versions of [IsIsomorphism] *)
    Lemma issig_isisomorphism
    : IsIsomorphism_sig_T <~> IsIsomorphism m.
    Proof.
      issig (@Build_IsIsomorphism _ _ _ m)
            (@morphism_inverse _ _ _ m)
            (@left_inverse _ _ _ m)
            (@right_inverse _ _ _ m).
    Defined.

    (** *** Being an isomorphism is a mere proposition *)
    Global Instance trunc_isisomorphism : IsHProp (IsIsomorphism m).
    Proof.
      eapply trunc_equiv'; [ exact issig_isisomorphism | ].
      apply hprop_allpath.
      intros [x [? ?]] [y [? ?]].
      let H := fresh in
      assert (H : x = y) by (apply inverse_unique; assumption);
        destruct H.
      repeat match goal with
               | _ => progress simpl
               | _ => exact (center _)
               | _ => (exists idpath)
               | _ => apply path_sigma_uncurried
             end.
    Qed.
  End IsIsomorphism.

  Local Notation Isomorphic_sig_T :=
    { m : morphism C s d
    | IsIsomorphism m } (only parsing).

  (** *** Equivalence between record and sigma versions of [Isomorphic] *)
  Lemma issig_isomorphic
  : Isomorphic_sig_T <~> Isomorphic s d.
  Proof.
    issig (@Build_Isomorphic C s d)
          (@morphism_isomorphic C s d)
          (@isisomorphism_isomorphic C s d).
  Defined.

  (** *** Isomorphisms form an hSet *)
  Global Instance trunc_Isomorphic : IsHSet (Isomorphic s d).
  Proof.
    eapply trunc_equiv'; [ exact issig_isomorphic | ].
    typeclasses eauto.
  Qed.

  (** *** Equality between isomorphisms is determined by equality between their forward components *)
  Definition path_isomorphic (i j : Isomorphic s d)
  : @morphism_isomorphic _ _ _ i = @morphism_isomorphic _ _ _ j
    -> i = j.
  Proof.
    destruct i, j; simpl.
    intro; path_induction.
    f_ap.
    exact (center _).
  Defined.

  (** *** Equality between isomorphisms is equivalent to by equality between their forward components *)
  Global Instance isequiv_path_isomorphic
  : IsEquiv (path_isomorphic i j).
  Proof.
    intros.
    apply (isequiv_adjointify
             (path_isomorphic i j)
             (ap (@morphism_isomorphic _ _ _)));
      intro; [ destruct i | destruct i, j ];
      path_induction_hammer.
  Defined.
End iso_contr.

Section iso_equiv_relation.
  Variable C : PreCategory.

  (** *** The identity is an isomorphism *)
  Global Instance isisomorphism_identity (x : C) : IsIsomorphism (identity x)
    := {| morphism_inverse := identity x;
          left_inverse := left_identity C x x (identity x);
          right_inverse := right_identity C x x (identity x) |}.

  (** *** Inverses of isomorphisms are isomorphisms *)
  Definition isisomorphism_inverse `(@IsIsomorphism C x y m) : IsIsomorphism m^-1
    := {| morphism_inverse := m;
          left_inverse := right_inverse;
          right_inverse := left_inverse |}.

  Local Ltac iso_comp_t inv_lemma :=
    etransitivity; [ | apply inv_lemma ];
    instantiate;
    first [ rewrite -> ?associativity; apply ap
          | rewrite <- ?associativity; apply ap ];
    first [ rewrite -> ?associativity; rewrite inv_lemma
          | rewrite <- ?associativity; rewrite inv_lemma ];
    auto with morphism.

  (** *** Composition of isomorphisms gives an isomorphism *)
  Global Instance isisomorphism_compose `(@IsIsomorphism C y z m0) `(@IsIsomorphism C x y m1)
  : IsIsomorphism (m0 o m1).
  Proof.
    exists (m1^-1 o m0^-1);
    [ abstract iso_comp_t @left_inverse
    | abstract iso_comp_t @right_inverse ].
  Defined.

  Hint Immediate isisomorphism_inverse : typeclass_instances.

  (** *** Being isomorphic is a reflexive relation *)
  Global Instance isomorphic_refl : Reflexive (@Isomorphic C)
    := fun x : C => {| morphism_isomorphic := identity x |}.

  (** *** Being isomorphic is a symmetric relation *)
  Global Instance isomorphic_sym : Symmetric (@Isomorphic C)
    := fun x y X => {| morphism_isomorphic := morphism_inverse |}.

  (** *** Being isomorphic is a transitive relation *)
  Global Instance isomorphic_trans : Transitive (@Isomorphic C)
    := fun x y z X Y => {| morphism_isomorphic := @morphism_isomorphic _ _ _ Y o @morphism_isomorphic _ _ _ X |}.

  (** *** Equality gives rise to isomorphism *)
  Definition idtoiso (x y : C) (H : x = y) : Isomorphic x y
    := match H in (_ = y0) return (x <~=~> y0) with
         | 1%path => reflexivity x
       end.
End iso_equiv_relation.

Hint Immediate isisomorphism_inverse : typeclass_instances.

(** ** Epimorphisms and Monomorphisms *)
(** Quoting Wikipedia:

    In category theory, an epimorphism (also called an epic morphism
    or, colloquially, an epi) is a morphism [f : X → Y] which is
    right-cancellative in the sense that, for all morphisms [g, g' : Y
    → Z], [g ∘ f = g' ∘ f → g = g']

    Epimorphisms are analogues of surjective functions, but they are
    not exactly the same. The dual of an epimorphism is a monomorphism
    (i.e. an epimorphism in a category [C] is a monomorphism in the
    dual category [Cᵒᵖ]).  *)

Class IsEpimorphism {C} {x y} (m : morphism C x y) :=
  is_epimorphism : forall z (m1 m2 : morphism C y z),
                     m1 o m = m2 o m
                     -> m1 = m2.
Class IsMonomorphism {C} {x y} (m : morphism C x y) :=
  is_monomorphism : forall z (m1 m2 : morphism C z x),
                      m o m1 = m o m2
                      -> m1 = m2.

Record Epimorphism {C} x y :=
  {
    Epimorphism_morphism :> morphism C x y;
    Epimorphism_IsEpimorphism :> IsEpimorphism Epimorphism_morphism
  }.

Record Monomorphism {C} x y :=
  {
    Monomorphism_morphism :> morphism C x y;
    Monomorphism_IsMonomorphism :> IsMonomorphism Monomorphism_morphism
  }.

Existing Instances Epimorphism_IsEpimorphism Monomorphism_IsMonomorphism.

Local Notation "x ->> y" := (Epimorphism x y)
                              (at level 99, right associativity, y at level 200).
Local Notation "x (-> y" := (Monomorphism x y)
                              (at level 99, right associativity, y at level 200).

Class IsSectionOf C x y (s : morphism C x y) (r : morphism C y x)
  := is_sect_morphism : r o s = identity _.

Arguments IsSectionOf [C x y] s r.

Section EpiMono.
  Variable C : PreCategory.

  Section properties.
    (** *** The identity is an epimorphism *)
    Global Instance isepimorphism_identity (x : C)
    : IsEpimorphism (identity x).
    Proof.
      repeat intro; autorewrite with morphism in *; trivial.
    Qed.

    (** *** The identity is a monomorphism *)
    Global Instance ismonomorphism_identity (x : C)
    : IsMonomorphism (identity x).
    Proof.
      repeat intro; autorewrite with morphism in *; trivial.
    Qed.

    (** *** Composition of epimorphisms gives an epimorphism *)
    Global Instance isepimorphism_compose s d d' m0 m1
    : IsEpimorphism m0
      -> IsEpimorphism m1
      -> IsEpimorphism (@compose C s d d' m0 m1).
    Proof.
      repeat intro.
      rewrite <- !associativity in *.
      apply_hyp.
    Qed.

    (** *** Composition of monomorphisms gives a monomorphism *)
    Global Instance ismonomorphism_compose s d d' m0 m1
    : IsMonomorphism m0
      -> IsMonomorphism m1
      -> IsMonomorphism (@compose C s d d' m0 m1).
    Proof.
      repeat intro.
      rewrite !associativity in *.
      apply_hyp.
    Qed.
  End properties.

  (** *** Existence of {epi,mono}morphisms are a preorder *)
  Section equiv.
    Global Instance reflexive_epimorphism : Reflexive (@Epimorphism C)
      := fun x => Build_Epimorphism (isepimorphism_identity x).

    Global Instance reflexive_monomorphism : Reflexive (@Monomorphism C)
      := fun x => Build_Monomorphism (ismonomorphism_identity x).

    Global Instance transitive_epimorphism : Transitive (@Epimorphism C)
      := fun _ _ _ m0 m1 => Build_Epimorphism (isepimorphism_compose m1 m0).

    Global Instance transitive_monomorphism : Transitive (@Monomorphism C)
      := fun _ _ _ m0 m1 => Build_Monomorphism (ismonomorphism_compose m1 m0).
  End equiv.

  Section sect.
    Local Ltac epi_mono_sect_t :=
      let t :=
          (solve [ autorewrite with morphism;
                   reflexivity
                 | rewrite_hyp;
                   autorewrite with morphism;
                   reflexivity ]) in
      first [ rewrite -> ?associativity; t
            | rewrite <- ?associativity; t].

    (** *** Retractions are epimorphisms *)
    Global Instance isepimorphism_retr `(@IsSectionOf C x y s r)
    : IsEpimorphism r | 1000.
    Proof.
      (intros ? m1 m2 ?).
      unfold IsSectionOf in *.
      transitivity ((m1 o r) o s);
        [ | transitivity ((m2 o r) o s) ];
        epi_mono_sect_t.
    Qed.

    (** *** Sections are monomorphisms *)
    Global Instance ismonomorphism_sect `(@IsSectionOf C x y s r)
    : IsMonomorphism s | 1000.
    Proof.
      (intros ? m1 m2 ?).
      transitivity (r o (s o m1));
        [ | transitivity (r o (s o m2)) ];
        epi_mono_sect_t.
    Qed.

    (** *** Isomorphisms are both sections and retractions *)
    Global Instance issect_isisomorphism `(@IsIsomorphism C x y m)
    : IsSectionOf m m^-1 | 1000
      := left_inverse.

    Global Instance isretr_isisomorphism `(@IsIsomorphism C x y m)
    : IsSectionOf m^-1 m | 1000
      := right_inverse.
  End sect.

  (** *** Isomorphisms are therefore epimorphisms and monomorphisms *)
  Section iso.
    Global Instance isepimorphism_isisomorphism `(@IsIsomorphism C s d m)
    : IsEpimorphism m | 1000
      := _.
    Global Instance ismonomorphism_isisomorphism `(@IsIsomorphism C s d m)
    : IsMonomorphism m | 1000
      := _.
  End iso.
End EpiMono.

Hint Immediate @isepimorphism_identity @ismonomorphism_identity @ismonomorphism_compose @isepimorphism_compose : category morphism.

(** ** Lemmas about [idtoiso] *)
Section iso_lemmas.
  Local Ltac idtoiso_t :=
    path_induction; simpl; autorewrite with morphism; reflexivity.

  (** *** [transport]ing across an equality of morphisms is the same as conjugating with [idtoiso] *)
  Lemma idtoiso_of_transport (C D : PreCategory) s d
        (m1 m2 : morphism C s d)
        (p : m1 = m2)
        (s' d' : morphism C s d -> D) u
  : @transport _ (fun m => morphism D (s' m) (d' m)) _ _ p u
    = idtoiso _ (ap d' p) o u o (idtoiso _ (ap s' p))^-1.
  Proof. idtoiso_t. Qed.

  (** *** [idtoiso] respects inverse *)
  Lemma idtoiso_inv (C : PreCategory) (s d : C) (p : s = d)
  : (idtoiso _ p)^-1 = idtoiso _ (p^)%path.
  Proof.
    path_induction; reflexivity.
  Defined.

  (** *** [idtoiso] respects composition *)
  Lemma idtoiso_comp (C : PreCategory) (s d d' : C)
        (m1 : d = d') (m2 : s = d)
  : idtoiso _ m1 o idtoiso _ m2 = idtoiso _ (m2 @ m1)%path.
  Proof. idtoiso_t. Qed.

  (** These are useful when tactics are too slow and [rewrite] doesn't
      work. *)
  Lemma idtoiso_comp3 (C : PreCategory) (s d d' d'' : C)
        (m0 : d' = d'') (m1 : d = d') (m2 : s = d)
  : idtoiso _ m0 o (idtoiso _ m1 o idtoiso _ m2) = idtoiso _ ((m2 @ m1) @ m0)%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp3' (C : PreCategory) (s d d' d'' : C)
        (m0 : d' = d'') (m1 : d = d') (m2 : s = d)
  : (idtoiso _ m0 o idtoiso _ m1) o idtoiso _ m2 = idtoiso _ (m2 @ (m1 @ m0))%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp4 (C : PreCategory) (s d d' d'' d''' : C)
        (m0 : d'' = d''') (m1 : d' = d'') (m2 : d = d') (m3 : s = d)
  : idtoiso _ m0 o (idtoiso _ m1 o (idtoiso _ m2 o idtoiso _ m3)) = idtoiso _ (((m3 @ m2) @ m1) @ m0)%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp4' (C : PreCategory) (s d d' d'' d''' : C)
        (m0 : d'' = d''') (m1 : d' = d'') (m2 : d = d') (m3 : s = d)
  : ((idtoiso _ m0 o idtoiso _ m1) o idtoiso _ m2) o idtoiso _ m3 = idtoiso _ (m3 @ (m2 @ (m1 @ m0)))%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp5 (C : PreCategory) (s d d' d'' d''' d'''' : C)
        (m0 : d''' = d'''') (m1 : d'' = d''') (m2 : d' = d'') (m3 : d = d') (m4 : s = d)
  : idtoiso _ m0 o (idtoiso _ m1 o (idtoiso _ m2 o (idtoiso _ m3 o idtoiso _ m4)))
    = idtoiso _ ((((m4 @ m3) @ m2) @ m1) @ m0)%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp5' (C : PreCategory) (s d d' d'' d''' d'''' : C)
        (m0 : d''' = d'''') (m1 : d'' = d''') (m2 : d' = d'') (m3 : d = d') (m4 : s = d)
  : (((idtoiso _ m0 o idtoiso _ m1) o idtoiso _ m2) o idtoiso _ m3) o idtoiso _ m4
    = idtoiso _ (m4 @ (m3 @ (m2 @ (m1 @ m0))))%path.
  Proof. idtoiso_t. Qed.

  (** *** [idtoiso] respects application of functors on morphisms and objects *)
  Lemma idtoiso_functor (C D : PreCategory) (s d : C) (m : s = d)
        (F : Functor C D)
  : morphism_of F (idtoiso _ m) = idtoiso _ (ap (object_of F) m).
  Proof.
    path_induction; simpl; apply identity_of.
  Defined.

  (** *** Functors preserve isomorphisms *)
  Global Instance iso_functor C D (F : Functor C D) `(@IsIsomorphism C s d m)
  : IsIsomorphism (morphism_of F m)
    := {| morphism_inverse := morphism_of F m^-1 |}.
  Proof.
    abstract (rewrite <- composition_of, ?left_inverse, ?right_inverse, identity_of; reflexivity).
    abstract (rewrite <- composition_of, ?left_inverse, ?right_inverse, identity_of; reflexivity).
  Defined.
End iso_lemmas.

Hint Extern 1 (@IsIsomorphism _ _ _ (@morphism_of ?C ?D ?F ?s ?d ?m))
=> apply (@iso_functor C D F s d m) : typeclass_instances.

Hint Rewrite idtoiso_of_transport idtoiso_inv idtoiso_comp idtoiso_functor.

(** ** Lemmas about how to move isomorphisms around equalities, following [HoTT.PathGroupoids] *)
Section iso_concat_lemmas.
  Variable C : PreCategory.

  Local Ltac iso_concat_t' :=
    intros;
    repeat match goal with
             | [ H : ?x = ?y |- _ ] => atomic y; induction H
             | [ H : ?x = ?y |- _ ] => atomic x; symmetry in H; induction H
           end;
    repeat first [ done
                 | rewrite -> ?associativity;
                   progress rewrite ?left_identity, ?right_identity, ?left_inverse, ?right_inverse
                 | rewrite <- ?associativity;
                   progress rewrite ?left_identity, ?right_identity, ?left_inverse, ?right_inverse
                 | rewrite -> ?associativity; progress f_ap; []
                 | rewrite <- ?associativity; progress f_ap; [] ].

  Local Ltac iso_concat_t_id_fin :=
    match goal with
      | [ |- appcontext[@identity ?C ?x] ]
        => generalize dependent (@identity C x)
    end;
    iso_concat_t'.

  Local Ltac iso_concat_t_id lem :=
    first [ solve [
                etransitivity; [ | eapply lem ];
                iso_concat_t_id_fin
              ]
          | solve [
                etransitivity; [ eapply symmetry; eapply lem | ];
                iso_concat_t_id_fin
          ] ].

  Local Ltac iso_concat_t :=
    iso_concat_t';
    try first [ solve [ iso_concat_t_id @left_identity ]
              | solve [ iso_concat_t_id @right_identity ] ].

  Definition iso_compose_pV `(@IsIsomorphism C x y p)
  : p o p^-1 = identity _
    := right_inverse.
  Definition iso_compose_Vp `(@IsIsomorphism C x y p)
  : p^-1 o p = identity _
    := left_inverse.

  Definition iso_compose_V_pp `(@IsIsomorphism C y z p) `(q : morphism C x y)
  : p^-1 o (p o q) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_p_Vp `(@IsIsomorphism C x z p) `(q : morphism C y z)
  : p o (p^-1 o q) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_pp_V `(p : morphism C y z) `(@IsIsomorphism C x y q)
  : (p o q) o q^-1 = p.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_pV_p `(p : morphism C x z) `(@IsIsomorphism C x y q)
  : (p o q^-1) o q = p.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_pp `(@IsIsomorphism C y z p) `(@IsIsomorphism C x y q)
  : (p o q)^-1 = q^-1 o p^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_Vp `(@IsIsomorphism C y z p) `(@IsIsomorphism C x z q)
  : (p^-1 o q)^-1 = q^-1 o p.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_pV `(@IsIsomorphism C x y p) `(@IsIsomorphism C x z q)
  : (p o q^-1)^-1 = q o p^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_VV `(@IsIsomorphism C x y p) `(@IsIsomorphism C y z q)
  : (p^-1 o q^-1)^-1 = q o p.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_Mp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C y z r)
  : p = (r^-1 o q) -> (r o p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_pM `(@IsIsomorphism C x y p) `(q : morphism C x z) `(r : morphism C y z)
  : r = (q o p^-1) -> (r o p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_Vp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C z y r)
  : p = (r o q) -> (r^-1 o p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_pV `(@IsIsomorphism C x y p) `(q : morphism C y z) `(r : morphism C x z)
  : r = (q o p) -> (r o p^-1) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_Mp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C y z r)
  : (r^-1 o q) = p -> q = (r o p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_pM `(@IsIsomorphism C x y p) `(q : morphism C x z) `(r : morphism C y z)
  : (q o p^-1) = r -> q = (r o p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_Vp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C _ _ r)
  : (r o q) = p -> q = (r^-1 o p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_pV `(@IsIsomorphism C x y p) `(q : morphism C y z) r
  : (q o p) = r -> q = (r o p^-1).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_1M `(p : morphism C x y) `(@IsIsomorphism C x y q)
  : p o q^-1 = identity _ -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_M1 `(p : morphism C x y) `(@IsIsomorphism C x y q)
  : q^-1 o p = identity _ -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_1V `(p : morphism C x y) `(@IsIsomorphism C y x q)
  : p o q = identity _ -> p = q^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_V1 `(p : morphism C x y) `(@IsIsomorphism C y x q)
  : q o p = identity _ -> p = q^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_M1 `(@IsIsomorphism C x y p) q
  : identity _ = p^-1 o q -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_1M `(@IsIsomorphism C x y p) q
  : identity _ = q o p^-1 -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_1V `(@IsIsomorphism C x y p) q
  : identity _ = q o p -> p^-1 = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_V1 `(@IsIsomorphism C x y p) q
  : identity _ = p o q -> p^-1 = q.
  Proof. iso_concat_t. Qed.
End iso_concat_lemmas.

(** ** Tactics for moving inverses around *)
Ltac iso_move_inverse' :=
  match goal with
    | [ |- _^-1 o _ = _ ] => apply iso_moveR_Vp
    | [ |- _ = _^-1 o _ ] => apply iso_moveL_Vp
    | [ |- _ o _^-1 = _ ] => apply iso_moveR_pV
    | [ |- _ = _ o _^-1 ] => apply iso_moveL_pV
    | [ |- _ o (_ o _^-1) = _ ] => rewrite <- associativity
    | [ |- _ = _ o (_ o _^-1) ] => rewrite <- associativity
    | [ |- (_^-1 o _) o _ = _ ] => rewrite -> associativity
    | [ |- _ = (_^-1 o _) o _ ] => rewrite -> associativity
  end.

Ltac iso_move_inverse := progress repeat iso_move_inverse'.

(** ** Tactics for collapsing [p ∘ p⁻¹] and [p⁻¹ ∘ p] *)
(** Now the tactics for collapsing [p ∘ p⁻¹] (and [p⁻¹ ∘ p]) in the
    middle of a chain of compositions of isomorphisms. *)

Ltac iso_collapse_inverse_left' :=
  first [ apply ap
        | progress rewrite ?iso_compose_p_Vp, ?iso_compose_V_pp ].

Ltac iso_collapse_inverse_left :=
  rewrite -> ?Category.Core.associativity;
  progress repeat iso_collapse_inverse_left'.

Ltac iso_collapse_inverse_right' :=
  first [ apply ap10; apply ap
        | progress rewrite ?iso_compose_pV_p, ?iso_compose_pp_V ].

Ltac iso_collapse_inverse_right :=
  rewrite <- ?Category.Core.associativity;
  progress repeat iso_collapse_inverse_right'.

Ltac iso_collapse_inverse :=
  progress repeat first [ iso_collapse_inverse_left
                        | iso_collapse_inverse_right ].

Section associativity_composition.
  Variable C : PreCategory.
  Variables x0 x1 x2 x3 x4 : C.

  (** This lemma is helpful for backwards reasoning. *)
  Lemma compose4associativity_helper
    (a : morphism C x3 x4) (b : morphism C x2 x3)
    (c : morphism C x1 x2) (d : morphism C x0 x1)
  : a o b o c o d = (a o ((b o c) o d)).
  Proof.
    rewrite !associativity; reflexivity.
  Qed.
End associativity_composition.

Module Export CategoryMorphismsNotations.
  Notation "m ^-1" := (morphism_inverse (m := m)) : morphism_scope.

  Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.

  Notation "x ->> y" := (Epimorphism x y)
                          (at level 99, right associativity, y at level 200).
  Notation "x (-> y" := (Monomorphism x y)
                          (at level 99, right associativity, y at level 200).
End CategoryMorphismsNotations.

End Morphisms.

End Category.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Category_DOT_Morphisms.

Module HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Module HoTT.
Module categories.
Module Functor.
Module Composition.
Module Core.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Composition of functors *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section composition.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  (** We usually don't want to see the proofs of composition in functors, because the proofs are hProps, and so we don't care about them.  But occasionally, we want to be able to reduce the proofs.  Having the proofs transparent allows the composition of the identity functor with itself to be judgementally the identity.  Since the only way to hide something from within a proof is [abstract], and that makes the definitions opaque, we need to define the laws separately. *)

  Local Notation c_object_of c := (G (F c)) (only parsing).
  Local Notation c_morphism_of m := (morphism_of G (morphism_of F m)) (only parsing).
  Definition compose_composition_of s d d'
      (m1 : morphism C s d) (m2 : morphism C d d')
  : c_morphism_of (m2 o m1) = c_morphism_of m2 o c_morphism_of m1
    := transport (@paths _ (c_morphism_of (m2 o m1)))
                 (composition_of G _ _ _ _ _)
                 (ap (@morphism_of _ _ G _ _) (composition_of F _ _ _ m1 m2)).

  Definition compose_identity_of x
  : c_morphism_of (identity x) = identity (c_object_of x)
    := transport (@paths _ _)
                 (identity_of G _)
                 (ap (@morphism_of _ _ G _ _) (identity_of F x)).

  Definition compose : Functor C E
    := Build_Functor
         C E
         (fun c => G (F c))
         (fun _ _ m => morphism_of G (morphism_of F m))
         compose_composition_of
         compose_identity_of.
End composition.

Global Arguments compose_composition_of / .
Global Arguments compose_identity_of / .

Module Export FunctorCompositionCoreNotations.
  Infix "o" := compose : functor_scope.
End FunctorCompositionCoreNotations.

End Core.

End Composition.

End Functor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.

Module HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Module HoTT.
Module categories.
Module Functor.
Module Identity.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Identity functor *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section identity.
  (** There is an identity functor.  It does the obvious thing. *)
  Definition identity C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End identity.

Module Export FunctorIdentityNotations.
  Notation "1" := (identity _) : functor_scope.
End FunctorIdentityNotations.

End Identity.

End Functor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Functor_DOT_Identity.

Module HoTT_DOT_categories_DOT_Category_DOT_Strict.
Module HoTT.
Module categories.
Module Category.
Module Strict.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Definition of a strict category *)
Export HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

(** Quoting the HoTT Book: *)
(** Definition. A _strict category_ is a precategory whose type of
    objects is a set. *)

Notation IsStrictCategory C := (IsHSet (object C)).

Record StrictCategory :=
  {
    precategory_strict :> PreCategory;
    isstrict_StrictCategory :> IsStrictCategory precategory_strict
  }.

Existing Instance isstrict_StrictCategory.

End Strict.

End Category.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Category_DOT_Strict.

Module HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Module HoTT.
Module categories.
Module Functor.
Module Paths.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Classification of path spaces of functors *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core.
Import HoTT_DOT_HProp.HoTT.HProp HoTT_DOT_Tactics.HoTT.Tactics HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_PathGroupoids.HoTT.PathGroupoids HoTT_DOT_types_DOT_Sigma.HoTT.types.Sigma HoTT_DOT_Trunc.HoTT.Trunc HoTT_DOT_types_DOT_Record.HoTT.types.Record.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

Section path_functor.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Open Scope equiv_scope.

  Local Notation functor_sig_T :=
    { OO : C -> D
    | { MO : forall s d, morphism C s d -> morphism D (OO s) (OO d)
      | { FCO : forall s d d' (m1 : morphism C s d) (m2 : morphism C d d'),
                  MO _ _ (m2 o m1) = MO d d' m2 o MO s d m1
        | forall x,
            MO x x (identity x) = identity (OO x) } } }
      (only parsing).

  (** ** Equivalence between the record and sigma-type versions of a functor *)
  Lemma equiv_sig_functor
  : functor_sig_T <~> Functor C D.
  Proof.
    issig (@Build_Functor C D) (@object_of C D) (@morphism_of C D) (@composition_of C D) (@identity_of C D).
  Defined.

  (** We could leave it at that and be done with it, but we want a more convenient form for actually constructing paths between functors.  For this, we write a trimmed down version of something equivalent to the type of paths between functors. *)

  Local Notation path_functor'_T F G
    := { HO : object_of F = object_of G
       | transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d))
                   HO
                   (morphism_of F)
         = morphism_of G }
         (only parsing).

  (** We could just go prove that the path space of [functor_sig_T] is equivalent to [path_functor'_T], but unification is far too slow to do this effectively.  So instead we explicitly classify [path_functor'_T], and provide an equivalence between it and the path space of [Functor C D]. *)

  (**
<<
  Definition equiv_path_functor'_sig_sig (F G : Functor C D)
  : path_functor'_T F G <~> (@equiv_inv _ _ _ equiv_sig_functor F
                              = @equiv_inv _ _ _ equiv_sig_functor G).
  Proof.
    etransitivity; [ | by apply equiv_path_sigma ].
    eapply @equiv_functor_sigma.
    repeat match goal with
             | [ |- appcontext[(@equiv_inv ?A ?B ?f ?H ?F).1] ]
               => change ((@equiv_inv A B f H F).1) with (object_of F)
           end.
    Time exact (isequiv_idmap (object_of F = object_of G)). (* 13.411 secs *)
  Abort.
>>
   *)

  (** ** Classify sufficient conditions to prove functors equal *)
  Definition path_functor'_sig (F G : Functor C D) : path_functor'_T F G -> F = G.
  Proof.
    intros [? ?].
    destruct F, G; simpl in *.
    path_induction; simpl.
    f_ap;
      eapply @center; abstract exact _.
  Defined.

  (** *** Said proof respects [object_of] *)
  Lemma path_functor'_sig_fst F G HO HM
  : ap object_of (@path_functor'_sig F G (HO; HM)) = HO.
  Proof.
    destruct F, G; simpl in *.
    path_induction_hammer.
  Qed.

  (** *** Said proof respects [idpath] *)
  Lemma path_functor'_sig_idpath F
  : @path_functor'_sig F F (idpath; idpath) = idpath.
  Proof.
    destruct F; simpl in *.
    rewrite !(contr idpath).
    reflexivity.
  Qed.

  (** ** Equality of functors gives rise to an inhabitant of the path-classifying-type *)
  Definition path_functor'_sig_inv (F G : Functor C D) : F = G -> path_functor'_T F G
    := fun H'
       => (ap object_of H';
           (transport_compose _ object_of _ _) ^ @ apD (@morphism_of _ _) H')%path.

  (** ** Curried version of path classifying lemma *)
  Lemma path_functor' (F G : Functor C D)
  : forall HO : object_of F = object_of G,
      transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d)) HO (morphism_of F) = morphism_of G
      -> F = G.
  Proof.
    intros.
    apply path_functor'_sig.
    esplit; eassumption.
  Defined.

  (** ** Curried version of path classifying lemma, using [forall] in place of equality of functions *)
  Lemma path_functor (F G : Functor C D)
  : forall HO : object_of F == object_of G,
      (forall s d m,
         transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d))
                   (path_forall _ _ HO)
                   (morphism_of F)
                   s d m
         = morphism_of G m)
      -> F = G.
  Proof.
    intros.
    eapply (path_functor' F G (path_forall _ _ HO)).
    repeat (apply path_forall; intro); apply_hyp.
  Defined.

  (** ** Classify equality of functors up to equivalence *)
  Lemma equiv_path_functor'_sig (F G : Functor C D)
  : path_functor'_T F G <~> F = G.
  Proof.
    apply (equiv_adjointify (@path_functor'_sig F G)
                            (@path_functor'_sig_inv F G)).
    - hnf.
      intros [].
      apply path_functor'_sig_idpath.
    - hnf.
      intros [? ?].
      apply path_sigma_uncurried.
      exists (path_functor'_sig_fst _ _ _).
      exact (center _).
  Defined.

  (** ** If the objects in [D] are n-truncated, then so is the type of  functors [C → D] *)
  Global Instance trunc_functor `{IsTrunc n D} `{forall s d, IsTrunc n (morphism D s d)}
  : IsTrunc n (Functor C D).
  Proof.
    eapply trunc_equiv'; [ exact equiv_sig_functor | ].
    induction n;
    simpl; intros;
    typeclasses eauto.
  Qed.
End path_functor.

(** ** Tactic for proving equality of functors *)
Ltac path_functor :=
  repeat match goal with
           | _ => intro
           | _ => reflexivity
           | _ => apply path_functor'_sig; simpl
           | _ => (exists idpath)
         end.

Global Arguments path_functor'_sig : simpl never.

End Paths.

End Functor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Functor_DOT_Paths.

Module HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Module HoTT.
Module categories.
Module NaturalTransformation.
Module Core.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Definition of natural transformation *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Delimit Scope natural_transformation_scope with natural_transformation.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section NaturalTransformation.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely,
     given two functors [F : C -> D], [G : C -> D], a natural
     transformation [T: F -> G] is a collection of maps [T A : F A ->
     G A], one for each object [A] of [C], such that [(T B) ∘ (F m) =
     (G m) ∘ (T A)] for every map [m : A -> B] of [C]; that is, the
     following diagram is commutative:

<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
>>
     **)

  Record NaturalTransformation :=
    Build_NaturalTransformation' {
        components_of :> forall c, morphism D (F c) (G c);
        commutes : forall s d (m : morphism C s d),
                     components_of d o F _1 m = G _1 m o components_of s;
        (* We require the following symmetrized version so that for eta-expanded [T], we have [(T^op)^op = T] judgementally. *)
        commutes_sym : forall s d (m : C.(morphism) s d),
                         G _1 m o components_of s = components_of d o F _1 m
      }.

  Definition Build_NaturalTransformation CO COM
    := Build_NaturalTransformation'
         CO
         COM
         (fun _ _ _ => symmetry _ _ (COM _ _ _)).
End NaturalTransformation.

Bind Scope natural_transformation_scope with NaturalTransformation.

Create HintDb natural_transformation discriminated.

Global Arguments components_of {C D}%category {F G}%functor T%natural_transformation
          c%object : rename, simpl nomatch.
Global Arguments commutes {C D F G} !T / _ _ _ : rename.
Global Arguments commutes_sym {C D F G} !T / _ _ _ : rename.

Hint Resolve @commutes : category natural_transformation.

(** ** Helper lemmas *)
(** Some helper lemmas for rewriting.  In the names, [p] stands for a
    morphism, [T] for natural transformation, and [F] for functor. *)
Definition commutes_pT_F C D (F G : Functor C D) (T : NaturalTransformation F G)
      s d d' (m : morphism C s d) (m' : morphism D _ d')
: (m' o T d) o F _1 m = (m' o G _1 m) o T s
  := ((Category.Core.associativity _ _ _ _ _ _ _ _)
        @ ap _ (commutes _ _ _ _)
        @ (Category.Core.associativity_sym _ _ _ _ _ _ _ _))%path.

Definition commutes_T_Fp C D (F G : Functor C D) (T : NaturalTransformation F G)
      s d d' (m : morphism C s d) (m' : morphism D d' _)
: T d o (F _1 m o m') = G _1 m o (T s o m')
  := ((Category.Core.associativity_sym _ _ _ _ _ _ _ _)
        @ ap10 (ap _ (commutes _ _ _ _)) _
        @ (Category.Core.associativity _ _ _ _ _ _ _ _))%path.

End Core.

End NaturalTransformation.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.

Module HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Module HoTT.
Module categories.
Module NaturalTransformation.
Module Composition.
Module Core.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Composition of natural transformations *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

(** ** Vertical composition *)
Section composition.
  (**
     We have the diagram
<<
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''
>>

     And we want the commutative diagram
<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B
>>
  *)

  Section compose.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variables F F' F'' : Functor C D.

    Variable T' : NaturalTransformation F' F''.
    Variable T : NaturalTransformation F F'.

    Local Notation CO c := (T' c o T c).

    Definition compose_commutes s d (m : morphism C s d)
    : CO d o morphism_of F m = morphism_of F'' m o CO s
      := (associativity _ _ _ _ _ _ _ _)
           @ ap (fun x => _ o x) (commutes T _ _ m)
           @ (associativity_sym _ _ _ _ _ _ _ _)
           @ ap (fun x => x o _) (commutes T' _ _ m)
           @ (associativity _ _ _ _ _ _ _ _).

    (** We define the symmetrized version separately so that we can get more unification in the functor [(C → D)ᵒᵖ → (Cᵒᵖ → Dᵒᵖ)] *)
    Definition compose_commutes_sym s d (m : morphism C s d)
    : morphism_of F'' m o CO s = CO d o morphism_of F m
      := (associativity_sym _ _ _ _ _ _ _ _)
           @ ap (fun x => x o _) (commutes_sym T' _ _ m)
           @ (associativity _ _ _ _ _ _ _ _)
           @ ap (fun x => _ o x) (commutes_sym T _ _ m)
           @ (associativity_sym _ _ _ _ _ _ _ _).

    Global Arguments compose_commutes : simpl never.
    Global Arguments compose_commutes_sym : simpl never.

    Definition compose
    : NaturalTransformation F F''
      := Build_NaturalTransformation' F F''
                                      (fun c => CO c)
                                      compose_commutes
                                      compose_commutes_sym.
  End compose.

  (** ** Whiskering *)
  Local Ltac whisker_t :=
    simpl;
    repeat first [ apply commutes
                 | apply ap
                 | progress (etransitivity; try apply composition_of); []
                 | progress (etransitivity; try (symmetry; apply composition_of)); [] ].

  Section whisker.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.

    Section L.
      Variable F : Functor D E.
      Variables G G' : Functor C D.
      Variable T : NaturalTransformation G G'.

      Local Notation CO c := (morphism_of F (T c)).

      Definition whisker_l_commutes s d (m : morphism C s d)
      : F _1 (T d) o (F o G) _1 m = (F o G') _1 m o F _1 (T s).
      Proof.
        whisker_t.
      Defined.

      Global Arguments whisker_l_commutes : simpl never.

      Definition whisker_l
        := Build_NaturalTransformation
             (F o G) (F o G')
             (fun c => CO c)
             whisker_l_commutes.
    End L.

    Section R.
      Variables F F' : Functor D E.
      Variable T : NaturalTransformation F F'.
      Variable G : Functor C D.

      Local Notation CO c := (T (G c)).

      Definition whisker_r_commutes s d (m : morphism C s d)
      : T (G d) o (F o G) _1 m = (F' o G) _1 m o T (G s).
      Proof.
        whisker_t.
      Defined.

      Global Arguments whisker_r_commutes : simpl never.

      Definition whisker_r
        := Build_NaturalTransformation
             (F o G) (F' o G)
             (fun c => CO c)
             whisker_r_commutes.
    End R.
  End whisker.
End composition.

Module Export NaturalTransformationCompositionCoreNotations.
  Infix "o" := compose : natural_transformation_scope.
  Infix "oL" := whisker_l (at level 40, left associativity) : natural_transformation_scope.
  Infix "oR" := whisker_r (at level 40, left associativity) : natural_transformation_scope.
End NaturalTransformationCompositionCoreNotations.

End Core.

End Composition.

End NaturalTransformation.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.

Module HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.
Module HoTT.
Module categories.
Module NaturalTransformation.
Module Paths.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Classify the path space of natural transformations *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core.
Import HoTT_DOT_Equivalences.HoTT.Equivalences HoTT_DOT_types_DOT_Sigma.HoTT.types.Sigma HoTT_DOT_Trunc.HoTT.Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section path_natural_transformation.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  Local Open Scope equiv_scope.

  (** ** Equivalence between record and sigma versions of natural transformation *)
  Lemma equiv_sig_natural_transformation
  : { CO : forall x, morphism D (F x) (G x)
    | forall s d (m : morphism C s d),
        CO d o F _1 m = G _1 m o CO s }
      <~> NaturalTransformation F G.
  Proof.
    let build := constr:(@Build_NaturalTransformation _ _ F G) in
    let pr1 := constr:(@components_of _ _ F G) in
    let pr2 := constr:(@commutes _ _ F G) in
    apply (equiv_adjointify (fun u => build u.1 u.2)
                            (fun v => (pr1 v; pr2 v)));
      hnf;
      [ intros []; intros; simpl; expand; f_ap; exact (center _)
      | intros; apply eta_sigma ].
  Defined.

  (** ** The type of natural transformations is an hSet *)
  Global Instance trunc_natural_transformation
  : IsHSet (NaturalTransformation F G).
  Proof.
    eapply trunc_equiv'; [ exact equiv_sig_natural_transformation | ].
    typeclasses eauto.
  Qed.

  Section path.
    Variables T U : NaturalTransformation F G.

    (** ** Equality of natural transformations is implied by equality of components *)
    Lemma path'_natural_transformation
    : components_of T = components_of U
      -> T = U.
    Proof.
      intros.
      destruct T, U; simpl in *.
      path_induction.
      f_ap;
        refine (center _).
    Qed.

    Lemma path_natural_transformation
    : components_of T == components_of U
      -> T = U.
    Proof.
      intros.
      apply path'_natural_transformation.
      apply path_forall; assumption.
    Qed.

    Let path_inv
    : T = U -> components_of T == components_of U
      := (fun H _ => match H with idpath => idpath end).

    Lemma eisretr_path_natural_transformation
    : Sect path_natural_transformation path_inv.
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    Lemma eissect_path_natural_transformation
    : Sect path_inv path_natural_transformation.
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    Lemma eisadj_path_natural_transformation
    : forall x,
        @eisretr_path_natural_transformation (path_inv x)
        = ap path_inv (eissect_path_natural_transformation x).
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    (** ** Equality of natural transformations is equivalent to equality of components *)
    Lemma equiv_path_natural_transformation
    : T = U <~> (components_of T == components_of U).
    Proof.
      econstructor. econstructor. exact eisadj_path_natural_transformation.
    Defined.
  End path.
End path_natural_transformation.

(** ** Tactic for proving equality of natural transformations *)
Ltac path_natural_transformation :=
  repeat match goal with
           | _ => intro
           | _ => apply path_natural_transformation; simpl
         end.

End Paths.

End NaturalTransformation.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.

Module HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.
Module HoTT.
Module categories.
Module NaturalTransformation.
Module Identity.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Identity natural transformation *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.Paths.
Import HoTT_DOT_PathGroupoids.HoTT.PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope path_scope.
Local Open Scope natural_transformation_scope.

Section identity.
  Variable C : PreCategory.
  Variable D : PreCategory.

  (** There is an identity natrual transformation.  We create a number
      of variants, for various uses. *)
  Section generalized.
    Variables F G : Functor C D.
    Hypothesis HO : object_of F = object_of G.
    Hypothesis HM : transport (fun GO => forall s d,
                                           morphism C s d
                                           -> morphism D (GO s) (GO d))
                              HO
                              (morphism_of F)
                    = morphism_of G.

    Local Notation CO c := (transport (fun GO => morphism D (F c) (GO c))
                                      HO
                                      (identity (F c))).

    Definition generalized_identity_commutes s d (m : morphism C s d)
    : CO d o morphism_of F m = morphism_of G m o CO s.
    Proof.
      case HM. case HO.
      exact (left_identity _ _ _ _ @ (right_identity _ _ _ _)^).
    Defined.

    Definition generalized_identity_commutes_sym s d (m : morphism C s d)
    : morphism_of G m o CO s = CO d o morphism_of F m.
    Proof.
      case HM. case HO.
      exact (right_identity _ _ _ _ @ (left_identity _ _ _ _)^).
    Defined.

    Definition generalized_identity
    : NaturalTransformation F G
      := Build_NaturalTransformation'
           F G
           (fun c => CO c)
           generalized_identity_commutes
           generalized_identity_commutes_sym.
  End generalized.

  Global Arguments generalized_identity_commutes / .
  Global Arguments generalized_identity_commutes_sym / .
  Global Arguments generalized_identity F G !HO !HM / .

  Section generalized'.
    Variables F G : Functor C D.
    Hypothesis H : F = G.

    Definition generalized_identity'
    : NaturalTransformation F G.
    Proof.
      apply (generalized_identity
               F G
               (ap (@object_of C D) H)).
      case H.
      reflexivity.
    Defined.
  End generalized'.

  Definition identity (F : Functor C D)
  : NaturalTransformation F F
    := Eval simpl in @generalized_identity F F 1 1.

  Global Arguments generalized_identity' F G !H / .
End identity.

Global Arguments generalized_identity_commutes : simpl never.
Global Arguments generalized_identity_commutes_sym : simpl never.

Module Export NaturalTransformationIdentityNotations.
  Notation "1" := (identity _) : natural_transformation_scope.
End NaturalTransformationIdentityNotations.

End Identity.

End NaturalTransformation.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.

Module HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.
Module HoTT.
Module categories.
Module NaturalTransformation.
Module Composition.
Module Laws.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Laws about composition of functors *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.Identity HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.NaturalTransformation.Identity HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section natural_transformation_identity.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  (** ** left identity : [1 ∘ T = T] *)
  Lemma left_identity (F F' : Functor C D)
        (T : NaturalTransformation F F')
  : 1 o T = T.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  (** ** right identity : [T ∘ 1 = T] *)
  Lemma right_identity (F F' : Functor C D)
        (T : NaturalTransformation F F')
  : T o 1 = T.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  (** ** right whisker left identity : [1 ∘ᴿ F = 1] *)
  Definition whisker_r_left_identity E
             (G : Functor D E) (F : Functor C D)
  : identity G oR F = 1.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  (** ** left whisker right identity : [G ∘ᴸ 1 = 1] *)
  Definition whisker_l_right_identity E
             (G : Functor D E) (F : Functor C D)
  : G oL identity F = 1.
  Proof.
    path_natural_transformation; auto with functor.
  Qed.
End natural_transformation_identity.

Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : natural_transformation.

Section whisker.
  Context `{H0 : Funext}.

  (** ** whisker exchange law : [(G' ∘ᴸ T) ∘ (T' ∘ᴿ F) = (T' ∘ᴿ F') ∘ (G ∘ᴸ T)] *)
  Section exch.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.
    Variables G G' : Functor D E.
    Variables F F' : Functor C D.
    Variable T' : NaturalTransformation G G'.
    Variable T : NaturalTransformation F F'.

    Lemma exchange_whisker
    : (G' oL T) o (T' oR F) = (T' oR F') o (G oL T).
    Proof.
      path_natural_transformation; simpl.
      symmetry.
      apply NaturalTransformation.Core.commutes.
    Qed.
  End exch.

  Section whisker.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variables F G H : Functor C D.
    Variable T : NaturalTransformation G H.
    Variable T' : NaturalTransformation F G.

    (** ** left whisker composition : [F ∘ᴸ (T ∘ T') = (F ∘ᴸ T) ∘ (F ∘ᴸ T')] *)
    Lemma composition_of_whisker_l E (I : Functor D E)
    : I oL (T o T') = (I oL T) o (I oL T').
    Proof.
      path_natural_transformation; apply composition_of.
    Qed.

    (** ** right whisker composition : [(T ∘ T') ∘ᴿ F = (T ∘ᴿ F) ∘ (T' ∘ᴿ F)] *)
    Lemma composition_of_whisker_r B (I : Functor B C)
    : (T o T') oR I = (T oR I) o (T' oR I).
    Proof.
      path_natural_transformation; apply idpath.
    Qed.
  End whisker.
End whisker.

Section associativity.
  (** ** associators - natural transformations between [F ∘ (G ∘ H)] and [(F ∘ G) ∘ H] *)
  Section functors.
    Variable B : PreCategory.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.
    Variable F : Functor D E.
    Variable G : Functor C D.
    Variable H : Functor B C.

    Local Notation F0 := ((F o G) o H)%functor.
    Local Notation F1 := (F o (G o H))%functor.

    Definition associator_1 : NaturalTransformation F0 F1
      := Eval simpl in
          generalized_identity F0 F1 idpath idpath.

    Definition associator_2 : NaturalTransformation F1 F0
      := Eval simpl in
          generalized_identity F1 F0 idpath idpath.
  End functors.

  (** ** associativity : [(T ∘ U) ∘ V = T ∘ (U ∘ V)] *)
  Section nt.
    Context `{H0 : Funext}.

    Local Open Scope natural_transformation_scope.

    Definition associativity
               C D F G H I
               (V : @NaturalTransformation C D F G)
               (U : @NaturalTransformation C D G H)
               (T : @NaturalTransformation C D H I)
    : (T o U) o V = T o (U o V).
    Proof.
      path_natural_transformation.
      apply associativity.
    Qed.
  End nt.
End associativity.

Section functor_identity.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Ltac nt_id_t := split; path_natural_transformation;
                        autorewrite with morphism; reflexivity.

  (** ** left unitors : natural transformations between [1 ∘ F] and [F] *)
  Section left.
    Variable F : Functor D C.

    Definition left_identity_natural_transformation_1
    : NaturalTransformation (1 o F) F
      := Eval simpl in generalized_identity (1 o F) F idpath idpath.
    Definition left_identity_natural_transformation_2
    : NaturalTransformation F (1 o F)
      := Eval simpl in generalized_identity F (1 o F) idpath idpath.

    Theorem left_identity_isomorphism
    : ((left_identity_natural_transformation_1 o left_identity_natural_transformation_2 = 1)
      * (left_identity_natural_transformation_2 o left_identity_natural_transformation_1 = 1))%type.
    Proof.
      nt_id_t.
    Qed.
  End left.

  (** ** right unitors : natural transformations between [F ∘ 1] and [F] *)
  Section right.
    Variable F : Functor C D.

    Definition right_identity_natural_transformation_1 : NaturalTransformation (F o 1) F
      := Eval simpl in generalized_identity (F o 1) F idpath idpath.
    Definition right_identity_natural_transformation_2 : NaturalTransformation F (F o 1)
      := Eval simpl in generalized_identity F (F o 1) idpath idpath.

    Theorem right_identity_isomorphism
    : ((right_identity_natural_transformation_1 o right_identity_natural_transformation_2 = 1)
      * (right_identity_natural_transformation_2 o right_identity_natural_transformation_1 = 1))%type.
    Proof.
      nt_id_t.
    Qed.
  End right.
End functor_identity.

(** ** Tactics for inserting appropriate associators, whiskers, and unitors *)
Ltac nt_solve_associator' :=
  repeat match goal with
           | _ => exact (associator_1 _ _ _)
           | _ => exact (associator_2 _ _ _)
           | _ => exact (left_identity_natural_transformation_1 _)
           | _ => exact (left_identity_natural_transformation_2 _)
           | _ => exact (right_identity_natural_transformation_1 _)
           | _ => exact (right_identity_natural_transformation_2 _)
           | [ |- NaturalTransformation (?F o _) (?F o _) ] =>
             refine (whisker_l F _)
           | [ |- NaturalTransformation (_ o ?F) (_ o ?F) ] =>
             refine (whisker_r _ F)
         end.
Ltac nt_solve_associator :=
  repeat match goal with
           | _ => refine (compose (associator_1 _ _ _) _); progress nt_solve_associator'
           | _ => refine (compose _ (associator_1 _ _ _)); progress nt_solve_associator'
           | _ => refine (compose (associator_2 _ _ _) _); progress nt_solve_associator'
           | _ => refine (compose _ (associator_2 _ _ _)); progress nt_solve_associator'
           | _ => progress nt_solve_associator'
         end.

End Laws.

End Composition.

End NaturalTransformation.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.

Module HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.
Module HoTT.
Module categories.
Module FunctorCategory.
Module Core.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Functor category [D → C] (also [Cᴰ] and [[D, C]]) *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.Strict HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.Paths.
(** These must come last, so that [identity], [compose], etc., refer to natural transformations. *)
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.NaturalTransformation.Identity HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.Composition.Laws.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

(** ** Definition of [C → D] *)
Section functor_category.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  (** There is a category Fun(C, D) of functors from [C] to [D]. *)
  Definition functor_category : PreCategory
    := @Build_PreCategory (Functor C D)
                          (@NaturalTransformation C D)
                          (@identity C D)
                          (@compose C D)
                          (@associativity _ C D)
                          (@left_identity _ C D)
                          (@right_identity _ C D)
                          _.
End functor_category.

Local Notation "C -> D" := (functor_category C D) : category_scope.

(** ** [C → D] is a strict category if [D] is *)
Lemma isstrict_functor_category `{Funext} C `{IsStrictCategory D}
: IsStrictCategory (C -> D).
Proof.
  typeclasses eauto.
Defined.

Module Export FunctorCategoryCoreNotations.
  (*Notation "C ^ D" := (functor_category D C) : category_scope.
  Notation "[ C , D ]" := (functor_category C D) : category_scope.*)
  Notation "C -> D" := (functor_category C D) : category_scope.
End FunctorCategoryCoreNotations.

End Core.

End FunctorCategory.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.

Module HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.
Module HoTT.
Module categories.
Module FunctorCategory.
Module Morphisms.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Morphisms in a functor category *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.Paths HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.Core HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.Morphisms HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Natural Isomorphisms - isomorphisms in a functor category *)
Definition NaturalIsomorphism `{Funext} (C D : PreCategory) F G :=
  @Isomorphic (C -> D) F G.

Arguments NaturalIsomorphism {_} [C D] F G / .

Global Instance reflexive_natural_isomorphism `{Funext} C D
: Reflexive (@NaturalIsomorphism _ C D) | 0
  := _.

Coercion natural_transformation_of_natural_isomorphism `{Funext} C D F G
         (T : @NaturalIsomorphism _ C D F G)
: NaturalTransformation F G
  := T : morphism _ _ _.

Local Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.

(** ** If [T] is an isomorphism, then so is [T x] for any [x] *)
Definition isisomorphism_components_of `{Funext}
           `{@IsIsomorphism (C -> D) F G T} x
: IsIsomorphism (T x).
Proof.
  exists (T^-1 x).
  - exact (apD10 (ap components_of left_inverse) x).
  - exact (apD10 (ap components_of right_inverse) x).
Defined.

Hint Immediate isisomorphism_components_of : typeclass_instances.
(** When one of the functors is the identity functor, we fail to match correctly, because [apply] is stupid.  So we do its work for it. *)
Hint Extern 10 (@IsIsomorphism _ _ _ (@components_of ?C ?D ?F ?G ?T ?x))
=> apply (fun H' => @isisomorphism_components_of _ C D F G T H' x)
   : typeclass_instances.

Definition inverse `{Funext}
           C D (F G : Functor C D) (T : NaturalTransformation F G)
           `{forall x, IsIsomorphism (T x)}
: NaturalTransformation G F.
Proof.
  exists (fun x => (T x)^-1);
  abstract (
      intros;
      iso_move_inverse;
      first [ apply commutes
            | symmetry; apply commutes ]
    ).
Defined.

(** ** If [T x] is an isomorphism for all [x], then so is [T] *)
Definition isisomorphism_natural_transformation `{Funext}
           C D F G (T : NaturalTransformation F G)
           `{forall x, IsIsomorphism (T x)}
: @IsIsomorphism (C -> D) F G T.
Proof.
  exists (inverse _);
  abstract (
      path_natural_transformation;
      first [ apply left_inverse
            | apply right_inverse ]
    ).
Defined.

Hint Immediate isisomorphism_natural_transformation : typeclass_instances.

(** ** Variant of [idtoiso] for natural transformations *)
Section idtoiso.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition idtoiso_natural_transformation
             (F G : object (C -> D))
             (T : F = G)
  : NaturalTransformation F G.
  Proof.
    refine (Build_NaturalTransformation'
              F G
              (fun x => idtoiso _ (ap10 (ap object_of T) x))
              _
              _);
    intros; case T; simpl;
    [ exact (left_identity _ _ _ _ @ (right_identity _ _ _ _)^)
    | exact (right_identity _ _ _ _ @ (left_identity _ _ _ _)^) ].
  Defined.

  Definition idtoiso
             (F G : object (C -> D))
             (T : F = G)
  : F <~=~> G.
  Proof.
    exists (idtoiso_natural_transformation T).
    exists (idtoiso_natural_transformation (T^)%path);
      abstract (path_natural_transformation; case T; simpl; auto with morphism).
  Defined.

  Lemma eta_idtoiso
        (F G : object (C -> D))
        (T : F = G)
  : Morphisms.idtoiso _ T = idtoiso T.
  Proof.
    case T.
    expand; f_ap.
    exact (center _).
  Qed.
End idtoiso.

Module Export FunctorCategoryMorphismsNotations.
  Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.
End FunctorCategoryMorphismsNotations.

End Morphisms.

End FunctorCategory.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.

Module HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.
Module HoTT.
Module categories.
Module NaturalTransformation.
Module Isomorphisms.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.FunctorCategory.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Natural isomorphisms *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.Morphisms HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.FunctorCategory.Morphisms.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.


Local Ltac iso_whisker_t :=
  path_natural_transformation;
  try rewrite <- composition_of, <- identity_of;
  try f_ap;
  match goal with
    | [ H : IsIsomorphism _
        |- appcontext[components_of ?T0 ?x o components_of ?T1 ?x] ]
      => change (T0 x o T1 x)
         with (components_of ((T0 : morphism (_ -> _) _ _)
                                o (T1 : morphism (_ -> _) _ _))%morphism
                             x);
        progress rewrite ?(@left_inverse _ _ _ _ H), ?(@right_inverse _ _ _ _ H)
  end;
  reflexivity.

Section composition.
  Context `{Funext}.

  (** ** Natural isomorphism respects composition *)
  Global Instance isisomorphism_compose
         `(T' : @NaturalTransformation C D F' F'')
         `(T : @NaturalTransformation C D F F')
         `{@IsIsomorphism (C -> D) F' F'' T'}
         `{@IsIsomorphism (C -> D) F F' T}
  : @IsIsomorphism (C -> D) F F'' (T' o T)%natural_transformation
    := @isisomorphism_compose (C -> D) _ _ T' _ _ T _.

  (** ** Left whiskering preserves natural isomorphisms *)
  Global Instance iso_whisker_l C D E
         (F : Functor D E)
         (G G' : Functor C D)
         (T : NaturalTransformation G G')
         `{@IsIsomorphism (C -> D) G G' T}
  : @IsIsomorphism (C -> E) (F o G)%functor (F o G')%functor (whisker_l F T).
  Proof.
    exists (whisker_l F (T : morphism (_ -> _) _ _)^-1);
    abstract iso_whisker_t.
  Defined.

  (** ** Right whiskering preserves natural isomorphisms *)
  Global Instance iso_whisker_r C D E
         (F F' : Functor D E)
         (T : NaturalTransformation F F')
         (G : Functor C D)
         `{@IsIsomorphism (D -> E) F F' T}
  : @IsIsomorphism (C -> E) (F o G)%functor (F' o G)%functor (whisker_r T G).
  Proof.
    exists (whisker_r (T : morphism (_ -> _) _ _)^-1 G);
    abstract iso_whisker_t.
  Defined.

  (** ** action of [idtoiso] on objects *)
  Definition idtoiso_components_of C D
             (F G : Functor C D)
             (T' : F = G)
             x
  : (Category.Morphisms.idtoiso (_ -> _) T' : morphism _ _ _) x
    = Category.Morphisms.idtoiso _ (ap10 (ap object_of T') x).
  Proof.
    destruct T'.
    reflexivity.
  Defined.

  (** ** [idtoiso] respsects composition *)
  Definition idtoiso_compose C D
         (F F' F'' : Functor C D)
         (T' : F' = F'')
         (T : F = F')
  : ((Category.Morphisms.idtoiso (_ -> _) T' : morphism _ _ _)
       o (Category.Morphisms.idtoiso (_ -> _) T : morphism _ _ _))%natural_transformation
    = (Category.Morphisms.idtoiso (_ -> _) (T @ T')%path : morphism _ _ _).
  Proof.
    path_natural_transformation; path_induction; simpl; auto with morphism.
  Defined.

  (** ** left whiskering respects [idtoiso] *)
  Definition idtoiso_whisker_l C D E
         (F : Functor D E)
         (G G' : Functor C D)
         (T : G = G')
  : whisker_l F (Category.Morphisms.idtoiso (_ -> _) T : morphism _ _ _)
    = (Category.Morphisms.idtoiso (_ -> _) (ap _ T) : morphism _ _ _).
  Proof.
    path_natural_transformation; path_induction; simpl; auto with functor.
  Defined.

  (** ** right whiskering respects [idtoiso] *)
  Definition idtoiso_whisker_r C D E
         (F F' : Functor D E)
         (T : F = F')
         (G : Functor C D)
  : whisker_r (Category.Morphisms.idtoiso (_ -> _) T : morphism _ _ _) G
    = (Category.Morphisms.idtoiso (_ -> _) (ap (fun _ => _ o _)%functor T) : morphism _ _ _).
  Proof.
    path_natural_transformation; path_induction; simpl; auto with functor.
  Defined.
End composition.

(** ** Equalities induced by isomorphisms of objects *)
Section object_isomorphisms.
  Lemma path_components_of_isisomorphism
        `{IsIsomorphism C s d m}
        D (F G : Functor C D) (T : NaturalTransformation F G)
  : (G _1 m)^-1 o (T d o F _1 m) = T s.
  Proof.
    apply iso_moveR_Vp.
    apply commutes.
  Qed.

  Lemma path_components_of_isisomorphism'
        `{IsIsomorphism C s d m}
        D (F G : Functor C D) (T : NaturalTransformation F G)
  : (G _1 m o T s) o (F _1 m)^-1 = T d.
  Proof.
    apply iso_moveR_pV.
    symmetry.
    apply commutes.
  Qed.

  Definition path_components_of_isomorphic
             `(m : @Isomorphic C s d)
             D (F G : Functor C D) (T : NaturalTransformation F G)
  : (G _1 m)^-1 o (T d o F _1 m) = T s
    := @path_components_of_isisomorphism _ _ _ m m D F G T.

  Definition path_components_of_isomorphic'
             `(m : @Isomorphic C s d)
             D (F G : Functor C D) (T : NaturalTransformation F G)
  : (G _1 m o T s) o (F _1 m)^-1 = T d
    := @path_components_of_isisomorphism' _ _ _ m m D F G T.
End object_isomorphisms.

End Isomorphisms.

End NaturalTransformation.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.

Module HoTT_DOT_categories_DOT_Pseudofunctor_DOT_Core.
Module HoTT.
Module categories.
Module Pseudofunctor.
Module Core.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.FunctorCategory.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Pseudofunctors *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.Morphisms HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.FunctorCategory.Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.Core HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.Identity.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.Composition.Laws.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.HoTT.categories.NaturalTransformation.Isomorphisms.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.Paths.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section pseudofunctor.
  Local Open Scope natural_transformation_scope.
  Context `{Funext}.

  Variable C : PreCategory.

  (** Quoting from nCatLab (http://ncatlab.org/nlab/show/pseudofunctor):

      Given bicategories [C] and [D], a pseudofunctor (or weak 2-functor,
      or just functor) [P : C → D] consists of:

      - for each object [x] of [C], an object [P_x] of [D];

      - for each hom-category [C(x,y)] in [C], a functor [P_{x,y} :
        C(x,y) → D(P_x, P_y)];

      - for each object [x] of [C], an invertible 2-morphism (2-cell)
        [P_{id_x} : id_{P_x} ⇒ P_{x,x}(id_x)];

      - for each triple [x],[y],[z] of [C]-objects, a isomorphism
        (natural in [f : x → y] and [g : y → z]) [P_{x,y,z}(f,g) :
        P_{x,y}(f);P_{y,z}(g) ⇒ P_{x,z}(f;g)];

      - for each hom-category [C(x,y)],
<<
                                    id_{Pₓ} ; P_{x, y}(f)
                                      //              \\
                                    //                  \\
        P_{idₓ} ; id_{P_{x,y}(f)} //                      \\  λ_{P_{x,y}(f)}
                                //                          \\
                               ⇙                              ⇘
              Pₓ,ₓ(idₓ) ; P_{x,y}(f)                       P_{x,y}(f)
                               \\                             ⇗
                                 \\                         //
                P_{x,x,y}(idₓ, f)  \\                     // P_{x,y}(λ_f)
                                     \\                 //
                                       ⇘              //
                                        P_{x,y}(idₓ ; f)
>>

        and

<<
                                    P_{x, y}(f) ; id_{P_y}
                                      //              \\
                                    //                  \\
       id_{P_{x,y}(f)} ; P_{id_y} //                      \\  ρ_{P_{x,y}(f)}
                                //                          \\
                               ⇙                              ⇘
              P_{x,y}(f) ; P_{y,y}(id_y)                   P_{x,y}(f)
                               \\                             ⇗
                                 \\                         //
                P_{x,y,y}(f, id_y) \\                     // P_{x,y}(ρ_f)
                                     \\                 //
                                       ⇘              //
                                       P_{x,y}(f ; id_y)
>>
        commute; and

      - for each quadruple [w],[x],[y],[z] of [C]-objects,
<<
                                                  α_{P_{w,x}(f),P_{x,y}(g),P_{y,z}(h)}
        (P_{w,x}(f) ; P_{x,y}(g)) ; P_{y,z}(h) ========================================⇒ P_{w,x}(f) ; (P_{x,y}(g) ; P_{y,z}(h))
                                         ∥                                                   ∥
                                         ∥                                                   ∥
        P_{w,x,y}(f,g) ; id_{P_{y,z}(h)} ∥                                                   ∥ id_{P_{w,x}(f)} ; P_{x,y,z}(g, h)
                                         ∥                                                   ∥
                                         ⇓                                                   ⇓
                   P_{w,y}(f ; g) ; P_{y,z}(h)                                           P_{w,x}(f) ; P_{x,z}(g ; h)
                                         ∥                                                   ∥
                                         ∥                                                   ∥
                     P_{w,y,z}(f ; g, h) ∥                                                   ∥ P_{w,x,z}(f, g ; h)
                                         ∥                                                   ∥
                                         ⇓                                                   ⇓
                          P_{w,z}((f ; g) ; h) ========================================⇒ P_{w,z}(f ; (g ; h))
                                                          P_{w,z}(α_{f,g,h})
>>
        commutes.
*)

  (* To obtain the [p_composition_of_coherent] type, I ran
<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (w x y z : C) (f : morphism C w x) (g : morphism C x y) (h : morphism C y z), Type.
  Proof.
    intros.
    pose ((idtoiso (_ -> _) (ap (p_morphism_of F w z) (associativity C _ _ _ _ f g h))) : morphism _ _ _).
    pose ((p_composition_of F w y z h (g ∘ f)) : NaturalTransformation _ _).
    pose (p_morphism_of F y z h ∘ p_composition_of F w x y g f).

    pose (associator_1 (p_morphism_of F y z h) (p_morphism_of F x y g) (p_morphism_of F w x f)).
    pose (p_composition_of F x y z h g ∘ p_morphism_of F w x f).
    pose ((p_composition_of F w x z (h ∘ g) f) : NaturalTransformation _ _).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>

<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (x y : C) (f : morphism C x y), Type.
  Proof.
    intros.
    pose (p_identity_of F y ∘ p_morphism_of F x y f).
    pose (p_composition_of F x y y (Identity y) f : NaturalTransformation _ _).
    pose (idtoiso (_ -> _) (ap (p_morphism_of F x y) (left_identity _ _ _ f)) : morphism _ _ _).
    pose (left_identity_natural_transformation_2 (p_morphism_of F x y f)).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>

<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (x y : C) (f : morphism C x y), Type.
  Proof.
    intros.
    pose (p_morphism_of F x y f ∘ p_identity_of F x).
    pose (p_composition_of F x x y f (Identity x) : NaturalTransformation _ _).
    pose (idtoiso (_ -> _) (ap (p_morphism_of F x y) (right_identity _ _ _ f)) : morphism _ _ _).
    pose (right_identity_natural_transformation_2 (p_morphism_of F x y f)).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>
 *)
  Time Record Pseudofunctor :=
    {
      p_object_of :> C -> PreCategory;
      p_morphism_of : forall s d, morphism C s d
                                  -> Functor (p_object_of s) (p_object_of d);
      p_composition_of : forall s d d'
                                (m1 : morphism C d d') (m2 : morphism C s d),
                           (p_morphism_of _ _ (m1 o m2))
                             <~=~> (p_morphism_of _ _ m1 o p_morphism_of _ _ m2)%functor;
      p_identity_of : forall x, p_morphism_of x x 1 <~=~> 1%functor;
      p_composition_of_coherent
      : forall w x y z
               (f : morphism C w x) (g : morphism C x y) (h : morphism C y z),
          ((associator_1 (p_morphism_of y z h) (p_morphism_of x y g) (p_morphism_of w x f))
             o ((p_composition_of x y z h g oR p_morphism_of w x f)
                  o (p_composition_of w x z (h o g) f)))
          = ((p_morphism_of y z h oL p_composition_of w x y g f)
               o ((p_composition_of w y z h (g o f))
                    o (Category.Morphisms.idtoiso (_ -> _) (ap (p_morphism_of w z) (Category.Core.associativity C w x y z f g h)) : morphism _ _ _)));
      p_left_identity_of_coherent
      : forall x y (f : morphism C x y),
          ((p_identity_of y oR p_morphism_of x y f)
             o p_composition_of x y y 1 f)
          = ((left_identity_natural_transformation_2 (p_morphism_of x y f))
               o (Category.Morphisms.idtoiso (_ -> _) (ap (p_morphism_of x y) (Category.Core.left_identity C x y f)) : morphism _ _ _));
      p_right_identity_of_coherent
      : forall x y (f : morphism C x y),
          ((p_morphism_of x y f oL p_identity_of x)
             o p_composition_of x x y f 1)
          = ((right_identity_natural_transformation_2 (p_morphism_of x y f))
               o (Category.Morphisms.idtoiso (_ -> _) (ap (p_morphism_of x y) (Category.Core.right_identity C x y f)) : morphism _ _ _))
    }. (* Finished transaction in 999.206 secs (998.952u,0.184s) (successful) *)
Time End pseudofunctor. (* Finished transaction in 981.981 secs (981.08u,0.488s) (successful) *)

Delimit Scope pseudofunctor_scope with pseudofunctor.
Bind Scope pseudofunctor_scope with Pseudofunctor.

Create HintDb pseudofunctor discriminated.

Arguments p_object_of {_} {C%category} F%pseudofunctor c%object : rename, simpl nomatch.
Arguments p_morphism_of {_} [C%category] F%pseudofunctor [s d]%object m%morphism : rename, simpl nomatch.

(*Notation "F ₀ x" := (p_object_of F x) : object_scope.
Notation "F ₁ m" := (p_morphism_of F m) : morphism_scope.*)

End Core.

End Pseudofunctor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Pseudofunctor_DOT_Core.

Module HoTT_DOT_categories_DOT_Pseudofunctor_DOT_RewriteLaws.
Module HoTT.
Module categories.
Module Pseudofunctor.
Module RewriteLaws.
Import HoTT_DOT_Overture.
Import HoTT_DOT_PathGroupoids.
Import HoTT_DOT_Contractible.
Import HoTT_DOT_Equivalences.
Import HoTT_DOT_types_DOT_Paths.
Import HoTT_DOT_types_DOT_Unit.
Import HoTT_DOT_Trunc.
Import HoTT_DOT_types_DOT_Forall.
Import HoTT_DOT_types_DOT_Prod.
Import HoTT_DOT_Tactics.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.
Import HoTT_DOT_types_DOT_Empty.
Import HoTT_DOT_types_DOT_Arrow.
Import HoTT_DOT_types_DOT_Sigma.
Import HoTT_DOT_types_DOT_Record.
Import HoTT_DOT_HProp.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.
Import HoTT_DOT_categories_DOT_Pseudofunctor_DOT_Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Pseudofunctor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.
Import HoTT_DOT_categories_DOT_Pseudofunctor_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Record.HoTT.
Import HoTT_DOT_types_DOT_Sigma.HoTT.
Import HoTT_DOT_types_DOT_Arrow.HoTT.
Import HoTT_DOT_types_DOT_Empty.HoTT.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.
Import HoTT_DOT_types_DOT_Prod.HoTT.
Import HoTT_DOT_types_DOT_Forall.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.
Import HoTT_DOT_types_DOT_Paths.HoTT.
Import HoTT_DOT_categories_DOT_Pseudofunctor_DOT_Core.HoTT.categories.Pseudofunctor.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.FunctorCategory.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Identity.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.
Import HoTT_DOT_categories_DOT_Functor_DOT_Paths.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Category_DOT_Strict.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.
Import HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.
Import HoTT_DOT_HProp.HoTT.
Import HoTT_DOT_types_DOT_Record.HoTT.types.
Import HoTT_DOT_types_DOT_Sigma.HoTT.types.
Import HoTT_DOT_types_DOT_Arrow.HoTT.types.
Import HoTT_DOT_types_DOT_Empty.HoTT.types.
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.
Import HoTT_DOT_Tactics.HoTT.
Import HoTT_DOT_types_DOT_Prod.HoTT.types.
Import HoTT_DOT_types_DOT_Forall.HoTT.types.
Import HoTT_DOT_Trunc.HoTT.
Import HoTT_DOT_types_DOT_Unit.HoTT.types.
Import HoTT_DOT_types_DOT_Paths.HoTT.types.
Import HoTT_DOT_Equivalences.HoTT.
Import HoTT_DOT_Contractible.HoTT.
Import HoTT_DOT_PathGroupoids.HoTT.
Import HoTT_DOT_Overture.HoTT.
(** * Pseudofunctor rewriting helper lemmas *)
Import HoTT_DOT_categories_DOT_Category_DOT_Core.HoTT.categories.Category.Core HoTT_DOT_categories_DOT_Functor_DOT_Core.HoTT.categories.Functor.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.HoTT.categories.NaturalTransformation.Core.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.Core.
Import HoTT_DOT_categories_DOT_Category_DOT_Morphisms.HoTT.categories.Category.Morphisms HoTT_DOT_categories_DOT_FunctorCategory_DOT_Morphisms.HoTT.categories.FunctorCategory.Morphisms.
Import HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.HoTT.categories.Functor.Composition.Core HoTT_DOT_categories_DOT_Functor_DOT_Identity.HoTT.categories.Functor.Identity.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.NaturalTransformation.Composition.Core HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Laws.HoTT.categories.NaturalTransformation.Composition.Laws.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Isomorphisms.HoTT.categories.NaturalTransformation.Isomorphisms.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Paths.HoTT.categories.NaturalTransformation.Paths.
Import HoTT_DOT_categories_DOT_FunctorCategory_DOT_Core.HoTT.categories.FunctorCategory.Core.
Import HoTT_DOT_categories_DOT_Pseudofunctor_DOT_Core.HoTT.categories.Pseudofunctor.Core.
Import HoTT_DOT_Tactics.HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section lemmas.
  Local Open Scope natural_transformation_scope.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable F : Pseudofunctor C.

  Lemma p_composition_of_coherent_for_rewrite_helper w x y z
        (f : morphism C w x) (g : morphism C x y) (h : morphism C y z)
        (p p0 p1 p2 : PreCategory) (f0 : morphism C w z -> Functor p2 p1)
        (f1 : Functor p0 p1) (f2 : Functor p2 p) (f3 : Functor p p0)
        (f4 : Functor p2 p0) `(@IsIsomorphism (_ -> _) f4 (f3 o f2)%functor n)
        `(@IsIsomorphism (_ -> _) (f0 (h o (g o f))%morphism) (f1 o f4)%functor n0)
  : @paths (NaturalTransformation _ _)
           (@morphism_isomorphic _ _ _ (Category.Morphisms.idtoiso (p2 -> p1) (ap f0 (Category.Core.associativity C w x y z f g h))))
           (n0^-1
              o ((f1 oL n^-1)
                   o ((f1 oL n)
                        o (n0
                             o (@morphism_isomorphic _ _ _ (Category.Morphisms.idtoiso (p2 -> p1) (ap f0 (Category.Core.associativity C w x y z f g h))))))))%natural_transformation.
  Proof.
    simpl in *.
    let C := match goal with |- @paths (@NaturalTransformation ?C ?D ?F ?G) _ _ => constr:(C -> D)%category end in
    apply (@iso_moveL_Vp C);
      apply (@iso_moveL_Mp C _ _ _ _ _ _ (iso_whisker_l _ _ _ _ _ _ _)).
    path_natural_transformation.
    reflexivity.
  Qed.

  Arguments p_composition_of_coherent_for_rewrite_helper {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

  Section helper.
    Context
      {w x y z}
      {f : Functor (F w) (F z)} {f0 : Functor (F w) (F y)}
      {f1 : Functor (F x) (F y)} {f2 : Functor (F y) (F z)}
      {f3 : Functor (F w) (F x)} {f4 : Functor (F x) (F z)}
      {f5 : Functor (F w) (F z)} {n : f5 <~=~> (f4 o f3)%functor}
      {n0 : f4 <~=~> (f2 o f1)%functor} {n1 : f0 <~=~> (f1 o f3)%functor}
      {n2 : f <~=~> (f2 o f0)%functor}.

    Lemma p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper'
    : @IsIsomorphism
        (_ -> _) _ _
        (n2 ^-1 o (f2 oL n1 ^-1 o (associator_1 f2 f1 f3 o (n0 oR f3 o n))))%natural_transformation.
    Proof.
      eapply isisomorphism_compose;
      [ eapply isisomorphism_inverse
      | eapply isisomorphism_compose;
        [ eapply iso_whisker_l; eapply isisomorphism_inverse
        | eapply isisomorphism_compose;
          [ typeclasses eauto
          | eapply isisomorphism_compose;
            [ eapply iso_whisker_r; typeclasses eauto
            | typeclasses eauto ] ] ] ].
    Defined.

    Definition p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper
      := Eval hnf in p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper'.

    Local Arguments p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper / .
    Let inv := Eval simpl in @morphism_inverse _ _ _ _ p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper.

    Definition p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper__to_inverse
          X
          (H' : X = @Build_Isomorphic (_ -> _) _ _ _ p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper)
    : @morphism_inverse _ _ _ _ X = inv.
    Proof.
      refine (ap (fun i => @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i)) H' @ _)%path.
      reflexivity. (** Why is [exact idpath] slow? *)
    Defined.
  End helper.

  Lemma p_composition_of_coherent_iso_for_rewrite w x y z
        (f : morphism C w x) (g : morphism C x y) (h : morphism C y z)
  : (Category.Morphisms.idtoiso (_ -> _) (ap (@p_morphism_of _ _ F w z) (Category.Core.associativity C w x y z f g h)))
    = @Build_Isomorphic
        (_ -> _) _ _
        ((((p_composition_of F w y z h (g o f))^-1)
            o ((p_morphism_of F h oL (p_composition_of F w x y g f)^-1)
                 o ((associator_1 (p_morphism_of F h) (p_morphism_of F g) (p_morphism_of F f))
                      o ((p_composition_of F x y z h g oR p_morphism_of F f)
                           o p_composition_of F w x z (h o g) f)))))%natural_transformation
        p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper.
  Proof.
    apply path_isomorphic; simpl.
    simpl rewrite (@p_composition_of_coherent _ C F w x y z f g h).
    exact p_composition_of_coherent_for_rewrite_helper.
  Qed.

  Lemma p_left_identity_of_coherent_iso_for_rewrite x y (f : morphism C x y)
  : (Category.Morphisms.idtoiso (_ -> _) (ap (@p_morphism_of _ _ F x y) (Category.Core.left_identity C x y f)))
    = @Build_Isomorphic
        (_ -> _) _ _
        ((left_identity_natural_transformation_1 (p_morphism_of F f))
           o ((p_identity_of F y oR p_morphism_of F f)
                o p_composition_of F x y y 1 f))%natural_transformation
        _.
  Proof.
    apply path_isomorphic; simpl.
    simpl rewrite (@p_left_identity_of_coherent _ C F x y f).
    path_natural_transformation.
    apply symmetry.
    etransitivity; apply Category.Core.left_identity.
  Qed.

  Lemma p_right_identity_of_coherent_iso_for_rewrite x y (f : morphism C x y)
  : (Category.Morphisms.idtoiso (_ -> _) (ap (@p_morphism_of _ _ F x y) (Category.Core.right_identity C x y f)))
    = @Build_Isomorphic
        (_ -> _) _ _
        ((right_identity_natural_transformation_1 (p_morphism_of F f))
           o ((p_morphism_of F f oL p_identity_of F x)
                o p_composition_of F x x y f 1))%natural_transformation
        _.
  Proof.
    apply path_isomorphic; simpl.
    simpl rewrite (@p_right_identity_of_coherent _ C F x y f).
    path_natural_transformation.
    apply symmetry.
    etransitivity; apply Category.Core.left_identity.
  Qed.

  Local Notation typeof x := ((fun T (_ : T) => T) _ x) (only parsing).

  Let p_composition_of_coherent_for_rewrite_type w x y z f g h
    := Eval simpl in typeof (ap (@morphism_isomorphic _ _ _)
                                (@p_composition_of_coherent_iso_for_rewrite w x y z f g h)).
  Definition p_composition_of_coherent_for_rewrite w x y z f g h
  : p_composition_of_coherent_for_rewrite_type w x y z f g h
    := ap (@morphism_isomorphic _ _ _)
          (@p_composition_of_coherent_iso_for_rewrite w x y z f g h).

  Let p_composition_of_coherent_inverse_for_rewrite_type w x y z f g h
    := Eval simpl in typeof (ap (fun i => @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
                                (@p_composition_of_coherent_iso_for_rewrite w x y z f g h)).
  Definition p_composition_of_coherent_inverse_for_rewrite w x y z f g h
  : p_composition_of_coherent_inverse_for_rewrite_type w x y z f g h
    := p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper__to_inverse
         (p_composition_of_coherent_iso_for_rewrite w x y z f g h).

  Let p_left_identity_of_coherent_for_rewrite_type x y f
    := Eval simpl in typeof (ap (@morphism_isomorphic _ _ _)
                                (@p_left_identity_of_coherent_iso_for_rewrite x y f)).
  Definition p_left_identity_of_coherent_for_rewrite x y f
  : p_left_identity_of_coherent_for_rewrite_type x y f
    := ap (@morphism_isomorphic _ _ _)
          (@p_left_identity_of_coherent_iso_for_rewrite x y f).

  Let p_left_identity_of_coherent_inverse_for_rewrite_type x y f
    := Eval simpl in typeof (ap (fun i => @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
                                (@p_left_identity_of_coherent_iso_for_rewrite x y f)).
  Definition p_left_identity_of_coherent_inverse_for_rewrite x y f
  : p_left_identity_of_coherent_inverse_for_rewrite_type x y f.
  Proof.
    refine (ap (fun i => @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
               (@p_left_identity_of_coherent_iso_for_rewrite x y f) @ _)%path.
    reflexivity.
  Defined.

  Let p_right_identity_of_coherent_for_rewrite_type x y f
    := Eval simpl in typeof (ap (@morphism_isomorphic _ _ _)
                                (@p_right_identity_of_coherent_iso_for_rewrite x y f)).
  Definition p_right_identity_of_coherent_for_rewrite x y f
  : p_right_identity_of_coherent_for_rewrite_type x y f
    := Eval simpl in ap (@morphism_isomorphic _ _ _)
                        (@p_right_identity_of_coherent_iso_for_rewrite x y f).

  Let p_right_identity_of_coherent_inverse_for_rewrite_type x y f
    := Eval simpl in typeof (ap (fun i => @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
                                (@p_right_identity_of_coherent_iso_for_rewrite x y f)).
  Definition p_right_identity_of_coherent_inverse_for_rewrite x y f
  : p_right_identity_of_coherent_inverse_for_rewrite_type x y f.
  Proof.
    refine (ap (fun i => @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
               (@p_right_identity_of_coherent_iso_for_rewrite x y f) @ _)%path.
    reflexivity.
  Defined.
Timeout 8 End lemmas.

End RewriteLaws.

End Pseudofunctor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Pseudofunctor_DOT_RewriteLaws.
