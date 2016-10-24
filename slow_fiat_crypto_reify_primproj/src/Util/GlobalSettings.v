(** * Global Settings across the project *)

(** Compatibility with 8.4 so we can write, e.g., [match p with
    ex_intro x y => _ end], rather than [match p with ex_intro _ x y
    => _ end]. *)
Global Set Asymmetric Patterns.

(** Consider also: *)
(** Judgmental η for records, faster projections *)
Global Set Primitive Projections.

(** Primitive [prod] *)
Record prod A B := pair { fst : A ; snd : B }.
Arguments pair {A B} _ _.
Arguments snd {A B} _.
Arguments fst {A B} _.
Add Printing Let prod.
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

(** Don't use non-imported hints *)
(** Set Loose Hint Behavior "Strict". *)

(** Universes *)
(** Set Universe Polymorphism. *)
(** Set Strict Universe Declaration. *)
(** Unset Universe Minimization ToSet. *)

(** Better control of unfolding in [rewrite] and [setoid_rewrite] *)
(** Set Keyed Unification. *)

(** Better-behaved [simpl] *)
(** Set SimplIsCbn. *)
