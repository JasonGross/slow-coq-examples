Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Program.Basics.

Global Instance arrow2_1_Proper {A B RA RB X Y}
       {H0 : Proper (RA ==> RB ==> flip impl) (fun (a : A) (b : B) => X a b)}
       {H1 : Proper (RA ==> RB ==> impl) (fun (a : A) (b : B) => Y a b)}
: Proper (RA ==> RB ==> impl) (fun (a : A) (b : B) => X a b -> Y a b) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow2_2_Proper {A B RA RB X} {Y : A -> B -> Type} {Z : A -> B -> Prop}
       {H0 : Proper (RA ==> RB ==> flip impl) (fun (a : A) (b : B) => X a b)}
       {H1 : Proper (RA ==> RB ==> impl) (fun (a : A) (b : B) => Y a b -> Z a b)}
: Proper (RA ==> RB ==> impl) (fun (a : A) (b : B) => X a b -> Y a b -> Z a b) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow3_1_Proper {A B C RA RB RC X Y}
       {H0 : Proper (RA ==> RB ==> RC ==> flip impl) X}
       {H1 : Proper (RA ==> RB ==> RC ==> impl) Y}
: Proper (RA ==> RB ==> RC ==> impl) (fun (a : A) (b : B) (c : C) => X a b c -> Y a b c) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow3_2_Proper {A B C RA RB RC X} {Y : A -> B -> C -> Type} {Z : A -> B -> C -> Prop}
       {H0 : Proper (RA ==> RB ==> RC ==> flip impl) X}
       {H1 : Proper (RA ==> RB ==> RC ==> impl) (fun (a : A) (b : B) (c : C) => Y a b c -> Z a b c)}
: Proper (RA ==> RB ==> RC ==> impl) (fun (a : A) (b : B) (c : C) => X a b c -> Y a b c -> Z a b c) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow3_1_Proper_flip {A B C RA RB RC X Y}
       {H0 : Proper (RA ==> RB ==> RC ==> impl) X}
       {H1 : Proper (RA ==> RB ==> RC ==> flip impl) Y}
: Proper (RA ==> RB ==> RC ==> flip impl) (fun (a : A) (b : B) (c : C) => X a b c -> Y a b c) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow3_2_Proper_flip {A B C RA RB RC X} {Y : A -> B -> C -> Type} {Z : A -> B -> C -> Prop}
       {H0 : Proper (RA ==> RB ==> RC ==> impl) X}
       {H1 : Proper (RA ==> RB ==> RC ==> flip impl) (fun (a : A) (b : B) (c : C) => Y a b c -> Z a b c)}
: Proper (RA ==> RB ==> RC ==> flip impl) (fun (a : A) (b : B) (c : C) => X a b c -> Y a b c -> Z a b c) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance flip_impl_reflexive {A} {f}
: Reflexive (fun x y : A => flip impl (f x) (f y)).
Proof.
  repeat intro; assumption.
Defined.
Global Instance split_cons_drop_1_Proper {T} {R : relation T}
       {A RA RLA RLA' B C RB RC} {f}
       {H0 : Proper (RA ==> RLA ==> RLA') (@Datatypes.cons _)}
       {H1 : Proper (RB ==> RLA' ==> R) f}
: Proper (RA ==> RLA ==> RB ==> RC ==> R)
         (fun (a : A) (la : list A) (b : B) (_ : C) => f b (@Datatypes.cons _ a la)).
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Qed.
Global Instance drop_4_Proper {T} {R : relation T}
       {A B C D RA RB RC RD f}
       {H0 : @Reflexive D RD}
       {H1 : Proper (RA ==> RB ==> RC ==> R) f}
: Proper (RA ==> RB ==> RC ==> RD ==> R) (fun (a : A) (b : B) (c : C) (_ : D) => f a b c).
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance drop_0_Proper {A B RA RB} {f : B}
       {H : Proper RB f}
: Proper (RA ==> RB) (fun _ : A => f).
Proof.
  lazy in H |- *; eauto with nocore.
Defined.
Global Instance idmap_Proper {A} {R : relation A}
: Proper (R ==> R) (fun x : A => x).
Proof.
  lazy; trivial.
Defined.
Global Instance forall_fun3_Proper {A X Y Z RX RY RZ} {B : _ -> _ -> _ -> _ -> Prop}
       {H : forall a, Proper (RX ==> RY ==> RZ ==> flip impl) (B a)}
: Proper (RX ==> RY ==> RZ ==> flip impl) (fun (x : X) (y : Y) (z : Z) => forall a : A, B a x y z) | 1000.
Proof.
  lazy in H |- *; eauto with nocore.
Defined.
