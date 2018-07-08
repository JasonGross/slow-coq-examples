Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope list_scope. Local Open Scope Z_scope.

Fixpoint update_nth {T} n f (xs:list T) {struct n} :=
	match n with
	| O => match xs with
				 | nil => nil
				 | x'::xs' => f x'::xs'
				 end
	| S n' =>  match xs with
				 | nil => nil
				 | x'::xs' => x'::update_nth n' f xs'
				 end
  end.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).

Definition encodemod := (fun (limbwidth_num limbwidth_den s : Z) (c : list (Z * Z)) (n : nat) =>
 (fun (weight : nat -> Z) (n0 : nat) (s0 : Z) (c0 : list (Z * Z)) (x : Z) =>
  (fun (weight0 : nat -> Z) (n1 : nat) (s1 : Z) (c1 : list (Z * Z)) (p : list Z) (idxs : list nat) =>
   fold_right
     (fun (a : nat) (b : list Z) =>
      (fun (weight1 : nat -> Z) (n2 : nat) (s2 : Z) (c2 : list (Z * Z)) (index : nat) (p0 : list Z) =>
       (fun (weight2 : nat -> Z) (n3 : nat) (p1 : list (Z * Z)) =>
        fold_right
          (fun (t : Z * Z) (ls : list Z) =>
           dlet p2 : nat * Z := (fun (weight3 : nat -> Z) (t0 : Z * Z) (i : nat) =>
                                 nat_rect (fun _ : nat => (nat * Z)%type) (0%nat, fst t0 * snd t0)
                                   (fun (i' : nat) (place_i' : (fun _ : nat => (nat * Z)%type) i') =>
                                    let i0 := S i' in
                                    if fst t0 mod weight3 i0 =? 0
                                    then (i0, let c3 := fst t0 / weight3 i0 in c3 * snd t0)
                                    else place_i') i) weight2 t (Init.Nat.pred n3) in
           (fun (i : nat) (x0 : Z) (ls0 : list Z) => update_nth i (fun y : Z => x0 + y) ls0) (fst p2) (snd p2) ls)
          ((fun n4 : nat => repeat 0 n4) n3) p1) weight1 n2
         ((fun (s3 : Z) (c3 p1 : list (Z * Z)) =>
           let lo_hi :=
             (fun (s4 : Z) (p2 : list (Z * Z)) =>
              let hi_lo := partition (fun t : Z * Z => fst t mod s4 =? 0) p2 in
              (snd hi_lo, map (fun t : Z * Z => (fst t / s4, snd t)) (fst hi_lo))) s3 p1 in
           fst lo_hi ++
           (fun p2 q : list (Z * Z) => flat_map (fun t : Z * Z => map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) q) p2)
             c3 (snd lo_hi)) s2 c2
            ((fun (weight2 : nat -> Z) (n3 : nat) (xs : list Z) => combine (map weight2 (seq 0 n3)) xs) weight1
               (S n2)
               ((fun (weight2 : nat -> Z) (n3 m index0 : nat) (p1 : list Z) =>
                 (fun (weight3 : nat -> Z) (n4 : nat) (p2 : list (Z * Z)) =>
                  fold_right
                    (fun (t : Z * Z) (ls : list Z) =>
                     dlet p3 : nat * Z := (fun (weight4 : nat -> Z) (t0 : Z * Z) (i : nat) =>
                                           nat_rect (fun _ : nat => (nat * Z)%type) (0%nat, fst t0 * snd t0)
                                             (fun (i' : nat) (place_i' : (fun _ : nat => (nat * Z)%type) i') =>
                                              let i0 := S i' in
                                              if fst t0 mod weight4 i0 =? 0
                                              then (i0, let c3 := fst t0 / weight4 i0 in c3 * snd t0)
                                              else place_i') i) weight3 t (Init.Nat.pred n4) in
                     (fun (i : nat) (x0 : Z) (ls0 : list Z) => update_nth i (fun y : Z => x0 + y) ls0) (fst p3) (snd p3) ls)
                    ((fun n5 : nat => repeat 0 n5) n4) p2) weight2 m
                   ((fun (w fw : Z) (p2 : list (Z * Z)) =>
                     flat_map
                       ((fun (w0 fw0 : Z) (t : Z * Z) =>
                         if fst t =? w0
                         then
                          dlet t2 : Z := snd t in
                         dlet d2 : Z := t2 / fw0 in
                         dlet m2 : Z := t2 mod fw0 in
                         [(w0 * fw0, d2); (w0, m2)]
                         else [t]) w fw) p2) (weight2 index0) (weight2 (S index0) / weight2 index0)
                      ((fun (weight3 : nat -> Z) (n4 : nat) (xs : list Z) => combine (map weight3 (seq 0 n4)) xs) weight2 n3 p1)))
                  weight1 n2 (S n2) index p0)))) weight0 n1 s1 c1 a b) p (rev idxs)) weight n0 s0 c0
    ((fun (weight0 : nat -> Z) (n1 : nat) (p : list (Z * Z)) =>
      fold_right
        (fun (t : Z * Z) (ls : list Z) =>
         dlet p0 : nat * Z := (fun (weight1 : nat -> Z) (t0 : Z * Z) (i : nat) =>
                               nat_rect (fun _ : nat => (nat * Z)%type) (0%nat, fst t0 * snd t0)
                                 (fun (i' : nat) (place_i' : (fun _ : nat => (nat * Z)%type) i') =>
                                  let i0 := S i' in
                                  if fst t0 mod weight1 i0 =? 0
                                  then (i0, let c1 := fst t0 / weight1 i0 in c1 * snd t0)
                                  else place_i') i) weight0 t (Init.Nat.pred n1) in
         (fun (i : nat) (x0 : Z) (ls0 : list Z) => update_nth i (fun y : Z => x0 + y) ls0) (fst p0) (snd p0) ls)
        ((fun n2 : nat => repeat 0 n2) n1) p) weight n0 [(1, x)]) (seq 0 n0))
   ((fun (limbwidth_num0 limbwidth_den0 : Z) (i : nat) => 2 ^ (- (- (limbwidth_num0 * Z.of_nat i) / limbwidth_den0)))
      limbwidth_num limbwidth_den) n s c).

Notation encodep := (encodemod 51 2 (2^255) [(1,19)] 10 (2^255-1)).
Notation encodepby := (encodemod 8 1 (2^255) [(1,19)] 32 (2^255-1)).
Definition test1 := encodep.
Definition test5 := (encodep, encodep, encodep, encodep, encodep).
Definition test1by := encodepby.
Definition test5by := (encodepby, encodepby, encodepby, encodepby, encodepby).
Time Eval lazy in test1. (* 10.211 s *)
Time Eval cbv in test1. (* 12.285 s *)
Time Eval vm_compute in test1. (* 0.551 s *)
Time Eval native_compute in test1. (* 0.382 s *)
Time Eval vm_compute in test5. (* 2.547 s *)
Time Eval native_compute in test5. (* 1.372 s *)
Time Eval vm_compute in test1by. (* 14.394 s *)
Time Eval native_compute in test1by. (* 6.883 s *)

Require Import Coq.extraction.Extraction.
Redirect "test1.ml" Recursive Extraction test1.
Redirect "test5.ml" Recursive Extraction test5.
Redirect "test1by.ml" Recursive Extraction test1by.
Redirect "test5by.ml" Recursive Extraction test5by.
Require Import Coq.extraction.ExtrOcamlBasic.
Redirect "test1b.ml" Recursive Extraction test1.
Redirect "test5b.ml" Recursive Extraction test5.
Redirect "test1byb.ml" Recursive Extraction test1by.
Redirect "test5byb.ml" Recursive Extraction test5by.
(*
test1
real    0m0.043s
user    0m0.040s
sys     0m0.000s


test5
real    0m0.104s
user    0m0.100s
sys     0m0.000s


test1b
real    0m0.042s
user    0m0.040s
sys     0m0.000s


test5b
real    0m0.114s
user    0m0.112s
sys     0m0.000stest1
real    0m0.043s
user    0m0.040s
sys     0m0.000s


test5
real    0m0.104s
user    0m0.100s
sys     0m0.000s


test1b
real    0m0.042s
user    0m0.040s
sys     0m0.000s


test5b
real    0m0.114s
user    0m0.112s
sys     0m0.000s

test1by
real    0m0.538s
user    0m0.532s
sys     0m0.004s


test5by
real    0m2.248s
user    0m2.244s
sys     0m0.004s


test1byb
real    0m0.533s
user    0m0.524s
sys     0m0.008s


test5byb
real    0m2.295s
user    0m2.292s
sys     0m0.000s
*)
