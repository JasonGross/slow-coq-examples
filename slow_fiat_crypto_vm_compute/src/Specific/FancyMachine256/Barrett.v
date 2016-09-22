Require Import Coq.PArith.BinPos.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Specific.FancyMachine256.Core.


Definition compiled_syntax
:= fun (ops : fancy_machine.instructions (2 * 128)) (var : base_type -> Type) =>
(λ (x x0 : var TZ) (x1 x2 : var TW),
 slet x3 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TZ) (@Tbase base_type TW) OPldi
              (@Var base_type (interp_base_type ops) op var TZ x) in
 slet x4 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TZ) (@Tbase base_type TW) OPldi
              (@Var base_type (interp_base_type ops) op var TZ x0) in
 slet x5 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TZ) (@Tbase base_type TW) OPldi
              (@Const base_type (interp_base_type ops) op var (@Tbase base_type TZ) 0) in
 slet x6 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type TZ)%ctype
              (@Tbase base_type TW) OPshrd
              (@Var base_type (interp_base_type ops) op var TW x2, @Var base_type (interp_base_type ops) op var TW x1,
              @Const base_type (interp_base_type ops) op var (@Tbase base_type TZ) 250) in
 slet x7 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW)%ctype
              (@Tbase base_type TW) OPmulhwhh
              (@Var base_type (interp_base_type ops) op var TW x6, @Var base_type (interp_base_type ops) op var TW x4) in
 slet x8 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW)%ctype
              (@Tbase base_type TW) OPmulhwhl
              (@Var base_type (interp_base_type ops) op var TW x6, @Var base_type (interp_base_type ops) op var TW x4) in
 slet x9 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW)%ctype
              (@Tbase base_type TW) OPmulhwll
              (@Var base_type (interp_base_type ops) op var TW x6, @Var base_type (interp_base_type ops) op var TW x4) in
 slet x10 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type Tbool)%ctype
               (@Tbase base_type Tbool * @Tbase base_type TW)%ctype OPadc
               (@Var base_type (interp_base_type ops) op var TW x9,
               @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TZ)%ctype
                 (@Tbase base_type TW) OPshl
                 (@Var base_type (interp_base_type ops) op var TW x8,
                 @Const base_type (interp_base_type ops) op var (@Tbase base_type TZ) 128),
               @Const base_type (interp_base_type ops) op var (@Tbase base_type Tbool) false) in
 slet x11 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type Tbool)%ctype
               (@Tbase base_type Tbool * @Tbase base_type TW)%ctype OPadc
               (@Var base_type (interp_base_type ops) op var TW x7,
               @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TZ)%ctype
                 (@Tbase base_type TW) OPshr
                 (@Var base_type (interp_base_type ops) op var TW x8,
                 @Const base_type (interp_base_type ops) op var (@Tbase base_type TZ) 128),
               @Var base_type (interp_base_type ops) op var Tbool (let (H, _) := x10 in H)) in
 slet x12 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW)%ctype
               (@Tbase base_type TW) OPmulhwhl
               (@Var base_type (interp_base_type ops) op var TW x4, @Var base_type (interp_base_type ops) op var TW x6) in
 slet x13 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type Tbool)%ctype
               (@Tbase base_type Tbool * @Tbase base_type TW)%ctype OPadc
               (@Var base_type (interp_base_type ops) op var TW (let (_, H) := x10 in H),
               @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TZ)%ctype
                 (@Tbase base_type TW) OPshl
                 (@Var base_type (interp_base_type ops) op var TW x12,
                 @Const base_type (interp_base_type ops) op var (@Tbase base_type TZ) 128),
               @Const base_type (interp_base_type ops) op var (@Tbase base_type Tbool) false) in
 slet x14 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type Tbool)%ctype
               (@Tbase base_type Tbool * @Tbase base_type TW)%ctype OPadc
               (@Var base_type (interp_base_type ops) op var TW (let (_, H) := x11 in H),
               @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TZ)%ctype
                 (@Tbase base_type TW) OPshr
                 (@Var base_type (interp_base_type ops) op var TW x12,
                 @Const base_type (interp_base_type ops) op var (@Tbase base_type TZ) 128),
               @Var base_type (interp_base_type ops) op var Tbool (let (H, _) := x13 in H)) in
 slet x15 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW)%ctype
               (@Tbase base_type TW) OPmulhwll
               (@Var base_type (interp_base_type ops) op var TW (let (_, H) := x14 in H),
               @Var base_type (interp_base_type ops) op var TW x3) in
 slet x16 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW)%ctype
               (@Tbase base_type TW) OPmulhwhl
               (@Var base_type (interp_base_type ops) op var TW (let (_, H) := x14 in H),
               @Var base_type (interp_base_type ops) op var TW x3) in
 slet x17 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type Tbool)%ctype
               (@Tbase base_type Tbool * @Tbase base_type TW)%ctype OPadc
               (@Var base_type (interp_base_type ops) op var TW x15,
               @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TZ)%ctype
                 (@Tbase base_type TW) OPshl
                 (@Var base_type (interp_base_type ops) op var TW x16,
                 @Const base_type (interp_base_type ops) op var (@Tbase base_type TZ) 128),
               @Const base_type (interp_base_type ops) op var (@Tbase base_type Tbool) false) in
 slet x18 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW)%ctype
               (@Tbase base_type TW) OPmulhwhl
               (@Var base_type (interp_base_type ops) op var TW x3,
               @Var base_type (interp_base_type ops) op var TW (let (_, H) := x14 in H)) in
 slet x19 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type Tbool)%ctype
               (@Tbase base_type Tbool * @Tbase base_type TW)%ctype OPadc
               (@Var base_type (interp_base_type ops) op var TW (let (_, H) := x17 in H),
               @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TZ)%ctype
                 (@Tbase base_type TW) OPshl
                 (@Var base_type (interp_base_type ops) op var TW x18,
                 @Const base_type (interp_base_type ops) op var (@Tbase base_type TZ) 128),
               @Const base_type (interp_base_type ops) op var (@Tbase base_type Tbool) false) in
 slet x20 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type Tbool)%ctype
               (@Tbase base_type Tbool * @Tbase base_type TW)%ctype OPsubc
               (@Var base_type (interp_base_type ops) op var TW x1,
               @Var base_type (interp_base_type ops) op var TW (let (_, H) := x19 in H),
               @Const base_type (interp_base_type ops) op var (@Tbase base_type Tbool) false) in
 slet x21 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type TW)%ctype
               (@Tbase base_type TW) OPaddm
               (@Var base_type (interp_base_type ops) op var TW (let (_, H) := x20 in H),
               @Var base_type (interp_base_type ops) op var TW x5, @Var base_type (interp_base_type ops) op var TW x3) in
 slet x22 := @Op base_type (interp_base_type ops) op var (@Tbase base_type TW * @Tbase base_type TW * @Tbase base_type TW)%ctype
               (@Tbase base_type TW) OPaddm
               (@Var base_type (interp_base_type ops) op var TW x21, @Var base_type (interp_base_type ops) op var TW x5,
               @Var base_type (interp_base_type ops) op var TW x3) in
 @Var base_type (interp_base_type ops) op var TW x22)%expr.

Definition v ops :=
  Eval cbv [compiled_syntax] in (DefaultAssembleSyntax (compiled_syntax ops)).

Local Open Scope positive_scope.

Require Import Crypto.Reflection.Named.Syntax.

Time Eval lazy in v. (* Finished transaction in 0.033 secs (0.032u,0.004s) (successful) *)
Time Eval compute in v. (* Finished transaction in 0.03 secs (0.032u,0.s) (successful) *)
Time Eval native_compute in v. (* Finished transaction in 0.081 secs (0.012u,0.016s) (successful) *)
Fail Timeout 5 Eval vm_compute in v. (* The command has indeed failed with message:
         Timeout! *)
Goal fancy_machine.instructions (2 * 128) -> True.
  intros ops.
  pose (v ops) as v'.
  unfold v in *; rename v' into v.
  let T := type of v in set (T' := T) in *; vm_compute in T'; subst T'.
  unfold DefaultAssembleSyntax, AssembleSyntax, AssembleSyntax', DeadCodeElimination.CompileAndEliminateDeadCode in (value of v).
  set (k := List.map _ _) in (value of v); vm_compute in k; subst k.
  set (v' := Compile.compile _ _) in (value of v); vm_compute in v'; subst v'.
  cbv beta iota in v.
  set (k := EstablishLiveness.insert_dead_names _ _ _) in (value of v).
  unfold EstablishLiveness.insert_dead_names in (value of k).
  revert v; set (n := DefaultRegisters _) in (value of k); intro v.
  vm_compute in n; subst n.
  revert v; set (l := EstablishLiveness.compute_liveness _ _ _) in (value of k); intro v.
  unfold EstablishLiveness.compute_liveness in (value of l).
  Notation hidden := (FMapPositive.PositiveMap.Node _ _ _).
  pose I as c.
  (* HERE: change 15 to other values to see exponential behavior of vm_compute *)
  do 15 (let m := fresh "c" in
         unfold EstablishLiveness.compute_livenessf in (value of l); fold (@EstablishLiveness.compute_livenessf base_type (interp_base_type _) op positive _) in (value of l); unfold EstablishLiveness.compute_livenessf_step at 1 in (value of l);
         revert k v; set (m := extend _ _ _) in (value of l); intros k v;
         vm_compute in m;
         subst c; rename m into c;
         simpl @List.app in (value of l));
    time vm_compute in v.
