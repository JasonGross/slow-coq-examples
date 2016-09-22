(** * A Fancy Machine with 256-bit registers *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.DeadCodeElimination.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Reflection.Named.ContextOn.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tuple.

Local Open Scope type_scope.
Local Open Scope Z_scope.

Class decoder (n : Z) W :=
  { decode : W -> Z }.
Coercion decode : decoder >-> Funclass.
Global Arguments decode {n W _} _.

Class is_decode {n W} (decode : decoder n W) :=
  decode_range : forall x, 0 <= decode x < 2^n.

Class bounded_in_range_cls (x y z : Z) := is_bounded_in_range : x <= y < z.
Ltac bounded_solver_tac :=
  solve [ eassumption | typeclasses eauto | omega ].
Hint Extern 0 (bounded_in_range_cls _ _ _) => unfold bounded_in_range_cls; bounded_solver_tac : typeclass_instances.
Global Arguments bounded_in_range_cls / .
Global Instance decode_range_bound {n W} {decode : decoder n W} {H : is_decode decode}
  : forall x, bounded_in_range_cls 0 (decode x) (2^n)
  := H.

(** This is required for typeclass resolution to be fast. *)
Typeclasses Opaque decode.

Section InstructionGallery.
  Context (n : Z) (* bit-width of width of [W] *)
          {W : Type} (* bounded type, [W] for word *)
          (Wdecoder : decoder n W).
  Local Notation imm := Z (only parsing). (* immediate (compile-time) argument *)

  Class load_immediate := { ldi : imm -> W }.
  Global Coercion ldi : load_immediate >-> Funclass.

  Class shift_right_doubleword_immediate := { shrd : W -> W -> imm -> W }.
  Global Coercion shrd : shift_right_doubleword_immediate >-> Funclass.

  Class shift_left_immediate := { shl : W -> imm -> W }.
  Global Coercion shl : shift_left_immediate >-> Funclass.

  Class shift_right_immediate := { shr : W -> imm -> W }.
  Global Coercion shr : shift_right_immediate >-> Funclass.

  Class spread_left_immediate := { sprl : W -> imm -> tuple W 2 (* [(low, high)] *) }.
  Global Coercion sprl : spread_left_immediate >-> Funclass.

  Class mask_keep_low := { mkl :> W -> imm -> W }.
  Global Coercion mkl : mask_keep_low >-> Funclass.

  Local Notation bit b := (if b then 1 else 0).

  Class add_with_carry := { adc : W -> W -> bool -> bool * W }.
  Global Coercion adc : add_with_carry >-> Funclass.

  Class sub_with_carry := { subc : W -> W -> bool -> bool * W }.
  Global Coercion subc : sub_with_carry >-> Funclass.

  Class multiply := { mul : W -> W -> W }.
  Global Coercion mul : multiply >-> Funclass.

  Class multiply_low_low := { mulhwll : W -> W -> W }.
  Global Coercion mulhwll : multiply_low_low >-> Funclass.
  Class multiply_high_low := { mulhwhl : W -> W -> W }.
  Global Coercion mulhwhl : multiply_high_low >-> Funclass.
  Class multiply_high_high := { mulhwhh : W -> W -> W }.
  Global Coercion mulhwhh : multiply_high_high >-> Funclass.
  Class multiply_double := { muldw : W -> W -> tuple W 2 }.
  Global Coercion muldw : multiply_double >-> Funclass.

  Class select_conditional := { selc : bool -> W -> W -> W }.
  Global Coercion selc : select_conditional >-> Funclass.

  Class add_modulo := { addm : W -> W -> W (* modulus *) -> W }.
  Global Coercion addm : add_modulo >-> Funclass.

End InstructionGallery.

Global Arguments load_immediate : clear implicits.
Global Arguments shift_right_doubleword_immediate : clear implicits.
Global Arguments shift_left_immediate : clear implicits.
Global Arguments shift_right_immediate : clear implicits.
Global Arguments spread_left_immediate : clear implicits.
Global Arguments mask_keep_low : clear implicits.
Global Arguments add_with_carry : clear implicits.
Global Arguments sub_with_carry : clear implicits.
Global Arguments multiply : clear implicits.
Global Arguments multiply_low_low : clear implicits.
Global Arguments multiply_high_low : clear implicits.
Global Arguments multiply_high_high : clear implicits.
Global Arguments multiply_double : clear implicits.
Global Arguments select_conditional : clear implicits.
Global Arguments add_modulo : clear implicits.
Global Arguments ldi {_ _} _.
Global Arguments shrd {_ _} _ _ _.
Global Arguments shl {_ _} _ _.
Global Arguments shr {_ _} _ _.
Global Arguments sprl {_ _} _ _.
Global Arguments mkl {_ _} _ _.
Global Arguments adc {_ _} _ _ _.
Global Arguments subc {_ _} _ _ _.
Global Arguments mul {_ _} _ _.
Global Arguments mulhwll {_ _} _ _.
Global Arguments mulhwhl {_ _} _ _.
Global Arguments mulhwhh {_ _} _ _.
Global Arguments muldw {_ _} _ _.
Global Arguments selc {_ _} _ _ _.
Global Arguments addm {_ _} _ _ _.

Module fancy_machine.
  Local Notation imm := Z (only parsing).

  Class instructions (n : Z) :=
    {
      W : Type (* [n]-bit word *);
      decode :> decoder n W;
      ldi :> load_immediate W;
      shrd :> shift_right_doubleword_immediate W;
      shl :> shift_left_immediate W;
      shr :> shift_right_immediate W;
      mkl :> mask_keep_low W;
      adc :> add_with_carry W;
      subc :> sub_with_carry W;
      mulhwll :> multiply_low_low W;
      mulhwhl :> multiply_high_low W;
      mulhwhh :> multiply_high_high W;
      selc :> select_conditional W;
      addm :> add_modulo W
    }.

End fancy_machine.


Open Scope Z_scope.
Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta3' x := (fst x, eta (snd x)).

(** ** Reflective Assembly Syntax *)
Section reflection.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Inductive base_type := TZ | Tbool | TW.
  Global Instance dec_base_type : DecidableRel (@eq base_type)
    := base_type_eq_dec.
  Definition interp_base_type (v : base_type) : Type :=
    match v with
    | TZ => Z
    | Tbool => bool
    | TW => fancy_machine.W
    end.
  Local Notation tZ := (Tbase TZ).
  Local Notation tbool := (Tbase Tbool).
  Local Notation tW := (Tbase TW).
  Local Open Scope ctype_scope.
  Inductive op : flat_type base_type -> flat_type base_type -> Type :=
  | OPldi     : op tZ tW
  | OPshrd    : op (tW * tW * tZ) tW
  | OPshl     : op (tW * tZ) tW
  | OPshr     : op (tW * tZ) tW
  | OPmkl     : op (tW * tZ) tW
  | OPadc     : op (tW * tW * tbool) (tbool * tW)
  | OPsubc    : op (tW * tW * tbool) (tbool * tW)
  | OPmulhwll : op (tW * tW) tW
  | OPmulhwhl : op (tW * tW) tW
  | OPmulhwhh : op (tW * tW) tW
  | OPselc    : op (tbool * tW * tW) tW
  | OPaddm    : op (tW * tW * tW) tW.
End reflection.


(** ** Raw Syntax Trees *)
(** These are used solely for pretty-printing the expression tree in a
    form that can be basically copy-pasted into other languages which
    can be compiled for the Fancy Machine.  Hypothetically, we could
    add support for custom named identifiers, by carrying around
    [string] identifiers and using them for pretty-printing...  It
    might also be possible to verify this layer, too, by adding a
    partial interpretation function... *)

Local Set Decidable Equality Schemes.
Local Set Boolean Equality Schemes.

Inductive Register :=
| RegPInv | RegMod | RegMuLow | RegZero
| y | t1 | t2 | lo | hi | out | src1 | src2 | tmp | q | qHigh | x | xHigh
| scratch | scratchplus (n : nat).

Notation "'scratch+' n" := (scratchplus n) (format "'scratch+' n", at level 10).

Definition pos_of_Register (r : Register) :=
  match r with
  | RegPInv => 1
  | RegMod => 2
  | RegMuLow => 3
  | RegZero => 4
  | y => 5
  | t1 => 6
  | t2 => 7
  | lo => 8
  | hi => 9
  | out => 10
  | src1 => 11
  | src2 => 12
  | tmp => 13
  | q => 14
  | qHigh => 15
  | x => 16
  | xHigh => 17
  | scratch => 18
  | scratchplus n => 18 + Pos.of_nat (S n)
  end%positive.

Global Instance RegisterContext {var : base_type -> Type} : Context Register var
  := ContextOn pos_of_Register (RegisterAssign.pos_context var).

Definition syntax {ops : fancy_machine.instructions (2 * 128)}
  := Named.expr base_type (interp_base_type ops) op Register.

(** Assemble a well-typed easily interpretable expression into a
    syntax tree we can use for pretty-printing. *)
Section assemble.
  Context {ops : fancy_machine.instructions (2 * 128)}.

  Definition AssembleSyntax' {t} (e : Expr base_type (interp_base_type _) op t) (ls : list Register)
    : option (syntax t)
    := CompileAndEliminateDeadCode e ls.
  Definition AssembleSyntax {t} e ls (res := @AssembleSyntax' t e ls)
    := match res return match res with None => _ | _ => _ end with
       | Some v => v
       | None => I
       end.

  Definition dummy_registers (n : nat) : list Register
    := List.map scratchplus (seq 0 n).
  Definition DefaultRegisters {t} (e : Expr base_type (interp_base_type _) op t) : list Register
    := dummy_registers (CountBinders e).

  Definition DefaultAssembleSyntax {t} e := @AssembleSyntax t e (DefaultRegisters e).
End assemble.
