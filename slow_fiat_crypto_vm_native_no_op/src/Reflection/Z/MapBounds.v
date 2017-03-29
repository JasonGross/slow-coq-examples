Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.BoundsInterpretations.
Require Import Crypto.Reflection.SmartMap.
(*Require Import Crypto.Reflection.Linearize.*)
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.MapCastByDeBruijn.

Local Notation pick_typeb := Bounds.bounds_to_base_type (only parsing).
Local Notation pick_type v := (SmartFlatTypeMap (fun _ => pick_typeb) v).

Section MapBoundsSig.
  Context {t}
          (e : Expr base_type op t)
          (input_bounds : interp_flat_type Bounds.interp_base_type (domain t)).

  Definition MapBoundsPreProcess
    := @MapCastPreProcess base_type op t e.
  Definition MapBoundsCompile e'
    := @MapCastCompile base_type op t e'.
  Definition MapBoundsDoCast e'
    := @MapCastDoCast base_type op
                      base_type_beq internal_base_type_dec_bl
                      Bounds.interp_base_type (@Bounds.interp_op)
                      (fun _ => pick_typeb)
                      (fun _ _ opc _ => genericize_op opc)
                      t input_bounds e'.
  Definition MapBoundsDoInterp e'
    := @MapCastDoInterp base_type op
                        base_type_beq internal_base_type_dec_bl
                        (fun _ t => Op (OpConst 0) TT)
                        Bounds.interp_base_type
                        (fun _ => pick_typeb)
                        t input_bounds e'.
  Local Notation P :=
    (fun output_bounds : interp_flat_type Bounds.interp_base_type (codomain t)
     => Expr base_type op (Arrow (pick_type input_bounds) (pick_type output_bounds)))
      (only parsing).
  Definition MapBoundsSig
    : option (sigT P)
    := option_map
         (fun v => let 'existT b e := v in existT P b (ExprEta (t:=Arrow _ _) (InlineConst is_const e)))
         (MapBoundsDoInterp (MapBoundsDoCast (MapBoundsCompile MapBoundsPreProcess))).
  Lemma unfold_MapBoundsSig
    : MapBoundsSig
      = option_map
         (fun v => let 'existT b e := v in existT P b (ExprEta (t:=Arrow _ _) (InlineConst is_const e)))
         (@MapCast base_type op
                   base_type_beq internal_base_type_dec_bl
                   (fun _ t => Op (OpConst 0) TT)
                   Bounds.interp_base_type (@Bounds.interp_op)
                   (fun _ => pick_typeb)
                   (fun _ _ opc _ => genericize_op opc)
                   t e input_bounds).
  Proof. reflexivity. Defined.
End MapBoundsSig.

Record MapBoundsPackage
  := { MapBoundsType : _;
       input_expr : Expr base_type op MapBoundsType;
       input_bounds : interp_flat_type Bounds.interp_base_type (domain MapBoundsType);
       output_bounds :> interp_flat_type Bounds.interp_base_type (codomain MapBoundsType);
       output_expr :> Expr base_type op (Arrow (pick_type input_bounds) (pick_type output_bounds)) }.

Notation MapBoundsOutputType pkg
  := (Arrow (pick_type (@input_bounds pkg)) (pick_type (@output_bounds pkg)))
       (only parsing).

Definition MapBoundsPackaged
           {t}
           (e : Expr base_type op t)
           (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
  : option MapBoundsPackage
  := option_map
       (fun be
        => let 'existT b e' := be in
           {| MapBoundsType := t ; input_expr := e ; input_bounds := input_bounds ; output_bounds := b ; output_expr := e' |})
       (MapBoundsSig e input_bounds).
