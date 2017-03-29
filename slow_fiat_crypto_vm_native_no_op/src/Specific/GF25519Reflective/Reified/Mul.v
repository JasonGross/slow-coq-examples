Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rmulZ_sig : rexpr_binop_sig mul. Proof. reify_sig. Defined.
Definition rmulZ : Expr _ := Eval vm_compute in proj1_sig rmulZ_sig.
Definition rmulW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option rmulZ ExprBinOp_bounds.
Definition rmulW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 rmulW_pkgo.
Definition rmulT := get_output_type rmulW_pkg.
Definition rmulW' : Expr _ := Eval vm_compute in get_output_expr rmulW_pkg.
Definition rmulW : Expr rmulT := Eval cbv [rmulW'] in rexpr_select_word_sizes_postprocess2 rmulW'.
Definition rmul_output_bounds := Eval vm_compute in get_bounds rmulW_pkg.
Definition rmulZ_Wf : rexpr_wfT rmulZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition rmulZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT rmulZ rmulW ExprBinOp_bounds rmul_output_bounds
  := rexpr_correct_and_bounded rmulZ rmulW ExprBinOp_bounds rmul_output_bounds rmulZ_Wf.

Local Open Scope string_scope.
Compute ("Mul", compute_bounds_for_display rmulW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Mul overflows? ", sanity_compute rmulW_pkg).
Compute ("Mul overflows (error if it does)? ", sanity_check rmulW_pkg).
