Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rsubZ_sig : rexpr_binop_sig sub. Proof. reify_sig. Defined.
Definition rsubZ : Expr _ := Eval vm_compute in proj1_sig rsubZ_sig.
Definition rsubW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option rsubZ ExprBinOp_bounds.
Definition rsubW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 rsubW_pkgo.
Definition rsubT := get_output_type rsubW_pkg.
Definition rsubW' : Expr _ := Eval vm_compute in get_output_expr rsubW_pkg.
Definition rsubW : Expr rsubT := Eval cbv [rsubW'] in rexpr_select_word_sizes_postprocess2 rsubW'.
Definition rsub_output_bounds := Eval vm_compute in get_bounds rsubW_pkg.
Definition rsubZ_Wf : rexpr_wfT rsubZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition rsubZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT rsubZ rsubW ExprBinOp_bounds rsub_output_bounds
  := rexpr_correct_and_bounded rsubZ rsubW ExprBinOp_bounds rsub_output_bounds rsubZ_Wf.

Local Open Scope string_scope.
Compute ("Sub", compute_bounds_for_display rsubW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Sub overflows? ", sanity_compute rsubW_pkg).
Compute ("Sub overflows (error if it does)? ", sanity_check rsubW_pkg).
