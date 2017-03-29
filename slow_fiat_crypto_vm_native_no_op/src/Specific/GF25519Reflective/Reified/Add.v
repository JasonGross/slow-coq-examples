Require Import Crypto.Specific.GF25519Reflective.Common.

Definition raddZ_sig : rexpr_binop_sig add. Proof. reify_sig. Defined.
Definition raddZ : Expr _ := Eval vm_compute in proj1_sig raddZ_sig.
Definition raddW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option raddZ ExprBinOp_bounds.
Definition raddW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 raddW_pkgo.
Definition raddT := get_output_type raddW_pkg.
Definition raddW' : Expr _ := Eval vm_compute in get_output_expr raddW_pkg.
Definition raddW : Expr raddT := Eval cbv [raddW'] in rexpr_select_word_sizes_postprocess2 raddW'.
Definition radd_output_bounds := Eval vm_compute in get_bounds raddW_pkg.
Definition raddZ_Wf : rexpr_wfT raddZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition raddZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT raddZ raddW ExprBinOp_bounds radd_output_bounds
  := rexpr_correct_and_bounded raddZ raddW ExprBinOp_bounds radd_output_bounds raddZ_Wf.

Local Open Scope string_scope.
Compute ("Add", compute_bounds_for_display raddW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Add overflows? ", sanity_compute raddW_pkg).
Compute ("Add overflows (error if it does)? ", sanity_check raddW_pkg).
