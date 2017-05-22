(** Sharpened ADT for JSON *)
Require Import Fiat.Parsers.Grammars.JSONImpoverished.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.

Ltac replace_with_vm_compute_in c H ::=
  let c' := (eval native_compute in c) in
  (* By constrast [set ... in ...] seems faster than [change .. with ... in ...] in 8.4?! *)
  replace c with c' in H by (clear; native_cast_no_check (eq_refl c')).
Section IndexedImpl.
  (*Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}.*)

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    (*Start Profiling.*)
    Time splitter_start.
    (*Show Profile.*)
    (*
total time:      1.250s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─splitter_start ------------------------  10.0% 100.0%       1    1.250s
─replace_with_at_by --------------------   1.3%  60.0%       1    0.750s
─set_tac -------------------------------   0.0%  46.3%       1    0.578s
─change x with x' ----------------------  46.3%  46.3%       1    0.578s
─apply_splitter_tower_lemma ------------   0.0%  28.7%       1    0.359s
─eapply lem ----------------------------  18.8%  18.8%       2    0.234s
─induction H ---------------------------   7.5%   7.5%       1    0.094s
─pose proof  (refine_opt2_fold_right_no_   5.0%   5.0%       1    0.063s
─assert (y = x') as H by (subst x'; tac)   0.0%   3.8%       1    0.047s
─cbv beta iota zeta delta [make_tower_no   3.8%   3.8%       1    0.047s
─tac -----------------------------------   0.0%   2.5%       1    0.031s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─splitter_start ------------------------  10.0% 100.0%       1    1.250s
 ├─replace_with_at_by ------------------   1.3%  60.0%       1    0.750s
 │ ├─set_tac ---------------------------   0.0%  46.3%       1    0.578s
 │ │└change x with x' ------------------  46.3%  46.3%       1    0.578s
 │ ├─induction H -----------------------   7.5%   7.5%       1    0.094s
 │ └─assert (y = x') as H by (subst x';    0.0%   3.8%       1    0.047s
 │  └tac -------------------------------   0.0%   2.5%       1    0.031s
 └─apply_splitter_tower_lemma ----------   0.0%  28.7%       1    0.359s
   ├─eapply lem ------------------------  18.8%  18.8%       1    0.234s
   ├─pose proof  (refine_opt2_fold_right   5.0%   5.0%       1    0.063s
   └─cbv beta iota zeta delta [make_towe   3.8%   3.8%       1    0.047s
*)
    (*Start Profiling.*)
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_rev_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time refine_binop_table; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time refine_binop_table; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_rev_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time refine_binop_table; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time refine_binop_table; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { Time rewrite_disjoint_search_for; reflexivity. }
    { simplify parser splitter.
      (*Show Profile.*)
      (*

total time:    106.375s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for_no_clear --   0.0%  49.7%      20    7.359s
─rewrite_disjoint_search_for -----------   0.0%  49.7%      20    7.359s
─rewrite_once_disjoint_search_for ------   0.0%  49.3%      40    7.313s
─rewrite_once_disjoint_search_for_specia  48.2%  49.0%      40    7.297s
─setoid_rewrite_refine_binop_table_idx -  43.5%  44.1%       4   12.969s
─refine_binop_table --------------------   0.0%  44.1%       4   12.969s
─rewrite_disjoint_rev_search_for_no_clea   0.0%   5.1%       2    2.703s
─rewrite_disjoint_rev_search_for -------   0.0%   5.1%       2    2.703s
─rewrite_once_disjoint_rev_search_for --   0.0%   5.0%       4    2.688s
─rewrite_once_disjoint_rev_search_for_sp   4.9%   5.0%       4    2.656s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  49.7%      20    7.359s
└rewrite_disjoint_search_for_no_clear --   0.0%  49.7%      20    7.359s
└rewrite_once_disjoint_search_for ------   0.0%  49.3%      40    7.313s
└rewrite_once_disjoint_search_for_specia  48.2%  49.0%      40    7.297s
─refine_binop_table --------------------   0.0%  44.1%       4   12.969s
└setoid_rewrite_refine_binop_table_idx -  43.5%  44.1%       4   12.969s
─rewrite_disjoint_rev_search_for -------   0.0%   5.1%       2    2.703s
└rewrite_disjoint_rev_search_for_no_clea   0.0%   5.1%       2    2.703s
└rewrite_once_disjoint_rev_search_for --   0.0%   5.0%       4    2.688s
└rewrite_once_disjoint_rev_search_for_sp   4.9%   5.0%       4    2.656s
 *)
      Time finish honing parser method.
    }

    Time finish_Sharpening_SplitterADT.

  Time Defined. (* 85 seconds *)

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    (*Start Profiling.*)
    Time make_simplified_splitter ComputationalSplitter'. (* 19 s *)
    (*Show Profile.*)
  Time Defined.

End IndexedImpl.
