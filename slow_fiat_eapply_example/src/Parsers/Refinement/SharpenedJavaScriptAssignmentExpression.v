Require Import Fiat.Parsers.Grammars.JavaScriptAssignmentExpression.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.Refinement.PossibleTerminalsSets.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Computation.SetoidMorphisms.
Fail Check ret_Proper_eq.
Global Instance ret_Proper_eq {A}
  : Proper (eq ==> eq) (ret (A:=A)).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance refine_Proper_eq_iff {A}
  : Proper (eq ==> eq ==> iff) (@refine A).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance refine_Proper_eq_impl {A}
  : Proper (eq ==> eq ==> impl) (@refine A) | 1.
Proof. repeat (assumption || subst || intro). Qed.
Global Instance refine_Proper_eq_flip_impl {A}
  : Proper (eq ==> eq ==> flip impl) (@refine A) | 1.
Proof. repeat (assumption || subst || intro). Qed.
Ltac uneta_fun :=
  repeat match goal with
         | [ |- appcontext[fun ch : ?T => ?f ch] ]
           => progress change (fun ch : T => f ch) with f
         end.
Ltac setoid_rewrite_ascii_mem :=
  idtac;
  let lem := match goal with
             | [ |- appcontext[MSetPositive.PositiveSet.mem (pos_of_ascii _) ?v] ]
               => constr:(@ascii_mem v eq_refl)
             end in
  let lem := constr:(lem _ eq_refl) in
  let lem := constr:(lem eq_refl _ eq_refl) in
  let lem := (eval cbv [ascii_of_pos shift one] in lem) in
  setoid_rewrite lem; uneta_fun.
Notation hidden_grammar_data := (@FromAbstractInterpretation.Build_fold_grammar_data _ _ _ _ _ _ _).
Global Arguments possible_data {_}.
Global Arguments all_possible_data {_}.

Section IndexedImpl.
  (*Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}.*)

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec javascript_assignment_expression_pregrammar string_stringlike).
  Proof.

    Time start sharpening ADT. (* 0. secs (0.u,0.s) *)

    (*Set Ltac Profiling.*)
    Time let G := match goal with |- Sharpened (string_spec ?G _) => G end in
    let G := match G with
             | _ => (eval cbv delta [G] in G)
             | _ => G
             end in
    let G := match G with
             | grammar_of_pregrammar ?G => G
             end in
    let v := make_possible_data G in
    let v' := make_all_possible_data G in
    let H := fresh in
    let H' := fresh in
    pose v as H; pose v' as H'; cbv beta in H, H'. (* 53.393 secs (53.36u,0.032s) *)
    (*Show Ltac Profile.*)
    (*total time:      0.092s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─vm_cast_no_check ----------------------  39.1%  39.1%       2    0.028s
─clear ---------------------------------  21.7%  21.7%       2    0.012s
─cbv beta in H, H' ---------------------  17.4%  17.4%       1    0.016s
─pose (H' := v') -----------------------  13.0%  13.0%       1    0.012s
─pose (H := v) -------------------------   8.7%   8.7%       1    0.008s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─vm_cast_no_check ----------------------  39.1%  39.1%       2    0.028s
─clear ---------------------------------  21.7%  21.7%       2    0.012s
─cbv beta in H, H' ---------------------  17.4%  17.4%       1    0.016s
─pose (H' := v') -----------------------  13.0%  13.0%       1    0.012s
─pose (H := v) -------------------------   8.7%   8.7%       1    0.008s*)

    (*Reset Ltac Profile.*)
    Time start honing parser using indexed representation. (* 9.779 secs (9.776u,0.s) *)
    (*Show Ltac Profile.*)
(*total time:      6.180s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─replace_by_vm_compute_opt0_proj -------   0.0%  99.2%       2    6.132s
─clearbody vH --------------------------  92.6%  92.6%       1    5.724s
─destruct H ----------------------------   3.4%   3.4%       1    0.212s
─assert (H : v'H = vH) by (subst vH v'H;   1.6%   2.2%       1    0.136s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─replace_by_vm_compute_opt0_proj -------   0.0%  99.2%       2    6.132s
 ├─clearbody vH ------------------------  92.6%  92.6%       1    5.724s
 ├─destruct H --------------------------   3.4%   3.4%       1    0.212s
 └─assert (H : v'H = vH) by (subst vH v'   1.6%   2.2%       1    0.136s*)

    (*Reset Ltac Profile.*)
    Time hone method "splits". (* 10.388 secs (10.384u,0.004s) *)
    (*Show Ltac Profile.*)
(*total time:      5.524s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─Fiat.ADTRefinement.BuildADTRefinements.   0.4%  99.9%       1    5.520s
─fast_set' -----------------------------   0.0%  90.0%       1    4.972s
─set (x := y) --------------------------  90.0%  90.0%       1    4.972s
─eapply  (SharpenStep_BuildADT_ReplaceMe   3.3%   3.3%       1    0.184s
─simpl in * ----------------------------   2.8%   2.8%       2    0.120s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─Fiat.ADTRefinement.BuildADTRefinements.   0.4%  99.9%       1    5.520s
 ├─fast_set' ---------------------------   0.0%  90.0%       1    4.972s
 │└set (x := y) ------------------------  90.0%  90.0%       1    4.972s
 ├─eapply  (SharpenStep_BuildADT_Replace   3.3%   3.3%       1    0.184s
 └─simpl in * --------------------------   2.8%   2.8%       2    0.120s
*)
    {
      (*Reset Ltac Profile.*)
      Time progress simplify with monad laws. (* 14.273 secs (14.263u,0.007s) *)
      (*Show Ltac Profile.*)
      (*total time:     14.272s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify_with_applied_monad_laws ------   0.0% 100.0%       1   14.272s
─apply refine_bind_unit_helper ---------  24.5%  24.5%      16    0.780s
─apply refine_bind_bind_helper ---------  18.6%  18.6%      15    0.456s
─apply refine_unit_bind_helper ---------  16.7%  16.7%      15    0.592s
─eapply refine_under_bind_helper_1 -----  13.3%  13.3%      14    0.428s
─eapply refine_under_bind_helper_2 -----  13.2%  13.2%      14    0.432s
─eapply refine_under_bind_helper -------  13.2%  13.2%      14    0.424s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify_with_applied_monad_laws ------   0.0% 100.0%       1   14.272s
 ├─apply refine_bind_unit_helper -------  24.5%  24.5%      16    0.780s
 ├─apply refine_bind_bind_helper -------  18.6%  18.6%      15    0.456s
 ├─apply refine_unit_bind_helper -------  16.7%  16.7%      15    0.592s
 ├─eapply refine_under_bind_helper_1 ---  13.3%  13.3%      14    0.428s
 ├─eapply refine_under_bind_helper_2 ---  13.2%  13.2%      14    0.432s
 └─eapply refine_under_bind_helper -----  13.2%  13.2%      14    0.424s
*)
      Time lazymatch goal with
          | [ |- refine (x0 <- (opt2.fold_right
                                  (fun a a0 => If @?test a Then @?test_true a Else a0)
                                  ?base
                                  ?ls);
                         (@?r_o x0))
                        ?retv ]
            => pose proof (@refine_opt2_fold_right _ r_o retv test test_true base ls) as lem
           end. (* 4.853 secs (4.856u,0.s) *)
      Ltac thing lem :=
        let T := type of lem in
        match T with
        | forall v : Comp ?V, @?F v -> _
          => let v' := fresh in
             evar (v' : Comp V);
             let v'' := (eval cbv [v'] in v') in
             clear v';
             specialize (lem v'');
             let H := fresh in
             cut (F v'');
             [ intro H; specialize (lem H); clear H (*; thing lem *)
             | ]
        | _ => idtac
        end.
      (*Reset Ltac Profile.*)
      Time try (cbv [make_tower] in lem; thing lem; fail). (* 53.806 secs (45.207u,8.6s) *)
      (*Show Ltac Profile.*)
(*
total time:     15.800s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─cbv[make_tower] in lem ----------------  42.4%  42.4%       1    6.692s
─cut -----------------------------------  27.8%  27.8%       1    4.392s
─clear H -------------------------------  15.0%  15.0%       1    2.364s
─clear v' ------------------------------  14.9%  14.9%       1    2.348s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─cbv[make_tower] in lem ----------------  42.4%  42.4%       1    6.692s
─cut -----------------------------------  27.8%  27.8%       1    4.392s
─clear H -------------------------------  15.0%  15.0%       1    2.364s
─clear v' ------------------------------  14.9%  14.9%       1    2.348s
*) (* Where is all the time spent?! *)
      Undo.
      Time eapply lem. (* some large amount of time *)
      Undo.
      Time try (simple eapply lem; fail). (* 7230.418 secs (7228.456u,1.436s) *)
      Time cbv [make_tower] in lem. (* 4.45 secs (4.451u,0.s) *)
      Time simple eapply lem. (* 307.908 secs (307.68u,0.24s) *)
      (*Show Ltac Profile.*)
(*
      { Set Ltac Profiling.
        rewrite_disjoint_search_for.
        unfold DisjointLemmas.possible_characters.
        setoid_rewrite_ascii_mem.
        reflexivity.


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

      simplify parser splitter.
      Show Ltac Profile.
      (*
total time:     84.328s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  39.4%      20    4.268s
─rewrite_disjoint_search_for_no_clear --   0.0%  39.3%      20    4.260s
─rewrite_once_disjoint_search_for ------   0.0%  38.8%      40    4.240s
─rewrite_once_disjoint_search_for_specia  33.6%  38.3%      40    4.212s
─refine_binop_table --------------------   0.0%  37.9%       4    8.036s
─setoid_rewrite_refine_binop_table_idx -  37.0%  37.9%       4    8.032s
─simplify parser splitter --------------   0.0%  18.7%       2   14.980s
─simplify_parser_splitter' -------------   0.0%  18.7%      31   12.444s
─simplify ------------------------------   0.0%  18.7%       2   14.980s
─eapply (refine_opt2_fold_right r_o retv  13.5%  13.5%       1   11.364s
─simplify with monad laws --------------   0.0%   4.4%      30    1.900s
─simplify_with_applied_monad_laws ------   0.0%   4.4%      30    1.900s
─rewrite_disjoint_rev_search_for -------   0.0%   3.9%       2    1.636s
─rewrite_disjoint_rev_search_for_no_clea   0.0%   3.8%       2    1.632s
─rewrite_once_disjoint_rev_search_for --   0.0%   3.8%       4    1.608s
─rewrite_once_disjoint_rev_search_for_sp   3.4%   3.7%       4    1.572s
─specialize (lem' H') ------------------   2.7%   2.7%      44    1.996s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  39.4%      20    4.268s
└rewrite_disjoint_search_for_no_clear --   0.0%  39.3%      20    4.260s
└rewrite_once_disjoint_search_for ------   0.0%  38.8%      40    4.240s
└rewrite_once_disjoint_search_for_specia  33.6%  38.3%      40    4.212s
└specialize (lem' H') ------------------   2.6%   2.6%      40    1.996s
─refine_binop_table --------------------   0.0%  37.9%       4    8.036s
└setoid_rewrite_refine_binop_table_idx -  37.0%  37.9%       4    8.032s
─simplify parser splitter --------------   0.0%  18.7%       2   14.980s
└simplify ------------------------------   0.0%  18.7%       2   14.980s
└simplify_parser_splitter' -------------   0.0%  18.7%      31   12.444s
 ├─eapply (refine_opt2_fold_right r_o re  13.5%  13.5%       1   11.364s
 └─simplify with monad laws ------------   0.0%   4.4%      30    1.900s
  └simplify_with_applied_monad_laws ----   0.0%   4.4%      30    1.900s
─rewrite_disjoint_rev_search_for -------   0.0%   3.9%       2    1.636s
└rewrite_disjoint_rev_search_for_no_clea   0.0%   3.8%       2    1.632s
└rewrite_once_disjoint_rev_search_for --   0.0%   3.8%       4    1.608s
└rewrite_once_disjoint_rev_search_for_sp   3.4%   3.7%       4    1.572s
 *)
      Time finish honing parser method.
    }

    Time finish_Sharpening_SplitterADT.

  Time Defined. (* 85 seconds *)

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    Set Ltac Profiling.
    Time make_simplified_splitter ComputationalSplitter'. (* 19 s *)
    Show Ltac Profile.
  Time Defined.

Time End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Set Ltac Profiling.
  Time make_parser (@ComputationalSplitter(* _ String.string_stringlike _ _*)). (* 75 seconds *)
  Show Ltac Profile.
Time Defined.

(*Definition json_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.*)

Print json_parser(*_ocaml*).

Recursive Extraction json_parser(*_ocaml*).
(*
Definition main_json := premain json_parser.
Definition main_json_ocaml := premain_ocaml json_parser_ocaml.

Parameter reference_json_parser : Coq.Strings.String.string -> bool.
Parameter reference_json_parser_ocaml : Ocaml.Ocaml.string -> bool.
Extract Constant reference_json_parser
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (List.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".
Extract Constant reference_json_parser_ocaml
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (String.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".

Definition main_json_reference := premain reference_json_parser.
Definition main_json_reference_ocaml := premain_ocaml reference_json_parser_ocaml.

(*
(* val needs_b : bool Pervasives.ref;; *)
let needs_b = Pervasives.ref false;;

let chan = match Array.length Sys.argv with
| 0 | 1 -> Pervasives.stdin
| 2 -> let chan = Pervasives.open_in Sys.argv.(1)
       in Pervasives.at_exit (fun () -> Pervasives.close_in chan);
	  chan
| argc -> Pervasives.exit argc;;

(* val line : string;; *)
let line = Pervasives.input_line chan;;

String.iter (fun ch ->
  match ch, !needs_b with
  | 'a', false -> needs_b := true; ()
  | 'b', true  -> needs_b := false; ()
  | _, _       -> Pervasives.exit 1)
  line;;

Pervasives.exit 0;;
*)
(*
Definition test0 := json_parser "".
Definition test1 := json_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := json_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
*)
*)
*)
