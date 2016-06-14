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

    Time start sharpening ADT.

    Start Profiling.
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
    pose v as H; pose v' as H'; cbv beta in H, H'. (* 134 s *)
    Show Profile.

    Start Profiling.
    Time start honing parser using indexed representation.
    Show Profile.

    Start Profiling.
    Time hone method "splits".
    Show Profile.
    {
      Start Profiling.
      Time progress simplify with monad laws.
      Time lazymatch goal with
          | [ |- refine (x0 <- (opt2.fold_right
                                  (fun a a0 => If @?test a Then @?test_true a Else a0)
                                  ?base
                                  ?ls);
                         (@?r_o x0))
                        ?retv ]
            => pose proof (@refine_opt2_fold_right _ r_o retv test test_true base ls) as lem
           end.
      Time eapply lem.
      Undo.
      Time try (simple eapply lem; fail).
      Time cbv [make_tower] in lem.
      Time simple eapply lem.
      Show Profile.
(*
      { Start Profiling.
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
      Show Profile.
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
    Start Profiling.
    Time make_simplified_splitter ComputationalSplitter'. (* 19 s *)
    Show Profile.
  Time Defined.

Time End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Start Profiling.
  Time make_parser (@ComputationalSplitter(* _ String.string_stringlike _ _*)). (* 75 seconds *)
  Show Profile.
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