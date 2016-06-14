(** Sharpened ADT for JSON *)
Require Import Fiat.Parsers.Grammars.JSONImpoverished.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.Refinement.SharpenedJSON.


Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  (*Set Ltac Profiling.*)
  Time let splitter := constr:(@ComputationalSplitter(* _ String.string_stringlike _ _*)) in
           (idtac;
  let str := match goal with
               | [ str : String.string |- _ ] => constr:(str)
               | [ str : Ocaml.Ocaml.string |- _ ] => constr:(str)
             end in
  let b := make_Parser splitter in
  let b := constr:(ParserInterface.has_parse b str) in
  let b' := (let term := b in
             let term := match term with
                | appcontext[ParserFromParserADT.parser _ ?splitter]
                  => let splitter' := head splitter in
                     (eval unfold splitter' in term)
                | _ => constr:(term)
              end in
  let term := match term with
                | appcontext[@ParserInterface.has_parse _ (grammar_of_pregrammar ?G)]
                  => let G' := head G in
                     (eval unfold G' in term)
                | _ => constr:(term)
              end in
  let dummy := cidtac "starting parser_red0" in
  let dummy := cidtac "starting parser_red0" in
  let term := (eval parser_red0 in term) in
  let dummy := cidtac "starting parser_red1" in
  let dummy := cidtac "starting parser_red1" in
  let term := (eval parser_red1 in term) in
  let dummy := cidtac "starting parser_red2" in
  let dummy := cidtac "starting parser_red2" in
  let term := (eval parser_red2 in term) in
  let dummy := cidtac "starting parser_red3" in
  let dummy := cidtac "starting parser_red3" in
  let term := (eval parser_red3 in term) in
  let dummy := cidtac "starting parser_red4" in
  let dummy := cidtac "starting parser_red4" in
  let term := (eval parser_red4 in term) in
  let dummy := cidtac "starting parser_red5" in
  let dummy := cidtac "starting parser_red5" in
  let term := (eval parser_red5 in term) in (* this runs through 64 GB of RAM *)
  let dummy := cidtac "starting parser_red6" in
  let dummy := cidtac "starting parser_red6" in
  let term := (eval parser_red6 in term) in
  let dummy := cidtac "starting parser_red7" in
  let dummy := cidtac "starting parser_red7" in
  let term := (eval parser_red7 in term) in
  let dummy := cidtac "starting parser_red8" in
  let dummy := cidtac "starting parser_red8" in
  let term := (eval parser_red8 in term) in
  let dummy := cidtac "starting parser_red9" in
  let dummy := cidtac "starting parser_red9" in
  let term := (parser_red9_manual term) in
  let dummy := cidtac "starting parser_red10" in
  let dummy := cidtac "starting parser_red10" in
  let term := (eval parser_red10 in term) in
  let dummy := cidtac "starting parser_red11" in
  let dummy := cidtac "starting parser_red11" in
  let term := (parser_red11_manual term) in
  let dummy := cidtac "starting parser_red12" in
  let dummy := cidtac "starting parser_red12" in
  let term := (eval parser_red12 in term) in
  let dummy := cidtac "finished parser_red12" in
  let dummy := cidtac "finished parser_red12" in
(*
  let term := (match do_simpl_list_map with
                 | true => eval simpl List.map in term
                 | _ => term
               end) in
  let term := (eval parser_red17 in term) in*)
  constr:(term)) in
  (* exact_no_check b' *)
  pose b').

  (*Time make_parser (@ComputationalSplitter(* _ String.string_stringlike _ _*)).*)
  Show Ltac Profile.
Time Defined.

(*Definition json_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.*)

Print json_parser(*_ocaml*).

Recursive Extraction json_parser(*_ocaml*).

(*

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Set Ltac Profiling.
  Time let splitter := constr:(@ComputationalSplitter(* _ String.string_stringlike _ _*)) in
       (idtac;
  let str := match goal with
               | [ str : String.string |- _ ] => constr:(str)
               | [ str : Ocaml.Ocaml.string |- _ ] => constr:(str)
             end in
  let b := make_Parser splitter in
  let b := constr:(ParserInterface.has_parse b str) in
  pose b).
Locate grammar_of_pregrammar.
  let term := (eval cbv [b] in b) in
  lazymatch term with
                | appcontext[@ParserInterface.has_parse _ (ContextFreeGrammar.PreNotations.grammar_of_pregrammar ?G)]
                  => let G' := head G in

              end.
  let b' := (let term := b in

  let term := lazymatch term with
                | context[@ParserInterface.has_parse _ (grammar_of_pregrammar ?G)]
                  => let G' := head G in
                     (eval unfold G' in term)
              end in
  let term := match term with
                | context[ParserFromParserADT.parser _ ?splitter]
                  => let splitter' := head splitter in
                     (eval unfold splitter' in term)
                | _ => constr:(term)
              end in
  let dummy := cidtac "starting parser_red0" in
  let dummy := cidtac "starting parser_red0" in
  let term := (eval parser_red0 in term) in
  let dummy := cidtac "starting parser_red1" in
  let dummy := cidtac "starting parser_red1" in
  let term := (eval parser_red1 in term) in
  let dummy := cidtac "starting parser_red2" in
  let dummy := cidtac "starting parser_red2" in
  let term := (eval parser_red2 in term) in
  let dummy := cidtac "starting parser_red3" in
  let dummy := cidtac "starting parser_red3" in
  let term := (eval parser_red3 in term) in
  let dummy := cidtac "starting parser_red4" in
  let dummy := cidtac "starting parser_red4" in
  let term := (eval parser_red4 in term) in
  let dummy := cidtac "starting parser_red5" in
  let dummy := cidtac "starting parser_red5" in
  let term := (eval parser_red5 in term) in
  let dummy := cidtac "starting parser_red6" in
  let dummy := cidtac "starting parser_red6" in
  let term := (eval parser_red6 in term) in
  let dummy := cidtac "starting parser_red7" in
  let dummy := cidtac "starting parser_red7" in
  let term := (eval parser_red7 in term) in
  let dummy := cidtac "starting parser_red8" in
  let dummy := cidtac "starting parser_red8" in
  let term := (eval parser_red8 in term) in
  let dummy := cidtac "starting parser_red9" in
  let dummy := cidtac "starting parser_red9" in
  let term := (parser_red9_manual term) in
  let dummy := cidtac "starting parser_red10" in
  let dummy := cidtac "starting parser_red10" in
  let term := (eval parser_red10 in term) in
  let dummy := cidtac "starting parser_red11" in
  let dummy := cidtac "starting parser_red11" in
  let term := (parser_red11_manual term) in
  let dummy := cidtac "starting parser_red12" in
  let dummy := cidtac "starting parser_red12" in
  let term := (eval parser_red12 in term) in
  let dummy := cidtac "finished parser_red12" in
  let dummy := cidtac "finished parser_red12" in
(*
  let term := (match do_simpl_list_map with
                 | true => eval simpl List.map in term
                 | _ => term
               end) in
  let term := (eval parser_red17 in term) in*)
  constr:(term)) in
  pose b').
Set Printing Depth 100000.

pose
(Def Method "length" (r : rep) : rep * nat :=   (r, length r) )%cMethDef.
Set Printing All.
Print getcMethDef.

  Time make_parser (@ComputationalSplitter(* _ String.string_stringlike _ _*)).
  Show Ltac Profile.
Time Defined.

(*Definition json_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.*)

Print json_parser(*_ocaml*).

Recursive Extraction json_parser(*_ocaml*).
*)
