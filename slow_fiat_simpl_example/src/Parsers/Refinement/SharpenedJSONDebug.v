(** Sharpened ADT for JSON *)
Require Import Fiat.Parsers.Grammars.JSONImpoverished.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.
Require Fiat.Parsers.Refinement.SharpenedJSON.

Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
Proof.
  (*Set Ltac Profiling.*)
  Time let splitter := constr:(SharpenedJSON.ComputationalSplitter') in
  idtac;
  let term := constr:(projT1 splitter) in
  let h := head splitter in
  let term := match constr:(Set) with
              | _ => (eval cbv [h] in term)
              | _ => term
              end in
  idtac "<infomsg>before splitter_red0</infomsg>";
  let term := (eval splitter_red0 in term) in
  pose term as term0. (* 16 s *)
  Time simpl @fst in term0. (* 0.008 s *)
  Time simpl @snd in term0. (* 158 hours and counting, even though really all I want to do is [change (fst (?x, ?y)) with x] *)
  Time let splitter := constr:(SharpenedJSON.ComputationalSplitter') in
  let impl := (eval cbv [term0] in term0) in
  refine (existT _ impl _);
  abstract (exact (projT2 splitter)).
  (*Show Ltac Profile.*)
Time Defined.
