(** Sharpened ADT for JSON *)
Require Import Fiat.Parsers.Grammars.JSONImpoverished.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.
Require Fiat.Parsers.Refinement.SharpenedJSON.

Section IndexedImpl.
  Time Definition ComputationalSplitter'
  : FullySharpened (string_spec json'_grammar string_stringlike)
    := Eval cbv delta [SharpenedJSON.ComputationalSplitter'] in SharpenedJSON.ComputationalSplitter'.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    (*Start Profiling.*)
    Time make_simplified_splitter ComputationalSplitter'.
    (*Show Profile.*)
  Time Defined.

Time End IndexedImpl.
