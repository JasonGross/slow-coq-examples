(** Sharpened ADT for JSON *)
Require Import Fiat.Parsers.Grammars.JSONImpoverished.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.
Require Fiat.Parsers.Refinement.SharpenedJSONNative.

Section IndexedImpl.
  Time Definition ComputationalSplitter'
  : FullySharpened (string_spec json'_grammar string_stringlike)
    := Eval cbv delta [SharpenedJSONNative.ComputationalSplitter'] in SharpenedJSONNative.ComputationalSplitter'.
Time End IndexedImpl.
