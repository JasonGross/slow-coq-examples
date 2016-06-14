Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.ParserSemantics.
Require Import Fiat.Parsers.Reflective.PartialUnfold.
Require Import Fiat.Parsers.Reflective.ParserPartialUnfold.
Require Import Fiat.Parsers.Reflective.ParserLogicalRelations.
Set Implicit Arguments.

Section polypnormalize.
  Context (is_valid_nonterminal : list nat -> nat -> bool)
          (strlen : nat)
          (char_at_matches_interp : nat -> Reflective.RCharExpr Ascii.ascii -> bool)
          (split_string_for_production : nat * (nat * nat) -> nat -> nat -> list nat).

  Let interp {T} := interp_has_parse_term (T := T) is_valid_nonterminal strlen char_at_matches_interp split_string_for_production.

  Lemma polypnormalize_correct {T} (term : polyhas_parse_term T)
    : ParserSyntaxEquivalence.has_parse_term_equiv
        nil
        (term interp_TypeCode) (term (normalized_of interp_TypeCode))
      -> interp (term _) = interp (polypnormalize term _).
  Proof.
    subst interp.
    apply polypnormalize_correct; assumption.
  Qed.
End polypnormalize.
