(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.MSets.MSetPositive.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.AsciiLattice.
Require Import Fiat.Parsers.Refinement.PossibleTerminalsSets.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Parsers.StringLike.LastChar.
Require Import Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Import Fiat.Parsers.StringLike.LastCharSuchThat.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Common.MSetExtensions.
Require Import Fiat.Common.
Require Import Fiat.Parsers.StringLike.Core.

Set Implicit Arguments.

Record possible_terminals_result :=
  { possible_characters :> possible_characters_result;
    might_be_empty :> bool }.

Definition possible_terminals_empty (v : possible_characters_result) : bool
  := PositiveSet.equal v PositiveSet.empty.

Definition possible_terminals_map {A} (f : Ascii.ascii -> A) (v : possible_characters_result) : list A
  := List.map (fun x => f (Ascii.ascii_of_pos x)) (PositiveSet.elements v).

Definition disjoint_characters (a b : possible_characters_result) : bool
  := PositiveSet.equal (PositiveSet.inter a b) PositiveSet.empty.

Definition disjoint (a b : possible_terminals_result) : bool
  := disjoint_characters a b.

Lemma disjoint_characters_sym x y : disjoint_characters x y = disjoint_characters y x.
Proof.
  unfold disjoint_characters.
  PositiveSetExtensions.to_caps; PositiveSetExtensions.BasicDec.fsetdec.
Qed.

Global Instance disjoint_characters_Symmetric : Symmetric disjoint_characters.
Proof.
  intros ???.
  rewrite disjoint_characters_sym; assumption.
Qed.

Global Instance disjoint_Symmetric : Symmetric disjoint
  := disjoint_characters_Symmetric.

Definition char_in_characters (ch : Ascii.ascii) (v : possible_characters_result) : bool
  := PositiveSet.mem (pos_of_ascii ch) v.

Definition char_in (ch : Ascii.ascii) (v : possible_terminals_result) : bool
  := char_in_characters ch v.

Lemma disjoint_in_char_in
      (ch : Ascii.ascii) (v1 v2 : possible_characters_result)
      (Hd : disjoint_characters v1 v2)
      (H : PositiveSet.In (pos_of_ascii ch) v1)
  : char_in_characters ch v2 = false.
Proof.
  unfold char_in_characters.
  PositiveSetExtensions.to_caps; intro H'.
  PositiveSetExtensions.BasicDec.fsetdec.
Qed.


Section definitions.
  Context (G : pregrammar' Ascii.ascii)
          {apdata : all_possible_data G}
          {pdata : possible_data G}.

  Definition possible_terminals_of : String.string -> possible_terminals_result
    := fun nt => {| possible_characters := all_possible_characters_of_nt G nt;
                    might_be_empty := might_be_empty_of_pr_nt G nt |}.

  Definition possible_first_terminals_of : String.string -> possible_terminals_result
    := fun nt => {| possible_characters := possible_first_characters_of_nt G nt;
                    might_be_empty := might_be_empty_of_pr_nt G nt |}.

  Definition possible_last_terminals_of : String.string -> possible_terminals_result
    := fun nt => {| possible_characters := possible_last_characters_of_nt G nt;
                    might_be_empty := might_be_empty_of_pr_nt G nt |}.

  Definition possible_terminals_of_production : production Ascii.ascii -> possible_terminals_result
    := fun ps => {| possible_characters := all_possible_characters_of_production G ps;
                    might_be_empty := might_be_empty_of_pr_production G ps |}.

  Definition possible_first_terminals_of_production : production Ascii.ascii -> possible_terminals_result
    := fun ps => {| possible_characters := possible_first_characters_of_production G ps;
                    might_be_empty := might_be_empty_of_pr_production G ps |}.

  Definition possible_last_terminals_of_production : production Ascii.ascii -> possible_terminals_result
    := fun ps => {| possible_characters := possible_last_characters_of_production G ps;
                    might_be_empty := might_be_empty_of_pr_production G ps |}.
End definitions.

Global Arguments possible_terminals_of_production G {_ _} _.
Global Arguments possible_terminals_of G {_ _} _.
Global Arguments possible_first_terminals_of_production G {_} _.
Global Arguments possible_first_terminals_of G {_} _.
Global Arguments possible_last_terminals_of_production G {_} _.
Global Arguments possible_last_terminals_of G {_} _.

Local Open Scope string_like_scope.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          (G : pregrammar' Ascii.ascii)
          {apdata : all_possible_data G}
          {pdata : possible_data G}.

  Lemma possible_first_terminals_of_production_is_char
        its str
        (pits : parse_of_production G str its)
        P
        (Heq : fold_right
                 and True
                 (possible_terminals_map
                    P
                    (possible_first_terminals_of_production G its)))
    : length str = 0 \/ exists ch, take 1 str ~= [ch] /\ P ch.
  Proof.
    pose proof (possible_first_characters_parse_of_production pits) as Hp.
    destruct (length str) eqn:Hlen; [ left; reflexivity | right ].
    apply for_first_char_exists in Hp; [ | omega ].
    destruct Hp as [ch [? Hp]]; exists ch; split; [ assumption | ].
    setoid_rewrite fold_right_and_True_map in Heq.
    rewrite <- ascii_of_pos_of_ascii.
    apply Heq.
    unfold possible_first_terminals_of_production; simpl.
    clear -Hp.
    rewrite <- InA_In_eq.
    rewrite <- PositiveSet.elements_spec1 in Hp.
    assumption.
  Qed.
End correctness.

Section search.
  Context {G : pregrammar' Ascii.ascii}
          {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {apdata : all_possible_data G}
          {pdata : possible_data G}.

  Local Ltac disjoint_t' :=
    idtac;
    match goal with
    | _ => assumption
    | [ |- is_true true ] => reflexivity
    | _ => congruence
    | [ |- is_first_char_such_that _ _ _ _ ] => split
    | [ |- is_after_last_char_such_that _ _ _ ] => split
    | _ => progress unfold possible_terminals_of, disjoint, char_in in *
    | _ => progress simpl in *
    | [ pit : parse_of_item (grammar_of_pregrammar ?G) _ (NonTerminal ?nt) |- _ ]
      => pose proof (all_possible_characters_of_item_nt pit);
         pose proof (possible_first_characters_parse_of_item_nt pit);
         pose proof (possible_last_characters_parse_of_item_nt pit);
         pose proof (fun Hlen => might_be_empty_pr_parse_of_item_nt Hlen pit);
         clear pit
    | [ pits : parse_of_production (grammar_of_pregrammar ?G) _ _ |- _ ]
      => pose proof (all_possible_characters_of_parse_of_production pits);
         pose proof (possible_first_characters_parse_of_production pits);
         pose proof (possible_last_characters_parse_of_production pits);
         pose proof (fun Hlen => might_be_empty_pr_parse_of_production Hlen pits);
         clear pits
    | _ => progress bool_congr_setoid
    | _ => progress rewrite_strat topdown hints bool_congr_setoid
    | [ H : context[length (drop _ _)] |- _ ] => rewrite drop_length in H
    | [ |- (_ /\ ?n < length ?str) \/ (_ /\ length ?str <= ?n) ]
      => destruct (Compare_dec.le_gt_dec (length str) n); [ right | left ]
    | [ H : context[?x - ?y], H' : ?x <= ?y |- _ ]
      => replace (x - y) with 0 in H by (clear -H'; omega)
    | _ => progress specialize_by ltac:(exact eq_refl)
    | [ H : forall_chars ?str _ |- for_first_char ?str _ ]
      => apply forall_chars__impl__for_first_char in H
    | [ H0 : is_true (disjoint_characters ?x ?y), H1 : ?P (fun ch => PositiveSet.In (pos_of_ascii ch) ?y') |- ?P _ ]
      => first [ constr_eq y y' | constr_eq x y' ];
         let x' := match goal with
                   | [ |- P (fun ch => is_true (negb (char_in_characters ch ?x'))) ] => x'
                   | [ |- P (fun ch => ~is_true (char_in_characters ch ?x')) ] => x'
                   end in
         first [ constr_eq y x' | constr_eq x x' ];
         revert H1;
         match goal with
         | [ |- for_first_char _ _ -> _ ] => apply for_first_char_Proper
         | [ |- for_last_char _ _ -> _ ] => apply for_last_char_Proper
         | [ |- forall_chars _ _ -> _ ] => apply forall_chars_Proper
         end;
         [ reflexivity | intros ?? ]
    | _ => erewrite disjoint_in_char_in by first [ eassumption | symmetry; eassumption ]
    | [ |- and _ _ ] => split
    end.

  Local Ltac disjoint_t := repeat disjoint_t'.

  Section forward.
    Context (str : String)
            {nt its}
            (H_disjoint : disjoint (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
            {n}
            (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
            (pits : parse_of_production G (StringLike.drop n str) its).

    Lemma terminals_disjoint_search_for_not
      : is_first_char_such_that
          (might_be_empty (possible_first_terminals_of_production G its))
          str
          n
          (fun ch => negb (char_in ch (possible_terminals_of G nt))).
    Proof. disjoint_t. Qed.

    Lemma terminals_disjoint_search_for
      : is_first_char_such_that
          (might_be_empty (possible_first_terminals_of_production G its))
          str
          n
          (fun ch => char_in ch (possible_first_terminals_of_production G its)).
    Proof. disjoint_t. Qed.
  End forward.

  Section backward.
    Context (str : String)
            {nt its}
            (H_disjoint : disjoint (possible_last_terminals_of G nt) (possible_terminals_of_production G its))
            {n}
            (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
            (pits : parse_of_production G (StringLike.drop n str) its).

    Lemma terminals_disjoint_rev_search_for_not
      : is_after_last_char_such_that
          str
          n
          (fun ch => negb (char_in ch (possible_terminals_of_production G its))).
    Proof. disjoint_t. Qed.

    Lemma terminals_disjoint_rev_search_for
      : is_after_last_char_such_that
          str
          n
          (fun ch => char_in ch (possible_last_terminals_of G nt)).
    Proof. disjoint_t. Qed.
  End backward.
End search.

Lemma ascii_mem v
      (H : PositiveSet.cardinal v = 1)
      ch'
      (H' : PositiveSet.choose v = Some ch')
      (Hch' : pos_of_ascii (Ascii.ascii_of_pos ch') = ch')
      ch''
      (Hch'' : Ascii.ascii_of_pos ch' = ch'')
      ch
  : PositiveSet.mem (pos_of_ascii ch) v = Equality.ascii_beq ch'' ch.
Proof.
  apply PositiveSet.choose_spec1 in H'.
  destruct (Equality.ascii_beq ch'' ch) eqn:Hch; subst ch''.
  { apply Equality.ascii_bl in Hch; instantiate; subst ch.
    PositiveSetExtensions.BasicDec.fsetdec. }
  { PositiveSetExtensions.to_caps.
    intro; apply Hch; clear Hch.
    apply Equality.ascii_beq_true_iff.
    rewrite <- ascii_of_pos_of_ascii; apply f_equal.
    eapply PositiveSetExtensions.cardinal_one_In_same; eassumption. }
Qed.
