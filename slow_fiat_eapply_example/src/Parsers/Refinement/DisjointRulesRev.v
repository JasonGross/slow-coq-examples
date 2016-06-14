(** Refinement rules for disjoint rules *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.Refinement.PreTactics.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.LastCharSuchThat.
Require Import Fiat.Parsers.StringLike.LastChar.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.Refinement.PossibleTerminalsSets.

Set Implicit Arguments.

Local Arguments minus !_ !_.

Definition rev_search_for_condition
           {HSLM : StringLikeMin Ascii.ascii}
           {HSL : StringLike Ascii.ascii}
           (G : pregrammar' Ascii.ascii)
           {pdata : possible_data G}
           str nt (n : nat)
  := is_after_last_char_such_that
       str
       n
       (fun ch => char_in ch (possible_last_terminals_of G nt)).

Global Arguments rev_search_for_condition {_ _} G {_} _ _ _.

Lemma refine_disjoint_rev_search_for'
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      (G : pregrammar' Ascii.ascii)
      {apdata : all_possible_data G}
      {pdata : possible_data G}
      {str offset len nt its}
      (H_disjoint : disjoint
                      (possible_last_terminals_of G nt)
                      (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str offset len
             (NonTerminal nt::its) splits}
         (n <- { n : nat | n <= length (substring offset len str)
                           /\ ((exists n', rev_search_for_condition G (substring offset len str) nt n')
                               -> rev_search_for_condition G (substring offset len str) nt n) };
          ret [n]).
Proof.
  intros ls H.
  computes_to_inv; subst.
  destruct H as [H0 H1].
  apply PickComputes.
  hnf; cbv zeta.
  intros Hlen it' its' Heq n ? H_reachable pit pits.
  inversion Heq; subst it' its'; clear Heq.
  left.
  pose proof (terminals_disjoint_rev_search_for _ H_disjoint pit pits) as H'.
  specialize (H1 (ex_intro _ n H')).
  unfold rev_search_for_condition in H1.
  pose proof (is_after_last_char_such_that_eq_nat_iff H1 H') as H''.
  destruct_head or; destruct_head and; subst;
  rewrite ?Min.min_r, ?Min.min_l by assumption;
  omega.
Qed.

Definition rev_search_for_not_condition
           {HSLM : StringLikeMin Ascii.ascii}
           {HSL : StringLike Ascii.ascii}
           (G : pregrammar' Ascii.ascii)
           {apdata : all_possible_data G}
           {pdata : possible_data G}
           str its n
  := is_after_last_char_such_that
       str
       n
       (fun ch => negb (char_in ch (possible_terminals_of_production G its))).

Global Arguments rev_search_for_not_condition {_ _} G {_ _} _ _ _.

Lemma refine_disjoint_rev_search_for_not'
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {apdata : all_possible_data G}
      {pdata : possible_data G}
      {str offset len nt its}
      (H_disjoint : disjoint
                      (possible_last_terminals_of G nt)
                      (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str offset len
             (NonTerminal nt::its)
             splits}
         (n <- { n : nat | n <= length (substring offset len str)
                           /\ ((exists n', rev_search_for_not_condition G (substring offset len str) its n')
                               -> rev_search_for_not_condition G (substring offset len str) its n) };
          ret [n]).
Proof.
  intros ls H.
  computes_to_inv; subst.
  destruct H as [H0 H1].
  apply PickComputes.
  hnf; cbv zeta.
  intros Hlen it' its' Heq n ? H_reachable pit pits.
  inversion Heq; subst it' its'; clear Heq.
  left.
  pose proof (terminals_disjoint_rev_search_for_not _ H_disjoint pit pits) as H'.
  specialize (H1 (ex_intro _ n H')).
  pose proof (is_after_last_char_such_that_eq_nat_iff H1 H') as H''.
  destruct_head or; destruct_head and; subst;
  rewrite ?Min.min_r by assumption;
  omega.
Qed.

Lemma find_after_last_char_such_that'_short {Char HSLM HSL}
      str P len
: @find_after_last_char_such_that' Char HSLM HSL P len str <= len.
Proof.
  revert str; induction len; simpl; intros; [ omega | ].
  destruct (get len str) eqn:H.
  { edestruct P; try omega.
    rewrite IHlen; omega. }
  { rewrite IHlen; omega. }
Qed.

Lemma find_after_last_char_such_that_short {Char HSLM HSL}
      str P
: @find_after_last_char_such_that Char HSLM HSL str P <= length str.
Proof.
  apply find_after_last_char_such_that'_short.
Qed.

Lemma refine_find_after_last_char_such_that {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
      (str : String)
      (P : Char -> bool)
: refine { n : nat | n <= length str
                     /\ ((exists n', is_after_last_char_such_that str n' P)
                         -> is_after_last_char_such_that str n P) }
         (ret (find_after_last_char_such_that str P)).
Proof.
  intros v H.
  computes_to_inv; subst.
  apply PickComputes.
  split; [ apply find_after_last_char_such_that_short | ].
  apply is_after_last_char_such_that__find_after_last_char_such_that.
Qed.

Lemma refine_disjoint_rev_search_for
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {apdata : all_possible_data G}
      {pdata : possible_data G}
      {str offset len nt its}
      (H_disjoint : disjoint
                      (possible_last_terminals_of G nt)
                      (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str offset len
             (NonTerminal nt::its)
             splits}
         (ret [find_after_last_char_such_that (substring offset len str) (fun ch => char_in ch (possible_last_terminals_of G nt))]).
Proof.
  rewrite refine_disjoint_rev_search_for' by eassumption.
  setoid_rewrite refine_find_after_last_char_such_that.
  simplify with monad laws; reflexivity.
Qed.

Lemma refine_disjoint_rev_search_for_not
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {apdata : all_possible_data G}
      {pdata : possible_data G}
      {str offset len nt its}
      (H_disjoint : disjoint
                      (possible_last_terminals_of G nt)
                      (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str offset len
             (NonTerminal nt::its)
             splits}
         (ret [find_after_last_char_such_that (substring offset len str) (fun ch => negb (char_in ch (possible_terminals_of_production G its)))]).
Proof.
  rewrite refine_disjoint_rev_search_for_not' by assumption.
  setoid_rewrite refine_find_after_last_char_such_that.
  simplify with monad laws; reflexivity.
Qed.

Lemma refine_disjoint_rev_search_for_idx
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {apdata : all_possible_data G}
      {pdata : possible_data G}
      {str offset len nt its idx}
      (Heq : default_to_production (G := G) idx = NonTerminal nt :: its)
      (H_disjoint : disjoint
                      (possible_last_terminals_of G nt)
                      (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete_idx
             G str offset len
             idx
             splits}
         (ret [find_after_last_char_such_that (substring offset len str) (fun ch => char_in ch (possible_last_terminals_of G nt))]).
Proof.
  unfold split_list_is_complete_idx.
  erewrite <- refine_disjoint_rev_search_for by eassumption.
  rewrite Heq.
  apply refine_pick_pick; intro; trivial.
Qed.

Lemma refine_disjoint_rev_search_for_not_idx
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {apdata : all_possible_data G}
      {pdata : possible_data G}
      {str offset len nt its idx}
      (Heq : default_to_production (G := G) idx = NonTerminal nt :: its)
      (H_disjoint : disjoint
                      (possible_last_terminals_of G nt)
                      (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete_idx
             G str offset len
             idx
             splits}
         (ret [find_after_last_char_such_that (substring offset len str) (fun ch => negb (char_in ch (possible_terminals_of_production G its)))]).
Proof.
  unfold split_list_is_complete_idx.
  erewrite <- refine_disjoint_rev_search_for_not by eassumption.
  rewrite Heq.
  apply refine_pick_pick; intro; trivial.
Qed.

Ltac solve_disjoint_side_conditions :=
  idtac;
  lazymatch goal with
  | [ |- Carriers.default_to_production (G := ?G) ?k = ?e ]
    => try cbv delta [G];
       cbv beta iota zeta delta [Carriers.default_to_production Lookup_idx fst snd List.map pregrammar_productions List.length List.nth minus Operations.List.drop];
       try reflexivity
  | [ |- is_true (DisjointLemmas.disjoint _ _) ]
    => vm_compute; try reflexivity
  end.

Ltac pose_disjoint_rev_search_for lem :=
  idtac;
  let G := match goal with |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] => G end in
  let HSLM := match goal with |- appcontext[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL] => HSLM end in
  let HSL := match goal with |- appcontext[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL] => HSL end in
  let lem' := constr:(@refine_disjoint_rev_search_for_idx HSLM HSL _ _ _ G) in
  let lem' := constr:(lem' _ _) in
  let lem' := match goal with
              | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
                => constr:(fun idx' nt its => lem' str offset len nt its idx')
              end in
  pose proof lem' as lem.
Ltac rewrite_once_disjoint_rev_search_for_specialize lem lem' :=
  idtac;
  let G := (lazymatch goal with
             | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
               => G
             end) in
  match goal with
  | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
    => pose proof (lem idx) as lem';
       do 2 (lazymatch type of lem' with
              | forall a : ?T, _ => idtac; let x := fresh in evar (x : T); specialize (lem' x); subst x
              end);
       let T := match type of lem' with forall a : ?T, _ => T end in
       let H' := fresh in
       assert (H' : T) by solve_disjoint_side_conditions;
       specialize (lem' H'); clear H';
       let x := match type of lem' with
                | context[possible_last_terminals_of ?G ?ls]
                  => constr:(possible_last_terminals_of G ls)
                end in
       replace_with_vm_compute_in x lem';
       unfold char_in, char_in_characters, possible_characters in lem';
       change (orb false) with (fun bv : bool => bv) in lem';
       cbv beta in lem';
       let T := match type of lem' with forall a : ?T, _ => T end in
       let H' := fresh in
       assert (H' : T) by solve_disjoint_side_conditions;
       specialize (lem' H'); clear H'
  end.
Ltac rewrite_once_disjoint_rev_search_for lem :=
  let lem' := fresh "lem'" in
  rewrite_once_disjoint_rev_search_for_specialize lem lem';
  setoid_rewrite lem'; clear lem'.
Ltac rewrite_disjoint_rev_search_for_no_clear lem :=
  pose_disjoint_rev_search_for lem;
  progress repeat rewrite_once_disjoint_rev_search_for lem.
Ltac rewrite_disjoint_rev_search_for :=
  idtac;
  let lem := fresh "lem" in
  rewrite_disjoint_rev_search_for_no_clear lem;
  clear lem.

Global Arguments possible_data {_}.
Global Arguments all_possible_data {_}.
