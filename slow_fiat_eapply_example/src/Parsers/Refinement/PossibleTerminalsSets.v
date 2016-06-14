Require Import Coq.MSets.MSetPositive.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.StringLike.FirstChar Fiat.Parsers.StringLike.LastChar Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.AsciiLattice.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Prod.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.ProdAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretation.
Require Import Fiat.Parsers.Refinement.EmptyLemmas.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope grammar_fixedpoint_scope.

Definition all_possible_ascii' : PositiveSet.t
  := List.fold_right
       PositiveSet.add
       PositiveSet.empty
       (List.map (fun x => BinPos.Pos.of_nat (S x))
                 (Operations.List.up_to (S (Ascii.nat_of_ascii (Ascii.Ascii true true true true true true true true))))).

Definition all_possible_ascii : PositiveSet.t
  := Eval compute in all_possible_ascii'.

Definition pos_of_ascii (x : Ascii.ascii) : BinNums.positive
  := BinPos.Pos.of_nat match Ascii.nat_of_ascii x with
                       | 0 => (S (Ascii.nat_of_ascii (Ascii.Ascii true true true true true true true true)))
                       | x' => x'
                       end.

Lemma ascii_of_pos_of_ascii x : Ascii.ascii_of_pos (pos_of_ascii x) = x.
Proof.
  destruct x; destruct_head bool; vm_compute; reflexivity.
Qed.

Lemma In_all ch
  : PositiveSet.In (pos_of_ascii ch) all_possible_ascii.
Proof.
  destruct ch; destruct_head bool; vm_compute; reflexivity.
Qed.

Definition all_but (P : Ascii.ascii -> bool) : PositiveSet.t
  := PositiveSet.filter (fun n => negb (P (Ascii.ascii_of_pos n))) all_possible_ascii.

Lemma not_In_all_but P ch
  : (~PositiveSet.In (pos_of_ascii ch) (all_but P)) <-> P ch.
Proof.
  unfold all_but.
  setoid_rewrite PositiveSet.filter_spec; [ | congruence.. ].
  setoid_rewrite (LogicFacts.True_iff (In_all ch)).
  rewrite ascii_of_pos_of_ascii.
  destruct (P ch); intuition.
Qed.

Global Instance all_possible_terminals_aidata : @AbstractInterpretation Ascii.ascii PositiveSet.t _.
Proof.
  refine {| on_terminal P := constant (all_but P);
            on_nil_production := constant all_possible_ascii;
            precombine_production x y := constant (PositiveSet.inter x y) |}.
Defined.

Section with_empty.
  Context (G : pregrammar' Ascii.ascii).

  Definition possible_terminals_prestate
    := (@state _ might_be_empty_lattice (* is_empty? *)
        * lattice_for (@state _ positive_set_fpdata (* possible first terminals *)
                       * @state _ positive_set_fpdata (* possible last terminals *)))%type.

  Global Instance possible_terminals_prestate_lattice : grammar_fixedpoint_lattice_data possible_terminals_prestate
    := _.

  Global Instance possible_terminals_aidata : @AbstractInterpretation Ascii.ascii possible_terminals_prestate _.
  Proof.
    refine (@prod_aidata_dep
              _ _ _ _ _
              on_terminal
              (@on_nil_production Ascii.ascii _ _ might_be_empty_aidata)
              (@precombine_production Ascii.ascii _ _ might_be_empty_aidata)
              (prod_on_terminal
                 (fun P => constant (all_but P))
                 (fun P => constant (all_but P)))
              (prod_on_nil_production (constant all_possible_ascii) (constant all_possible_ascii))
              (fun xmbe ymbe
               => prod_precombine_production_nondep
                    (fun x' y'
                     => constant (if collapse_might_be_empty xmbe
                                  then PositiveSet.inter x' y'
                                  else x'))
                    (fun x' y'
                     => constant (if collapse_might_be_empty ymbe
                                  then PositiveSet.inter x' y'
                                  else y')))
              _ _).
    intros x0 y0 H0 x1 y1 H1 x2 y2 H2 x3 y3 H3.
    repeat match goal with
           | [ H : is_true (state_beq ?x ?y) |- context[collapse_might_be_empty ?x] ]
             => replace (collapse_might_be_empty x)
                with (collapse_might_be_empty y)
               by (rewrite H; reflexivity);
                  clear x H
           end.
    eapply @prod_precombine_production_nondep_Proper; try eassumption;
      edestruct collapse_might_be_empty;
      clear;
      abstract (
          repeat intro;
          PositiveSetExtensions.to_caps;
          PositiveSetExtensions.simplify_sets; reflexivity
        ).
  Defined.
End with_empty.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}.

  Definition all_possible_accurate
             (P : String -> Prop) (chars : PositiveSet.t)
    : Prop
    := forall str, P str -> forall_chars str (fun ch => ~PositiveSet.In (pos_of_ascii ch) chars).

  Definition possible_accurate
    : forall (P : String -> Prop) (st : possible_terminals_prestate), Prop
    := prod_prerelated
         might_be_empty_accurate
         (prod_prerelated
            (fun P st
             => forall str, P str -> for_first_char str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st))
            (fun P st
             => forall str, P str -> for_last_char str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st))).

  Local Ltac pull_lattice_for_rect :=
    repeat lazymatch goal with
           | [ |- appcontext G[match ?v with ⊤ => ?T | ⊥ => ?B | constant x => @?C x end] ]
             => let RT := type of T in
                let G' := context G[lattice_for_rect (fun _ => RT) T C B v] in
                change G'
           | [ |- appcontext G[fun k : ?KT => match @?v k with ⊤ => @?T k | ⊥ => @?B k | constant x => @?C k x end] ]
             => let RT := match type of T with forall k, @?RT k => RT end in
                let G' := context G[fun k : KT => lattice_for_rect (fun _ => RT k) (T k) (C k) (B k) (v k)] in
                change G'; cbv beta
           end;
    rewrite !(fun A T T' x y z => lattice_for_rect_pull (A := A) (lattice_for_rect (T := T) (fun _ => T') x y z));
    setoid_rewrite (fun A T T' x y z => lattice_for_rect_pull (A := A) (lattice_for_rect (T := T) (fun _ => T') x y z)).

  Local Ltac handle_match_two_lattice_either_bottom_same :=
    idtac;
    lazymatch goal with
    | [ |- match ?l1 with ⊤ => match ?l2 with _ => _ end | ⊥ => ?P | _ => _ end ]
      => let H := fresh in
         assert (H : (l1 = ⊥ \/ l2 = ⊥) \/ (l1 <> ⊥ /\ l2 <> ⊥))
           by (destruct l1;
               [ destruct l2; [ right; split; congruence.. | left; right; reflexivity ]..
               | left; left; reflexivity ]);
         destruct H as [H|H];
         [ cut P; [ destruct l1, l2; trivial; destruct H; congruence | ]
         | destruct l1, l2, H; try congruence; [] ]
    end.

  Local Ltac clear_unused_T T :=
    repeat match goal with
           | [ x : T |- _ ]
             => lazymatch goal with
                | [ |- appcontext[x] ] => fail
                | _ => clear dependent x
                end
           end.

  Local Ltac t_step :=
    idtac;
    match goal with
    | [ |- ?R ?x ?x ] => reflexivity
    | _ => assumption
    | _ => congruence
    | _ => tauto
    | _ => progress unfold Proper, respectful, all_possible_accurate, possible_accurate, flip, PositiveSetBoundedLattice.lift_ltb, ensemble_least_upper_bound, ensemble_on_terminal, ensemble_on_nil_production, prestate_le, ensemble_combine_production, Equality.prod_beq, might_be_empty_accurate in *
    | _ => progress intros
    | _ => progress simpl in *
    | [ H : is_true (?a || (?b && negb ?a)) |- _ ]
      => apply simplify_bool_expr' in H;
         [ | clear; unfold state_le; simpl; bool_congr_setoid; tauto ]
    | [ |- context[(?a || (?b && negb ?a))%bool] ]
      => rewrite (@simplify_bool_expr a b) by (clear; unfold state_le; simpl; bool_congr_setoid; tauto)
    | [ H : forall x y, _ -> (?f x <-> ?g y) |- _ ]
      => setoid_rewrite (fun x => H x x (reflexivity _));
         clear f H
    | [ H : lattice_for_related _ _ ?x |- _ ] => is_var x; destruct x
    | [ |- lattice_for_related _ _ ?x ] => is_var x; destruct x
    | _ => progress destruct_head ex
    | _ => progress destruct_head and
    | _ => progress subst
    | _ => progress bool_congr_setoid
    | _ => progress PositiveSetExtensions.simplify_sets
    | _ => progress PositiveSetExtensions.to_caps
    | [ H : is_true (is_char ?str _) |- forall_chars ?str _ ]
      => setoid_rewrite <- (forall_chars_singleton _ _ _ H)
    | [ H : is_true (is_char ?str _) |- for_first_char ?str _ ]
      => setoid_rewrite <- (for_first_char_singleton _ _ _ H)
    | [ H : is_true (is_char ?str _) |- for_last_char ?str _ ]
      => setoid_rewrite <- (for_last_char_singleton _ _ _ H)
    | _ => progress autorewrite with sets in *
    | [ H : PositiveSet.Subset ?x _ |- forall_chars _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | [ H : PositiveSet.Subset ?x _ |- for_first_char _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | [ H : PositiveSet.Subset ?x _ |- for_last_char _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | _ => solve [ eauto using forall_chars_nil, for_first_char_nil, for_last_char_nil with nocore
                 | auto with sets
                 | exfalso; unfold not in *; eauto with nocore ]
    | _ => progress PositiveSetExtensions.push_In
    | [ H : forall str, ?P str -> forall_chars str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | [ H : forall str, ?P str -> for_first_char str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | [ H : forall str, ?P str -> for_last_char str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | _ => eapply forall_chars_Proper; [ reflexivity | intros ?? | eassumption ];
           cbv beta in *; tauto
    | _ => progress destruct_head or
    | [ |- ~(or _ _) ] => intro
    | _ => setoid_rewrite not_In_all_but
    | [ H : forall v, ~?P v |- context[?P _] ]
      => setoid_rewrite (fun v => False_iff (H v))
    | _ => progress setoid_rewrite_logic
    | [ H : forall_chars (take ?n ?str) (fun ch => ~@?P ch),
            H' : forall_chars (drop ?n ?str) (fun ch => ~@?P' ch)
        |- forall_chars ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => setoid_rewrite (forall_chars__split str _ n); split
    | [ H : for_first_char ?str (fun ch => ~@?P ch) |- for_first_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_first_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_first_char ?str (fun ch => ~@?P' ch) |- for_first_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_first_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_last_char ?str (fun ch => ~@?P ch) |- for_last_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_last_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_last_char ?str (fun ch => ~@?P' ch) |- for_last_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_last_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_first_char (drop ?x ?str) _, H' : for_first_char (take ?x ?str) _ |- for_first_char ?str _ ]
      => rewrite (for_first_char__split str _ x); destruct x; [ left | right ]; (split; [ omega | ])
    | [ H : for_last_char (drop ?x ?str) _, H' : for_last_char (take ?x ?str) _ |- for_last_char ?str _ ]
      => rewrite (for_last_char__split str _ x); destruct (Compare_dec.le_lt_dec (length str) x); [ right | left ]; (split; [ assumption | ])
    | [ H : forall str, ?P str -> length str <> 0, H' : ?P (take 0 ?str') |- _ ]
      => exfalso; apply (H _ H'); rewrite take_length; omega_with_min_max
    | [ H : forall str, ?P str -> length str <> 0, Hlt : (length ?str' <= ?x)%nat, H' : ?P (drop ?x ?str') |- _ ]
      => exfalso; apply (H _ H'); rewrite drop_length; omega_with_min_max
    | [ |- context[collapse_might_be_empty ?st] ]
      => is_var st; destruct st
    | [ H : PositiveSet.Subset ?x _ |- PositiveSet.Subset (PositiveSet.inter _ _) _ ]
      => progress setoid_subst_rel PositiveSet.Subset; auto with sets
    | _ => rewrite ascii_of_pos_of_ascii
    end.

  Local Ltac t := repeat t_step.

  Global Instance all_possible_aicdata
    : AbstractInterpretationCorrectness all_possible_accurate.
  Proof.
    split; try exact _;
      try solve [ t ].
  Qed.

  Global Instance constant_inter_Proper
    : Proper (prestate_le ==> prestate_le ==> state_le) (fun x' y' => constant (PositiveSet.inter x' y')).
  Proof. t. Qed.

  Global Instance possible_aicdata
    : AbstractInterpretationCorrectness possible_accurate
    := { prerelated_ext
         := prod_prerelated_ext
              (@prerelated_ext Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_prerelated_ext _ _);
         related_monotonic
         := prod_related_monotonic
              (@related_monotonic Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_related_monotonic _ _);
         lub_correct
         := prod_lub_correct
              (@lub_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_lub_correct _ _);
         on_terminal_correct
         := prod_on_terminal_correct
              (@on_terminal_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_on_terminal_correct _ _);
         on_nil_production_correct
         := prod_on_nil_production_correct
              (@on_nil_production_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_on_nil_production_correct _ _);
         precombine_production_Proper_le
         := prod_precombine_production_dep_Proper_le
              (@precombine_production_Proper_le Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_precombine_production_nondep_dep_Proper_le _ _);
         combine_production_correct
         := prod_combine_production_dep_correct
              (@combine_production_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              _
       }.
  Proof.
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { intros; apply prod_combine_production_nondep_correct_specific; eauto with nocore;
      intros; subst; unfold prod_prerelated, ensemble_combine_production in *; simpl in *;
      unfold lattice_for_related, might_be_empty_accurate, lattice_for_combine_production in *;
      destruct_head prod;
      destruct_head and;
      clear_unused_T (lattice_for PositiveSet.t);
      pull_lattice_for_rect; simpl; unfold lattice_for_rect;
      handle_match_two_lattice_either_bottom_same;
      t. }
  Qed.
End correctness.

Definition all_possible_data (G : pregrammar' Ascii.ascii)
  := @fold_grammar_data _ _ _ all_possible_terminals_aidata G.
Definition possible_data (G : pregrammar' Ascii.ascii)
  := @fold_grammar_data _ _ _ possible_terminals_aidata G.
Existing Class all_possible_data.
Existing Class possible_data.

Definition possible_characters_result := PositiveSet.t.
Definition all_possible_result := possible_characters_result.
Record possible_result :=
  { might_be_empty_of_pr : bool;
    possible_first_characters_of_pr : possible_characters_result;
    possible_last_characters_of_pr : possible_characters_result }.

Definition make_all_possible_result (negated_set : lattice_for PositiveSet.t) : all_possible_result
  := match negated_set with
     | ⊤ => all_possible_ascii
     | constant v' => PositiveSet.filter (fun ch => negb (PositiveSet.mem ch v')) all_possible_ascii
     | ⊥ => PositiveSet.empty
     end.

Definition norm_lattice_prod {A B} (x : lattice_for (lattice_for A * lattice_for B)) : lattice_for A * lattice_for B
  := match x with
     | ⊤ => (⊤, ⊤)
     | constant v => v
     | ⊥ => (⊥, ⊥)
     end.

Definition collapse_to_possible_result (x : lattice_for possible_terminals_prestate) : possible_result
  := let x := norm_lattice_prod x in
     let x0 := fst x in
     let x12 := norm_lattice_prod (snd x) in
     let '(x1, x2) := (fst x12, snd x12) in
     {| might_be_empty_of_pr := collapse_might_be_empty x0;
        possible_first_characters_of_pr := make_all_possible_result x1;
        possible_last_characters_of_pr := make_all_possible_result x2 |}.

Definition is_possible_character_of (v : possible_characters_result) (ch : Ascii.ascii) : bool
  := PositiveSet.mem (pos_of_ascii ch) v.
Coercion is_possible_character_of : possible_characters_result >-> Funclass.

Section defs.
  Context (G : pregrammar' Ascii.ascii)
          {apdata : all_possible_data G}
          {pdata : possible_data G}.

  Definition all_possible_characters_of_nt
    : String.string -> all_possible_result
    := fun nt => make_all_possible_result (lookup_state apdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)).

  Definition might_be_empty_of_pr_nt
    : String.string -> bool
    := fun nt => might_be_empty_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).

  Definition possible_first_characters_of_nt
    : String.string -> possible_characters_result
    := fun nt => possible_first_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).

  Definition possible_last_characters_of_nt
    : String.string -> possible_characters_result
    := fun nt => possible_last_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).

  Definition all_possible_characters_of_production
    : production Ascii.ascii -> all_possible_result
    := fun ps => make_all_possible_result (fold_production' G (lookup_state apdata) ps).

  Definition might_be_empty_of_pr_production
    : production Ascii.ascii -> bool
    := fun ps => might_be_empty_of_pr (collapse_to_possible_result (fold_production' G (lookup_state pdata) ps)).

  Definition possible_first_characters_of_production
    : production Ascii.ascii -> possible_characters_result
    := fun ps => possible_first_characters_of_pr (collapse_to_possible_result (fold_production' G (lookup_state pdata) ps)).

  Definition possible_last_characters_of_production
    : production Ascii.ascii -> possible_characters_result
    := fun ps => possible_last_characters_of_pr (collapse_to_possible_result (fold_production' G (lookup_state pdata) ps)).
End defs.
Global Arguments all_possible_characters_of_nt G {_} _.
Global Arguments might_be_empty_of_pr_nt G {_} _.
Global Arguments possible_first_characters_of_nt G {_} _.
Global Arguments possible_last_characters_of_nt G {_} _.
Global Arguments all_possible_characters_of_production G {_} _.
Global Arguments might_be_empty_of_pr_production G {_} _.
Global Arguments possible_first_characters_of_production G {_} _.
Global Arguments possible_last_characters_of_production G {_} _.

Section correctness_lemmas.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          (G : pregrammar' Ascii.ascii)
          {apdata : all_possible_data G}
          {pdata : possible_data G}
          (nt : String.string)
          (ps : production Ascii.ascii)
          (str : String).

  Local Ltac pre_correct_t :=
    idtac;
    let x := match goal with
             | [ |- ?v = _ ] => head v
             end in
    unfold x.
  Local Ltac correct_t_step :=
    idtac;
    match goal with
    | _ => assumption
    | _ => tauto
    | [ |- ?R ?x ?x ] => reflexivity
    | _ => rewrite fgd_fold_grammar_correct
    | [ p : parse_of_item _ _ _ |- appcontext[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct_item _ _ _ _ _ _ aidata _ _) in p
    | [ p : parse_of_production _ _ _ |- appcontext[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct_production _ _ _ _ _ _ aidata _ _) in p
    | [ p : parse_of _ _ _ |- appcontext[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct _ _ _ _ _ _ aidata _ _) in p
    | [ |- context[lookup_state ?g ?nt] ]
      => destruct (lookup_state g nt) eqn:?
    | [ |- context[fold_production' ?G ?f ?ps] ]
      => destruct (fold_production' G f ps) eqn:?
    | _ => progress simpl in *
    | _ => progress destruct_head ex
    | _ => progress destruct_head and
    | _ => progress destruct_head prod
    | _ => progress unfold possible_accurate, all_possible_accurate, possible_terminals_prestate, state, prod_prerelated, lattice_for_related, collapse_might_be_empty, might_be_empty_accurate, related, norm_lattice_prod, make_all_possible_result in *
    | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
    | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
    | _ => solve [ exfalso; unfold not in *; eauto with nocore ]
    | [ |- context[PositiveSet.In _ all_possible_ascii] ]
      => first [ rewrite forall_chars_get | apply for_first_char_True | apply for_last_char_True ];
         setoid_rewrite (fun v => True_iff (In_all v)); constructor
    | [ |- context[PositiveSet.In _ all_possible_ascii] ]
      => setoid_rewrite (fun v => True_iff (In_all v))
    | [ H : ?P _, H' : forall str, ?P str -> _ |- _ ] => unique pose proof (H' _ H)
    | _ => progress PositiveSetExtensions.push_In
    | _ => progress PositiveSetExtensions.to_caps
    | _ => progress setoid_rewrite_logic
    end.
  Local Ltac correct_t := try pre_correct_t; repeat correct_t_step.

  Lemma all_possible_characters_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : forall_chars str (fun ch => PositiveSet.In (pos_of_ascii ch) (all_possible_characters_of_nt G nt)).
  Proof.
    unfold all_possible_characters_of_nt; correct_t.
    eapply forall_chars_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma all_possible_characters_of
        (p : parse_of G str (Lookup G nt))
    : forall_chars str (fun ch => PositiveSet.In (pos_of_ascii ch) (all_possible_characters_of_nt G nt)).
  Proof.
    unfold all_possible_characters_of_nt; correct_t.
    eapply forall_chars_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma might_be_empty_pr_parse_of_item_nt
        (Hlen : length str = 0)
        (p : parse_of_item G str (NonTerminal nt))
    : might_be_empty_of_pr_nt G nt = true.
  Proof. correct_t. Qed.

  Lemma might_be_empty_pr_parse_of
        (Hlen : length str = 0)
        (p : parse_of G str (Lookup G nt))
    : might_be_empty_of_pr_nt G nt = true.
  Proof. correct_t. Qed.

  Lemma possible_first_characters_parse_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : for_first_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_first_characters_of_nt G nt)).
  Proof.
    unfold possible_first_characters_of_nt; correct_t.
    eapply for_first_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_first_characters_parse_of
        (p : parse_of G str (Lookup G nt))
    : for_first_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_first_characters_of_nt G nt)).
  Proof.
    unfold possible_first_characters_of_nt; correct_t.
    eapply for_first_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_last_characters_parse_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : for_last_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_last_characters_of_nt G nt)).
  Proof.
    unfold possible_last_characters_of_nt; correct_t.
    eapply for_last_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_last_characters_parse_of
        (p : parse_of G str (Lookup G nt))
    : for_last_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_last_characters_of_nt G nt)).
  Proof.
    unfold possible_last_characters_of_nt; correct_t.
    eapply for_last_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma all_possible_characters_of_parse_of_production
        (p : parse_of_production G str ps)
    : forall_chars str (fun ch => PositiveSet.In (pos_of_ascii ch) (all_possible_characters_of_production G ps)).
  Proof.
    unfold all_possible_characters_of_production; correct_t.
    eapply forall_chars_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma might_be_empty_pr_parse_of_production
        (Hlen : length str = 0)
        (p : parse_of_production G str ps)
    : might_be_empty_of_pr_production G ps = true.
  Proof. correct_t. Qed.


  Lemma possible_first_characters_parse_of_production
        (p : parse_of_production G str ps)
    : for_first_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_first_characters_of_production G ps)).
  Proof.
    unfold possible_first_characters_of_production; correct_t.
    eapply for_first_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_last_characters_parse_of_production
        (p : parse_of_production G str ps)
    : for_last_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_last_characters_of_production G ps)).
  Proof.
    unfold possible_last_characters_of_production; correct_t.
    eapply for_last_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.
End correctness_lemmas.

Set Printing Implicit.

Ltac make_all_possible_data G :=
  let v := constr:(@fold_grammar _ _ _ all_possible_terminals_aidata G) in
  let v := make_fold_grammar_data_from v in
  constr:(v : all_possible_data G).
Ltac make_possible_data G :=
  let v := constr:(@fold_grammar _ _ _ possible_terminals_aidata G) in
  let v := make_fold_grammar_data_from v in
  constr:(v : possible_data G).
