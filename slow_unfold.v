(* Lifted from https://coq.inria.fr/bugs/show_bug.cgi?id=4662 *)
(* File reduced by coq-bug-finder from original input, then from 503 lines to 49 lines, then from 306 lines to 69 lines, then from 659 lines to 127 lines, then from 374 lines to 134 lines, then from 260 lines to 160 lines, then from 279 lines to 186 lines, then from 338 lines to 203 lines, then from 458 lines to 223 lines, then from 512 lines to 225 lines, then from 936 lines to 226 lines, then from 2061 lines to 227 lines, then from 349 lines to 245 lines, then from 398 lines to 280 lines, then from 460 lines to 342 lines, then from 356 lines to 343 lines *)
(* coqc version 8.4pl6 (March 2016) compiled on Mar 28 2016 12:55:49 with OCaml 4.02.3
   coqtop version 8.4pl6 (March 2016) *)
Require Coq.Strings.String.
Require Coq.Lists.SetoidList.
Require Coq.Program.Program.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Module Export StringLike.
  Module Export Core.
    Import Coq.Relations.Relation_Definitions.
    Import Coq.Classes.Morphisms.

    Local Coercion is_true : bool >-> Sortclass.

    Module Export StringLike.
      Class StringLikeMin {Char : Type} :=
        {
          String :> Type;
          char_at_matches : nat -> String -> (Char -> bool) -> bool;
          unsafe_get : nat -> String -> Char;
          length : String -> nat
        }.

      Class StringLike {Char : Type} {HSLM : @StringLikeMin Char} :=
        {
          is_char : String -> Char -> bool;
          take : nat -> String -> String;
          drop : nat -> String -> String;
          get : nat -> String -> option Char;
          bool_eq : String -> String -> bool;
          beq : relation String := fun x y => bool_eq x y
        }.

      Arguments StringLikeMin : clear implicits.
      Arguments StringLike Char {HSLM}.
      Infix "=s" := (@beq _ _ _) (at level 70, no associativity) : type_scope.
      Notation "s ~= [ ch ]" := (is_char s ch) (at level 70, no associativity) : string_like_scope.
      Local Open Scope string_like_scope.

      Class StringLikeProperties (Char : Type) `{StringLike Char} :=
        {
          singleton_unique : forall s ch ch', s ~= [ ch ] -> s ~= [ ch' ] -> ch = ch';
          singleton_exists : forall s, length s = 1 -> exists ch, s ~= [ ch ];
          char_at_matches_correct : forall s n P ch, get n s = Some ch -> (char_at_matches n s P = P ch);
          get_0 : forall s ch, take 1 s ~= [ ch ] <-> get 0 s = Some ch;
          get_S : forall n s, get (S n) s = get n (drop 1 s);
          unsafe_get_correct : forall n s ch, get n s = Some ch -> unsafe_get n s = ch;
          length_singleton : forall s ch, s ~= [ ch ] -> length s = 1;
          bool_eq_char : forall s s' ch, s ~= [ ch ] -> s' ~= [ ch ] -> s =s s';
          is_char_Proper :> Proper (beq ==> eq ==> eq) is_char;
          length_Proper :> Proper (beq ==> eq) length;
          take_Proper :> Proper (eq ==> beq ==> beq) take;
          drop_Proper :> Proper (eq ==> beq ==> beq) drop;
          bool_eq_Equivalence :> Equivalence beq;
          bool_eq_empty : forall str str', length str = 0 -> length str' = 0 -> str =s str';
          take_short_length : forall str n, n <= length str -> length (take n str) = n;
          take_long : forall str n, length str <= n -> take n str =s str;
          take_take : forall str n m, take n (take m str) =s take (min n m) str;
          drop_length : forall str n, length (drop n str) = length str - n;
          drop_0 : forall str, drop 0 str =s str;
          drop_drop : forall str n m, drop n (drop m str) =s drop (n + m) str;
          drop_take : forall str n m, drop n (take m str) =s take (m - n) (drop n str);
          take_drop : forall str n m, take n (drop m str) =s drop m (take (n + m) str);
          bool_eq_from_get : forall str str', (forall n, get n str = get n str') -> str =s str'
        }.
    End StringLike.

  End Core.

End StringLike.

Module Export Core.
  Import Coq.Strings.String.
  Import Coq.Lists.List.

  Section cfg.
    Context {Char : Type}.

    Section definitions.

      Inductive item :=
      | Terminal (_ : Char -> bool)
      | NonTerminal (_ : string).

      Definition production := list item.
      Definition productions := list production.

      Record grammar :=
        {
          Start_symbol :> string;
          Lookup :> string -> productions;
          Start_productions :> productions := Lookup Start_symbol;
          Valid_nonterminals : list string;
          Valid_productions : list productions := map Lookup Valid_nonterminals
        }.
    End definitions.

  End cfg.

  Arguments item _ : clear implicits.
  Arguments production _ : clear implicits.
  Arguments productions _ : clear implicits.
  Arguments grammar _ : clear implicits.

End Core.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.

  Class parser_computational_predataT :=
    { nonterminals_listT : Type;
      nonterminal_carrierT : Type;
      of_nonterminal : String.string -> nonterminal_carrierT;
      to_nonterminal : nonterminal_carrierT -> String.string;
      production_carrierT : Type;
      to_production : production_carrierT -> production Char;
      nonterminal_to_production : nonterminal_carrierT -> list production_carrierT;
      production_tl : production_carrierT -> production_carrierT;
      production_carrier_valid : production_carrierT -> bool;
      initial_nonterminals_data : nonterminals_listT;
      nonterminals_length : nonterminals_listT -> nat;
      is_valid_nonterminal : nonterminals_listT -> nonterminal_carrierT -> bool;
      remove_nonterminal : nonterminals_listT -> nonterminal_carrierT -> nonterminals_listT }.
End recursive_descent_parser.

Import Coq.Lists.SetoidList.

Global Coercion is_true : bool >-> Sortclass.
Coercion bool_of_sumbool {A B} (x : {A} + {B}) : bool := if x then true else false.

Import Coq.Strings.String.
Scheme Equality for string.
Definition uniquize {A} (beq : A -> A -> bool) (ls : list A) : list A.
  admit.
Defined.

Fixpoint up_to (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S n' => n'::up_to n'
  end.

Class Enumerable A
  := { enumerate : list A;
       enumerate_correct : forall x, List.In x enumerate }.

Global Arguments enumerate A {_}.

Definition enumerate_ascii : list Ascii.ascii
  := Eval compute in List.map Ascii.ascii_of_nat (up_to 256).

Global Instance enumerable_ascii : Enumerable Ascii.ascii
  := { enumerate := enumerate_ascii }.
admit.
Defined.

Import Coq.Strings.Ascii.
Inductive RCharExpr :=
| rbeq (ch : Ascii.ascii)
| ror (_ _ : RCharExpr)
| rand (_ _ : RCharExpr)
| rneg (_ : RCharExpr)
| rcode_le_than (code : nat)
| rcode_ge_than (code : nat).

Inductive ritem :=
| RTerminal (_ : RCharExpr)
| RNonTerminal (_ : String.string).

Definition rproduction := list ritem.
Definition rproductions := list rproduction.
Global Coercion interp_rproductions (expr : rproductions) : productions Ascii.ascii.
admit.
Defined.

Class PreGensym A :=
  { s_gt : A -> A -> Prop;
    sym_init : A;
    combine_symbols : A -> A -> A;
    s_gt_Asymmetric :> Asymmetric s_gt;
    s_gt_Transitive :> Transitive s_gt;
    combine_respectful_l : forall x y, s_gt (combine_symbols x y) x;
    combine_respectful_r : forall x y, s_gt (combine_symbols x y) y }.

Fixpoint gensym {A} {H : PreGensym A} (used : list A) : A
  := match used with
     | nil => sym_init
     | cons x xs => combine_symbols x (gensym xs)
     end.

Global Instance gensym_string : PreGensym string
  := { s_gt x y := gt (length x) (length y);
       sym_init := ""%string;
       combine_symbols x y := String.String "a"%char (x ++ y)%string }.
Proof.
  repeat intro; admit.
  repeat intro; admit.
  simpl; repeat intro; admit.
  simpl; repeat intro; admit.
Defined.

Class NoDupR {T} beq (ls : list T) := nodupr : uniquize beq ls = ls.
Definition list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T.
  admit.
Defined.

Record pregrammar :=
  {
    pregrammar_rproductions : list (string * rproductions);
    pregrammar_productions :> list (string * productions Ascii.ascii)
    := List.map (fun xy => (fst xy, interp_rproductions (snd xy))) pregrammar_rproductions;
    pregrammar_nonterminals : list string
    := map fst pregrammar_productions;
    invalid_nonterminal : string
    := gensym pregrammar_nonterminals;
    Lookup_idx : nat -> productions Ascii.ascii
    := fun n => nth n (map snd pregrammar_productions) nil;
    Lookup_string : string -> productions Ascii.ascii
    := list_to_productions nil pregrammar_productions;
    nonterminals_unique
    : NoDupR string_beq pregrammar_nonterminals
  }.

Definition default_nonterminal_carrierT : Type.
  admit.
Defined.
Definition default_production_carrierT : Type.
  admit.
Defined.

Section recursive_descent_parser_list.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HLSP : StringLikeProperties Ascii.ascii} {G : pregrammar}.
  Definition rdp_list_nonterminals_listT : Type.
    exact (list nat).
  Defined.
  Notation rdp_list_nonterminal_carrierT := default_nonterminal_carrierT.

  Notation rdp_list_production_carrierT := default_production_carrierT.
  Definition rdp_list_is_valid_nonterminal : rdp_list_nonterminals_listT -> rdp_list_nonterminal_carrierT -> bool.
    admit.
  Defined.

  Local Notation valid_nonterminals := (map fst (pregrammar_productions G)).
  Definition rdp_list_initial_nonterminals_data
    : rdp_list_nonterminals_listT.
    exact (up_to (List.length valid_nonterminals)).
  Defined.
  Definition rdp_list_of_nonterminal
    : String.string -> rdp_list_nonterminal_carrierT.
    admit.
  Defined.
  Definition rdp_list_to_nonterminal
    : rdp_list_nonterminal_carrierT -> String.string.
    admit.
  Defined.
  Definition rdp_list_to_production : rdp_list_production_carrierT -> production Ascii.ascii.
    admit.
  Defined.
  Definition rdp_list_nonterminal_to_production : rdp_list_nonterminal_carrierT -> list rdp_list_production_carrierT.
    admit.
  Defined.
  Definition rdp_list_production_tl : rdp_list_production_carrierT -> rdp_list_production_carrierT.
    admit.
  Defined.
  Definition rdp_list_production_carrier_valid
    : rdp_list_production_carrierT -> bool.
    admit.
  Defined.
  Definition rdp_list_remove_nonterminal : rdp_list_nonterminals_listT -> rdp_list_nonterminal_carrierT -> rdp_list_nonterminals_listT.
    admit.
  Defined.

  Global Instance rdp_list_predata : @parser_computational_predataT Ascii.ascii
    := { nonterminals_listT := rdp_list_nonterminals_listT;
         initial_nonterminals_data := rdp_list_initial_nonterminals_data;
         of_nonterminal := rdp_list_of_nonterminal;
         to_nonterminal := rdp_list_to_nonterminal;
         production_carrierT := rdp_list_production_carrierT;
         to_production := rdp_list_to_production;
         nonterminal_to_production := rdp_list_nonterminal_to_production;
         production_tl := rdp_list_production_tl;
         production_carrier_valid := rdp_list_production_carrier_valid;
         is_valid_nonterminal := rdp_list_is_valid_nonterminal;
         remove_nonterminal := rdp_list_remove_nonterminal;
         nonterminals_length := @List.length _ }.
End recursive_descent_parser_list.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {predata : @parser_computational_predataT Char} {HEC : Enumerable Char}.
  Definition pb_check_level (hiding : bool) (ch : Char) (start_level : nat) : bool.
    admit.
  Defined.
  Definition pb_check_level_fun (hiding : bool) (P : Char -> bool) (start_level : nat) : bool.
    exact (List.fold_right
             andb
             true
             (List.map
                (fun ch => pb_check_level hiding ch start_level)
                (List.filter
                   P
                   (enumerate Char)))).
  Defined.
  Definition pb_new_level_fun (P : Char -> bool) (start_level : nat) : list nat.
    admit.
  Defined.

End cfg.

Local Open Scope bool_scope.
Context (G : pregrammar).
Let predata := (@rdp_list_predata G).
Local Existing Instance predata.
Context (pb_nts pbh_nts : nonterminals_listT).

Definition paren_balanced''_production_step
           (hiding : bool)
  := fun (it : item Ascii.ascii) (rest_balanced : nat -> bool) level
     => let predata := @rdp_list_predata G in
        match it with
        | Terminal P
          => ((pb_check_level_fun hiding P level)
                && match pb_new_level_fun P level with
                   | new_level::nil => rest_balanced new_level
                   | _ => false
                   end)%bool
        | NonTerminal nt
          =>
          (if (hiding && Compare_dec.zerop level)
           then is_valid_nonterminal pbh_nts (of_nonterminal nt)
           else is_valid_nonterminal pb_nts (of_nonterminal nt))
            && rest_balanced level
        end.

Goal forall (pats : production Ascii.ascii) (hiding : bool) (level : nat) (P : Ascii.ascii -> bool),
    paren_balanced''_production_step hiding (Terminal P)
                                     (fold_right (paren_balanced''_production_step hiding) (fun n : nat => Compare_dec.zerop n) pats) level ->
    paren_balanced''_production_step hiding (Terminal P)
                                     (fold_right (paren_balanced''_production_step hiding) (fun n : nat => Compare_dec.zerop n) pats) level.
Proof.
  intros ???? H.
  unfold paren_balanced''_production_step at 1.
  timeout 1 abstract (revert H; unfold paren_balanced''_production_step at 1; exact (fun x => x)) || fail 1 "too early".
  Undo.
  Timeout 10 abstract (unfold paren_balanced''_production_step at 1 in H; revert H; exact (fun x => x)). (* takes longer than 6 minutes *)
