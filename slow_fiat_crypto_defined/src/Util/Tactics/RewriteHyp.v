Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.DoWithHyp.


(** Rewrite with any applicable hypothesis. *)
Tactic Notation "rewrite_hyp" "*" := do_with_hyp' ltac:(fun H => rewrite H).
Tactic Notation "rewrite_hyp" "->" "*" := do_with_hyp' ltac:(fun H => rewrite -> H).
Tactic Notation "rewrite_hyp" "<-" "*" := do_with_hyp' ltac:(fun H => rewrite <- H).
Tactic Notation "rewrite_hyp" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite !H).
Tactic Notation "rewrite_hyp" "->" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite -> !H).
Tactic Notation "rewrite_hyp" "<-" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite <- !H).
Tactic Notation "rewrite_hyp" "!*" := progress rewrite_hyp ?*.
Tactic Notation "rewrite_hyp" "->" "!*" := progress rewrite_hyp -> ?*.
Tactic Notation "rewrite_hyp" "<-" "!*" := progress rewrite_hyp <- ?*.

Tactic Notation "rewrite_hyp" "*" "in" "*" := do_with_hyp' ltac:(fun H => rewrite H in * ).
Tactic Notation "rewrite_hyp" "->" "*" "in" "*" := do_with_hyp' ltac:(fun H => rewrite -> H in * ).
Tactic Notation "rewrite_hyp" "<-" "*" "in" "*" := do_with_hyp' ltac:(fun H => rewrite <- H in * ).
Tactic Notation "rewrite_hyp" "?*" "in" "*" := repeat do_with_hyp' ltac:(fun H => rewrite !H in * ).
Tactic Notation "rewrite_hyp" "->" "?*" "in" "*" := repeat do_with_hyp' ltac:(fun H => rewrite -> !H in * ).
Tactic Notation "rewrite_hyp" "<-" "?*" "in" "*" := repeat do_with_hyp' ltac:(fun H => rewrite <- !H in * ).
Tactic Notation "rewrite_hyp" "!*" "in" "*" := progress rewrite_hyp ?* in *.
Tactic Notation "rewrite_hyp" "->" "!*" "in" "*" := progress rewrite_hyp -> ?* in *.
Tactic Notation "rewrite_hyp" "<-" "!*" "in" "*" := progress rewrite_hyp <- ?* in *.

Tactic Notation "erewrite_hyp" "*" := do_with_hyp' ltac:(fun H => erewrite H).
Tactic Notation "erewrite_hyp" "->" "*" := do_with_hyp' ltac:(fun H => erewrite -> H).
Tactic Notation "erewrite_hyp" "<-" "*" := do_with_hyp' ltac:(fun H => erewrite <- H).
Tactic Notation "erewrite_hyp" "?*" := repeat do_with_hyp' ltac:(fun H => erewrite !H).
Tactic Notation "erewrite_hyp" "->" "?*" := repeat do_with_hyp' ltac:(fun H => erewrite -> !H).
Tactic Notation "erewrite_hyp" "<-" "?*" := repeat do_with_hyp' ltac:(fun H => erewrite <- !H).
Tactic Notation "erewrite_hyp" "!*" := progress erewrite_hyp ?*.
Tactic Notation "erewrite_hyp" "->" "!*" := progress erewrite_hyp -> ?*.
Tactic Notation "erewrite_hyp" "<-" "!*" := progress erewrite_hyp <- ?*.

Tactic Notation "erewrite_hyp" "*" "in" "*" := do_with_hyp' ltac:(fun H => erewrite H in * ).
Tactic Notation "erewrite_hyp" "->" "*" "in" "*" := do_with_hyp' ltac:(fun H => erewrite -> H in * ).
Tactic Notation "erewrite_hyp" "<-" "*" "in" "*" := do_with_hyp' ltac:(fun H => erewrite <- H in * ).
Tactic Notation "erewrite_hyp" "?*" "in" "*" := repeat do_with_hyp' ltac:(fun H => erewrite !H in * ).
Tactic Notation "erewrite_hyp" "->" "?*" "in" "*" := repeat do_with_hyp' ltac:(fun H => erewrite -> !H in * ).
Tactic Notation "erewrite_hyp" "<-" "?*" "in" "*" := repeat do_with_hyp' ltac:(fun H => erewrite <- !H in * ).
Tactic Notation "erewrite_hyp" "!*" "in" "*" := progress erewrite_hyp ?* in *.
Tactic Notation "erewrite_hyp" "->" "!*" "in" "*" := progress erewrite_hyp -> ?* in *.
Tactic Notation "erewrite_hyp" "<-" "!*" "in" "*" := progress erewrite_hyp <- ?* in *.
