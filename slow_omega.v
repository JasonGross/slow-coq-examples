Require Import Coq.omega.Omega.


Lemma min_def {x y} : min x y = x - (x - y).
Proof. apply Min.min_case_strong; omega. Qed.
Lemma max_def {x y} : max x y = x + (y - x).
Proof. apply Max.max_case_strong; omega. Qed.

Lemma min_minus_l x y
  : min (x - y) x = x - y.
Proof. Time apply Min.min_case_strong; omega. Qed. (* Finished transaction in 0. secs (0.06u,0.004s) *)

Lemma min_minus_l' x y
  : min (x - y) x = x - y.
Proof. Time rewrite min_def; omega. Qed. (* Finished transaction in 1. secs (1.128u,0.004s) *)
