Require Import
        Coq.Strings.String
        Fiat.Common.BoundedLookup
        Fiat.Common.Tactics.HintDbExtra
        Fiat.Common.Tactics.TransparentAbstract.

Create HintDb stringCache.

Ltac fold_string_hyps :=
  (repeat foreach [ stringCache ] run (fun id => progress fold id in *)).

Ltac fold_string_hyps_in H :=
  repeat foreach [ stringCache ] run (fun id => progress fold id in H).

Ltac pose_string_hyps :=
  fold_string_hyps;
  repeat match goal with
         | |- context [String ?R ?R'] =>
           let str := fresh "StringId" in
           cache_term (String R R') as str
                                         run (fun id => fold id in *;
                                                add id to stringCache)
         | |- context [ @Build_BoundedIndex ?A ?n ?Bound ?bindex' ?indexb' ] =>
           let str := fresh "BStringId" in
           cache_term (@Build_BoundedIndex A n Bound bindex' indexb') as str
                                         run (fun id => fold id in *;
                                                add id to stringCache)
         end.

Ltac pose_string_hyps_in H :=
  fold_string_hyps_in H;
  repeat
    (let H' := eval unfold H in H in
         match H' with
         | context [String ?R ?R'] =>
           let str := fresh "StringId" in
           cache_term (String R R') as str
                                         run (fun id => fold id in *;
                                                add id to stringCache)
         | context [ @Build_BoundedIndex ?A ?n ?Bound ?bindex' ?indexb' ] =>
           let str := fresh "BStringId" in
           cache_term (@Build_BoundedIndex A n Bound bindex' indexb') as str
                                         run (fun id => fold id in *;
                                                add id to stringCache)
         end).
