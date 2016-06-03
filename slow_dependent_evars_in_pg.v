(* -*- coq-end-goals-regexp-show-subgoals: nil -*- *)
(** The above variable setting is required to make this example work.
    It is a kludge to work around the fact that, by default, things
    that you [idtac] or [Time] in Coq 8.4 don't show up in the *goals*
    nor *response* buffers in Coq 8.4 *)

Goal True. do 5000 (evar (x : Set); clear x).

 (* now scroll down to the bottom of the goals buffer, at the bottom
    of the dependent evars line, and place the cursor there, and then
    hit up arrow a few times.  Or try typing something in the script
    buffer with the cursor at the bottom of the goals buffer.  To see
    this slowness, you must have the variable
    coq-end-goals-regexp-show-subgoals set to nil, as per the bit at
    the top of this file *)
