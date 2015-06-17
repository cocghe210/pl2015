Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
   intros c st nw. generalize dependent st. induction nw.
    Case "skip". intros st. exists st. admit. Qed.
 
(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

