Require Export Assignment05_26.

(* problem #27: 10 points *)


Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
intros n. induction n. unfold even.  simpl. intros H. apply ev_0.
apply even__ev_strong.
Qed.
(** [] *)


