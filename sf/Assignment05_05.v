Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
unfold iff.
split. split. inversion H. left. apply H0. inversion H0. right. apply H1. inversion H. left. apply H0. inversion H0. right. apply H2.
intros H. inversion H. inversion H0. left. apply H2. inversion H0. left. apply H3. inversion H1. left. apply H4. right. split. apply H2. apply H4.
Qed.
(** [] *)


