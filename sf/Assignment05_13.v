Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n. induction n. intros. unfold not. intros F. destruct m. inversion H. inversion F.
intros. unfold not. intros Y. destruct m. inversion Y. rewrite <- Y in H. inversion H. apply IHn in H1.
unfold not in H1. apply H1. reflexivity.
Qed.
(** [] *)



