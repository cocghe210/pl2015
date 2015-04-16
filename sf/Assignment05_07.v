Require Export Assignment05_06.

(* problem #07: 10 points *)



(** 2 stars, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
intros b c H. destruct b. inversion H. simpl in H. split. reflexivity. apply H.
Qed.
(** [] *)



