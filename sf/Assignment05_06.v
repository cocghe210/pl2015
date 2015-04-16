Require Export Assignment05_05.

(* problem #06: 10 points *)


(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
intros b c H. destruct b. left. reflexivity. simpl in H. right. apply H. 
Qed.


