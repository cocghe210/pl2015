Require Export Assignment05_08.

(* problem #09: 10 points *)



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
intros P Q. intros H. unfold not. intros H1 H2. apply H in H2. apply H1 in H2. apply H2.
Qed.
(** [] *)



