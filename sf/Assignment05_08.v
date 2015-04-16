Require Export Assignment05_07.

(* problem #08: 10 points *)



(** 2 stars, advanced (double_neg_inf)  *)
Theorem double_neg_inf: forall (P: Prop),
  P -> ~~P.
Proof.
intros P. unfold not. intros H H1. apply H1. apply H.
Qed.
(** [] *)



