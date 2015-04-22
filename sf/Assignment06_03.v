Require Export Assignment06_02.

(* problem #03: 10 points *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
intros . unfold iff. split. intros H.  inversion H as [x H1]. destruct H1. left. exists x. apply H0.
right. exists x. apply H0. intros H. inversion H.  inversion H0 as [x H1]. exists x. left. apply H1.
inversion H0 as [x H1]. exists x. right. apply H1. Qed.

(** [] *)


