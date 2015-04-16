Require Export Assignment05_28.

(* problem #29: 10 points *)





(** 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
 intros m n o Lmn Lno.
  generalize dependent Lmn.
  generalize dependent m.
  induction Lno.
  intros. apply Lmn.
  intros. apply le_S. apply IHLno. apply Lmn.
Qed.

