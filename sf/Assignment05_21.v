Require Export Assignment05_20.

(* problem #21: 10 points *)





(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros n m En Em. induction En. simpl. apply Em. simpl. apply ev_SS. apply IHEn.
Qed.
(** [] *)





