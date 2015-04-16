Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
intros n. induction n as [|n]. split. intro H. apply ev_0. intro H. inversion H.
apply ev_0. split. inversion IHn. simpl.  apply H0.  inversion IHn.
unfold even. destruct n. simpl. intros K. inversion K. simpl in H. 
intros H1. apply ev_SS. apply H. unfold even. apply H1 .
Qed.
(** [] *)


