Require Export Assignment05_34.

(* problem #35: 10 points *)

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
    unfold lt. intros n m H. apply le_S. apply H.
Qed.