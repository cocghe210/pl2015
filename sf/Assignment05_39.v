Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
intros n m. generalize dependent n. induction m as [| m'].
intros n h lte. inversion lte. rewrite -> H0 in h. inversion h.
intros n h lte. destruct n as [| n']. inversion h.
apply IHm' in h. apply h. apply Sn_le_Sm__n_le_m. apply lte.
Qed.
(** [] *)

