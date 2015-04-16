Require Export Assignment05_37.

(* problem #38: 10 points *)

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
 intros n m o H1 H2. apply le_ble_nat. apply ble_nat_true in H1.
 apply ble_nat_true in H2. apply le_trans with (n:=m) (m:=n) (o:=o). apply H1.
 apply H2.
Qed.

