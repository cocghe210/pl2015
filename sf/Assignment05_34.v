Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
unfold lt.
intros n1 n2 m. generalize dependent n1. generalize dependent n2. induction m as [| m'].
intros n1 n2 lt'. inversion lt'. intros n1 n2 lte. destruct n1 as [| n1']. destruct n2 as [| n2']. 
apply conj. apply n_le_m__Sn_le_Sm. apply O_le_n. apply n_le_m__Sn_le_Sm. apply O_le_n.
apply conj. rewrite -> plus_0_r in lte. apply lte. apply n_le_m__Sn_le_Sm. apply O_le_n.
rewrite <- plus_n_Sm in lte. apply Sn_le_Sm__n_le_m in lte. apply IHm' in lte. destruct lte. apply conj.
apply le_S. apply H. apply n_le_m__Sn_le_Sm. apply H0.
Qed.


