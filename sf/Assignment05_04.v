Require Export Assignment05_03.

(* problem #04: 10 points *)



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
intros P Q R H1 H2. unfold iff. split. inversion H1. inversion H2. intros H5. apply H3. apply H. apply H5.
inversion H1. inversion H2. intros H5. apply H0. apply H4. apply H5.    
Qed.


