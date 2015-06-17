Require Export Assignment08_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof. 
   intros c1 c1' c2 c2' c1eq c2eq. split; intros H.
  Case "->".
    inversion H; subst. apply E_Seq with st'0.
      apply c1eq. apply H2.
      apply c2eq. apply H5.
  Case "<-".
    inversion H; subst. apply E_Seq with st'0.
      apply c1eq. apply H2.
      apply c2eq. apply H5.
Qed.

(*-- Check --*)
Check CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').

