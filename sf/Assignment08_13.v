Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
    intros b b' c1 c1' c2 c2' beq c1eq c2eq. split; intros H.
  Case "->".
    inversion H; subst.
      SCase "condition is true".
        apply E_IfTrue.
          rewrite <- beq. assumption.
          apply c1eq. assumption.
      SCase "condition is false".
        apply E_IfFalse.
          rewrite <- beq. assumption.
          apply c2eq. assumption.
  Case "->".
    inversion H; subst.
      SCase "condition is true".
        apply E_IfTrue.
          rewrite -> beq. assumption.
          apply c1eq. assumption.
      SCase "condition is false".
        apply E_IfFalse.
          rewrite -> beq. assumption.
          apply c2eq. assumption.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

