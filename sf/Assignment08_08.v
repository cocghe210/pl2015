Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
 intros b e1 e2.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "beval st b = true".
      apply E_IfFalse. simpl. rewrite H5. reflexivity. assumption.
    SCase "beval st b = false".
      apply E_IfTrue. simpl. rewrite H5. reflexivity. assumption.
  Case "<-".
   inversion H; remember (beval st b) as eval_b; destruct eval_b; subst.
    SCase "beval st (BNot b) = true".
      simpl in H5. rewrite <- Heqeval_b in H5. inversion H5.
      apply E_IfFalse. symmetry. assumption. assumption.
    SCase "beval st (BNot b) = false".
      apply E_IfTrue. symmetry. assumption. assumption.
      simpl in H5. rewrite <- Heqeval_b in H5. inversion H5.
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).

