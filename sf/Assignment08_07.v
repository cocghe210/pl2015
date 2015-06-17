Require Export Assignment08_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.
Proof.
   intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst. 
    SCase "b evaluates to true (contradiction)".
      rewrite Hb in H5. inversion H5.
    SCase "b evaluates to false".
       assumption.
  Case "<-".
    apply E_IfFalse. rewrite Hb. reflexivity. assumption.
Qed.

(*-- Check --*)
Check IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.

