Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof. 
  intros n st H. induction n.
  Case "n = 0".
    exists st. split.
      apply multi_refl.
      apply H.
  Case "S n".
    destruct IHn as [st' [A [B C]]].
    exists (update st' X (S n)).
    split.
      eapply multi_trans.
        apply A.
        apply par_body_n__Sn. split; assumption.
      split.
        rewrite update_eq. reflexivity.
        rewrite update_neq; try reflexivity. assumption.
inversion A.
inversion H. subst.
intro.
intuition.
discriminate.
intro.
discriminate. 
Qed.
(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

