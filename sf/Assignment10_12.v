Require Export Assignment10_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).
Proof.
  
  intros n st [H1 H2].
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. rewrite H2. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  rewrite H1.
  replace (n + 1) with (S n) by omega.
  eapply multi_refl.
Qed.

(*-- Check --*)
Check par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).




