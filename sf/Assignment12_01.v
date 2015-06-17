Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.


  intros [S [T HT]].
  inversion HT; subst; clear HT.
  inversion H4; subst; clear H4.
  inversion H2; subst; clear H2.
  inversion H5; subst; clear H5.
  rewrite H1 in H2; clear H1.
  inversion H2; clear H2.
  induction T1.
    inversion H0.
    inversion H0. apply IHT1_1. rewrite H2. assumption.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate. 
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

