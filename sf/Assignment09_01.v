Require Export Assignment09_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (hoare_asgn_examples)  *)


Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
  intros Q X a.
  unfold hoare_triple.
  intros st st' Hc HQ.
  inversion Hc.
  unfold assn_sub in HQ.
  subst.
  assumption.
Qed.

Theorem assn_sub_ex1: 
  {{ (fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1)] }}
      X ::= APlus (AId X) (ANum 1)
  {{ fun st => st X <= 5 }}.
Proof.
apply hoare_asgn.
Qed.

(*-- Check --*)
Check assn_sub_ex1: 
  {{ (fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1)] }}
      X ::= APlus (AId X) (ANum 1)
  {{ fun st => st X <= 5 }}.

