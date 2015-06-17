Require Export Assignment09_03.

(* problem #04: 10 points *)

(** **** Exercise: 2 stars (hoare_asgn_example4)  *)
(** Translate this "decorated program" into a formal proof:
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
    eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence.
      apply hoare_asgn.
      intros st H. assert(((fun st : state => st X = 1) [X |-> ANum 1]) st).
      reflexivity. apply H0.
    intros st H. unfold assn_sub.
    destruct (eq_id_dec X Y) eqn:eq.
    inversion e. apply conj. rewrite update_neq; auto.
      rewrite update_eq; auto.
  Qed.

(*-- Check --*)
Check hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.

