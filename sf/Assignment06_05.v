Require Export Assignment06_04.

(* problem #05: 20 points *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_empty : all P []
  | all_cons  : forall (x:X) (l:list X), P x -> all P l -> all P (x::l).

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
 


intros X test l. split.
   intros H. induction l as [|h t]. apply all_empty.
apply all_cons. simpl in H.
destruct (test h). reflexivity. apply H.
apply IHt.
Lemma andb_true1: forall b c : bool, andb b c = true -> c = true.
Proof. intros. induction b. induction c. reflexivity. inversion H. inversion H. Qed.  
apply andb_true1 in H. apply H.

intros H. induction H. reflexivity. simpl. rewrite H. rewrite IHall. reflexivity. Qed.

(** [] *)

