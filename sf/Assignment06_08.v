Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
intros. induction l1. simpl. reflexivity. simpl. rewrite IHl1. reflexivity.

Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.

intros. induction H. exists []. simpl. exists l. reflexivity.
inversion H. exists (b::[]). exists l0. simpl. reflexivity.
inversion IHappears_in. inversion proof. rewrite H1. rewrite proof0. 
exists (b::witness). exists witness0. reflexivity. Qed.


(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| rep_base : forall l x, appears_in x l -> repeats (x::l)
| rep_step : forall l x, repeats l -> repeats (x::l).

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.

intros X l1 l2 EM.
unfold excluded_middle in EM.
assert (forall P, ~~P -> P) as NNPP.
  intros.
  destruct (EM P); [assumption | ].
  elimtype False; exact (H H0).
revert l2.
induction l1.

  simpl; intros.
  inversion H0.

  simpl.
  intros.
  apply NNPP; intro L1; apply L1.
  destruct (EM (appears_in x l1)).

    apply RP_hd.
    assumption.

    apply RP_tl.
    destruct (appears_in_app_split x l2).

      apply H.
      apply ai_here.

      destruct H2.
      apply (IHl1 (witness++witness0)).
      intros.
      rewrite H2 in *; clear H2.
      cut (appears_in x0 (witness ++ x :: witness0)).

        intro.
        apply app_appears_in.
        destruct (EM (appears_in x0 witness)).

          left; assumption.

          apply NNPP.
          intro L2.
          apply L2.
          generalize (or_comm (appears_in x0 witness) (appears_in x0 witness0)); intro.
          destruct H5.
          set (M := appears_in x0 witness) in *.
          set (N := appears_in x0 witness0) in *.
          apply H6.



   intros X l1. induction l1 as [|x l1'].

   (* FILL IN HERE *) admit. admit.
Qed.

