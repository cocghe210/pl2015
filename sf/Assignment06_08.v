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
 intros X l1. induction l1 as [|x l1'].
  induction l2. intros H1 H2 H3. inversion H3. intros H1 H2 H3. inversion H3.
  intros l2 EM A L.
  assert (repeats l1' \/ ~ repeats l1'). apply EM. induction H.
  apply rep_step . apply H.

  assert ((appears_in x l1' \/ ~ appears_in x l1')). apply EM. inversion H0. apply rep_base. apply H1.
apply rep_step. assert (appears_in x l2). apply A. apply ai_here.
apply  appears_in_app_split in H2. inversion H2. inversion proof.
apply IHl1' with (l2:=witness++ witness0). apply EM. intros.
 assert(forall x0:X, x0 <> x -> appears_in x0 l1' -> appears_in x0 (witness++witness0)).
intros. apply ai_later with (b :=x)in H5. apply A in H5. rewrite proof0 in H5.


Lemma app_nil_right : forall (X:Type) (l : list X),
  l ++ [] = l.
Proof. intros. induction l as [|h t]. simpl. reflexivity. simpl. rewrite -> IHt. reflexivity.
Qed.

Lemma unapp : forall (X:Type) (x:X) (l1 l2 : list X),
  x :: l1 ++ l2 = (x::l1) ++ l2.
Proof. intros. simpl. reflexivity. Qed.

Lemma appears_in_reorder : forall (X:Type) (x:X) (l1 l2 : list X),
  appears_in x (l1++l2) -> appears_in x (l2++l1).
Proof.
  intros X x l1. induction l1 as [|h t].
  Case "l=[]". intros. simpl in H. rewrite -> app_nil_right. apply H.
  Case "l=h::t". intros. simpl in H. apply app_appears_in.
  rewrite -> unapp in H. apply appears_in_app in H.
  inversion H. right. apply H0. left. apply H0.
Qed.


apply appears_in_reorder in H5. simpl in H5. 

Lemma appears_in_subl : forall (X:Type) (x  y :X) (xs : list X),
  x <> y -> appears_in x (y::xs) -> appears_in x xs.
Proof. intros. inversion H0. apply H in H2. inversion H2. apply H2. Qed.

 apply appears_in_subl in H5. apply appears_in_reorder in H5. apply H5.
intros. apply H4. apply H4. intro. rewrite H5 in H3.
apply H1.  apply H3. apply H3.
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Lmn Lno.
  generalize dependent Lmn.
  generalize dependent m.
  induction Lno.
 intros. apply Lmn.
 intros. apply le_S. apply IHLno. apply Lmn.
Qed.

Theorem n_le_Sn : forall n, n <= S n.
Proof. intros. apply le_S. apply le_n. Qed.

Theorem SnleSm : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
    apply le_n.
    apply le_trans with (n := S n). apply n_le_Sn.
    apply H1.
Qed.

rewrite proof0 in L. rewrite -> app_length with (l1:=witness) (l2:=x::witness0) in L.
simpl in L. rewrite -> plus_comm in L. simpl in L. rewrite -> plus_comm in L. rewrite <-app_length in L. apply SnleSm in L.
apply L. Qed.
