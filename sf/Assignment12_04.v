Require Export Assignment12_03.

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
   intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti. destruct (progress x T Hhas_type); auto.
    apply IHHmulti; try assumption.
      apply (preservation x y T Hhas_type H).
Qed.


(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').

