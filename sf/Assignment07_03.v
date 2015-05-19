Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=

| E_BTrue : bevalR BTrue true
    | E_BFalse : bevalR BFalse false
    | E_BEq : forall (e1 e2 : aexp) (n1 n2 : nat),
                (e1 || n1) -> (e2 || n2) -> (bevalR (BEq e1 e2) (beq_nat n1 n2))
    | E_BLe : forall (e1 e2 : aexp) (n1 n2 : nat),
                (e1 || n1) -> (e2 || n2) -> (bevalR (BLe e1 e2) (ble_nat n1 n2))
    | E_BNot : forall (e : bexp) (b : bool),
                 (bevalR e b) -> (bevalR (BNot e) (negb b))
    | E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
                 (bevalR e1 b1) -> (bevalR e2 b2) -> (bevalR (BAnd e1 e2) (b1 && b2)).

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.

 split.
    + intros H; induction H; subst; simpl;
      try rewrite aeval_iff_aevalR in H;  try rewrite H; 
      try rewrite aeval_iff_aevalR in H0; try rewrite H0; reflexivity.
    + generalize dependent bv; induction b; simpl; intros; subst; constructor;
      try apply aeval_iff_aevalR; try apply IHe; try apply IHe1; try apply IHe2.
      reflexivity. auto. auto. auto. auto. auto. auto. Qed.
(** [] *)

