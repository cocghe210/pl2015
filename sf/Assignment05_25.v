Require Export Assignment05_24.

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
intros n m p Emn En. apply ev_ev__ev with (n :=(n+n)) (m:=(m+p)). replace (n + n + (m + p)) with ((n + m) + (n + p)).
apply ev_sum. apply Emn. apply En. replace (n + p) with (p + n).
rewrite plus_assoc. rewrite plus_comm. rewrite <- plus_assoc. rewrite <- plus_assoc. reflexivity.
apply plus_comm. rewrite <- double_plus. apply double_even.
Qed.
(** [] *)


