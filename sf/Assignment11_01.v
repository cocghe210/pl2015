Require Export Assignment11_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue).
  unfold stuck, normal_form, value.
  split; unfold not; intros.
  solve by inversion 3.
  solve by inversion 3. 
Qed.

(*-- Check --*)
Check some_term_is_stuck :
  exists t, stuck t.

