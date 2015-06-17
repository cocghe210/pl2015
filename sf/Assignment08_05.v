Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
   match e with
  | ANum n     => [SPush n]
  | AId v      => [SLoad v]
  | APlus a b  => s_compile a ++ s_compile b ++ [SPlus]
  | AMinus a b => s_compile a ++ s_compile b ++ [SMinus]
  | AMult a b  => s_compile a ++ s_compile b ++ [SMult]
  end.
(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)
Check s_execute.
Check s_compile.
Theorem s_execute_app : forall st stack c1 c2,
  s_execute st stack (c1 ++ c2) = s_execute st (s_execute st stack c1) c2.
Proof.
  intros. generalize dependent stack. induction c1 as [| cmd c1' ].
    reflexivity. destruct cmd; simpl; intros stack; try apply IHc1'; destruct stack as [| s' stack']; try apply IHc1'; destruct stack' as [| s'' stack'']; apply IHc1'.
Qed.

Theorem s_compile_correct' : forall st stack e,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  intros. generalize dependent stack. aexp_cases (induction e) Case; try reflexivity;
    simpl; intros stack; rewrite -> s_execute_app; rewrite IHe1; rewrite -> s_execute_app; rewrite IHe2; reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply s_compile_correct'.
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].

