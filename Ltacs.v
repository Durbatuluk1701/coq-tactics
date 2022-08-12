Tactic Notation "smp" := (simpl in *).

Ltac ind x := induction x.

Ltac dest x := destruct x.

Ltac refl := reflexivity.

Ltac cong := congruence.

(*
  Inversion simpler notation tactics
*)
Ltac inv x := inversion x.
Ltac invc x := inversion x; clear x.
Ltac invsc x := inversion x; subst; clear x.

(*
  Print Goal - 
    Helpful tactic when you want to see where something is failing
    before restoring to original state
*)
(* Tactic Notation "PG" *)
Ltac PG := match goal with |- ?A => idtac A end.

(*
  Solve_By_Inversion
*)
(* Tactic Notation "sbi" *)


(*
  Contradiction Solving
*)
Ltac qcon := 
  (* TODO: Make more robust *)
  intros C; try (inversion C || cong).
