Tactic Notation "smp" := (simpl in *).

Ltac gendep x :=
  generalize dependent x.

Ltac clearAll :=
  repeat 
  match goal with
  | H : _ |- _ => clear H
  end.

Tactic Notation "destH_or" :=
  match goal with
  | H : _ \/ _ |- _  => 
      let H1' := fresh "H" in
      let H2' := fresh "H" in
      destruct H as [H1' | H2']
  end.

Tactic Notation "destH_and" :=
  match goal with
  | H : _ /\ _ |- _ =>
      let H1' := fresh "H" in
      let H2' := fresh "H" in
      destruct H as [H1' H2']
  end.

Tactic Notation "destH_exists" :=
  match goal with
  | H : exists X , _  |- _  =>
      let X' := fresh X in
      let H' := fresh "H" in
      destruct H as [X' H']
  end.

Tactic Notation "destH" :=
  do 2 (* doing twice in case it unfolds something *)
  (repeat destH_exists;  
  repeat destH_or;
  repeat destH_and).


Ltac ind x := induction x.

Ltac dest x := destruct x.

Ltac refl := reflexivity.

Ltac cong := congruence.

Ltac intu := intuition.

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
Ltac sbi' n :=
  match goal with
  | H : _ |- _ =>
    match n with
    | 0 => idtac "SBI Failed - try increasing 'n'"
    | S ?n' => invsc H; sbi' n'
    end
  end.

Ltac sbi := sbi' 5.

(*
  Contradiction Solving
*)
Ltac qcon := 
  (* TODO: Make more robust *)
  intros C; try (inversion C || cong); try (cong).
