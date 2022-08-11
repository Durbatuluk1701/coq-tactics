Tactic Notation "smp" := (simpl in *).

Ltac ind x := induction x.
Ltac inv x := inversion x.
Ltac invc x := inversion x; clear x.
Ltac invsc x := 
  let x' := fresh "x" in
  inversion x as x'; rewrite x' in *; clear x.
