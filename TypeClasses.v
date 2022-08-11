Require Import Ltacs.

Class Dec (P : Prop) := { dec : P + ~ P }.

Theorem dec_impl_excluded_middle: forall P,
  Dec P ->
  (P \/ ~ P).
Proof.
  intros.
  destruct H; destruct dec0; eauto.
Qed.

Class DecEq {A : Type} (x1 x2 : A) `(Dec (x1 = x2)) := 
{
  decEq : { x1 = x2 } + {x1 <> x2}
}.

Lemma nat_eq_dec' : forall n1 n2 : nat,
    {n1 = n2} + {n1 <> n2}.
Proof with eauto.
  induction n1; destruct n2...
  destruct (IHn1 n2)...
Qed.

#[global]
Instance nat_eq_dec (n1 n2 : nat) : Dec (n1 = n2).
destruct (nat_eq_dec' n1 n2); constructor; eauto.
Defined.

(* 
  Any type that has a decision procedure for equality -> equality is decidable
*)
#[global]
Instance dec_impl_deceq {A : Type} (a1 a2 : A) `{D : Dec (a1 = a2)} : DecEq a1 a2 D.
constructor. inv D. inv dec0; eauto. Defined.

#[global]
Instance decEq_nat (n1 n2 : nat) `{d : Dec (n1 = n2)} : DecEq n1 n2 d.
apply (@dec_impl_deceq nat n1 n2 d). Defined.

#[global]
Instance decEq_string (s1 s2 : string) `(d : Dec (s1 = s2)) : 

Class Ord `(E : EqDec A) := { le : A -> A -> bool }.