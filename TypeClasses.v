Require Import Ltacs.
Require Import String.

Set Typeclasses Debug.

Class Dec (P : Prop) := { dec : P + ~ P }.

Theorem dec_impl_excluded_middle: forall P,
  Dec P ->
  (P \/ ~ P).
Proof.
  intros.
  destruct H; destruct dec0; eauto.
Qed.

Class DecEq (A : Type) := 
{
  decEq : forall x1 x2 : A, { x1 = x2 } + {x1 <> x2}
}.

Lemma nat_eq_dec' : forall n1 n2 : nat,
    {n1 = n2} + {n1 <> n2}.
Proof with eauto.
  ind n1; destruct n2...
  destruct (IHn1 n2)...
Qed.

(** Setting up some baseline Decidable props related to equality
    - This should allow for the other classes to be easily built
*)

#[global]
Instance nat_eq_dec (n1 n2 : nat) : Dec (n1 = n2).
destruct (nat_eq_dec' n1 n2); constructor; eauto.
Defined.

#[global]
Instance decEq_nat : DecEq nat.
constructor. ind x1; destruct x2; eauto.
specialize IHx1 with x2.
destruct IHx1; eauto. Defined.

#[global]
Instance decEq_string : DecEq string.
constructor. apply string_dec. Defined.

#[global]
Instance decEq_list (A : Type) `{DA : DecEq A} : DecEq (list A).
constructor. 
ind x1; dest x2; eauto; try (right; qcon; fail). 
(* Checking for list head equality *)
dest DA. dest (decEq0 a a0);
specialize IHx1 with x2; 
dest IHx1; subst; eauto; try (right; qcon; congruence).
Defined.

#[global]
Instance decEq_pair (A B : Type) `{DA : DecEq A} `{DB : DecEq B} : DecEq (A * B).
constructor.
ind x1; dest x2; eauto; try (right; qcon; fail).
dest DA; dest DB; dest (decEq0 a a0); dest (decEq1 b b0); 
subst; eauto; try (right; qcon; congruence).
Defined.

Class EqClass (A : Type) `{DE : DecEq A} :=
{
  eqb : A -> A -> bool ;
  eqb_leibniz   : forall x y, eqb x y = true <-> x = y  ;
  neqb_leibniz  : forall x y, eqb x y = false <-> x <> y;
}.

Definition gen_deceq_eqb {A : Type} `{DE : DecEq A} (a1 a2 : A) : bool :=
  match (decEq a1 a2) with
  | left e => true
  | right e => false
  end.

Lemma gen_eqb_impl_eqb_leibniz : forall {A : Type} `{Eq : DecEq A} (x y : A), 
  gen_deceq_eqb x y = true <-> x = y.
Proof.
  unfold gen_deceq_eqb.
  intros.
  destruct (decEq x y); split; eauto; try qcon.
Defined.

Lemma gen_eqb_impl_neqb_leibniz : forall {A : Type} `{Eq : DecEq A} (x y : A),
  gen_deceq_eqb x y = false <-> x <> y.
Proof.
  unfold gen_deceq_eqb.
  intros.
  destruct (decEq x y); split; eauto; try qcon.
Defined.

#[global]
Instance deceq_impl_eqb (A : Type) `{DE : DecEq A} : EqClass A :=
{
  eqb := gen_deceq_eqb ;
  eqb_leibniz := gen_eqb_impl_eqb_leibniz ;
  neqb_leibniz := gen_eqb_impl_neqb_leibniz
}.
