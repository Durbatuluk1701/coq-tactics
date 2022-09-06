Require Import Ltacs.
Require Import String.

(* Set Typeclasses Debug. *)

Class Dec (P : Prop) := { dec : P + ~ P }.

Theorem dec_impl_excluded_middle: forall P,
  Dec P ->
  (P \/ ~ P).
Proof.
  intros.
  destruct H; destruct dec0; eauto.
Qed.

Theorem dec_impl_equiv_bool : forall (P : Prop),
  Dec P ->
  exists f, (P <-> f = true) /\ (~ P <-> f = false).
Proof.
  intros.
  dest H.
  dest dec0; eauto.
  - exists true; split; split; eauto; qcon.
  - exists false; split; split; eauto; qcon.
Qed.

Lemma dec_le_nat : forall (a b : nat),
  Dec (a <= b).
Proof.
  induction a; dest b; econstructor; eauto.
  - left. ind b; eauto.
  - right. qcon.
  - specialize IHa with b. dest IHa.
    dest dec0.
    * left. eapply le_n_S. eauto.
    * right. intros HC. eapply le_S_n in HC. cong.
Defined.

#[global]
Instance dec_le_nat_inst (a b : nat) : Dec (a <= b).
eapply dec_le_nat. Defined.

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

Theorem eqb_refl_all : forall {A : Type} `{H : EqClass A} (a : A),
  eqb a a = true.
Proof.
  destruct H; intros.
  rewrite eqb_leibniz0. auto.
Qed.

Definition gen_deceq_eqb {A : Type} `{DE : DecEq A} (a1 a2 : A) : bool :=
  match (decEq a1 a2) with
  | left e => true
  | right e => false
  end.

Theorem gen_deceq_eqb_refl: forall {A : Type} `{DE : DecEq A} (a : A),
  gen_deceq_eqb a a = true.
Proof.
  intros. 
  unfold gen_deceq_eqb.
  destruct DE. simpl.
  destruct (decEq0 a a).
  - refl.
  - cong.
Qed.

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


Class Partial_Order {A : Type} `{Eq : EqClass A} (lte : A -> A -> Prop) :=
{
  po_reflexive : forall (a : A), lte a a ;
  po_antiSym : forall (a b : A), lte a b -> lte b a -> eqb a b = true ;
  po_transitivity : forall (a b c : A),
      lte a b ->
      lte b c ->
      lte a c
}.

Lemma nat_eqb_sn : forall (a b : nat),
  eqb a b = true <->
  eqb (S a) (S b) = true.
Proof.
  ind a; dest b; eauto; split; eauto; intros.
  - unfold eqb, deceq_impl_eqb, gen_deceq_eqb, decEq, decEq_nat, nat_rec, nat_rect in *.
    destruct (match
        (fix F (n : nat) : forall x2 : nat, {n = x2} + {n <> x2} :=
           match n as n0 return (forall x2 : nat, {n0 = x2} + {n0 <> x2}) with
           | 0 =>
               fun x2 : nat =>
               match x2 as n0 return ({0 = n0} + {0 <> n0}) with
               | 0 => left eq_refl
               | S n0 => right (O_S n0)
               end
           | S n0 =>
               fun x2 : nat =>
               match x2 as n1 return ({S n0 = n1} + {S n0 <> n1}) with
               | 0 => right (not_eq_sym (O_S n0))
               | S n1 =>
                   match F n0 n1 with
                   | left a => left (f_equal_nat nat S n0 n1 a)
                   | right b => right (not_eq_S n0 n1 b)
                   end
               end
           end) a b
      with
      | left a0 => left (f_equal_nat nat S a b a0)
      | right b0 => right (not_eq_S a b b0)
      end); eauto.
  - unfold eqb, deceq_impl_eqb, gen_deceq_eqb, decEq, decEq_nat, nat_rec, nat_rect in *.
    destruct (match
          (fix F (n : nat) : forall x2 : nat, {n = x2} + {n <> x2} :=
             match n as n0 return (forall x2 : nat, {n0 = x2} + {n0 <> x2}) with
             | 0 =>
                 fun x2 : nat =>
                 match x2 as n0 return ({0 = n0} + {0 <> n0}) with
                 | 0 => left eq_refl
                 | S n0 => right (O_S n0)
                 end
             | S n0 =>
                 fun x2 : nat =>
                 match x2 as n1 return ({S n0 = n1} + {S n0 <> n1}) with
                 | 0 => right (not_eq_sym (O_S n0))
                 | S n1 =>
                     match F n0 n1 with
                     | left a => left (f_equal_nat nat S n0 n1 a)
                     | right b => right (not_eq_S n0 n1 b)
                     end
                 end
             end) a b
        with
        | left a0 => left (f_equal_nat nat S a b a0)
        | right b0 => right (not_eq_S a b b0)
        end); eauto.
Qed.



#[global]
Instance partial_order_nats : Partial_Order le.
constructor.
- induction a; eauto.
- induction a; destruct b; intros; eauto.
  * inv H0.
  * inv H.
  * eapply le_S_n in H, H0. assert (eqb a b = true). eauto.
    rewrite <- nat_eqb_sn; eauto.
- induction a; dest b; dest c; intros; eauto;
  eapply PeanoNat.Nat.le_trans; eauto.
Defined.

Class Total_Order {A : Type} (lte : A -> A -> Prop) `{PO : Partial_Order A lte} :=
{
  decLte : forall (a b : A), Dec (lte a b)
}.

Lemma nat_0_le_sn : forall (n : nat),
  0 <= S n.
Proof.
  induction n; eauto.
Qed.

#[global]
Instance total_order_nat : Total_Order le.
constructor.
induction a; dest b; constructor; eauto.
- left. eapply nat_0_le_sn.
- right. intros HC. inv HC.
- specialize IHa with b. dest IHa.
  dest dec0.
  * (* a <= b *)
    left. apply le_n_S; eauto.
  * (* ~ a <= b *)
    right. intros HC. 
    eapply le_S_n in HC. cong.
Defined.

Class WellFounded {A : Type} (R : A -> A -> Prop) `{PO : Partial_Order A R} :=
{
  min : A ;
  minElemProof : 
    (forall (a : A), (R min a)) /\
    (forall (a : A), a <> min -> ~ (R a min))
}.

#[global]
Instance wf_nat : WellFounded le.
pose proof (Build_WellFounded _ le _ _ _ 0).
apply H. clear H.
intros. split.
- induction a; eauto.
- induction a; eauto.
  intros; qcon.
Defined.

Class Defaultable (A : Type) := 
{
  defVal : A 
}.

#[global]
Instance nat_defaultable : Defaultable nat :=
{
  defVal := 0
}.

#[global]
Instance string_defaultable : Defaultable string :=
{
  defVal := ""
}.

#[global]
Instance list_defaultable {A : Type} : Defaultable (list A) :=
{
  defVal := nil
}.

#[global]
Instance pair_defaultable {A B : Type} `{HA : Defaultable A} `{HB : Defaultable B} : Defaultable(A * B) :=
{
  defVal := (defVal, defVal)
}.
