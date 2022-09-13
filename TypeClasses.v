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


Class Partial_Order {A : Type} `{Eq : EqClass A} (R : A -> A -> Prop) :=
{
  po_reflexive : forall (a : A), R a a ;
  po_antiSym : forall (a b : A), R a b -> R b a -> eqb a b = true ;
  po_transitivity : forall (a b c : A),
      R a b ->
      R b c ->
      R a c
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

Class Total_Order {A : Type} (R : A -> A -> Prop) `{PO : Partial_Order A R} :=
{
  dec_t_order : forall (a b : A), R a b + R b a
}.

Theorem total_order_invertible : forall {A : Type} {R : A -> A -> Prop} 
  `{HT : Total_Order A R} (a b : A),
    a <> b ->
    R a b <-> ~ R b a.
Proof.
  split; intros.
  - dest PO. intros HC.
    pose proof (po_antiSym0 _ _ H0 HC).
    rewrite eqb_leibniz in H1. cong.
  - dest (dec_t_order a b); eauto.
    cong.
Qed.

Require Import List.

#[global]
Instance dec_in {A : Type} `{Heq : EqClass A} (a : A) (l : list A) : Dec (In a l).
constructor.
induction l; smp; eauto.
destruct IHl.
- (* In a l *)
  eauto.
- (* ~ In a l *)
  destruct (eqb a0 a) eqn:E.
  * (* a0 = a *)
    rewrite eqb_leibniz in E. eauto.
  * (* a0 <> a *)
    rewrite neqb_leibniz in E. 
    right. qcon.
Defined.

Require Import Lia.

Fixpoint t_order_max_in_list {A : Type} (l : list A) 
  (R : A -> A -> Prop) `{TO : Total_Order A R} : option A.
destruct l eqn:L'.
- apply None.
- destruct (t_order_max_in_list A l0 R DE Eq0 PO TO) eqn:Rec.
  * (* rec = Some a0 *)
    destruct (dec_t_order a a0).
    ** (* R a a0 - so a0 max *)
      apply (Some a0).
    ** (* R a0 a - so a max *)
      apply (Some a).
  * (* rec = None *)
    apply (Some a).
Defined.

Class WeakMaximal {A : Type} (R : A -> A -> Prop) :=
{
  weakMaxElemProof : forall (l : list A), l <> nil -> exists (max : A),
      (forall (elem : A), In elem l -> R elem max)
}.

#[global]
Instance maximal_nats : WeakMaximal le.
constructor.
induction l.
- intros. cong.
- intros.
  destruct l; smp.
  * (* l = nil *)
    exists a; intros; eauto.
    destruct H0; subst; eauto; try exfalso; eauto.
  * (* l = n :: l *)
    assert (n :: l <> nil). {
      clearAll.
      induction l; eauto; try qcon.
    }
    pose proof (IHl H0) as IHl. 
    clear H. clear H0.
    destruct IHl as [max' H].
    assert (n < max' \/ n = max' \/ max' < n). lia.
    destruct H0.
    **  (* n < max' *)
        assert (a < max' \/ a = max' \/ max' < a). lia.
        destruct H1.
      *** (* a < max' => max' is greatest *)
          exists max'; intros; eauto.
          destruct H2; eauto; subst; eauto; try lia.
      *** destruct H1.
        ****  (* a = max' => a/max' is greatest *)
              subst.
              exists max'; intros; eauto.
              destruct H1; eauto; subst; eauto; try lia.
        ****  (* max' < a => a is greatest *)
              exists a; intros; eauto.
              destruct H2; eauto; subst; eauto; try lia;
              destruct H2; subst; eauto; try lia.
              eapply PeanoNat.Nat.le_trans.
              eapply H; eauto. lia.
    **  (* n = max' \/ max' < n*)
        destruct H0.
      *** (* n = max' *)
          subst.
          assert (a < max' \/ a = max' \/ max' < a). lia.
          destruct H0.
        ****  exists max'; intros; eauto.
              destruct H1; eauto; subst; eauto; try lia.
        ****  destruct H0.
          ***** subst. (* a = max' *)
                exists max'; intros; eauto.
                destruct H0; eauto.
          ***** (* max' < a *)
                exists a; intros; eauto.
                destruct H1; subst; eauto.
                destruct H1; subst; eauto; try lia.
                eapply PeanoNat.Nat.le_trans.
                eapply H; eauto. lia.
      *** (* max' < n *)
          assert (a < n \/ a = n \/ n < a). lia.
          destruct H1; eauto.
        ****  (* max' < n, a < n -> n greatest *)
              exists n; intros; eauto.
              destruct H2; subst; eauto; try lia.
              destruct H2; subst; eauto; try lia.
              eapply PeanoNat.Nat.le_trans.
              eapply H; eauto. lia.
        ****  (* a = n \/ n < a *)
              destruct H1; subst; eauto.
          ***** (* a = n -> n greatest *)
                exists n; intros; eauto.
                destruct H1; subst; eauto; try lia.
                destruct H1; subst; eauto; try lia.
                eapply PeanoNat.Nat.le_trans.
                eapply H; eauto. lia.
          ***** (* n < a -> a greatest *)
                exists a; intros; eauto.
                destruct H2; subst; eauto; try lia.
                destruct H2; subst; eauto; try lia.
                eapply PeanoNat.Nat.le_trans.
                eapply H; eauto. lia.
Defined.

Lemma nat_0_le_sn : forall (n : nat),
  0 <= S n.
Proof.
  induction n; eauto.
Qed.

#[global]
Instance total_order_nat : Total_Order le.
constructor.
induction a; destruct b; eauto.
- left. lia.
- right. lia.
- specialize IHa with b. dest IHa.
  * (* a <= b *)
    left. apply le_n_S; eauto.
  * (* ~ a <= b *)
    right. lia.
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
