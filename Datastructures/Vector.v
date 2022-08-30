Require Import List Lia.
Require Import TypeClasses Ltacs.
(* Requiring, but not yet importing *)
Require Coq.Program.Equality.
Import ListNotations.

Tactic Notation "exT" hyp(H) := 
  eapply (Eqdep_dec.inj_pair2_eq_dec) in H;
  try (apply nat_eq_dec').

(*
  [Vectors] are lists plus size built in. More unwieldy to construct,
  more powerful to use.
*)
Inductive Vector {A : Type} : nat -> Type :=
| vecnil  : @Vector A 0
| veccons : forall (x : A) (n : nat), Vector n -> Vector (S n).

Definition vector_length {A : Type} {len : nat} (v : @Vector A len) := len.

Fixpoint default_vector {A : Type} `{H : Defaultable A} (n : nat) : (@Vector A n) :=
  match n with
  | 0 => vecnil
  | S n' => (veccons defVal n' (default_vector n'))
  end.

#[global]
Instance defaultable_vector {A : Type} `{H : Defaultable A} (n : nat) : Defaultable (@Vector A n) :=
{
  defVal := default_vector n
}.

Fixpoint vector_get_value {A : Type} {len : nat}
  (vec : @Vector A len) (index : nat) : option A :=
  match index with
  | 0 => 
      match vec with
      | vecnil => None
      | (veccons curA remLen vec') =>
          Some curA
      end
  | S ind' =>
      match vec with
      | vecnil => None
      | (veccons curA remLen vec') =>
          vector_get_value vec' ind'
      end
  end.

Lemma vgv_gte_len_none : forall {A : Type} {len : nat} (n : nat)
  (v : @Vector A len),
  n >= len ->
  vector_get_value v n = None.
Proof.
  intros A len n v.
  generalize dependent n.
  induction v; intros; destruct n; simpl; eauto.
  - destruct n0; try (eapply IHv); lia.
  - destruct n0; try (eapply IHv); lia.
Qed.

Lemma vgv_lt_len_some : forall {A : Type} {len : nat} (n : nat)
  (v : @Vector A len),
  n < len ->
  exists aVal, vector_get_value v n = Some aVal.
Proof.
  intros A len n v.
  generalize dependent n.
  induction v; intros; destruct n; simpl; try lia.
  - destruct n0; try (eapply IHv); try lia.
    eexists. eauto.
  - destruct n0; try (eapply IHv); try lia.
    eexists. eauto.
Qed.

Fixpoint vector_set_value {A : Type} {len : nat} 
    (vec : (@Vector A len)) (index : nat) (newV : A) : (@Vector A len) :=
  match index with
  | 0 => 
      match vec with
      | vecnil => vecnil
      | (veccons curA remLen vec') =>
          (veccons newV remLen vec')
      end
  | S ind' =>
      match vec with
      | vecnil => vecnil
      | (veccons curA remLen vec') =>
          (veccons curA remLen (vector_set_value vec' ind' newV))
      end
  end.

Lemma vsv_gte_len_same : forall {A : Type} {len : nat} (n : nat)
  (v : @Vector A len) (newV : A),
  n >= len ->
  vector_set_value v n newV = v.
Proof.
  intros A len n v.
  generalize dependent n.
  induction v; intros; destruct n; simpl; eauto.
  - destruct n0; try (erewrite IHv); eauto; lia.
  - destruct n0; try (erewrite IHv); eauto; lia.
Qed.

(** This sort of lemma is slightly convoluted and 
    we wont prove until needed.
*)
Lemma vsv_lt_len_some : forall {A : Type} {len : nat} (n : nat)
  (v v' : @Vector A len) (curV newV : A),
  n < len ->
  vector_get_value v n = Some curV ->
  vector_set_value v n newV = v' ->
  curV <> newV ->
  v <> v'.
Proof.
  intros A len n v.
  generalize dependent n.
  induction v; intros; destruct n; simpl; try lia.
  - inv H0. inv H1. destruct n0; try lia.
    inv H4. subst. simpl. intros HC.
    inversion HC. cong.
  - inv H0. inv H1. destruct n0; try lia.
    * (* n0 = 0 *)
      inv H4. subst. simpl. intros HC.
      inversion HC. cong.
    * (* n0 = S n0 *)
      simpl in *. assert (n0 < S n). lia.
      destruct (vector_set_value v n0 newV) eqn:VSV.
      ** (* vsv = vecnil *)
         specialize IHv with n0 vecnil curV newV.
         eapply (IHv H5 H0 VSV) in H2.
         intros HC. inversion HC. exT H7; eauto.
      ** (* vsv = (veccons x0 n1 v0) *)
         specialize IHv with n0 (veccons x0 n1 v0) curV newV.
         eapply (IHv H5 H0 VSV) in H2.
         intros HC. inversion HC. exT H7; eauto.
Qed.

Module VectorNotations.
Declare Scope vector_scope.
Delimit Scope vector_scope with vector.
Notation "<[ ]" := vecnil (format "<[ ]") : vector_scope.
Notation "h <:: t" := (veccons h _ t) (at level 60, right associativity)
  : vector_scope.
Notation "<[ x ]" := (veccons x 0 vecnil) (at level 105) : vector_scope.
Notation "<[ x ; y ; .. ; z ]" := (veccons x _ (veccons y _ .. (veccons z _ (vecnil)) ..)) (at level 105) : vector_scope.
Notation "v <@[ i ]" := (vector_get_value v i) (at level 60, right associativity) : vector_scope.
Notation "v set<@[ i ] <- v'" := (vector_set_value v i v') (at level 65, left associativity) : vector_scope.
Open Scope vector_scope.
End VectorNotations.

Import VectorNotations.

Example vec1 : @Vector nat 0. econstructor. Defined.

Example vec2 : @Vector nat 2.
repeat econstructor. Defined.

Example vec3 : @Vector nat 3 := <[1 ; 2 ; 3].

Example vec3get : vec3 <@[2] = Some 3. reflexivity. Defined.

Example vec3set : (vec3 set<@[1] <- 42) = <[ 1 ; 42 ; 3].
reflexivity. Defined.

Example vec4 : @Vector nat 1 := 1 <:: vecnil.

Fixpoint list_to_vec {A : Type} (l : list A) : @Vector A (length l).
destruct l; simpl.
- apply vecnil.
- apply veccons; eauto.
Defined.

Lemma list_to_vec_preserve_len : forall {A : Type} (l : list A),
  length l = vector_length (list_to_vec l).
Proof.
  induction l; eauto.
Qed.

Example ltv1test : (list_to_vec [1;2;3]) = <[ 1 ;2;3].
reflexivity. Defined.

Fixpoint vec_to_list {A : Type} {n : nat} (ls : Vector n) : list A :=
  match ls with
  | vecnil => nil
  | veccons x n vec' =>
      x :: (vec_to_list vec')
  end.

Lemma vec_to_list_preserve_len : forall {A : Type} {len : nat} (v : @Vector A len),
  vector_length v = length (vec_to_list v).
Proof.
  induction v; eauto. simpl.
  unfold vector_length in *.
  eauto.
Qed.

Example vec11 : 
  vec_to_list (<[ 1 ]) = [1].
unfold vec_to_list. reflexivity. Defined.

Example vec1test : (vec_to_list (<[ 12 ; 42 ])) = [12; 42].
reflexivity. Defined.

Lemma vector_forall_lists : forall A (l : list A),
  exists v : (@Vector A (length l)), True.
Proof with (repeat econstructor; eauto).
  intros.
  induction l; simpl in *.
  - eexists...
  - inversion IHl. eexists...
Qed.

Theorem vectors_equiv_lists : forall A (l : list A),
  exists v : (@Vector A (length l)),
    v = list_to_vec l.
Proof with (repeat econstructor; eauto).
  intros.
  induction l; simpl in *.
  - eexists...
  - inversion IHl. eexists...
Qed.

Theorem vec_to_list_involutive :
  forall A (l : list A),
  vec_to_list (list_to_vec l) = l.
Proof with eauto.
  induction l...
  simpl. rewrite IHl...
Qed.

(** Vector Testing
    - We need to ensure that the access of vectors is intuitive
*)
Definition tvec1 := <[ 1 ; 2 ; 3; 4].
Example testVec1_1 : tvec1 <@[1] = Some 2. reflexivity. Defined.
Example testVec1_2 : tvec1 <@[0] = Some 1. reflexivity. Defined.
Example testVec1_3 : tvec1 <@[4] = None. reflexivity. Defined.
Example testVec1_4 : tvec1 <@[3] = Some 4. reflexivity. Defined.

Fixpoint eqb_vector {A : Type} `{H : EqClass A} {n1 n2 : nat} 
  (v1 : (@Vector A n1)) (v2 : (@Vector A n2)) : bool :=
  match v1, v2 with
  | vecnil, vecnil => true
  | (veccons curA1 n1' vec1'), (veccons curA2 n2' vec2') =>
      if (eqb curA1 curA2)
      then eqb_vector vec1' vec2'
      else false
  | _, _ => false
  end.

Theorem eqb_vector_refl: forall {A : Type} `{H : EqClass A} {len : nat}
  (v : (@Vector A len)),
    eqb_vector v v = true.
Proof.
  destruct H.
  induction v; simpl; eauto.
  assert (eqb x x = true). rewrite eqb_leibniz. auto.
  rewrite H. auto.
Qed.

Lemma eqb_vector_only_same_size : forall {A : Type} `{H : EqClass A} {n1 n2 : nat}
  (v1 : (@Vector A n1)) (v2 : (@Vector A n2)),
  eqb_vector v1 v2 = true -> n1 = n2.
Proof.
  intros. generalize dependent n2.
  induction v1; destruct v2; eauto; intros Hvec.
  - inversion Hvec.
  - inversion Hvec.
  - inversion Hvec.
    destruct (Nat.eqb n n0) eqn:Neq.
    * (* n = n0*) 
      destruct H.
      destruct (eqb x x0) eqn:Xeq.
      ** (* x = x0 *) 
        destruct (eqb_vector v1 v2) eqn:Veq.
        *** (* v1 = v2 *) 
            eapply IHv1 in Veq. subst. eauto.
        *** (* v1 <> v2 *) inversion H1.
            destruct (eqb x x0); eauto.
      ** (* x <> x0 *) inversion H1.
          destruct (eqb x x0); eauto; cong.
    * (* n <> n0 *) 
      destruct (eqb x x0); eauto. cong.
Qed.

Theorem eqb_vector_works : forall {A : Type} `{H : EqClass A} {len : nat}
  (v1 v2 : @Vector A len),
  eqb_vector v1 v2 = true ->
  (forall (i : nat),
    (v1 <@[i]) = (v2 <@[i])).
Proof.
  induction v1; destruct v2; eauto; intros; try inversion H0.
  destruct (eqb x x0) eqn:Eqx; try congruence.
  * (* x = x0 *)
    pose proof (eqb_vector_only_same_size _ _ H2). subst.
    pose proof (IHv1 _ H2).
    destruct i; eauto.
    simpl. erewrite eqb_leibniz in Eqx. subst. eauto.
Qed.

Module VectorTypeClass.
(** Note: Importing this also comes with the burden of JMeq
    it is necessary for proving things related to vector equality
    implying leibniz equality
    - Specifically it includes "dependent destruction" which is 
      very powerful
*)
Import Coq.Program.Equality.

Lemma tail_neq_impl_neq : forall {A : Type} `{H : EqClass A} {n : nat} 
  (v1 v2 : @Vector A n) (h1 h2 : A),
  v1 <> v2 ->
  h1 <:: v1 <> h2 <:: v2.
Proof.
  induction v1; dependent destruction v2; intros; simpl in *; eauto.
  intros HC.
  inversion HC.
  eapply (Eqdep_dec.inj_pair2_eq_dec) in H4.
  subst. congruence.
  apply nat_eq_dec'. 
Qed.

#[global]
Instance deceq_vector {A : Type} `{H : EqClass A} {n : nat} : DecEq (@Vector A n).
constructor.
induction x1; dependent destruction x2; simpl in *; eauto; destruct H.
destruct (IHx1 x2).
- (* x1 = x2 *)
  subst.
  destruct (eqb x x3) eqn:Heq.
  * (* x = x3 *)
    apply eqb_leibniz in Heq. subst. eauto.
  * (* x <> x3 *)
    apply neqb_leibniz in Heq. right.
    qcon.
- (* x1 <> x2 *)
  right. apply tail_neq_impl_neq; eauto.
Defined.

#[global]
Instance eq_class_vector {A : Type} `{H : EqClass A} {n : nat} : EqClass (@Vector A n) :=
{
  eqb := gen_deceq_eqb ;
  eqb_leibniz := gen_eqb_impl_eqb_leibniz ;
  neqb_leibniz := gen_eqb_impl_neqb_leibniz ;
}. 

End VectorTypeClass.