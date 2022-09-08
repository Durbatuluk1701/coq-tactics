Require Import List Lia.
Require Import TypeClasses Ltacs Vector.
Import VectorNotations.
Import ListNotations.
(*
Formallizing a matrix so that we can use them for operations
*)

(* 
  At its most fundamental level, a matrix is a list of lists.

  We want every list within the top-level list to be the same length.

  Maybe this would be better represented using vectors?
*)

Inductive Matrix {A : Type} : nat -> nat -> Type :=
| mtMatrix  : forall (rows cols : nat), rows = 0 ->
    Matrix rows cols
| nMatrix   : forall (rows cols : nat) {rows' : nat} 
      (curRow : (@Vector A cols)),
    S rows' = rows ->
    Matrix rows' cols ->
    Matrix rows cols.

Definition mat_num_rows {A : Type} {rows cols : nat} (m : (@Matrix A rows cols)) :=
  rows.

Definition mat_num_cols {A : Type} {rows cols : nat} (m : (@Matrix A rows cols)) :=
  cols.

(** Testing Matrix Row/Cols
    - We want the establishment of matrices to have n = rows, m = cols
      so that they can be specified using a row by columns idea
*)
Definition tMat1 := nMatrix 2 3 (<[ 1 ; 2; 3]) eq_refl (nMatrix 1 3 (<[4;5;6]) eq_refl (mtMatrix 0 3 eq_refl)).
Example testTmat1_rows : mat_num_rows tMat1 = 2. reflexivity. Defined.
Example testTmat1_cols : mat_num_cols tMat1 = 3. reflexivity. Defined.

Fixpoint matrix_get_value_row {A : Type} {rows cols : nat} (mat : @Matrix A rows cols)
        (rowIndex : nat) : option (@Vector A _) :=
  match rowIndex with
  | 0 => 
      match mat with
      | mtMatrix _ _ _ => None
      | nMatrix rows' cols' curVec rowProof subMat =>
          Some curVec
      end
  | S ri' =>
      match mat with
      | mtMatrix _ _ _ => None
      | nMatrix rows' cols' curVec rowProof subMat =>
          matrix_get_value_row subMat ri'
      end
  end.

Definition matrix_get_value {A : Type} {rows cols : nat} (mat : @Matrix A rows cols)
        (rowInd colInd : nat) : option A :=
  match (matrix_get_value_row mat rowInd) with
  | None => None (* row index out of bounds*)
  | Some rowVec =>
      rowVec <@[colInd]
  end.

Fixpoint matrix_set_value {A : Type} {rows cols : nat} (mat : @Matrix A rows cols)
        (rowInd colInd : nat) (newV : A) {struct mat} : (@Matrix A rows cols).

destruct rowInd eqn:RI.
- (* rowInd = 0 *)
  destruct mat eqn:MAT.
  * (* mat = mtMatrix *)
    apply mat.
  * (* mat = nMatrix rows cols curRow e m *)
    apply (nMatrix rows cols (curRow set<@[colInd] <- newV) e m).
    (* updating the row since we are at it (rowInd = 0 )*)
- (* rowInd = S n *)
  destruct mat eqn:MAT.
  * (* mat = mtMatrix *)
    apply mat.
  * (* mat = nMatrix rows cols curRow e m *)
    apply (nMatrix rows cols curRow e (matrix_set_value _ _ _ m n colInd newV)).
    (* recursive case, keep moving down rows *)
Defined.

(** Testing Matrix Get/Set
    - Want intuitive get/set functions
*)
Definition inVec := (<[ <[ 0 ; 1] ; <[ 2; 3] ; <[ 4; 5]]).
Definition tMat2 := nMatrix 3 2 (<[ 0 ; 1]) eq_refl (nMatrix 2 2 (<[ 2 ; 3]) eq_refl
  (nMatrix 1 2 (<[ 4 ; 5]) eq_refl (mtMatrix 0 2 eq_refl))).
(* Testing gets *)
Example testTmat2_get1 : matrix_get_value tMat2 0 0 = Some 0. reflexivity. Defined.
Example testTmat2_get2 : matrix_get_value tMat2 0 1 = Some 1. reflexivity. Defined.
Example testTmat2_get3 : matrix_get_value tMat2 1 0 = Some 2. reflexivity. Defined.
Example testTmat2_get4 : matrix_get_value tMat2 1 1 = Some 3. reflexivity. Defined.
Example testTmat2_get5 : matrix_get_value tMat2 2 0 = Some 4. reflexivity. Defined.
Example testTmat2_get6 : matrix_get_value tMat2 2 1 = Some 5. reflexivity. Defined.
(* Testing sets *)
Example testTmat2_set1 : matrix_set_value tMat2 0 0 42 = 
  nMatrix 3 2 (<[ 42 ; 1]) eq_refl (
    nMatrix 2 2 (<[ 2 ; 3]) eq_refl (
      nMatrix 1 2 (<[ 4 ; 5]) eq_refl (
        mtMatrix 0 2 eq_refl
      )
    )
  ). reflexivity. Defined.
Example testTmat2_set2 : matrix_set_value tMat2 0 1 42 = 
    nMatrix 3 2 (<[ 0 ; 42]) eq_refl (
    nMatrix 2 2 (<[ 2 ; 3]) eq_refl (
      nMatrix 1 2 (<[ 4 ; 5]) eq_refl (
        mtMatrix 0 2 eq_refl
      )
    )
  ). reflexivity. Defined.
Example testTmat2_set3 : matrix_set_value tMat2 1 0 42 = 
    nMatrix 3 2 (<[ 0 ; 1]) eq_refl (
    nMatrix 2 2 (<[ 42 ; 3]) eq_refl (
      nMatrix 1 2 (<[ 4 ; 5]) eq_refl (
        mtMatrix 0 2 eq_refl
      )
    )
    ). reflexivity. Defined.
Example testTmat2_set4 : matrix_set_value tMat2 1 1 42 = 
    nMatrix 3 2 (<[ 0 ; 1]) eq_refl (
    nMatrix 2 2 (<[ 2 ; 42]) eq_refl (
      nMatrix 1 2 (<[ 4 ; 5]) eq_refl (
        mtMatrix 0 2 eq_refl
      )
    )
  ). reflexivity. Defined.
Example testTmat2_set5 : matrix_set_value tMat2 2 0 42 = 
    nMatrix 3 2 (<[ 0 ; 1]) eq_refl (
    nMatrix 2 2 (<[ 2 ; 3]) eq_refl (
      nMatrix 1 2 (<[ 42 ; 5]) eq_refl (
        mtMatrix 0 2 eq_refl
      )
    )
  ). reflexivity. Defined.
Example testTmat2_set6 : matrix_set_value tMat2 2 1 42 = 
    nMatrix 3 2 (<[ 0 ; 1]) eq_refl (
    nMatrix 2 2 (<[ 2 ; 3]) eq_refl (
      nMatrix 1 2 (<[ 4 ; 42]) eq_refl (
        mtMatrix 0 2 eq_refl
      )
    )
  ). reflexivity. Defined.
  
Fixpoint default_matrix {A : Type} `{H : Defaultable A} (n : nat) (m : nat) : (@Matrix A n m).
destruct n.
- (* n = 0 (rows) *)
  apply (@mtMatrix A 0 m eq_refl).
- (* need Matrix (S n) m *)
  pose proof (default_matrix A H n m).
  pose proof (defaultable_vector m) as curRow.
  destruct curRow.
  apply (nMatrix (S n) m defVal eq_refl X).
Defined.

#[global]
Instance defaultable_matrix {A : Type} `{H : Defaultable A} (n : nat) (m : nat) : Defaultable (@Matrix A n m) :=
{
  defVal := default_matrix n m
}.

Fixpoint vec_of_vecs_to_matrix {A : Type} {rows cols : nat} 
    (vVec : (@Vector (@Vector A cols) rows)) : (@Matrix A rows cols).
destruct vVec eqn:VEC.
- (* vVec = <[] *)
  apply (mtMatrix 0 cols eq_refl).
- (* vVec = x <:: v *) 
  pose proof (vec_of_vecs_to_matrix A n cols v).
  apply (nMatrix (S n) cols x eq_refl X).
Defined.

Module MatrixNotations.
Declare Scope matrix_scope.
(* For constructing matrices from the vector vector more easily *)
Notation "'MAT' v" := (vec_of_vecs_to_matrix v) (at level 50) : matrix_scope.
(* For lookup *)
Notation "m @[ x ][ y ]" := (matrix_get_value m x y) (at level 70, right associativity) : matrix_scope.
(* For setting values *)
Notation "m set@[ x ][ y ] <- v" := (matrix_set_value m x y v) (at level 75, right associativity) :
matrix_scope.
Open Scope matrix_scope.
End MatrixNotations.

Import MatrixNotations.
Definition exampleMatrix : (@Matrix nat 2 2) :=
  (nMatrix 2 2 (<[ 1 ; 2 ]) eq_refl (nMatrix 1 2 (<[ 3; 4]) eq_refl (mtMatrix 0 2 eq_refl))).

Example em1test1 : (exampleMatrix @[1][1]) = Some 4. reflexivity. Defined.
Example em1test2 : (exampleMatrix @[0][1]) = Some 2. reflexivity. Defined.
Example vecGetTest : ((<[ 1 ; 2 ; 3]) <@[2]) = Some 3. reflexivity. Defined.
Example em1setTest : (exampleMatrix set@[1][1] <- 42) = (nMatrix 2 2 (<[ 1 ; 2 ]) eq_refl (nMatrix 1 2 (<[ 3; 42]) eq_refl (mtMatrix 0 2 eq_refl))). reflexivity. Defined.
Example defMatrices : ((@defaultable_matrix nat _ 3 3).(defVal))
  = (nMatrix 3 3 (<[ 0 ; 0 ; 0 ]) eq_refl (nMatrix 2 3 (<[ 0 ; 0 ; 0]) eq_refl (nMatrix 1 3 (<[ 0 ; 0 ;0 ]) eq_refl (mtMatrix 0 3 eq_refl)))). reflexivity. Defined.
(** Testing Matrix Notation
    - We want the matrix notation to make sense and be easy to use
*)
Definition tMat3 := (MAT <[ <[ 1 ; 2 ; 3] ; <[ 4 ; 5 ; 6] ; <[ 7 ; 8; 9]]).
(* Testing getters *)
Example testTmat3_get1 : tMat3 @[0][0] = Some 1. reflexivity. Defined.
Example testTmat3_get2 : tMat3 @[1][1] = Some 5. reflexivity. Defined.
Example testTmat3_get3 : tMat3 @[2][2] = Some 9. reflexivity. Defined.
Example testTmat3_get4 : tMat3 @[0][2] = Some 3. reflexivity. Defined.
Example testTmat3_get5 : tMat3 @[2][0] = Some 7. reflexivity. Defined.
(* Testing setters *)
Example testTmat3_set1 : (tMat3 set@[0][0] <- 42) =
(MAT <[ <[ 42 ; 2 ; 3] ; <[ 4 ; 5 ; 6] ; <[ 7 ; 8; 9]]). reflexivity. Defined.
Example testTmat3_set2 : (tMat3 set@[1][1] <- 42) =
(MAT <[ <[ 1 ; 2 ; 3] ; <[ 4 ; 42 ; 6] ; <[ 7 ; 8; 9]]). reflexivity. Defined.
Example testTmat3_set3 : (tMat3 set@[2][2] <- 42) =
(MAT <[ <[ 1 ; 2 ; 3] ; <[ 4 ; 5 ; 6] ; <[ 7 ; 8; 42]]). reflexivity. Defined.
Example testTmat3_set4 : (tMat3 set@[0][2] <- 42) =
(MAT <[ <[ 1 ; 2 ; 42] ; <[ 4 ; 5 ; 6] ; <[ 7 ; 8; 9]]). reflexivity. Defined.
Example testTmat3_set5 : (tMat3 set@[2][0] <- 42) =
(MAT <[ <[ 1 ; 2 ; 3] ; <[ 4 ; 5 ; 6] ; <[ 42 ; 8; 9]]). reflexivity. Defined.

Fixpoint eqb_matrix {A : Type} `{H : EqClass A} 
    {rows1 cols1 rows2 cols2: nat}
    (m1 : (@Matrix A rows1 cols1)) 
    (m2 : (@Matrix A rows2 cols2)): bool :=
  match m1, m2 with
  | mtMatrix r1 c1 _, mtMatrix r2 c2 _ =>
      if (andb (eqb r1 r2) (eqb c1 c2))
      then (* if number of rows and cols eq *)
          true
      else false
  | nMatrix r1 c1 curR1 pf1 subM1, nMatrix r2 c2 curR2 pf2 subM2 =>
      if (andb (eqb r1 r2) (andb (eqb c1 c2) (eqb_vector curR1 curR2)))
      then (* rows, cols, and current row eq *)
          eqb_matrix subM1 subM2
      else false
  | _, _ => false
  end.

Example eqb_matrix_test1 :
eqb_matrix (MAT <[ <[ 1 ; 2] ; <[ 3 ; 4]]) (MAT <[ <[ 1; 2] ; <[3;4]]) = true. reflexivity. Defined.

Lemma eqb_matrix_refl : forall {A : Type} `{H : EqClass A} {n m : nat}
  (mat : (@Matrix A n m)),
  eqb_matrix mat mat = true.
Proof.
  induction mat; simpl; repeat (rewrite gen_deceq_eqb_refl); eauto.
  simpl. rewrite eqb_vector_refl. auto.
Qed.

Theorem eqb_matrix_same_length : forall {A : Type} {rows1 rows2 cols1 cols2 : nat} 
  `{H : EqClass A}
  (m1 : (@Matrix A rows1 cols1)) (m2 : (@Matrix A rows2 cols2)),
    eqb_matrix m1 m2 = true ->
    rows1 = rows2 /\ cols1 = cols2.
Proof.
  induction m1; destruct m2; intros; inversion H0.
  - destruct (gen_deceq_eqb rows rows0) eqn:Req;
    destruct (gen_deceq_eqb cols cols0) eqn:Ceq; 
    simpl in *; try congruence.
    apply gen_eqb_impl_eqb_leibniz in Req.
    apply gen_eqb_impl_eqb_leibniz in Ceq; eauto.
  - destruct (gen_deceq_eqb rows rows0) eqn:Req;
    destruct (gen_deceq_eqb cols cols0) eqn:Ceq; 
    simpl in *; try congruence.
    apply gen_eqb_impl_eqb_leibniz in Req.
    apply gen_eqb_impl_eqb_leibniz in Ceq; eauto.
Qed.

Theorem eqb_matrix_works : forall {A : Type} `{H : EqClass A} {rows cols : nat}
  (m1 m2 : @Matrix A rows cols),
  eqb_matrix m1 m2 = true ->
  (forall (i j : nat),
    (m1 @[i][j]) = (m2 @[i][j])).
Proof.
  induction m1; destruct m2; eauto; intros; try inversion H0.
  unfold matrix_get_value.
  assert (gen_deceq_eqb rows rows = true). apply gen_eqb_impl_eqb_leibniz; auto.
  assert (gen_deceq_eqb cols cols = true). apply gen_eqb_impl_eqb_leibniz; auto.
  rewrite H1, H3 in *. simpl in H2.
  destruct (eqb_vector curRow curRow0) eqn:EQvec.
  - (* eqb_matrix m1 m2 = true *)
    assert (rows' = rows'0). lia. subst.
    pose proof (IHm1 m2 H2).
    unfold matrix_get_value in H4.
    destruct i.
    * (* i = 0 *)
      simpl. eapply eqb_vector_works. eauto.
    * (* i = S i *) 
      simpl. eauto.
  - congruence.
Qed.

Module MatrixTypeClass.

(** UIP is needed here because the proofs embedded in each matrix
    are unable to be proven equal without it. 
    This is a safe assumption to make here as eq_refl on nats will
    have unique identity proofs and should be considered roughly
    proof irrelevant
*)
Axiom uip : forall A (x y : A) (p q : x = y), p = q.

#[global]
Instance deceq_matrix {A : Type} `{H : EqClass A} {n m : nat} : DecEq (@Matrix A n m).
constructor.
induction x1; destruct x2; simpl in *.
- assert (e = e0). apply uip. subst. eauto.
- right. qcon.
- right. qcon.
- destruct (eqb curRow curRow0) eqn:Eqvec.
  * (* vecs eq *)
    rewrite eqb_leibniz in Eqvec. subst.
    assert (rows' = rows'0). lia. subst.
    specialize IHx1 with x2.
    destruct IHx1.
    ** (* rest eq *)
      subst. left.
      assert (eq_refl = e0). eapply uip.
      subst. eauto.
    ** (* rest neq *) 
      right. qcon. 
      exT H1. exT H1. congruence.
  * (* vecs neq *)
    rewrite neqb_leibniz in Eqvec.
    right. qcon. exT H2.
    congruence.
Defined.

#[global]
Instance eq_class_matrix {A : Type} `{H : EqClass A} {n m : nat} : EqClass (@Matrix A n m) :=
{
  eqb := gen_deceq_eqb ;
  eqb_leibniz := gen_eqb_impl_eqb_leibniz ;
  neqb_leibniz := gen_eqb_impl_neqb_leibniz ;
}.

End MatrixTypeClass.


Fixpoint matrix_entries {A : Type} {r c : nat} (m : @Matrix A r c) : list A :=
  match m with
  | mtMatrix _ _ _ => nil
  | nMatrix rows cols curRow rPrf subMat =>
      vec_to_list curRow ++ matrix_entries subMat
  end.

Example m_ent_1 : (matrix_entries (MAT <[ <[ 1;2] ; <[3;4]])) = [1;2;3;4].
reflexivity. Defined.

Example m_ent_2 : (matrix_entries (MAT <[ <[ 41;42;40] ; <[40;41;42]])) = [41;42;40;40;41;42].
reflexivity. Defined.

Lemma in_app_impl_or_in : forall {A : Type} (l1 l2 : list A) x,
  In x (l1 ++ l2) ->
  In x l1 \/ In x l2.
Proof.
  induction l1; smp; eauto; intros.
  dest H; eauto.
  eapply IHl1 in H. dest H; eauto.
Qed.
(* 
Lemma matrix_column_height_change_get : forall {A : Type} {r c : nat}
  (m : @Matrix A r c) curRow ent x,
  forall (i j : nat), (nMatrix (S r) c curRow eq_refl m @[i][j] = Some ent) ->
    exists (i j : nat), (nMatrix (S r) (S c) (x <:: curRow) eq_refl m @[i][j] = Some ent). *)

Lemma in_impl_exists'' : forall {A : Type} {c : nat} (curRow : @Vector A c) ent,
  In ent (vec_to_list curRow) ->
  (exists (j : nat), 
    curRow <@[j] = Some ent).
Proof.
  induction curRow; intros; smp; eauto.
  - inv H.
  - dest H; subst.
    * exists 0. refl.
    * eapply IHcurRow in H. dest H. 
      exists (S x0); eauto.
Qed. 

Lemma in_impl_exists' : forall {A : Type} {r c : nat} (curRow : @Vector A c) (m : @Matrix A r c) ent,
  In ent (vec_to_list curRow) ->
  exists (i j : nat), (nMatrix (S r) c curRow eq_refl m @[i][j] = Some ent).
Proof.
  induction curRow; intros; eauto.
  - inv H.
  - inv H; subst.
    * exists 0, 0. refl.
    * exists 0. unfold matrix_get_value. smp.
      pose proof (@in_impl_exists'' _ _ _ _ H0).
      dest H1. exists (S x0). eauto.
Qed.

Lemma in_impl_exists : forall {A : Type} {r c : nat} (m : @Matrix A r c) ent,
  In ent (matrix_entries m) ->
  exists (i j : nat), (m @[i][j] = Some ent).
Proof.
  induction m; intros; smp; eauto.
  - inv H.
  - apply in_app_impl_or_in in H. dest H.
    * (* in curRow *) 
      dest (curRow); smp.
      ** inv H.
      ** eapply in_impl_exists'. eauto.
    * eapply IHm in H. dest H. dest H.
      exists (S x). exists x0. 
      unfold matrix_get_value; smp. eauto.
Qed.

Lemma all_matrix_entries_in_matrix : forall {A : Type} {r c : nat} (m : @Matrix A r c) lm,
  matrix_entries m = lm ->
  (forall ent, In ent lm ->
      exists (i j : nat), m @[i][j] = Some ent).
Proof.
  intros. rewrite <- H in *.
  eapply in_impl_exists. eauto.
Qed.