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
| nMatrix   : forall (rows cols : nat) {rows' : nat} (curRow : (@Vector A cols)),
    S rows' = rows ->
    Matrix rows' cols ->
    Matrix rows cols.

Definition mat_num_rows {A : Type} {rows cols : nat} (m : (@Matrix A rows cols)) :=
  rows.

Definition mat_num_cols {A : Type} {rows cols : nat} (m : (@Matrix A rows cols)) :=
  cols.

Require Import Program Arith.
(** Testing Matrix Row/Cols
    - We want the establishment of matrices to have n = rows, m = cols
      so that they can be specified using a row by columns idea
*)
Compute nMatrix.
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
(* 

destruct rowInd eqn:RI.

- (* rowInd = 0 *) 
  (* if the row index is 0, then we have reached where we are done *)
  remember mat as mat'.
  induction mat.
  * (* rows = 0, so mat = mtMatrix *)
    (* we have no-where we could update *)
    apply mat'.
  * (* S rows' = rows *)
    (* curRow is the correct row *)
    (* update curRow[colInd] with newV *)
    pose proof (curRow' := curRow set<@[colInd] <- newV).
    pose proof (nMatrix rows cols curRow' e mat).
    apply X.
- (* rowInd = S n *)
  remember mat as mat'.
  induction mat.
  * (* rows = 0, so mat = mtMatrix *)
    apply mat'.
  * (* S rows' = rows *)
    (* find the sub matrix *)
    pose proof (SubM := matrix_set_value A rows' cols mat rows' colInd newV).
    pose proof (nMatrix rows cols curRow e SubM).
    apply X.
Defined.   *)
(* 
Definition matrix_set_value {A : Type} {rows cols : nat} (mat : @Matrix A rows cols)
        (rowInd colInd : nat) (newV : A) : (@Matrix A rows cols) :=
  match (matrix_get_value_row mat rowInd) with
  | None => 
  match mat with
  | mtMatrix => mtMatrix
  | nMatrix n' m' vecs =>
      if (andb (Nat.leb n n') (Nat.leb m m'))
      then (
        let row := vecs <@[n] (* get row *) in
        match row with
        | None => nMatrix n' m' vecs (* Couldnt find so default *)
        | Some row' =>
            let updRowCol := row' set<@[m] <- newV in (* update at the col *)
            let updMat    := vecs set<@[n] <- updRowCol in
            nMatrix n' m' updMat
        end
      )
      else nMatrix n' m' vecs
  end. *)

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

Module MatrixNotations.
Declare Scope matrix_scope.
(* For constructing matrices from the vector vector more easily *)
Notation "'MAT' v" := (nMatrix _ _ v) (at level 50) : matrix_scope.
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
