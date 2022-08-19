Require Import List Lia.
Require Import TypeClasses Ltacs Vector.
Import ListNotations.
(*
Formallizing a matrix so that we can use them for operations
*)

(* 
  At its most fundamental level, a matrix is a list of lists.

  We want every list within the top-level list to be the same length.

  Maybe this would be better represented using vectors?
*)

Inductive Matrix {A : Type} : Type :=
| mtMatrix  : Matrix
| oneMatrix : forall (m : pos),
    @Vector (@Vector A m) 1 ->
    Matrix
| nMatrix   : forall (n m : pos),
    @Vector (@Vector A m) n -> 
    Matrix.

Theorem gen_auto_mat_less : forall n,
  n <> 0 ->
  0 < n.
Proof.
  lia.
Qed.

Definition mat_num_rows {A : Type} (m : (@Matrix A)) :=
  match m with
  | mtMatrix => 0
  | (nMatrix n m _ _ _) => n
  end.

Definition mat_num_cols {A : Type} (m : (@Matrix A)) :=
  match m with
  | mtMatrix => 0
  | (nMatrix n m _ _ _) => m
  end.

(** Testing Matrix Row/Cols
    - We want the establishment of matrices to have n = rows, m = cols
      so that they can be specified using a row by columns idea
*)
Definition tMat1 := nMatrix 2 3 _ _ (<[ <[ 1;2;3] ; <[4;5;6]]).
Example testTmat1_rows : mat_num_rows tMat1 = 2. reflexivity. Defined.
Example testTmat1_cols : mat_num_cols tMat1 = 3. reflexivity. Defined.

Definition matrix_get_value {A : Type} (mat : @Matrix A)
        (n m : nat) : option A :=
  match mat with
  | mtMatrix => None
  | nMatrix n' m' vecs =>
      if (andb (Nat.leb n n') (Nat.leb m m'))
      then (
        match (vector_get_value vecs n) with
        (* Get row first *)
        | None => None
        | Some vec' => (vector_get_value vec' m) (* get value at col *)
        end)
      else None
  end.

Definition matrix_set_value {A : Type} (mat : @Matrix A)
        (n m : nat) (newV : A) : (@Matrix A) :=
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
  end.

(** Testing Matrix Get/Set
    - Want intuitive get/set functions
*)
Definition inVec := (<[ <[ 0 ; 1] ; <[ 2; 3] ; <[ 4; 5]]).
Definition tMat2 := nMatrix 3 2 inVec.
(* Testing gets *)
Example testTmat2_get1 : matrix_get_value tMat2 0 0 = Some 0. reflexivity. Defined.
Example testTmat2_get2 : matrix_get_value tMat2 0 1 = Some 1. reflexivity. Defined.
Example testTmat2_get3 : matrix_get_value tMat2 1 0 = Some 2. reflexivity. Defined.
Example testTmat2_get4 : matrix_get_value tMat2 1 1 = Some 3. reflexivity. Defined.
Example testTmat2_get5 : matrix_get_value tMat2 2 0 = Some 4. reflexivity. Defined.
Example testTmat2_get6 : matrix_get_value tMat2 2 1 = Some 5. reflexivity. Defined.
(* Testing sets *)
Example testTmat2_set1 : matrix_set_value tMat2 0 0 42 = 
  (nMatrix 3 2 (inVec set<@[0] <- (<[ 42 ; 1]))). reflexivity. Defined.
Example testTmat2_set2 : matrix_set_value tMat2 0 1 42 = 
  (nMatrix 3 2 (inVec set<@[0] <- (<[ 0 ; 42]))). reflexivity. Defined.
Example testTmat2_set3 : matrix_set_value tMat2 1 0 42 = 
  (nMatrix 3 2 (inVec set<@[1] <- (<[ 42 ; 3]))). reflexivity. Defined.
Example testTmat2_set4 : matrix_set_value tMat2 1 1 42 = 
  (nMatrix 3 2 (inVec set<@[1] <- (<[ 2 ; 42]))). reflexivity. Defined.
Example testTmat2_set5 : matrix_set_value tMat2 2 0 42 = 
  (nMatrix 3 2 (inVec set<@[2] <- (<[ 42 ; 5]))). reflexivity. Defined.
Example testTmat2_set6 : matrix_set_value tMat2 2 1 42 = 
  (nMatrix 3 2 (inVec set<@[2] <- (<[ 4 ; 42]))). reflexivity. Defined.
  
Fixpoint default_matrix {A : Type} `{H : Defaultable A} (n : nat) (m : nat) : (@Matrix A).
pose proof (defaultable_vector m).
pose proof (@defaultable_vector _ X n).
destruct X0.
pose proof (@nMatrix A n m defVal).
apply X0.
Defined.

#[global]
Instance defaultable_matrix {A : Type} `{H : Defaultable A} (n : nat) (m : nat) : Defaultable (@Matrix A) :=
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
Definition exampleMatrix : (@Matrix nat) :=
  (@nMatrix nat 2 2) (<[ <[ 1 ; 2 ] ; <[ 3; 4]]).

Example em1test1 : (exampleMatrix @[1][1]) = Some 4. reflexivity. Defined.
Example em1test2 : (exampleMatrix @[0][1]) = Some 2. reflexivity. Defined.
Example vecGetTest : ((<[ 1 ; 2 ; 3]) <@[2]) = Some 3. reflexivity. Defined.
Example em1setTest : (exampleMatrix set@[1][1] <- 42) = MAT <[ <[ 1 ; 2] ; <[ 3 ; 42]].
reflexivity. Defined.
Example defMatrices : ((@defaultable_matrix nat _ 3 3).(defVal))
  = MAT <[ <[ 0 ; 0 ; 0 ] ; <[ 0 ; 0 ; 0] ; <[ 0; 0; 0] ].
reflexivity. Defined.
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
