Require Import TypeClasses Ltacs.
Require Import List.
Import ListNotations.

Definition Map (A:Type) (B:Type) `{H : EqClass A} := list (A * B).

Definition map_empty{A B:Type} `{H : EqClass A} : Map A B := [].

Fixpoint map_get{A B:Type} `{H : EqClass A} (m : Map A B ) x : option B :=
  match m with
  | [] => None
  | (k, v) :: m' => if eqb x k then Some v else map_get m' x
  end.

Definition map_set{A B:Type} `{H : EqClass A} (m:Map A B) (x:A) (v:B) : Map A B := (x, v) :: m.

Fixpoint map_vals{A B:Type} `{H : EqClass A} (m : Map A B ) : list B :=
  match m with
  | [] => []
  | (k', v) :: m' => v :: map_vals m'
  end.

(* A two-way implementation of list maps, where you can lookup from a key, or value *)
Definition BiMap (A:Type) (B:Type) `{H : EqClass A} `{H1 : EqClass B} := list (A * B).

Definition bimap_empty{A B:Type} `{H : EqClass A} `{H1 : EqClass B} : BiMap A B := [].

Fixpoint bimap_get_value{A B:Type} `{H : EqClass A} `{H1 : EqClass B} (m : BiMap A B ) x : option B :=
  match m with
  | [] => None
  | (k, v) :: m' => if eqb x k then Some v else bimap_get_value m' x
  end.
  
Fixpoint bimap_get_key{A B:Type} `{H : EqClass A} `{H1 : EqClass B} 
          (m : BiMap A B ) (v : B) : option A :=
  match m with
  | [] => None
  | (k, v') :: m' => if eqb v v' then Some k else bimap_get_key m' v
  end.

Definition bimap_set{A B:Type} `{H : EqClass A} `{H1 : EqClass B} 
                    (m:BiMap A B) (x:A) (v:B) : BiMap A B := (x, v) :: m.

Fixpoint bimap_vals{A B:Type} `{H : EqClass A} `{H1 : EqClass B} (m : BiMap A B ) : list B :=
  match m with
  | [] => []
  | (k', v) :: m' => v :: bimap_vals m'
  end.

Fixpoint bimap_keys{A B : Type} `{H : EqClass A} `{H1 : EqClass B} (m : BiMap A B) : list A :=
  match m with
  | nil => nil
  | (k',v') :: m' => k' :: bimap_keys m'
  end.

Module MapNotations.
Declare Scope mapc_scope.
Delimit Scope mapc_scope with mapc.
Notation "{}" := (map_empty) : mapc_scope.
Notation "k '!->' v ; m" := (map_set m k v) (at level 70, right associativity): mapc_scope.
Notation "m ![ k ]" := (map_get m k) (at level 70) : mapc_scope.
Declare Scope mapd_scope.
Delimit Scope mapd_scope with mapd.
Notation "bi{}" := (bimap_empty) : mapd_scope.
Notation "k 'bi!->' v ; m" := (bimap_set m k v) (at level 70, right associativity): mapd_scope.
Notation "m bik![ k ]" := (bimap_get_value m k) (at level 70) : mapd_scope.
Notation "m biv![ v ]" := (bimap_get_key m v) (at level 70) : mapd_scope.
Open Scope mapc_scope.
Open Scope mapd_scope.
(* Little test examples *)
Example m1 := (0 !-> 100 ; 1 !-> 200 ; {}).
Example m1test : (m1 ![0]) = Some 100. reflexivity. Defined.
Example m1test2 : (m1 ![3]) = None. reflexivity. Defined.
Example dm1 := (0 bi!-> 20 ; 2 bi!-> 50 ; 3 bi!-> 40 ; bi{}).

Example dm1test1 : (dm1 bik![0]) = Some 20. reflexivity. Defined.
Example dm1test2 : (dm1 biv![50]) = Some 2. reflexivity. Defined.
Example dm1test3 : (dm1 biv![0]) = None. (* not a value *) reflexivity. Defined.
End MapNotations.

Lemma bimap_key_values_length : forall (T1 T2 : Type) `{ECT1 : EqClass T1} `{ECT2 : EqClass T2} 
    (m : BiMap T1 T2),
  length (bimap_vals m) = length (bimap_keys m).
Proof.
  intros.
  ind m; smp.
  - refl.
  - dest a. smp. rewrite IHm. refl.
Qed.

Theorem bimap_kv_len_match: forall (T1 T2 : Type) `{ECT1 : EqClass T1} `{ECT2 : EqClass T2}
    (m : BiMap T1 T2),
  length (bimap_vals m) = length m.
Proof.
  intros.
  ind m; smp.
  - refl.
  - dest a; smp; rewrite IHm; refl.
Qed.

Theorem bimap_get_works : forall (T1 T2 : Type) `{ECT1 : EqClass T1} `{ECT2 : EqClass T2} 
    (m : BiMap T1 T2) (x : T1) (v : T2),
  bimap_get_key (bimap_set m x v) v = Some x.
Proof with eauto.
  intros.
  ind m; smp;
  assert (eqb v v = true) by (eapply ECT2; refl);
  rewrite H...
Qed.
