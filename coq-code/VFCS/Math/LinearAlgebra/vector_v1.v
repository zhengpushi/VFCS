(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Spaces
  author    : ZhengPu Shi
  date      : 2023.03

  reference :
  1. Handbook of Linear Algebra, Leslie Hogben
  
  remark    :
  1. do not use matrix theory in CoqMatrix, a fresh implementation.

 *)

Require Qcanon.
Require Import List. Import ListNotations.
Require Import AlgebraStructure.
Require Import Complex.



(** * Preliminaries *)

(** A field *)
Record field {A:Type} := {
    F0 : A;
    F1 : A;
    Fadd : A -> A -> A;
    Fopp : A -> A;
    Fmul : A -> A -> A;
    Finv : A -> A;
    Fadd_comm : forall a b : A, Fadd a b = Fadd b a;
    Fmul_comm : forall a b : A, Fmul a b = Fmul b a;
    Fadd_assoc : forall a b c : A, Fadd (Fadd a b) c = Fadd a (Fadd b c);
    Fmul_assoc : forall a b c : A, Fmul (Fmul a b) c = Fmul a (Fmul b c);
    Fadd_id_l : forall a : A, Fadd F0 a = a;
    Fmul_id_l : forall a : A, Fmul F1 a = a;
    Fadd_inv_l : forall a : A, Fadd (Fopp a) a = F0;
    Fmul_inv_l : forall a : A, a <> F0 -> Fmul (Finv a) a = F1;
    Fdistr_l : forall a b c : A, Fmul a (Fadd b c) = Fadd (Fmul a b) (Fmul a c);
    F0_neq_F1 : F0 <> F1;
  }.

Definition Fsub {A} (f : @field A) := (fun a b => (Fadd f) a (Fopp f b)).
Definition Fdiv {A} (f : @field A) := (fun a b => (Fmul f) a (Finv f b)).

Definition field_to_field_theory {A} (f : @field A) :
  field_theory (F0 f) (F1 f) (Fadd f) (Fmul f) (Fsub f) (Fopp f)
    (Fdiv f) (Finv f) eq.
  constructor; auto.
  - constructor; intros; try (destruct f; easy).
    + rewrite Fmul_comm. rewrite Fdistr_l. f_equal; apply Fmul_comm.
    + rewrite Fadd_comm. rewrite Fadd_inv_l. auto.
  - apply not_eq_sym. apply F0_neq_F1.
  - intros. apply Fmul_inv_l. auto.
Qed.

(** Abstract field *)
Section test.
  Variable A : Type.
  Variable f : @field A.
  Add Field f_inst : (field_to_field_theory f).
  Goal forall a b : A, Fadd f a b = Fadd f b a. intros. field. Qed.
End test.

(** Concrete field *)
Import Qcanon.
Open Scope Qc_scope.
Definition fieldQc : @field Qc.
  refine (Build_field Qc 0 1 Qcplus Qcopp Qcmult Qcinv _ _ _ _ _ _ _ _ _ _); intros;
    try field; auto.
  apply not_eq_sym. apply Q_apart_0_1.
Defined.

Section test.
  Goal forall a b : Qc, a + b = b + a. intros. field. Qed.
End test.

Import Reals.
Open Scope R_scope.
Definition fieldR : @field R.
  refine (Build_field R 0 1 Rplus Ropp Rmult Rinv _ _ _ _ _ _ _ _ _ _); intros;
    try field; auto.
Defined.

Import Complex.
Open Scope C_scope.
Definition fieldC : @field C.
  refine (Build_field C 0 1 Cadd Copp Cmul Cinv _ _ _ _ _ _ _ _ _ _); intros;
    try field; auto.
  apply not_eq_sym. apply C1_neq_C0.
Defined.


(** * 1.1 Vector Spaces *)

(** ** Definitions *)

(** vector *)
Section vector.
  Context {A : Type} {f : @field A}.
  Inductive vector (n : nat) : Type :=
    mk_vec (f : nat -> A).

  (** get function of a vector *)
  Definition vecf {n} (v : vector n) : nat -> A :=
    let '(mk_vec _ f) := v in f.

  Definition vec_add {n} (x y : vector n) : vector n :=
    mk_vec _ (fun i => Fadd f (vecf x i) (vecf y i)).

  Definition vec_scal {n} (c : A) (x : vector n) : vector n :=
    mk_vec _ (fun i => Fmul f c (vecf x i)).

  Definition vec_ith {n} (x : vector n) (i : nat) :=
    if leb i n then vecf x i else F0 f.

  Definition l2v n (l : list A) : vector n :=
    mk_vec _ (fun i => nth i l (F0 f)).

  Definition v2l n (x : vector n) : list A :=
    map (fun i => vecf x i) (seq 0 n).

End vector.

Arguments mk_vec {A n}.


(** vector space *)
Record vector_space {A} {f : @field A} (n : nat) := {
    VS0 : @vector A n;
    (* this operation implys a property: closure under addition *)
    VSadd : @vector A n -> @vector A n -> @vector A n;
    (* this operation implys a property: closure under scalar multiplication *)
    VSscal : A -> @vector A n -> @vector A n;
    VSopp : @vector A n -> @vector A n;
    VSadd_comm : forall x y, VSadd x y = VSadd y x;
    VSadd_assoc : forall x y z, VSadd (VSadd x y) z = VSadd x (VSadd y z);
    VSscal_assoc : forall a b x, VSscal (Fmul f a b) x = VSscal a (VSscal b x);
    VSadd_id_l : forall x, VSadd VS0 x = x;
    VSadd_inv_l : forall x, VSadd (VSopp x) x = VS0;
    VSdistr_l : forall a x y, VSscal a (VSadd x y) = VSadd (VSscal a x) (VSscal a y);
    VSdistr_r : forall a b x, VSscal (Fadd f a b) x = VSadd (VSscal a x) (VSscal b x);
    VSscal_id_l : forall x, VSscal (F1 f) x = x
  }.

(** real/complex vector space *)
Definition real_vector_space (n : nat) := vector_space (f:=fieldR) n.
Definition complex_vector_space (n : nat) := vector_space (f:=fieldC) n.


(** n-tuples *)
Section ntuples.
  Context {A} {f : @field A}.
  Definition ntuples (n : nat) := @vector A n.

  Definition ntuples_add {n} (x y : ntuples n) : ntuples n :=
    @vec_add A f n x y.

  (** coordinate *)
  Definition ntuples_coordinate {n} (x : ntuples n) (i : nat) : A :=
    @vec_ith A f n x i.
  
End ntuples.


(** subspace *)


(** ** Facts *)

(** ** Examples *)

Section examples.

  Open Scope R_scope.
  (* Let ex1_x := *)

End examples.

