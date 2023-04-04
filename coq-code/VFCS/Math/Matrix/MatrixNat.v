(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix on nat.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export NatExt.
Require Export Matrix.


(* ======================================================================= *)
(** ** Matrix theory come from common implementations *)

Open Scope nat_scope.
Open Scope mat_scope.

(** general notations *)
Notation dlist := (dlist nat).

(** *** matrix type and basic operation *)
Definition mat (r c : nat) : Type := @mat nat r c.

Notation "m ! i ! j " := (mnth 0 m i j) : mat_scope.

(** *** convert between list and matrix *)
Definition l2m (r c : nat) (dl : dlist) : mat r c := l2m 0 dl.
Definition m2l {r c : nat} (m : mat r c) : dlist := m2l m.

Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
Proof. intros. apply m2l_length. Qed.

Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
Proof. intros. apply m2l_width. Qed.

Lemma m2l_l2m_id : forall {r c} (dl : dlist),
    length dl = r -> width dl c -> m2l (l2m r c dl) = dl.
Proof. intros. apply m2l_l2m_id; auto. Qed.

Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m r c (m2l m) == m.
Proof. intros. apply l2m_m2l_id; auto. Qed.

Lemma l2m_inj : forall {r c} (d1 d2 : dlist),
    length d1 = r -> width d1 c -> length d2 = r -> width d2 c -> 
    d1 <> d2 -> ~(l2m r c d1 == l2m r c d2).
Proof. intros. apply l2m_inj; auto. Qed.

Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m r c d == m). 
Proof. intros. apply l2m_surj; auto. Qed.

Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~ (m1 == m2) -> m2l m1 <> m2l m2.
Proof. intros. apply (m2l_inj 0); auto. Qed.

Lemma m2l_surj : forall {r c} (d : dlist), length d = r -> width d c -> 
    (exists m : mat r c, m2l m = d).
Proof. intros. apply (m2l_surj 0); auto. Qed.

(** *** convert between tuple and matrix *)
Definition t2m_3_3 (t : T_3_3) : mat 3 3 := t2m_3_3 0 t.
Definition m2t_3_3 (m : mat 3 3) : T_3_3 := m2t_3_3 m.
Definition m2t_1_1 (m : mat 1 1) := m2t_1_1 m.

(** *** build matrix from elements *)
Definition mk_mat_1_1 a11 : mat 1 1 :=
  mk_mat_1_1 (A0:=0) a11.
Definition mk_mat_3_1 a11 a12 a13 : mat 3 1 :=
  mk_mat_3_1 (A0:=0) a11 a12 a13.
Definition mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
  mk_mat_3_3 (A0:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

(** *** matrix transposition *)
Definition mtrans {r c : nat} (m : mat r c) : mat c r := mtrans m.
Notation "m \T" := (mtrans m) : mat_scope.

Lemma mtrans_trans : forall {r c} (m : mat r c), m \T\T == m.
Proof. intros. apply mtrans_trans. Qed.

(** *** matrix mapping *)
Definition mmap {r c} f (m : mat r c) : mat r c := mmap f m.
Definition mmap2 {r c} f (m1 m2 : mat r c) : mat r c := mmap2 f m1 m2.

Lemma mmap2_comm : forall {r c} (m1 m2 : mat r c) f (fcomm : Commutative f),
    mmap2 f m1 m2 == mmap2 f m2 m1.
Proof. intros. apply mmap2_comm; auto. Qed.

Lemma mmap2_assoc : forall {r c} f (m1 m2 m3 : mat r c) (fassoc : Associative f),
    mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
Proof. intros. apply mmap2_assoc; auto. Qed.


(* ======================================================================= *)
(** ** Matrix theory applied to this type *)


(* ======================================================================= *)
(** ** Usage demo *)
Section test.
  Let m1 := l2m 2 2 [[1;2];[3;4]].
  (* Compute m2l m1.       (* = [[1; 2]; [3; 4]] *) *)
  (* Compute m2l (mmap S m1).       (* = [[2; 3]; [4; 5]] *) *)

  Variable a11 a12 a21 a22 : nat.
  Let m2 := l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.       (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap S m2).     (* = [[S a11; S a12]; [S a21; S a22]] *) *)
  
End test.
