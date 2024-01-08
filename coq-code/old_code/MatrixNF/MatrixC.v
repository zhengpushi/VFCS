(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Complex.
  author    : ZhengPu Shi
  date      : 2023.04
 *)

Require Export Complex.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryC :=
  DecidableFieldMatrixTheory DecidableFieldElementTypeC.

Open Scope C_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)

Section test.

  Let l1 := [[1 +i 2; 3 +i 4];[5 +i 6; 7 +i 8]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Copp m1). *)
  (* Compute m2l (m1 * m1). *)

  Variable a11 a12 a21 a22 : T.
  Variable f : T -> T.
  Let m2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.     (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  (* Compute m2l (m2 * m2). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

  (** Outer/inner product of two vectors *)
  Variables a1 a2 a3 b1 b2 b3 : T.
  Let m10 := @l2m 3 1 [[a1];[a2];[a3]].
  Let m11 := @l2m 1 3 [[b1;b2;b3]].
  (* Compute m2l (m10 * m11). *)
  (* Compute m2l (m11 * m10). *)

  (** mmul_sub_distr_r *)
  Goal forall r c s (m1 m2 : mat r c) (m3 : mat c s), (m1 - m2) * m3 == m1 * m3 - m2 * m3.
    intros. rewrite mmul_msub_distr_r. easy. Qed.

  (* test rewriting *)
  Goal forall r c (m1 m2 : mat r c) x, m1 == m2 -> x c* m1 == x c* m2.
  Proof. intros. f_equiv. easy. Qed.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 == m2 -> m3 == m4 -> m1 - m3 == m2 - m4.
  Proof. clear. intros. f_equiv. easy. easy. Qed.

End test.

Section test_monoid.
  Goal forall r c (m1 m2 : mat r c), mat0 + m1 == m1.
    monoid_simp. Qed.
End test_monoid.

