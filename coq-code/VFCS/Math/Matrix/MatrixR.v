(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on R.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export RExt.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryR :=
  DecidableFieldMatrixTheory DecidableFieldElementTypeR.

Open Scope R_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)


(* ==================================== *)
(** ** Orthogonal matrix *)
Section morthogonal.

  (** orthogonal m -> |m| = ± 1 *)
  Lemma morthogonal_mdet : forall {n} (m : smat n),
      morthogonal m -> (mdet m == 1 \/ mdet m == - (1))%A.
  Proof.
    intros.
    assert (m\T * m == mat1).
    { unfold morthogonal in H. unfold Matrix.morthogonal in H. rewrite H. easy. }
    assert (mdet (m\T * m)%M == mdet (@mat1 n))%A.
    { rewrite H0. easy. }
    rewrite mdet_mmul in H1. rewrite mdet_mtrans in H1. rewrite mdet_1 in H1.
    apply Rsqr_eq1 in H1. easy.
  Qed.

End morthogonal.


(* ==================================== *)
(** ** SO(3): special orthogonal group on 3D *)

Section SO3.

  (** SO3 *)
  Definition SO3 := SOn 3.

  Variable m : SO3.

  Goal m\T == m⁻¹.
  Proof. destruct m. rewrite morthogonal_imply_inv_eq_trans; try easy. Qed.

End SO3.


(* ==================================== *)
(** ** Usage demo *)
Section test.
  Let l1 := [[1;2];[3;4]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Ropp m1). *)
  (* Compute m2l (m1 * m1). *)

  Variable a11 a12 a21 a22 : A.
  Variable f : A -> A.
  Let m2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.     (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  (* Compute m2l (m2 * m2). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

  (** Simulate Outer/inner product of two vectors *)
  Variables a1 a2 a3 b1 b2 b3 : A.
  Let m31 := @l2m 3 1 [[a1];[a2];[a3]].
  Let m13 := @l2m 1 3 [[b1;b2;b3]].
  (* Compute m2l (m31 * m13). *)
  (* Compute m2l (m13 * m31). *)

  (** mmul_sub_distr_r *)
  Goal forall r c s (m1 m2 : mat r c) (m3 : mat c s), (m1 - m2) * m3 == m1 * m3 - m2 * m3.
    intros. rewrite mmul_msub_distr_r. easy. Qed.

  (* test rewriting *)
  Goal forall r c (m1 m2 : mat r c) x, m1 == m2 -> x c* m1 == x c* m2.
  Proof. intros. f_equiv. easy. Qed.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 == m2 -> m3 == m4 -> m1 - m3 == m2 - m4.
  Proof. clear. intros. f_equiv. easy. easy. Qed.

  (* test_monoid. *)
  Goal forall r c (m1 m2 : mat r c), mat0 + m1 == m1.
    monoid_simp. Qed.
End test.


Section Example4CoordinateSystem.
  Variable ψ θ φ: R.
  Let Rx := (mk_mat_3_3 1 0 0 0 (cos φ) (sin φ) 0 (-sin φ) (cos φ))%R.
  Let Ry := (mk_mat_3_3 (cos θ) 0 (-sin θ) 0 1 0 (sin θ) 0 (cos θ))%R.
  Let Rz := (mk_mat_3_3 (cos ψ) (sin ψ) 0 (-sin ψ) (cos ψ) 0 0 0 1)%R.
  Let Rbe := (mk_mat_3_3
                (cos θ * cos ψ) (cos ψ * sin θ * sin φ - sin ψ * cos φ)
                (cos ψ * sin θ * cos φ + sin φ * sin ψ) (cos θ * sin ψ)
                (sin ψ * sin θ * sin φ + cos ψ * cos φ)
                (sin ψ * sin θ * cos φ - cos ψ * sin φ)
                (-sin θ) (sin φ * cos θ) (cos φ * cos θ))%R.
  Lemma Rbe_ok : (Rbe == Rz\T * Ry\T * Rx\T).
  Proof. lma. Qed.
    
End Example4CoordinateSystem.


(** example for symbol matrix *)
Module Exercise_Ch1_Symbol.

  (* for better readibility *)
  Notation "0" := R0.
  Notation "1" := R1.
  Notation "2" := (R1 + R1)%R.
  Notation "3" := (R1 + (R1 + R1))%R.
  Notation "4" := ((R1 + R1) * (R1 + R1))%R.
  
  Example ex6_1 : forall a b : R,
      (let m := mk_mat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1 in
      mdet m = (a - b)^3)%R.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_2 : forall a b x y z : A,
      (let m1 := mk_mat_3_3
                   (a*x+b*y) (a*y+b*z) (a*z+b*x)
                   (a*y+b*z) (a*z+b*x) (a*x+b*y)
                   (a*z+b*x) (a*x+b*y) (a*y+b*z) in
       let m2 := mk_mat_3_3 x y z y z x z x y in
       mdet m1 = (a^3 + b^3) * mdet m2)%R.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_3 : forall a b e d : A,
      (let m := mk_mat_4_4
                 (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
                 (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
                 (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
                 (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2) in
      mdet m = 0)%R.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_4 : forall a b e d : A,
      let m := mk_mat_4_4
                 1 1 1 1
                 a b e d
                 (a^2) (b^2) (e^2) (d^2)
                 (a^4) (b^4) (e^4) (d^4) in
      (mdet m = (a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%R.
  Proof. intros. cbv. ring. Qed.
  
  (* (** 6.(5), it is an infinite structure, need more work, later... *) *)

End Exercise_Ch1_Symbol.
