(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on function of R to R.
  author    : ZhengPu Shi
  date      : 2023.04
*)

Require Export RExt.
(* Require Export RealFunction. *)
Require Export Calculus.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryRFun := RingMatrixTheory RingElementTypeRFun.

Open Scope R_scope.
Open Scope Rfun_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)

(* ==================================== *)
(** ** Derivative of matrix *)
(* ref: page 162, QuanQuan, 多旋翼设计与控制 *)

(** 标量(函数)对矩阵(函数)的梯度 *)
(* Variable f : R -> R. *)
(* Set Printing All. *)
(* Check f '. *)
(* Definition mderiv {r c} (a : A) (X : mat r c) := *)
  

(* ======================================================================= *)
(** * Usage demo *)

Section test.
  Let f00 : A := fun t => 1.
  Let f01 : A := fun t => 2.
  Let f10 : A := fun t => 3.
  Let f11 : A := fun t => 4.
  Let l1 := [[f00;f01];[f10;f11]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Aopp m1). *)
  (* Compute m2l (m1 * m1). *)

  Variable a00 a01 a10 a11 : A.
  Variable f : A -> A.
  Let m2 := @l2m 2 2 [[a00;a01];[a10;a11]].
  (* Compute m2l m2.       (* = [[a00; a01]; [a10; a11]] *) *)
  (* Compute m2l (mmap f m2).     (* = [[f a00; f a01]; [f a10; f a11]] *) *)
  (* Compute m2l (m2 * m2). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

  (** mmul_sub_distr_r *)
  Goal forall r c s (m0 : mat r s) (m1 m2 : mat r c) (m3 : mat c s),
      m0 + (m1 - m2) * m3 == m0 + m1 * m3 - m2 * m3.
    intros. rewrite mmul_msub_distr_r.
    unfold msub. unfold Matrix.msub. monoid_simp.
  Qed.
  
End test.

Section Example4CoordinateSystem.
  Open Scope fun_scope.
  Notation "1" := Aone : fun_scope.
  Notation "0" := Azero : fun_scope.
  (* Infix "+" := Aadd : fun_scope. *)
  (* Notation "- a" := (Aopp a) : fun_scope. *)
  (* Infix "*" := Amul : fun_scope. *)

  
  Variable ψ θ ϕ : A.
  Let cθ : A := fun t => cos (θ t).
  Let sθ : A := fun t => sin (θ t).
  Let cψ : A := fun t => cos (ψ t).
  Let sψ : A := fun t => sin (ψ t).
  Let cϕ : A := fun t => cos (ϕ t).
  Let sϕ : A := fun t => sin (ϕ t).
  
  Let Rx := mk_mat_3_3 1 0 0 0 cϕ sϕ 0 (-sϕ) cϕ.
  Let Ry := mk_mat_3_3 cθ 0 (-sθ) 0 1 0 sθ 0 cθ.
  Let Rz := mk_mat_3_3 cψ sψ 0 (-sψ) cψ 0 0 0 1.
  Let Rbe :=
        mk_mat_3_3
          (cθ * cψ) (cψ * sθ * sϕ - sψ * cϕ)
          (cψ * sθ * cϕ + sϕ * sψ) (cθ * sψ)
          (sψ * sθ * sϕ + cψ * cϕ)
          (sψ * sθ * cϕ - cψ * sϕ)
          (-sθ) (sϕ * cθ) (cϕ * cθ).
  Lemma Rbe_ok : (Rbe == Rz\T * Ry\T * Rx\T)%M.
  Proof. lma; unfold Aadd,Azero,Amul,Aone,Aeq,A; ring_simplify; auto. Qed.
    
End Example4CoordinateSystem.

