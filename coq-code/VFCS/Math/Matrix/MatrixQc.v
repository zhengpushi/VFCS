(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Qc.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export QcExt.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryQc :=
  DecidableFieldMatrixTheory DecidableFieldElementTypeQc.

Open Scope Qc_scope.
Open Scope mat_scope.

(* ======================================================================= *)
(** * Matrix theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let l1 := Q2Qc_dlist [[1;-3;-2];[-2;1;-4];[-1;4;-1]]%Q.
  Let m1 := @l2m 3 3 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Qcopp m1). *)
  (* Compute m2l (m1 * m1). *)

  Variable a11 a12 a21 a22 : Qc.
  Variable f : Qc -> Qc.
  Let m2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.       (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  (* Eval cbn in m2l (m2 * m2). *)


  (** matrix inversion by gauss elimnation *)
  Opaque Aadd Amul Aopp.
  (* Eval cbn in minv_gauss (l2m 1 1 [[1]]). *)
  (* Eval cbv in minv_gauss (l2m 1 1 [[1]]). *)
  (* Eval cbn in minv_gauss (l2m 2 2 [[1;0];[0;1]]). *)
  
End test.
