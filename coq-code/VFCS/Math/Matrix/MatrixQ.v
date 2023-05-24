(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Q.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export QExt.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryQ :=
  DecidableFieldMatrixTheory DecidableFieldElementTypeQ.

Open Scope Q_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let l1 := [[1;-3;-2];[-2;1;-4];[-1;4;-1]]%Q.
  Let m1 := @l2m 3 3 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Qopp m1). *)
  (* Compute m2l (m1 * m1). *)
  
  (* Eval cbn in (minv_gauss m1). *)
  (* Compute minv_gauss m1. *)

  Variable a11 a12 a21 a22 : T.
  Variable f : T -> T.
  Let m2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.     (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)

  (** matrix inversion by gauss elimnation *)
  Opaque Tadd Tmul Topp.
  (* Eval cbn in minv_gauss (l2m 1 1 [[1]]). *)
  (* Eval cbv in minv_gauss (l2m 1 1 [[1]]). *)
  (* Eval cbn in minv_gauss (l2m 2 2 [[1;0];[0;1]]). *)
  (* Eval cbv in minv_gauss (l2m 2 2 [[1;0];[0;1]]). *)
  
End test.
