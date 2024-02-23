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

Module Export MatrixTheoryQ := BasicMatrixTheory ElementTypeQ.

Open Scope Q_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let M1 := @l2m 3 3 [[1;-3;-2];[-2;1;-4];[-1;4;-1]].
  (* Compute m2l M1. *)
  (* Compute m2l (mmap Qopp M1). *)

  Variable a11 a12 a21 a22 : A.
  Variable f : A -> A.
  Let M2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l M2.              (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f M2).     (* = [[f a11; f a12]; [f a21; f a22]] *) *)
End test.
