(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Z.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export ZExt.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryZ := RingMatrixTheory RingElementTypeZ.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)
Open Scope Z_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let l1 := [[1;2];[3;4]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1.       (* = [[1; 2]; [3; 4]] *) *)
  (* Compute m2l (mmap Z.opp m1).       (* = [[-1; -2]; [-3; -4]] *) *)
  (* Compute m2l (m1 * m1).     (* = [[7; 10]; [15; 22]] *) *)

  Variable a00 a01 a10 a11 : A.
  Variable f : A -> A.
  Let m2 := @l2m 2 2 [[a00;a01];[a10;a11]].
  (* Compute m2l m2.       (* = [[a00; a01]; [a10; a11]] *) *)
  (* Compute m2l (mmap f m2).     (* = [[f a00; f a01]; [f a10; f a11]] *) *)
  (* Eval cbn in m2l (m2 * m2). *)
  
End test.
