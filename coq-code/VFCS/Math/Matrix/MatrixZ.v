(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Z.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export ZExt.
Require Import MatrixModule.


(* ======================================================================= *)
(** ** Matrix theory come from common implementations *)

Module Export BasicMatrixTheoryZ := RingMatrixTheory RingElementTypeZ.


(* ======================================================================= *)
(** ** Matrix theory applied to this type *)
Open Scope Z_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** ** Usage demo *)
Section test.
  Let l1 := [[1;2];[3;4]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1.       (* = [[1; 2]; [3; 4]] *) *)
  (* Compute m2l (mmap Z.opp m1).       (* = [[-1; -2]; [-3; -4]] *) *)
  (* Compute m2l (m1 * m1).     (* = [[7; 10]; [15; 22]] *) *)

  Variable a11 a12 a21 a22 : Z.
  Variable f : Z -> Z.
  Let m2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.       (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  (* Eval cbn in m2l (m2 * m2). *)
  
End test.
