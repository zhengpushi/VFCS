(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix on nat.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export NatExt.
Require Import MatrixModule.


(* ======================================================================= *)
(** ** Matrix theory come from common implementations *)

Open Scope nat_scope.
Open Scope mat_scope.

Module Export BasicMatrixTheoryNat := BasicMatrixTheory ElementTypeNat.

(* ======================================================================= *)
(** ** Matrix theory applied to this type *)


(* ======================================================================= *)
(** ** Usage demo *)
Section test.
  Let l1 := [[1;2;3];[4;5;6]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1.       (* = [[1; 2]; [3; 4]] *) *)
  (* Compute m2l (mmap S m1).       (* = [[2; 3]; [4; 5]] *) *)

  Variable a11 a12 a21 a22 : nat.
  Let m2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.       (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap S m2).     (* = [[S a11; S a12]; [S a21; S a22]] *) *)

  Let m3 : mat 2 2 := l2m [[1;2];[3;4]].
  Goal m3.11 = 1. auto. Qed.
  
End test.


