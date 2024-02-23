(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix on nat.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export NatExt.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryNat := BasicMatrixTheory ElementTypeNat.

Open Scope nat_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let M1 := @l2m 2 2 [[1;2;3];[4;5;6]].
  (* Compute m2l M1.            (* = [[1; 2]; [4; 5]] *) *)
  (* Compute m2l (mmap S M1).   (* = [[2; 3]; [5; 6]] *) *)

  Goal M1.11 = 1.
  Proof. auto. Qed.
  
  Variable a11 a12 a21 a22 : A.
  Variable f : A -> A.
  Let M2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l M2.               (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f M2).      (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  
End test.


