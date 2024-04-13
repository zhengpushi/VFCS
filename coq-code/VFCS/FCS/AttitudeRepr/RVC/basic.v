(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Basic of RVC
  author    : ZhengPu Shi
  date      : Apr, 2023
  
  reference :
  1. Peter Corke, Robotics Vision and Control
 *)


(* Ch2 Representing Position and Orientation 位置和朝向表示
 *)

Require Import Lra.

(* Require Import Quaternion. *)
Require Import VectorC.
Require Import VectorR.
Require Import VectorR3.

(* short name for matrix/vector theory on C *)
Module C.
  Include MatrixTheoryC.
  Include VectorTheoryC.
End C.

