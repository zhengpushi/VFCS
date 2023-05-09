(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       Vector.v
  author:     ZhengPu Shi
  date:       2021.01.01
  purpose:
  1. vector (it is similiar with array, but fixed length
  
*)

From FlyCtrl Require Export Array.
Require Import Reals.
Require Import Lra.


(* --------------------------------------------------------------- *)
(* Vector *)

(* we use Array module based on Real Number *)
Export Module_ArrayR.
Open Scope R.

Notation v2 := (array 2).
Notation v3 := (array 3).

Notation m_3x1 := (matrix 3 1).
Notation m_3x3 := (matrix 3 3).

Definition v2_len (v : v2) : R :=
  let '(x,y) := a2_to_tuples v in
  let x : R := x in
  let y : R := y in
  let cond_plus_x2_y2_gt0 : 0 <= x * x + y * y 
    := Rplus_le_le_0_compat (x*x) (y*y) (Rle_0_sqr x) (Rle_0_sqr y) in
    Rsqrt (mknonnegreal (x * x + y * y) cond_plus_x2_y2_gt0).


Definition v3_len (v : v3) : R :=
  let '(x,y,z) := a3_to_tuples v in
  let x : R := x in
  let y : R := y in
  let z : R := z in
  let cond_plus_x2_y2_gt0 : 0 <= x * x + y * y 
    := Rplus_le_le_0_compat (x*x) (y*y) (Rle_0_sqr x) (Rle_0_sqr y) in
  let cond_plus_x2_y2_z2_gt0 : 0 <= x * x + y * y + z * z
    := Rplus_le_le_0_compat (x*x+y*y) (z*z) 
    cond_plus_x2_y2_gt0 (Rle_0_sqr z) in
    Rsqrt (mknonnegreal (x * x + y * y + z * z) 
    cond_plus_x2_y2_z2_gt0).
