(*
  Copyright 2024 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : The configuration of a multicopter
  author    : Zhengpu Shi
  date      : Jun, 2024

  reference : 
  1. Introduction to Multicopter Design and Control, QuanQuan, 2017
 *)

Require Import Reals.
Open Scope R_scope.

(* 
   对多旋翼建模时，做如下假设：
   1. 多旋翼是刚体
   2. 质量和转动惯量不变
   3. 多旋翼几何中心与重心一致
   4. 多旋翼只受重力和螺旋桨拉力，其中，
      重力沿o_ez_e轴正方向，螺旋桨拉力沿o_bz_b轴负方向
   5. 奇数标号的螺旋桨为逆时针转动，偶数标号的螺旋桨为顺时针转动。
 *)


(* 旋翼数目 *)
Inductive RotorCount :=
| RotorCount4       (* 四旋翼 *)
| RotorCount6       (* 六旋翼 *)
.

(* 四旋翼的两种机头方向 *)
Inductive QuadcopterHead :=
| QHeadPLUS         (* +字型 *)
| QHeadCross        (* x字型 *)
.

(* 多旋翼的配置，即不变的一些参数。
   ToDo: 是否需要使用 Record 来设计结构体，作为各个函数的参数？或许会增加复杂度 *)
Module Config.

  (* 旋翼数目 *)
  Parameter RotorCount : RotorCount.

  (* 重力加速度 (m/s²) *)
  Parameter g : R.
  Axiom g_gt0 : 0 < g.          (* g是正值 *)

  (* 整机质量 (kg) *)
  Parameter m : R.
End Config.
