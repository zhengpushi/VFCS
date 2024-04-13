(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Linear equations
  author    : ZhengPu Shi
  date      : 2024.01

  reference :
  1. 丘维声《高等代数》，第2版，清华大学出版社，2019
  
  remark    :
 *)

Require Export Hierarchy.
Require Export Matrix.
Require Export MatrixGauss.
Require Export Vector.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Adiv Alt Ale.

Open Scope A_scope.
Open Scope mat_scope.
Open Scope vec_scope.


(** ** linear equation *)
Section leqs.
  Context `{HField : Field}.
  Check 
  Compute mat nat 3 4.
  Check mrowK.
  Check vec.
  Check mat.
  (* 含有 s 个方程的 n 元线性方程组。
     其中，a称为系数，x称为未知量，b称为常数项。*)
  Record leqs {n s : nat} := {
      leqs_a : @vec (@vec A n) s;
      leqs_b : @vec V s
    }.
  Context `{HVectorSpace : VectorSpace}.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vcmul).


  (* 若n元有序数组(c1,c2,...,cn)'代入方程后使得每个方程是恒等式，则称它是
     该方程组的一个解。方程组的所有解组成的集合称为这个方程组的解集。
     符合实际问题需要的解称为可行解。*)
  
  (* x is the answer of the equation `e` *)
  Definition leqsAnswer {n s} (e : @leqs n s) (x : @vec V n) : Prop :=
    vmap (fun ai => lcomb ai x) (leqs_a e) = (leqs_b e).
  
  (* n元线性方程组，s和n之间可能的关系：s = n, s < n, s > n *)

  (* 如何求解线性方程组？方程组的消元法。 *)
  (* 线性方程组的初等变换，三种。 *)
  (* 阶梯形方程组，简化阶梯形方程组 *)
  (* Check mrowK. *)
  (* Check mrowSwap. *)
  (* Check mrowKAdd. *)

  (* 可以在这个模块中开发线性方程组的理论 *)
  (* MatrixGauss *)
(* 若n元线性方程组I与II的解集相同，则称方程组I与II同解。
   n元线性方程组的“同解”关系是等价关系。
   不难看出，n元线性方程组经过初等变换1,2,3，得到的方程组与原方程同解。
   因此，经过一系列初等变换变成的简化阶梯形方程组与原线性方程组同解。*)

  (*  在求解过程中，只对线性方程组的系数和常数项进行运算，相应的有系数矩阵和增广矩阵。 *)
   
End leqs.
