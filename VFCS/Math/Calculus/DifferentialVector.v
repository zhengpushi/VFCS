(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Differential calculus for vector and matrix
  author    : Zhengpu Shi
  date      : 2024.06
  
 *)

Require Export Differential.
From FinMatrix Require Export Matrix.

(* ======================================================================= *)
(** ** 向量值函数 (vector-valued function)，以及矩阵值函数 *)
(* 向量值函数是指分量都是关于同一自变量的一元函数，就是说 n 元向量值函数是x到x^n上的映射。
   常见的是二维和三维的向量值函数，即n = 2和n = 3的情形。
   向量值函数简称向量函数，同理，矩阵值函数简称矩阵函数
 *)

(** 向量函数的导数 *)
Definition vderiv {n} (f : R -> vec n) : R -> vec n :=
  fun t => (fun i => (fun x => f x i)' t).

(* 向量函数的导数的一个元素 *)
Lemma vnth_vderiv : forall {n} (f : R -> vec n) (i : 'I_n),
    (fun t => (vderiv f t) i) = (fun t => f t i)'.
Proof. auto. Qed.

(* 示例：速度矢量 v = 位置矢量 p 的导数  *)
Section example.
  (* 给定位置矢量的三个分量 *)
  Variable px py pz : R -> R.

  (* 位置矢量 *)
  Let p : R -> @vec R 3 := fun t => l2v R0 [px t; py t; pz t].
  (* 速度矢量 *)
  Let v : R -> vec 3 := vderiv p.
  (* 计算其表达式 *)
  (* Eval cbv in fun t => v2l (v t). *)
  
  (* 验证位置矢量和速度矢量的等式 *)
  Goal forall t, (vderiv p) t = l2v R0 [px ' t; py ' t; pz ' t].
  Proof. intros. veq. Qed.
End example.


(** 矩阵函数的导数 *)
Definition mderiv {r c} (F : R -> mat R r c) : R -> mat R r c :=
  fun t => (fun i j => (fun x => F x i j)' t).

(* 矩阵函数的导数的一个元素 *)
Lemma mnth_mderiv : forall {r c} (F : R -> mat R r c) (i : 'I_r) (j : 'I_c),
    (fun t => (mderiv F t) i j) = (fun t => F t i j)'.
Proof. auto. Qed.

(* 矩阵函数的导数的一行，等于该行的导数 *)
Lemma mrow_mderiv_eq_vderiv : forall {r c} (f : R -> mat R r c) (i : fin r),
    (fun t => (mderiv f t) i) = vderiv (fun t => (f t) i).
Proof. intros. auto. Qed.

(* 矩阵函数的导数的一列，等于该列的导数 *)
Lemma mcol_mderiv_eq_vderiv : forall {r c} (f : R -> mat R r c) (j : fin c),
    (fun t => mcol (mderiv f t) j) = vderiv (fun t => mcol (f t) j).
Proof. intros. auto. Qed.

(* 矩阵函数的导数等于每行的导数构成的矩阵 *)
Lemma mderiv_eq_vderiv_row : forall {r c} (f : R -> mat R r c),
    mderiv f = fun t => (fun i => vderiv (fun x => f x i) t).
Proof. auto. Qed.

(* 矩阵函数的导数等于每列的导数构成的矩阵 *)
Lemma mderiv_eq_vderiv_col : forall {r c} (f : R -> mat R r c),
    mderiv f = fun t => (fun i j => vderiv (fun x => mcol (f x) j) t i).
Proof. auto. Qed.
