(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Multicopter Control Model 多旋翼控制模型
  author    : Zhengpu Shi
  date      : Nov, 2023

  reference : Introduction to Multicopter Design and Control, QuanQuan, 2017
 *)

Require Export Calculus.
From FinMatrix Require Matrix MatrixR.
From OrienRepr Require Orien3D.


(* ######################################################################### *)
(** * Preliminary things *)

Import Matrix.
(* ======================================================================= *)
(** ** 向量值函数 (vector-valued function)，以及矩阵值函数 *)
(* 向量值函数是指分量都是关于同一自变量的一元函数，就是说 n 元向量值函数是x到x^n上的映射。
   常见的是二维和三维的向量值函数，即n = 2和n = 3的情形。
   向量值函数简称向量函数，同理，矩阵值函数简称矩阵函数
 *)

(** 向量函数的导数 *)
Definition vderiv {n} (v : R -> @vec R n) : R -> @vec R n :=
  fun x => (fun i => (fun x0 => v x0 i)' x).

(* 示例：速度矢量 v = 位置矢量 p 的导数  *)
Section example.
  (* 给定位置矢量的三个分量 *)
  Variable px py pz : R -> R.

  (* 位置矢量 *)
  Let p : R -> vec 3 := fun t => l2v R0 [px t; py t; pz t].
  (* 速度矢量 *)
  Let v : R -> vec 3 := vderiv p.
  (* 计算其表达式 *)
  (* Eval cbv in fun t => v2l (v t). *)
  
  (* 验证位置矢量和速度矢量的等式 *)
  Goal forall t, (vderiv p) t = l2v R0 [px ' t; py ' t; pz ' t].
  Proof. intros. veq. Qed.
End example.


(** 矩阵函数的导数 *)
Definition mderiv {r c} (f : R -> mat R r c) : R -> mat R r c :=
  fun t => (fun i j => (fun x => f x i j)' t).


(* ######################################################################### *)
(** * 姿态表示 *)

(* ======================================================================= *)
(** ** 坐标系  *)

Import MatrixR.

(* EFCF: Earth-Fixed Coordinate Frame，地球固连坐标系，记作 e *)
(* ABCF: Aircraft-Body Coordinate Frame，机体坐标系，记作 b *)

(* 单位向量 *)
Definition e1 : vec 3 := l2v [1;0;0].
Definition e2 : vec 3 := l2v [0;1;0].
Definition e3 : vec 3 := l2v [0;0;1].

(* 机体轴在机体坐标系下的向量。随时间而确定的向量，此处是常量 *)
Definition b_b_1 : R -> vec 3 := fun t => e1.
Definition b_b_2 : R -> vec 3 := fun t => e2.
Definition b_b_3 : R -> vec 3 := fun t => e3.

(* 机体轴在地球坐标系下的向量 *)
Parameter b_e_1 b_e_2 b_e_3 : R -> vec 3.

(* 给定机体旋转角速度（绕机体轴的，可由传感器直接测量得到） *)
Parameter ω_b : R -> vec 3.

(* 欧拉角模型 *)
Section Euler.
  (* 采用的欧拉角定义方式：intrinsic + ZYX，即B321 *)
  
  (* 给定机体姿态角（即，欧拉角） *)
  Variable ϕ θ ψ : R -> R.
  Definition Θ : R -> vec 3 := fun t => l2v [ϕ t; θ t; ψ t].

  (* 欧拉角与旋转矩阵 *)
  
    (* 中间变换矩阵 W *)
    Definition W : R -> mat 3 3 :=
          fun t =>
            let θ := θ t in
            let ϕ := ϕ t in
            l2m [[1; tan θ * sin ϕ; tan θ * cos ϕ];
                 [0; cos ϕ; - sin ϕ];
                 [0; sin ϕ/ cos θ; cos ϕ/ cos θ]]%R.
    
    (* 姿态角与旋转角速度的关系 *)
    Axiom H_Θ_ω : vderiv Θ = fun t => W t *v ω_b t.

  End Euler.

  (* 旋转矩阵 *)
  Section RotationMatrix.

    (*  *)

    (* 给定旋转矩阵 *)
    Variable Rbe : mat 3 3.     (* 向量 r_b 从 b  *)
    (* b_e_i 满足如下关系 *)

  End RotationMatrix.

End PoseRepr.


(* ######################################################################### *)
(** * 多旋翼控制模型 *)
Section ControlModel.
  Import MatrixR.

  (* 多旋翼的重心向量(与时间相关的函数) *)
  Variable p_e : R -> vec 3.

  (* 多旋翼的速度向量 *)
  Variable v_e : R -> vec 3.

  (* 给定机体旋转角速度（绕机体轴的，可由传感器直接测量得到） *)
  Variable ω_b : R -> vec 3.

  (** ** 多旋翼刚体运动学模型 *)
  Section RigidKinematicsModel.

    (* 速度与位置的关系 *)
    Axiom H_v_p : vderiv p_e = v_e.
    
    (* 欧拉角模型 *)
    Section Euler.
      (* 给定机体姿态角 *)
      Variable ϕ θ ψ : R -> R.

      (* 姿态角变化率与机体旋转角速度的关系 *)
      Check H_Θ_ω ω_b ϕ θ ψ.
    End Euler.

    (* 旋转矩阵模型 *)
    Section RotationMatrix.
      (* 给定旋转矩阵 *)
      Variable Rbe : R -> mat 3 3.

      (* 旋转矩阵变化率与机体旋转角速度的关系 *)
      Axiom H_Rbe_ω : mderiv Rbe = fun t => (Rbe t * skew3 (ω_b t))%M.
    End RotationMatrix.

    (* 四元数模型 *)
    Section Quaternion.
      (* 给定四元数，这里分别给出实部和虚部 *)
      Variable q0 : R -> R.
      Variable qv : R -> vec 3.

      (* 四元数变化率与机体旋转角速度的关系 *)
      Axiom H_q0 :
        q0 ' =
          fun t =>
            let m : mat 1 1 := (qv t) * (ω_b t) in
            (- (1/2) * m.11)%R.
      Axiom H_qv :
        cvderiv qv =
          fun t =>
            ((1/2) c* ((q0 t) c* @mat1 3 + cv3skew (qv t)) * ω_b t) %M.
    End Quaternion.
    
  End RigidKinematicsModel.

  (** ** 多旋翼刚体动力学模型 *)
  Section RigidDynamicsModel.

    (* 位置动力学模型 *)
    Section Position.

      (* 螺旋桨总拉力 *)
      Variable f : R -> R.
      Axiom f_ge0 : forall t, f t >= 0. (* 拉力非负 *)

      (* 重力加速度 *)
      Variable g : R.
      (* 整机质量 *)
      Variable m : R.

      (* 速度与拉力的关系 *)
      Variable t : R.
      Check cvderiv v_e.
      Definition e1 : vec 3 := l2v [1;0;0].
      Definition e2 : vec 3 := l2v [0;1;0].
      Definition e3 : vec 3 := l2v [0;0;1].
      Check g c* e3.
      Check b_e_3
?      Axiom H_6_5 : v_e
    

    End Position.

    (* 姿态动力学模型 *)
    Section Pose.

    End Pose.
    
  End RigidDynamicsModel.
End ControlModel.
