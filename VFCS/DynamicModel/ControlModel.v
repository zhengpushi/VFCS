(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Multicopter Control Model 多旋翼控制模型
  author    : Zhengpu Shi
  date      : Nov, 2023

  reference : 
  1. Introduction to Multicopter Design and Control, QuanQuan, 2017
 *)

Require Export Calculus.
From FinMatrix Require Matrix MatrixR.
From OrienRepr Require Orien3D.


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
