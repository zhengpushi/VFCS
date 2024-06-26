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

Require Export MulticopterConfig.
Require Export AttitudeRepr.
               

(* ######################################################################### *)
(** * 多旋翼飞行控制刚体模型 *)

(* 对多旋翼建模时，做了一些简化的假设，见 Config.v 中的说明 *)

(* ======================================================================= *)
(** ** 刚体运动学模型 *)
Section RigidKinematicsModel.

  (* 多旋翼的重心向量(与时间相关的函数) *)
  Variable e_p : R -> vec 3.

  (* 多旋翼的速度向量 *)
  Variable e_v : R -> vec 3.

  (* 速度与位置的模型 *)
  Axiom positionVelocityMODEL : vderiv e_p = e_v.

  (* 机体旋转角速度，可由传感器测量得到 *)
  Variable b_angvx b_angvy b_angvz : R -> R.
  Notation b_ωx := b_angvx. Notation b_ωy := b_angvy. Notation b_ωz := b_angvz.
  Let b_angv (t : R) : vec 3 := l2v [b_ωx t; b_ωy t; b_ωz t].
  Notation b_ω := b_angv.

  (* 欧拉角模型 *)
  Section eulerMODEL.
    (* 给定欧拉角（姿态角）*)
    Variable roll : R -> R.      (* 绕 x 轴旋转的滚转角 *)
    Variable pitch : R -> R.     (* 绕 y 轴旋转的俯仰角 *)
    Variable yaw : R -> R.       (* 绕 z 轴旋转的偏航角 *)
    Notation ϕ := roll. Notation θ := pitch. Notation ψ := yaw.
    Let Φ : R -> vec 3 := fun t => l2v [ϕ t; θ t; ψ t].
    
    (* 从机体旋转角速度到欧拉角变化率（导数）的转换矩阵 *)
    Let W (t : R) : smat 3 :=
          let s1 := sin (ϕ t) in
          let c1 := cos (ϕ t) in
          let s2 := sin (θ t) in
          let c2 := cos (θ t) in
          let t2 := tan (θ t) in
          l2m [[1; t2 * s1; t2 * c1];
               [0; c1; - s1];
               [0; s1 / c2; c1 / c2]]%R.

    (* 欧拉角模型，即欧拉角变化率与机体旋转角速度的关系 *)
    Lemma eulerMODEL :
      (forall t, pitchValid (θ t)) ->
      vderiv Φ = fun t => W t *v b_ω t.
    Proof.
      intros.
      pose proof (angv2eulerRateMAT_spec ϕ θ ψ b_ωx b_ωy b_ωz).
      extensionality t. apply (H0 t). auto.
    Qed.
  End eulerMODEL.

  (* 旋转矩阵模型 *)
  Section matrixMODEL.
    (* 给定旋转矩阵 *)
    Variable Rb2e : R -> mat 3 3.

    (* 旋转矩阵模型，即旋转矩阵变化率与机体旋转角速度的关系 *)
    Lemma matrixMODEL :
      (forall t, SOnP (Rb2e t)) ->
      mderiv Rb2e = fun t => Rb2e t * skew3 (b_ω t).
    Proof. intros. apply derivRb2e_eq; auto. Qed.
  End matrixMODEL.

  (* 四元数模型 *)
  Section quatMODEL.
    (* 任给 {e}相对于{b} 的四元数 *)
    Variable q_e2b : R -> quat.
    Let q0 := fun t => (q_e2b t).W.
    Let qv := fun t => (q_e2b t).Im.

    (* 四元数W分量q0的模型，即q0的导数与机体角速度b_ω的关系 *)
    Lemma quatMODEL_W :
      (forall t : R, b_ω t <> vzero) ->
      (forall t h : R, is_small ((||b_ω t||) * h / 2)) ->
      q0 ' = fun t => <((-(1/2))%R s* qv t)%V, b_ω t>.
    Proof. intros. apply derivQuat_W_eq; auto. Qed.

    (* 四元数Im分量qv的模型，即qv的导数与机体角速度b_ω的关系 *)
    Lemma quatMODEL_Im :
      (forall t : R, b_ω t <> vzero) ->
      (forall t h : R, is_small ((||b_ω t||) * h / 2)) ->
      vderiv qv = fun t => ((1/2) s* (q0 t s* mat1 + skew3 (qv t))) *v (b_ω t).
    Proof. intros. apply derivQuat_Im_eq; auto. Qed.
  End quatMODEL.
End RigidKinematicsModel.

(* ======================================================================= *)
(** ** 多旋翼刚体动力学模型 *)


Section RigidDynamicsModel.

  (* 位置动力学模型，即速度的导数、姿态角、拉力之间的关系 *)
  Section Position.

    (* 螺旋桨总拉力 *)
    Variable f : R -> R.
    Axiom f_ge0 : forall t, 0 <= f t. (* 拉力非负 *)

    (* 假设速度矢量 v 在 {e} 中的坐标如下 *)
    Variable e_v : R -> vec 3.

    (* 假设 {b} 相对于 {e} 的旋转矩阵为 *)
    Variable R_b2e : R -> smat 3.

    (* 机体 z 轴的矢量在 {b} 中的表示为 *)
    Let b_b3 : R -> vec 3 := fun t => v3j.
    (* 于是，机体 z 轴的矢量在 {e} 中的表示为 *)
    Let e_b3 : R -> vec 3 := fun t => (R_b2e t) *v (b_b3 t).

    (* 受力分析：有两个，沿e_z轴正向的重力，沿b_z轴负向的拉力 *)
    Axiom forceMODEL :
      vderiv e_v = fun t => (Config.g s* v3j + ((- f t) / Config.m)%R s* e_b3 t)%V.

    (* 在{e}下的位置动力学模型 *)
    Lemma positionMODEL_E :
      vderiv e_v =
        fun t => (Config.g s* v3j + ((- f t) / Config.m)%R s* (R_b2e t) *v v3j)%V.
    Proof. intros. rewrite forceMODEL. unfold e_b3. auto. Qed.

    (* 在{b}下的位置动力学模型 *)
    Lemma positionMODEL_B :
      vderiv e_v =?
        fun t => (Config.g s* v3j + ((- f t) / Config.m)%R s* (R_b2e t) *v v3j)%V.
    Proof. intros. rewrite forceMODEL. unfold e_b3. auto. Qed.

    

  
  End Position.

    (* 姿态动力学模型 *)
    Section Pose.

    End Pose.
    
  End RigidDynamicsModel.
End ControlModel.
