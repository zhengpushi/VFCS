(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Euler angle
  author    : ZhengPu Shi
  date      : Apr, 2023
  
  reference :
  1. Peter Corke, Robotics Vision and Control. page34.
  2. https://en.wikipedia.org/wiki/Euler_angles
  3. https://krasjet.github.io/quaternion
  4. https://zhuanlan.zhihu.com/p/98320567
  5. Carlos M. Roithmayr and Deway H. Hodges, Dynamics: Theory and Application of 
     Kane's Method. page22, page484.

  remark    :
  一、欧拉角
  1. 右手定则与左手定则(right- or left-handed rule)，可用于决定旋转角的符号
     右手和左手参考系( .. coordinates)，按照x->y->z的顺序，可用于决定第三个轴的方向。
  2. 主动和被动旋转 (Alibi or alias, 也称 active or passive)，
     主动是旋转物体（刚体、表示刚体的向量），被动是旋转坐标系
  3. 内部和外部旋转 (intrinsic or extrinsic rotation)，
     内部是绕物体自身的坐标系，旋转轴对于物体不变，但对于外部参考系在变化；
     外部是绕固定的参考坐标系，旋转轴对于外部参考系不变，但对于物体在变化。
  4. 预乘和后乘 (pre- or post-multiplication)
     同一个点P，可以被表示为列向量v或行向量w。
     旋转矩阵能被预乘以列向量 Rv，或者后乘以行向量 wR。
     然而，Rv产生的旋转与wR的是反向的。
     为了得到相同的旋转（即，P点相同的最终坐标），等价的行向量必须后乘以R的转置（即，wR\T）
  5. 经典欧拉角和Tait-Bryan角
     欧拉角通常表示为 α,β,γ 或 ψ,θ,ϕ。
     不同作者可能使用不同的旋转轴来定义欧拉角，或者为相同的角起不同的名字。
     因此，任何涉及欧拉角的讨论都应该先说它们的定义。
     不考虑旋转轴的两种不同惯例时，旋转轴顺序存在12种可能，分为两组：
     Proper Euler angles: (xyx,xzx,yxy,yzy,zxz,zyz)
     Tait-Bryan angles: (xyz,xzy,yxz,yzx,zxy,zyx)
     其中，Tait-Bryan角，也称 Cardan angles; nautical angles; heading,elevation, and 
     bank; or yaw, pitch, and roll.
     有时这两种顺序都称“Euler angles”。
     此时，第一种顺序也称为 proper or classic 欧拉角。
  6. 欧拉角的定义有24种
     (内部 or 外部) * (Proper or Tait-Bryan) = 2 * (6 + 6) = 24 
  二、旋转矩阵
  1. 向量的旋转变换矩阵 vs 坐标系的旋转变换矩阵
     向量的旋转变换，写作 v' = R v，表示：坐标系不动，向量 v 旋转到了 v'
     坐标系的旋转变换，写作 v' = R\T v，表示：坐标系旋转，得到的是不动的点 v 在新坐标系
     下的表示。
     注意以下对应关系：
     (1) v' = R v 表示v经过R旋转到达v'，对应的， R' v' = v 表示v'经过R'旋转到达v。 
     (2) R\T 就是 R^(-1)，也写作 R'，它表示一个逆的旋转
     (3) 旋转矩阵R表示向量旋转一个正角度(逆时针)，R\T则表示向量旋转一个负角度（顺时针）。
     (4) 向量旋转正角度，相当于坐标系旋转负角度
     (5) v' = (RxRyRz) v 表示对向量 v 按z,y,x轴的顺序进行旋转得到 v'，
         而需要由 v' 计算 v 时，令 v' W = v，则 W = (RxRyRz)' = Rz'Ry'Rx'
  2. 任意朝向都能分解为从已知的标准朝向开始的三个基本旋转。
     等价的，任意旋转矩阵R能被分解为三个基本旋转矩阵的乘积。
     例如 R = X(α)Y(β)Z(γ) 是一个旋转矩阵，可表示关于 z,y,x轴的外部旋转的复合，
     或是关于 x,y',z''轴的内部旋转的复合。
  三、线性化处理
  1. 小角度变化经常被用来近似描述系统的动态特性，此时系统的相应可通过线性模型来预测和控制。
  2. 角度变化很小(通常认为10度以内)时，可线性化处理，
     sin(α)->α, cos(α)->1, 高阶项sin(α)*sin(β)->0
*)

Require Import Lra.
Require Import VectorR.

Open Scope cvec_scope.

(* 手性：左手定、和右手定则 *)
Inductive HandRule := HRLeft | HRRight.

(* 变换类型：主动变换、被动变换 *)
Inductive Transformation := TActive | TPassive.

(* 旋转轴类型：绕机体轴的内旋、绕固定轴的外旋 *)
Inductive RotateMode := RMIntrinsic | RMExtrinsic.
                              

(* Lemma Rabs_1 : Rabs 1 = 1. *)
(* Proof. ra. Qed. *)

(* Lemma Rabs_R1 : Rabs R1 = 1. *)
(* Proof. ra. Qed. *)

(* Hint Rewrite *)
(*   Rabs_1            (* Rabs 1 = 1 *) *)
(*   Rabs_R1           (* Rabs R1 = 1 *) *)
(*   : R. *)

(* (* Lemma sin_eq1_pi2 : forall (x : R) (k : nat), sin x = 1 -> x = (INR k * 2 * PI + PI/2)%R. *) *)
(* Lemma sin_eq1_pi2 : forall (x : R), (-PI/2 <= x <= PI/2) -> sin x = 1 -> x = PI/2. *)
(* Proof. *)
(*   intros x H1 H2. rewrite <- sin_asin in H2; try lra. *)
(*   rewrite asin_1 in H2. apply sin_inj in H2; try lra. *)
(* Qed. *)

(* Global Hint Rewrite *)
(*   Rinv_r_simpl_l      (* (r2 * r1) * /r1 = r2 *) *)
(*   : R. *)


Section BasicRotationMatrics.
  
  (** Orthogormal rotation matrices for rotation of θ aobout 
     the x-,y- and z- axes.

     Notes:
     1. Give a column-vector v1 respect to this coordinate, when actively rotate it 
     about the x-axes, we could get a new vector v1' respect to this coordinate by
     this formula:
          v1' = Rx(θ) v1
     2. If give a row-vector v2, ..., v2' ...
         v2' = v2 (Rx(θ))\T

   *)
  Definition Rx (θ : R) : mat 3 3 :=
    l2m
      [[1; 0; 0];
       [0; cos θ; - sin θ];
       [0; sin θ; cos θ]]%R.

  Definition Ry (θ : R) : mat 3 3 :=
    l2m
      [[cos θ; 0; sin θ];
       [0; 1; 0];
       [- sin θ; 0; cos θ]]%R.

  Definition Rz (θ : R) : mat 3 3 :=
    l2m
      [[cos θ; - sin θ; 0];
       [sin θ; cos θ; 0];
       [0; 0; 1]]%R.

  (* Fact Rx_inv : forall θ, minv (Rx θ) == (Rx θ)\T. *)
  (* Proof. lma; autounfold with A; autorewrite with R; auto. Qed. *)

  (* Fact Ry_inv : forall θ, minv (Ry θ) == (Ry θ)\T. *)
  (* Proof. lma; autounfold with A; autorewrite with R; auto. Qed. *)
  
  (* Fact Rz_inv : forall θ, minv (Rz θ) == (Rz θ)\T. *)
  (* Proof. lma; autounfold with A; autorewrite with R; auto. Qed. *)

  (* Theorem Rx_neg : forall θ, Rx (-θ) == (Rx θ)\T. *)
  (* Proof. lma; autounfold with A; autorewrite with R; auto. Qed. *)

  (* Theorem Ry_neg : forall θ, Ry (-θ) == (Ry θ)\T. *)
  (* Proof. lma; autounfold with A; autorewrite with R; auto. Qed. *)
  
  (* Theorem Rz_neg : forall θ, Rz (-θ) == (Rz θ)\T. *)
  (* Proof. lma; autounfold with A; autorewrite with R; auto. Qed. *)

End BasicRotationMatrics.


Section EulerAngle24.

  Variable θ1 θ2 θ3 : R.
  Notation c1 := (cos θ1). Notation s1 := (sin θ1).
  Notation c2 := (cos θ2). Notation s2 := (sin θ2).
  Notation c3 := (cos θ3). Notation s3 := (sin θ3).

  (** 1. Body-three, 123 *)
  Definition B3_123 : mat 3 3 :=
    l2m
      [[c2 * c3; -c2 * s3; s2];
       [s1 * s2 * c3 + s3 * c1; - s1 * s2 * s3 + c3 * c1; - s1 * c2];
       [-c1 * s2 * c3 + s3 * s1; c1 * s2 * s3 + c3 * s1; c1 * c2]]%R.

  Theorem B3_123_ok : B3_123 == Rx θ1 * Ry θ2 * Rz θ3.
  Proof. lma. Qed.

  (** 2. Body-three, 231 *)
  Definition B3_231 : mat 3 3 :=
    l2m
      [[c1 * c2; - c1 * s2 * c3 + s3 * s1; c1 * s2 * s3 + c3 * s1];
       [s2; c2 * c3; - c2 * s3];
       [- s1 * c2; s1 * s2 * c3 + s3 * c1; - s1 * s2 * s3 + c3 * c1]]%R.

  Theorem B3_231_ok : B3_231 == Ry θ1 * Rz θ2 * Rx θ3.
  Proof. lma. Qed.

  (** 3. Body-three, 312 *)
  Definition B3_312 : mat 3 3 :=
    l2m
      [[- s1 * s2 * s3 + c3 * c1; - s1 * c2; s1 * s2 * c3 + s3 * c1];
       [c1 * s2 * s3 + c3 * s1; c1 * c2; - c1 * s2 * c3 + s3 * s1];
       [- c2 * s3; s2; c2 * c3]]%R.

  Theorem B3_312_ok : B3_312 == Rz θ1 * Rx θ2 * Ry θ3.
  Proof. lma. Qed.

  (** 4. Body-three, 132 *)
  Definition B3_132 : mat 3 3 :=
    l2m
      [[c2 * c3; - s2; c2 * s3];
       [c1 * s2 * c3 + s3 * s1; c1 * c2; c1 * s2 * s3 - c3 * s1];
       [s1 * s2 * c3 - s3 * c1; s1 * c2; s1 * s2 * s3 + c3 * c1]]%R.

  Theorem B3_132_ok : B3_132 == Rx θ1 * Rz θ2 * Ry θ3.
  Proof. lma. Qed.

  (** 5. Body-three, 213 *)
  Definition B3_213 : mat 3 3 :=
    l2m
      [[s1 * s2 * s3 + c3 * c1; s1 * s2 * c3 - s3 * c1; s1 * c2];
       [c2 * s3; c2 * c3; - s2];
       [c1 * s2 * s3 - c3 * s1; c1 * s2 * c3 + s3 * s1; c1 * c2]]%R.
        
  Theorem B3_213_ok : B3_213 == Ry θ1 * Rx θ2 * Rz θ3.
  Proof. lma. Qed.

  (** 6. Body-three, 321 *)
  Definition B3_321 : mat 3 3 :=
    l2m
      [[c1 * c2; c1 * s2 * s3 - c3 * s1; c1 * s2 * c3 + s3 * s1];
       [s1 * c2; s1 * s2 * s3 + c3 * c1; s1 * s2 * c3 - s3 * c1];
       [- s2; c2 * s3; c2 * c3]]%R.
  
  Theorem B3_321_ok : B3_321 == Rz θ1 * Ry θ2 * Rx θ3.
  Proof. lma. Qed.

  (** 7. Body-two, 121 *)
  Definition B2_121 : mat 3 3 :=
    l2m
      [[c2; s2 * s3; s2 * c3];
       [s1 * s2; - s1 * c2 * s3 + c3 * c1; - s1 * c2 * c3 - s3 * c1];
       [- c1 * s2; c1 * c2 * s3 + c3 * s1; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem B2_121_ok : B2_121 == Rx θ1 * Ry θ2 * Rx θ3.
  Proof. lma. Qed.
  
  (** 8. Body-two, 131 *)
  Definition B2_131 : mat 3 3 :=
    l2m
      [[c2; - s2 * c3; s2 * s3];
       [c1 * s2; c1 * c2 * c3 - s3 * s1; - c1 * c2 * s3 - c3 * s1];
       [s1 * s2; s1 * c2 * c3 + s3 * c1; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem B2_131_ok : B2_131 == Rx θ1 * Rz θ2 * Rx θ3.
  Proof. lma. Qed.
  
  (** 9. Body-two, 212 *)
  Definition B2_212 : mat 3 3 :=
    l2m
      [[- s1 * c2 * s3 + c3 * c1; s1 * s2; s1 * c2 * c3 + s3 * c1];
       [s2 * s3; c2; - s2 * c3];
       [- c1 * c2 * s3 - c3 * s1; c1 * s2; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem B2_212_ok : B2_212 == Ry θ1 * Rx θ2 * Ry θ3.
  Proof. lma. Qed.
  
  (** 10. Body-two, 232 *)
  Definition B2_232 : mat 3 3 :=
    l2m
      [[c1 * c2 * c3 - s3 * s1; - c1 * s2; c1 * c2 * s3 + c3 * s1];
       [s2 * c3; c2; s2 * s3];
       [- s1 * c2 * c3 - s3 * c1; s1 * s2; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem B2_232_ok : B2_232 == Ry θ1 * Rz θ2 * Ry θ3.
  Proof. lma. Qed.
  
  (** 11. Body-two, 313 *)
  Definition B2_313 : mat 3 3 :=
    l2m
      [[- s1 * c2 * s3 + c3 * c1; - s1 * c2 * c3 - s3 * c1; s1 * s2];
       [c1 * c2 * s3 + c3 * s1; c1 * c2 * c3 - s3 * s1; - c1 * s2];
       [s2 * s3; s2 * c3; c2]]%R.
  
  Theorem B2_313_ok : B2_313 == Rz θ1 * Rx θ2 * Rz θ3.
  Proof. lma. Qed.
  
  (** 12. Body-two, 323 *)
  Definition B2_323 : mat 3 3 :=
    l2m
      [[c1 * c2 * c3 - s3 * s1; - c1 * c2 * s3 - c3 * s1; c1 * s2];
       [s1 * c2 * c3 + s3 * c1; - s1 * c2 * s3 + c3 * c1; s1 * s2];
       [- s2 * c3; s2 * s3; c2]]%R.
  
  Theorem B2_323_ok : B2_323 == Rz θ1 * Ry θ2 * Rz θ3.
  Proof. lma. Qed.

  (** 13. Space-three, 123 *)
  Definition S3_123 : mat 3 3 :=
    l2m
      [[c2 * c3; s1 * s2 * c3 - s3 * c1; c1 * s2 * c3 + s3 * s1];
       [c2 * s3; s1 * s2 * s3 + c3 * c1; c1 * s2 * s3 - c3 * s1];
       [- s2; s1 * c2; c1 * c2]]%R.
                                                               
  Theorem S3_123_ok : S3_123 == Rz θ3 * Ry θ2 * Rx θ1.
  Proof. lma. Qed.

  (** 14. Space-three, 231 *)
  Definition S3_231 : mat 3 3 :=
    l2m
      [[c1 * c2; - s2; s1 * c2];
       [c1 * s2 * c3 + s3 * s1; c2 * c3; s1 * s2 * c3 - s3 * c1];
       [c1 * s2 * s3 - c3 * s1; c2 * s3; s1 * s2 * s3 + c3 * c1]]%R.
  
  Theorem S3_231_ok : S3_231 == Rx θ3 * Rz θ2 * Ry θ1.
  Proof. lma. Qed.

  (** 15. Space-three, 312 *)
  Definition S3_312 : mat 3 3 :=
    l2m
      [[s1 * s2 * s3 + c3 * c1; c1 * s2 * s3 - c3 * s1; c2 * s3];
       [s1 * c2; c1 * c2; - s2];
       [s1 * s2 * c3 - s3 * c1; c1 * s2 * c3 + s3 * s1; c2 * c3]]%R.
  
  Theorem S3_312_ok : S3_312 == Ry θ3 * Rx θ2 * Rz θ1.
  Proof. lma. Qed.

  (** 16. Space-three, 132 *)
  Definition S3_132 : mat 3 3 :=
    l2m
      [[c2 * c3; - c1 * s2 * c3 + s3 * s1; s1 * s2 * c3 + s3 * c1];
       [s2; c1 * c2; - s1 * c2];
       [- c2 * s3; c1 * s2 * s3 + c3 * s1; - s1 * s2 * s3 + c3 * c1]]%R.
  
  Theorem S3_132_ok : S3_132 == Ry θ3 * Rz θ2 * Rx θ1.
  Proof. lma. Qed.

  (** 17. Space-three, 213 *)
  Definition S3_213 : mat 3 3 :=
    l2m
      [[- s1 * s2 * s3 + c3 * c1; - c2 * s3; c1 * s2 * s3 + c3 * s1];
       [s1 * s2 * c3 + s3 * c1; c2 * c3; - c1 * s2 * c3 + s3 * s1];
       [- s1 * c2; s2; c1 * c2]]%R.
  
  Theorem S3_213_ok : S3_213 == Rz θ3 * Rx θ2 * Ry θ1.
  Proof. lma. Qed.

  (** 18. Space-three, 321 *)
  Definition S3_321 : mat 3 3 :=
    l2m
      [[c1 * c2; - s1 * c2; s2];
       [c1 * s2 * s3 + c3 * s1; - s1 * s2 * s3 + c3 * c1; - c2 * s3];
       [- c1 * s2 * c3 + s3 * s1; s1 * s2 * c3 + s3 * c1; c2 * c3]]%R.
        
  Theorem S3_321_ok : S3_321 == Rx θ3 * Ry θ2 * Rz θ1.
  Proof. lma. Qed.

  (** 19. Space-two, 121 *)
  Definition S2_121 : mat 3 3 :=
    l2m
      [[c2; s1 * s2; c1 * s2];
       [s2 * s3; - s1 * c2 * s3 + c3 * c1; - c1 * c2 * s3 - c3 * s1];
       [- s2 * c3; s1 * c2 * c3 + s3 * c1; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem S2_121_ok : S2_121 == Rx θ3 * Ry θ2 * Rx θ1.
  Proof. lma. Qed.

  (** 20. Space-two, 131 *)
  Definition S2_131 : mat 3 3 :=
    l2m
      [[c2; - c1 * s2; s1 * s2];
       [s2 * c3; c1 * c2 * c3 - s3 * s1; - s1 * c2 * c3 - s3 * c1];
       [s2 * s3; c1 * c2 * s3 + c3 * s1; - s1 * c2 * s3 + c3 * c1]]%R.
          
  Theorem S2_131_ok : S2_131 == Rx θ3 * Rz θ2 * Rx θ1.
  Proof. lma. Qed.

  (** 21. Space-two, 212 *)
  Definition S2_212 : mat 3 3 :=
    l2m
      [[- s1 * c2 * s3 + c3 * c1; s2 * s3; c1 * c2 * s3 + c3 * s1];
       [s1 * s2; c2; - c1 * s2];
       [-s1 * c2 * c3 - s3 * c1; s2 * c3; c1 * c2 * c3 - s3 * s1]]%R.
  
  Theorem S2_212_ok : S2_212 == Ry θ3 * Rx θ2 * Ry θ1.
  Proof. lma. Qed.

  (** 22. Space-two, 232 *)
  Definition S2_232 : mat 3 3 :=
    l2m
      [[c1 * c2 * c3 - s3 * s1; - s2 * c3; s1 * c2 * c3 + s3 * c1];
       [c1 * s2; c2; s1 * s2];
       [- c1 * c2 * s3 - c3 * s1; s2 * s3; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem S2_232_ok : S2_232 == Ry θ3 * Rz θ2 * Ry θ1.
  Proof. lma. Qed.

  (** 23. Space-two, 313 *)
  Definition S2_313 : mat 3 3 :=
    l2m
      [[- s1 * c2 * s3 + c3 * c1; - c1 * c2 * s3 - c3 * s1; s2 * s3];
       [s1 * c2 * c3 + s3 * c1; c1 * c2 * c3 - s3 * s1; - s2 * c3];
       [s1 * s2; c1 * s2; c2]]%R.
  
  Theorem S2_313_ok : S2_313 == Rz θ3 * Rx θ2 * Rz θ1.
  Proof. lma. Qed.

  (** 24. Space-two, 323 *)
  Definition S2_323 : mat 3 3 :=
    l2m
      [[c1 * c2 * c3 - s3 * s1; - s1 * c2 * c3 - s3 * c1; s2 * c3];
       [c1 * c2 * s3 + c3 * s1; - s1 * c2 * s3 + c3 * c1; s2 * s3];
       [-c1 * s2; s1 * s2; c2]]%R.
  
  Theorem S2_323_ok : S2_323 == Rz θ3 * Ry θ2 * Rz θ1.
  Proof. lma. Qed.

End EulerAngle24.


(** Convert Rotation Matrix to Euler angles *)
Module R2Euler.

  Open Scope R.
  
  (** 1. Body-three, 123 *)
  Module B3_123.

    (* 这是最弱的算法，只能求解小机动的值。更好的算法比较复杂，需要更多验证 *)
    Section r2euler.
      Variable C : mat 3 3.
      Definition θ1' := atan (- C.23 / C.33).
      Definition θ2' := asin (C.13).
      Definition θ3' := atan (- C.12 / C.11).

      Variable θ1 θ2 θ3 : R.
      Hypotheses θ1_range : - PI / 2 < θ1 < PI / 2.
      Hypotheses θ2_range : - PI / 2 < θ2 < PI / 2.
      Hypotheses θ3_range : - PI / 2 < θ3 < PI / 2.

      Lemma θ1_ok : C == B3_123 θ1 θ2 θ3 -> θ1' = θ1.
      Proof. intros; cbv; rewrite !H; auto; cbv; autorewrite with R; ra. Qed.

      Lemma θ2_ok : C == B3_123 θ1 θ2 θ3 -> θ2' = θ2.
      Proof. intros; cbv; rewrite !H; auto; cbv; autorewrite with R; ra. Qed.

      Lemma θ3_ok : C == B3_123 θ1 θ2 θ3 -> θ3' = θ3.
      Proof. intros; cbv; rewrite !H; auto; cbv; autorewrite with R; ra. Qed.
      
    End r2euler.

  End B3_123.

End R2Euler.

(** Skew-symmetric matrix of 3-dimensions *)
Section skew3.

  Open Scope R.

  (** Given matrix is skew-symmetric matrices *)
  (* Check cv3skewP. *)
  (* Check cv3skewP_spec. *)

  (** Convert a vector to its corresponding skew-symmetric matrix *)
  (* Check cv3skew. *)

  (** Convert a skew-symmetric matrix to its corresponding vector *)
  (* Check cv3skew2v. *)

  (* Check cv3skew_skew2v_id. *)
  (* Check cv3skew2v_skew_id. *)
  
End skew3.

(** Eliminate tail expressions, which ring tactic may not work *)
Ltac ring_tail :=
  rewrite !associative;
  repeat
    match goal with
    | |- (?a - ?b = ?c - ?b)%R => f_equal
    | |- (?a + ?b = ?c + ?b)%R => f_equal
    end;
  rewrite <- !associative.


(** * Axis-Angle *)
Module AxisAngle.

  Open Scope nat.
  (* Open Scope R_scope. *)
  Open Scope mat_scope.

  (** 推导一个绕任意轴 k̂ 旋转 θ 角度的矩阵 R(k̂,θ)，使得 v' = R(k̂,θ) * v *)
  Section derive_AxisAngleMatrix.

    (* Check rotAxisAngle. *)
    (* Check rotAxisAngle_spec. *)

    (** Also known as Rodrigues formula. *)
    (* Check rotAxisAngleMat. *)
    Definition Rrod := rotAxisAngleMat.

  End derive_AxisAngleMatrix.

  (** Rodrigues formula. *)
  Section Rodrigues.

    Local Open Scope fun_scope.
    
    (** Three basic rotation matrix are the special case of Rrod. *)
    Theorem Rrod_eq_Rx : forall θ : R, Rrod θ cv3i == Rx θ.
    Proof. lma. Qed.

    Theorem Rrod_eq_Ry : forall θ : R, Rrod θ cv3j == Ry θ.
    Proof. lma. Qed.

    Theorem Rrod_eq_Rz : forall θ : R, Rrod θ cv3k == Rz θ.
    Proof. lma. Qed.

    (** The matrix form of Rrod, so that the computer can directly calculate *)
    Definition RrodM (θ : R) (k : cvec 3) : mat 3 3 :=
      let x := k.1 in
      let y := k.2 in
      let z := k.3 in
      let C := cos θ in
      let S := sin θ in
      l2m
        [[C + x * x * (1 - C); x * y * (1 - C) - z * S; x * z * (1 - C) + y * S];
         [y * x * (1 - C) + z * S; C + y * y * (1 - C); y * z * (1 - C) - x * S];
         [z * x * (1 - C) - y * S; z * y * (1 - C) + x * S; C + z * z * (1 - C)]]%R.

    Theorem RrodM_eq : forall (θ : R) (k : cvec 3), cvunit k -> Rrod θ k == RrodM θ k.
    Proof.
      intros. lma.
      - pose proof (cv3unit_eq1 k H);
          cvec2fun; ring_simplify; ring_simplify in H0; rewrite H0; cbv; field.
      - pose proof (cv3unit_eq2 k H);
          cvec2fun; ring_simplify; ring_simplify in H0; rewrite H0; cbv; field.
      - pose proof (cv3unit_eq3 k H);
          cvec2fun; ring_simplify; ring_simplify in H0; rewrite H0; cbv; field.
    Qed.
    
  End Rodrigues.

End AxisAngle.
