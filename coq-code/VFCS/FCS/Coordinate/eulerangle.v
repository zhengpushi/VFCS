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
*)

Require Import Lra.
Require Import VectorR.

Open Scope cvec_scope.


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

(* Hint Rewrite *)
(*   Rinv_r_simpl_l      (* (r2 * r1) * /r1 = r2 *) *)
(*   : R. *)


Section BasicRotationMatrics.
  
  (** Orthogormal rotation matrices for rotation of θ aobout 
     the x-,y- and z- axes *)
  Definition Rx (θ : R) : mat 3 3 :=
    l2m _ _
      [[1; 0; 0];
       [0; cos θ; - sin θ];
       [0; sin θ; cos θ]]%R.

  Definition Ry (θ : R) : mat 3 3 :=
    l2m _ _
      [[cos θ; 0; sin θ];
       [0; 1; 0];
       [- sin θ; 0; cos θ]]%R.

  Definition Rz (θ : R) : mat 3 3 :=
    l2m _ _
      [[cos θ; - sin θ; 0];
       [sin θ; cos θ; 0];
       [0; 0; 1]]%R.

  (* Fact Rx_inv : forall θ, minv (Rx θ) == (Rx θ)\T. *)
  (* Proof. lma; autorewrite with R; auto. Qed. *)

  (* Fact Ry_inv : forall θ, minv (Ry θ) == (Ry θ)\T. *)
  (* Proof. lma; autorewrite with R; auto. Qed. *)
  
  (* Fact Rz_inv : forall θ, minv (Rz θ) == (Rz θ)\T. *)
  (* Proof. lma; autorewrite with R; auto. Qed. *)

  Theorem Rx_neg : forall θ, Rx (-θ) == (Rx θ)\T.
  Proof. lma; autorewrite with R; auto. Qed.

  Theorem Ry_neg : forall θ, Ry (-θ) == (Ry θ)\T.
  Proof. lma; autorewrite with R; auto. Qed.
  
  Theorem Rz_neg : forall θ, Rz (-θ) == (Rz θ)\T.
  Proof. lma; autorewrite with R; auto. Qed.

End BasicRotationMatrics.


Section EulerAngle24.

  Variable θ1 θ2 θ3 : R.
  Notation c1 := (cos θ1). Notation s1 := (sin θ1).
  Notation c2 := (cos θ2). Notation s2 := (sin θ2).
  Notation c3 := (cos θ3). Notation s3 := (sin θ3).

  (** 1. Body-three, 123 *)
  Definition B3_123 : mat 3 3 :=
    l2m _ _
      [[c2 * c3; -c2 * s3; s2];
       [s1 * s2 * c3 + s3 * c1; - s1 * s2 * s3 + c3 * c1; - s1 * c2];
       [-c1 * s2 * c3 + s3 * s1; c1 * s2 * s3 + c3 * s1; c1 * c2]]%R.

  Theorem B3_123_ok : B3_123 == Rx θ1 * Ry θ2 * Rz θ3.
  Proof. lma. Qed.

  (** 2. Body-three, 231 *)
  Definition B3_231 : mat 3 3 :=
    l2m _ _
      [[c1 * c2; - c1 * s2 * c3 + s3 * s1; c1 * s2 * s3 + c3 * s1];
       [s2; c2 * c3; - c2 * s3];
       [- s1 * c2; s1 * s2 * c3 + s3 * c1; - s1 * s2 * s3 + c3 * c1]]%R.

  Theorem B3_231_ok : B3_231 == Ry θ1 * Rz θ2 * Rx θ3.
  Proof. lma. Qed.

  (** 3. Body-three, 312 *)
  Definition B3_312 : mat 3 3 :=
    l2m _ _
      [[- s1 * s2 * s3 + c3 * c1; - s1 * c2; s1 * s2 * c3 + s3 * c1];
       [c1 * s2 * s3 + c3 * s1; c1 * c2; - c1 * s2 * c3 + s3 * s1];
       [- c2 * s3; s2; c2 * c3]]%R.

  Theorem B3_312_ok : B3_312 == Rz θ1 * Rx θ2 * Ry θ3.
  Proof. lma. Qed.

  (** 4. Body-three, 132 *)
  Definition B3_132 : mat 3 3 :=
    l2m _ _
      [[c2 * c3; - s2; c2 * s3];
       [c1 * s2 * c3 + s3 * s1; c1 * c2; c1 * s2 * s3 - c3 * s1];
       [s1 * s2 * c3 - s3 * c1; s1 * c2; s1 * s2 * s3 + c3 * c1]]%R.

  Theorem B3_132_ok : B3_132 == Rx θ1 * Rz θ2 * Ry θ3.
  Proof. lma. Qed.

  (** 5. Body-three, 213 *)
  Definition B3_213 : mat 3 3 :=
    l2m _ _
      [[s1 * s2 * s3 + c3 * c1; s1 * s2 * c3 - s3 * c1; s1 * c2];
       [c2 * s3; c2 * c3; - s2];
       [c1 * s2 * s3 - c3 * s1; c1 * s2 * c3 + s3 * s1; c1 * c2]]%R.
        
  Theorem B3_213_ok : B3_213 == Ry θ1 * Rx θ2 * Rz θ3.
  Proof. lma. Qed.

  (** 6. Body-three, 321 *)
  Definition B3_321 : mat 3 3 :=
    l2m _ _
      [[c1 * c2; c1 * s2 * s3 - c3 * s1; c1 * s2 * c3 + s3 * s1];
       [s1 * c2; s1 * s2 * s3 + c3 * c1; s1 * s2 * c3 - s3 * c1];
       [- s2; c2 * s3; c2 * c3]]%R.
  
  Theorem B3_321_ok : B3_321 == Rz θ1 * Ry θ2 * Rx θ3.
  Proof. lma. Qed.

  (** 7. Body-two, 121 *)
  Definition B2_121 : mat 3 3 :=
    l2m _ _
      [[c2; s2 * s3; s2 * c3];
       [s1 * s2; - s1 * c2 * s3 + c3 * c1; - s1 * c2 * c3 - s3 * c1];
       [- c1 * s2; c1 * c2 * s3 + c3 * s1; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem B2_121_ok : B2_121 == Rx θ1 * Ry θ2 * Rx θ3.
  Proof. lma. Qed.
  
  (** 8. Body-two, 131 *)
  Definition B2_131 : mat 3 3 :=
    l2m _ _
      [[c2; - s2 * c3; s2 * s3];
       [c1 * s2; c1 * c2 * c3 - s3 * s1; - c1 * c2 * s3 - c3 * s1];
       [s1 * s2; s1 * c2 * c3 + s3 * c1; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem B2_131_ok : B2_131 == Rx θ1 * Rz θ2 * Rx θ3.
  Proof. lma. Qed.
  
  (** 9. Body-two, 212 *)
  Definition B2_212 : mat 3 3 :=
    l2m _ _
      [[- s1 * c2 * s3 + c3 * c1; s1 * s2; s1 * c2 * c3 + s3 * c1];
       [s2 * s3; c2; - s2 * c3];
       [- c1 * c2 * s3 - c3 * s1; c1 * s2; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem B2_212_ok : B2_212 == Ry θ1 * Rx θ2 * Ry θ3.
  Proof. lma. Qed.
  
  (** 10. Body-two, 232 *)
  Definition B2_232 : mat 3 3 :=
    l2m _ _
      [[c1 * c2 * c3 - s3 * s1; - c1 * s2; c1 * c2 * s3 + c3 * s1];
       [s2 * c3; c2; s2 * s3];
       [- s1 * c2 * c3 - s3 * c1; s1 * s2; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem B2_232_ok : B2_232 == Ry θ1 * Rz θ2 * Ry θ3.
  Proof. lma. Qed.
  
  (** 11. Body-two, 313 *)
  Definition B2_313 : mat 3 3 :=
    l2m _ _
      [[- s1 * c2 * s3 + c3 * c1; - s1 * c2 * c3 - s3 * c1; s1 * s2];
       [c1 * c2 * s3 + c3 * s1; c1 * c2 * c3 - s3 * s1; - c1 * s2];
       [s2 * s3; s2 * c3; c2]]%R.
  
  Theorem B2_313_ok : B2_313 == Rz θ1 * Rx θ2 * Rz θ3.
  Proof. lma. Qed.
  
  (** 12. Body-two, 323 *)
  Definition B2_323 : mat 3 3 :=
    l2m _ _
      [[c1 * c2 * c3 - s3 * s1; - c1 * c2 * s3 - c3 * s1; c1 * s2];
       [s1 * c2 * c3 + s3 * c1; - s1 * c2 * s3 + c3 * c1; s1 * s2];
       [- s2 * c3; s2 * s3; c2]]%R.
  
  Theorem B2_323_ok : B2_323 == Rz θ1 * Ry θ2 * Rz θ3.
  Proof. lma. Qed.

  (** 13. Space-three, 123 *)
  Definition S3_123 : mat 3 3 :=
    l2m _ _
      [[c2 * c3; s1 * s2 * c3 - s3 * c1; c1 * s2 * c3 + s3 * s1];
       [c2 * s3; s1 * s2 * s3 + c3 * c1; c1 * s2 * s3 - c3 * s1];
       [- s2; s1 * c2; c1 * c2]]%R.
                                                               
  Theorem S3_123_ok : S3_123 == Rz θ3 * Ry θ2 * Rx θ1.
  Proof. lma. Qed.

  (** 14. Space-three, 231 *)
  Definition S3_231 : mat 3 3 :=
    l2m _ _
      [[c1 * c2; - s2; s1 * c2];
       [c1 * s2 * c3 + s3 * s1; c2 * c3; s1 * s2 * c3 - s3 * c1];
       [c1 * s2 * s3 - c3 * s1; c2 * s3; s1 * s2 * s3 + c3 * c1]]%R.
  
  Theorem S3_231_ok : S3_231 == Rx θ3 * Rz θ2 * Ry θ1.
  Proof. lma. Qed.

  (** 15. Space-three, 312 *)
  Definition S3_312 : mat 3 3 :=
    l2m _ _
      [[s1 * s2 * s3 + c3 * c1; c1 * s2 * s3 - c3 * s1; c2 * s3];
       [s1 * c2; c1 * c2; - s2];
       [s1 * s2 * c3 - s3 * c1; c1 * s2 * c3 + s3 * s1; c2 * c3]]%R.
  
  Theorem S3_312_ok : S3_312 == Ry θ3 * Rx θ2 * Rz θ1.
  Proof. lma. Qed.

  (** 16. Space-three, 132 *)
  Definition S3_132 : mat 3 3 :=
    l2m _ _
      [[c2 * c3; - c1 * s2 * c3 + s3 * s1; s1 * s2 * c3 + s3 * c1];
       [s2; c1 * c2; - s1 * c2];
       [- c2 * s3; c1 * s2 * s3 + c3 * s1; - s1 * s2 * s3 + c3 * c1]]%R.
  
  Theorem S3_132_ok : S3_132 == Ry θ3 * Rz θ2 * Rx θ1.
  Proof. lma. Qed.

  (** 17. Space-three, 213 *)
  Definition S3_213 : mat 3 3 :=
    l2m _ _
      [[- s1 * s2 * s3 + c3 * c1; - c2 * s3; c1 * s2 * s3 + c3 * s1];
       [s1 * s2 * c3 + s3 * c1; c2 * c3; - c1 * s2 * c3 + s3 * s1];
       [- s1 * c2; s2; c1 * c2]]%R.
  
  Theorem S3_213_ok : S3_213 == Rz θ3 * Rx θ2 * Ry θ1.
  Proof. lma. Qed.

  (** 18. Space-three, 321 *)
  Definition S3_321 : mat 3 3 :=
    l2m _ _
      [[c1 * c2; - s1 * c2; s2];
       [c1 * s2 * s3 + c3 * s1; - s1 * s2 * s3 + c3 * c1; - c2 * s3];
       [- c1 * s2 * c3 + s3 * s1; s1 * s2 * c3 + s3 * c1; c2 * c3]]%R.
        
  Theorem S3_321_ok : S3_321 == Rx θ3 * Ry θ2 * Rz θ1.
  Proof. lma. Qed.

  (** 19. Space-two, 121 *)
  Definition S2_121 : mat 3 3 :=
    l2m _ _
      [[c2; s1 * s2; c1 * s2];
       [s2 * s3; - s1 * c2 * s3 + c3 * c1; - c1 * c2 * s3 - c3 * s1];
       [- s2 * c3; s1 * c2 * c3 + s3 * c1; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem S2_121_ok : S2_121 == Rx θ3 * Ry θ2 * Rx θ1.
  Proof. lma. Qed.

  (** 20. Space-two, 131 *)
  Definition S2_131 : mat 3 3 :=
    l2m _ _
      [[c2; - c1 * s2; s1 * s2];
       [s2 * c3; c1 * c2 * c3 - s3 * s1; - s1 * c2 * c3 - s3 * c1];
       [s2 * s3; c1 * c2 * s3 + c3 * s1; - s1 * c2 * s3 + c3 * c1]]%R.
          
  Theorem S2_131_ok : S2_131 == Rx θ3 * Rz θ2 * Rx θ1.
  Proof. lma. Qed.

  (** 21. Space-two, 212 *)
  Definition S2_212 : mat 3 3 :=
    l2m _ _
      [[- s1 * c2 * s3 + c3 * c1; s2 * s3; c1 * c2 * s3 + c3 * s1];
       [s1 * s2; c2; - c1 * s2];
       [-s1 * c2 * c3 - s3 * c1; s2 * c3; c1 * c2 * c3 - s3 * s1]]%R.
  
  Theorem S2_212_ok : S2_212 == Ry θ3 * Rx θ2 * Ry θ1.
  Proof. lma. Qed.

  (** 22. Space-two, 232 *)
  Definition S2_232 : mat 3 3 :=
    l2m _ _
      [[c1 * c2 * c3 - s3 * s1; - s2 * c3; s1 * c2 * c3 + s3 * c1];
       [c1 * s2; c2; s1 * s2];
       [- c1 * c2 * s3 - c3 * s1; s2 * s3; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem S2_232_ok : S2_232 == Ry θ3 * Rz θ2 * Ry θ1.
  Proof. lma. Qed.

  (** 23. Space-two, 313 *)
  Definition S2_313 : mat 3 3 :=
    l2m _ _
      [[- s1 * c2 * s3 + c3 * c1; - c1 * c2 * s3 - c3 * s1; s2 * s3];
       [s1 * c2 * c3 + s3 * c1; c1 * c2 * c3 - s3 * s1; - s2 * c3];
       [s1 * s2; c1 * s2; c2]]%R.
  
  Theorem S2_313_ok : S2_313 == Rz θ3 * Rx θ2 * Rz θ1.
  Proof. lma. Qed.

  (** 24. Space-two, 323 *)
  Definition S2_323 : mat 3 3 :=
    l2m _ _
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
  Definition is_skew3 (m : mat 3 3) : Prop := (- m)%M == m\T.

  Lemma is_skew3_spec : forall m : mat 3 3,
      is_skew3 m ->
      m.11 = 0 /\ m.22 = 0 /\ m.33 = 0 /\ m.12 = -m.21 /\ m.13 = -m.31 /\ m.23 = -m.32.
  Proof.
    intros. destruct m as [m]; simpl in *. cbv in H. split_intro.
    - epose proof (H 0 0 _ _)%nat. ra.
    - epose proof (H 1 1 _ _)%nat. ra.
    - epose proof (H 2 2 _ _)%nat. ra.
    - epose proof (H 0 1 _ _)%nat. ra.
    - epose proof (H 0 2 _ _)%nat. ra.
    - epose proof (H 1 2 _ _)%nat. ra.
      Unshelve. all: ra.
  Qed.

  (** Convert a vector to its corresponding skew-symmetric matrix *)
  Definition skew3 (v : cvec 3) : mat 3 3 :=
    let x := v.1 in
    let y := v.2 in
    let z := v.3 in
    l2m _ _ [[0; -z; y]; [z; 0; -x]; [-y; x; 0]].

  (** Convert a skew-symmetric matrix to its corresponding vector *)
  Definition vex3 (m : mat 3 3) : cvec 3 := l2cv 3 [m.32; m.13; m.21].

  Lemma skew3_vex3_id : forall (m : mat 3 3), is_skew3 m -> skew3 (vex3 m) == m.
  Proof.
    intros [m]. intros.
    apply is_skew3_spec in H. simpl in *. do 5 destruct H as [? H].
    lma. ra.
  Qed.

  Lemma vex3_skew3_id : forall (v : cvec 3), vex3 (skew3 v) == v.
  Proof.
    intros. cvec_to_fun. cbv. intros.
    assert (j = 0%nat) by lia. rewrite H1.
    destruct i; try easy.
    destruct i; try easy.
    destruct i; try easy. lia.
  Qed.
  
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

  (** Rodrigues' rotation formula *)
  Section Rodrigues.

    (** 最简的数学形式，要求 k 是单位向量，如不是则请先单位化 *)
    Definition Rrod (θ : R) (k : cvec 3) : mat 3 3 :=
      let K := skew3 k in
      mat1 + sin θ c* K + (1 - cos θ) c* (K * K).

    (** Three basic rotation matrix are the special case of Rrod. *)
    Theorem Rrod_eq_Rx : forall θ : R, Rrod θ v3i == Rx θ.
    Proof. lma. Qed.

    Theorem Rrod_eq_Ry : forall θ : R, Rrod θ v3j == Ry θ.
    Proof. lma. Qed.

    Theorem Rrod_eq_Rz : forall θ : R, Rrod θ v3k == Rz θ.
    Proof. lma. Qed.

    (** 最初的一种带有向量作用效果的表达式，请确保 k 是单位向量 *)
    Definition Rrodv (θ : R) (k : cvec 3) (v : cvec 3) : cvec 3 :=
      v *c cos θ + (cv3cross k v) *c sin θ + k *c (k ⋅ v) *c (1 - cos θ).

    (* Theorem Rrodv_eq : forall θ k v, cvunit k -> Rrodv θ k v == (Rrod θ k) * v. *)
    (* Proof. *)
    (*   lma; *)
    (*     cvec_to_fun; cbv in *; autorewrite with R in *; ring_simplify; ring_tail; *)
    (*     autorewrite with R in *; ring_simplify; *)
    (*     replace (k`00 ²) with (1 - k`10² - k`20²)%R by lra; field. *)
    (* Qed. *)

    (** The matrix form of Rrod, so that the computer can directly calculate *)
    Definition RrodM (θ : R) (k : cvec 3) : mat 3 3 :=
      let x := k.1 in
      let y := k.2 in
      let z := k.3 in
      let C := cos θ in
      let S := sin θ in
      l2m _ _
        [[C + x * x * (1 - C); x * y * (1 - C) - z * S; x * z * (1 - C) + y * S];
         [y * x * (1 - C) + z * S; C + y * y * (1 - C); y * z * (1 - C) - x * S];
         [z * x * (1 - C) - y * S; z * y * (1 - C) + x * S; C + z * z * (1 - C)]]%R.

    Theorem RrodM_eq : forall (θ : R) (k : cvec 3), cvunit k -> Rrod θ k == RrodM θ k.
    Proof.
      lma; cvec_to_fun; cbv in *; autorewrite with R in *;
        replace (k`00 ²) with (1 - k`10² - k`20²)%R by lra; field.
    Qed.

    (** Derivation of Rrod *)
    Section Rrod_derivation.

      (* Let k be a unit vector defining a rotation axis *)
      Variable k : cvec 3.
      Hypotheses kunit : cvunit k.

      (* , and let v be any vector to rotate about k by angle θ (right hand rule, 
         anticlockwise) *)
      Variable θ : R.
      Variable v : cvec 3.

      (** The scalar projection of a on b is a scalar defined here, where θ is
          the angle between a and b *)
      Definition vsproj {n} (a b : cvec n) := a ⋅ cvnormalize b.

      (** The scalar projection of a on b is a simple triangle relation *) ?
      Lemma vsproj_spec : forall {n} (a b : cvec n), vsproj a b = `|a| * cvangle.
      
      (** The vector projection of a on b is a vector whose magnitude is the scalar 
          projection of a on b
      Definition vproj {n} (a b : cvec n)

      (** The component parallel to k is called the vector projection of v on k *)
      Definition v1 := (v ⋅ k) c* k.
      (** The component perpendicular to k is called the vector rejection of v on k *)
      Definition v2 := v - v1 (v ⋅ k) c* k.
                   
      

      
      

    End Rrod_derivation.
    
    
  End Rodrigues.
  

End AxisAngle.



(** * Convert a angle between degree and radian *)
Module Export Angle.

  Inductive AngleKind := Radian | Degree.

  Definition deg2rad (d : R) : R := d * PI / 180.
  Definition rad2deg (r : R) : R := r * 180 / PI.

  Record angle := {
      angle_radian : R;
      angle_degree : R
    }.
  
  Definition mk_angle_deg (d : R) : angle :=
    Build_angle (deg2rad d) d.

  Definition mk_angle_rad (r : R) : angle :=
    Build_angle r (rad2deg r).

  Notation "r 'rad" := (mk_angle_rad r) (at level 30).
  Notation "d 'deg" := (mk_angle_deg d) (at level 30).

  Goal 180 'deg = PI 'rad.
    cbv. f_equal; field. ra. Qed.

End Angle.

?






(** Calculate engenvalues and eigenvectors of a matrix.
    if [x,e] = eig(R), then:
    the eigenvalues are returned on the diagonal of the matrix e,
    and the corresponding eigenvectors are the corresponding columns of x *)
Parameter eig : forall {n : nat} (m : matR n n), matC n n * matC n n.
  

(** A matrix is orthonormal:
 1. each column is a unit vector
 2. the columns are orthogonal *)
(* Definition orthogonal {r c} (m : mat r c) :=?. *)
(* Definition orthonormal {n} (m : smat n) :=?. *)

(** Two vectors are orthogonal *)
Definition cvorthogonal {n} (v1 v2 : cvec n) := (v1 ⋅ v2 == A0)%A.

(** * Orientation in 2-Dimensions *)
Module SO2.

  (** A 2D square matrix is orthonormal *)
  Definition orthonormal2 (m : smat 2) :=
    let c0 := mat2col m 0 in
    let c1 := mat2col m 1 in
    cvunit c0 /\ cvunit c1 /\ (cvorthogonal c0 c1).


  (** Special Orthogonal Group of dimension 2: R ∈ SO(2) ⊂ R^(2x2) *)
  Record SO2 := {
      SO2R :> mat 2 2;
      _ : orthonormal2 SO2R
    }.

  Definition SO2_mul (a b : SO2) : SO2.
    destruct a as [a [a1 [a2 a3]]].
    destruct b as [b [b1 [b2 b3]]].
    refine (Build_SO2 (a * b) _).
    split_intro.
    - Admitted.
  
  (* Fact Group_SO2 : Group SO2_mul. *)

  (** 2D rotation matrix *)
  Section rot2.
    (*  列向量表示该新坐标系的坐标轴在参考坐标系中的单位向量 *)
    Definition R (θ : R) : mat 2 2 :=
      l2m _ _
        [[cos θ; - sin θ];
         [sin θ; cos θ]]%R.

    (** Note that: pure rotation is commutative in 2D, but noncommutative in 3D *)
    
    (** Create a rotation matrix of dimension 2 *)
    Definition rot2 (θ : angle) : mat 2 2 := R (angle_radian θ).

    Lemma rot2_orthonormal : forall θ, orthonormal2 (rot2 θ).
    Proof. intros. cbv. split_intro; autorewrite with R; ra. Qed.

    Lemma rot2_det1 : forall θ, det (rot2 θ) = 1.
    Proof. intros. cbv. autorewrite with R. auto. Qed.

    Lemma rot2_inv_eq_trans : forall θ, minv2 (rot2 θ) == (rot2 θ)\T.
    Proof. lma; rewrite det2_eq_det, rot2_det1; ra. Qed.
  End rot2.

  (** Skew-symmetric matrix of 2-dimensions *)
  Section skew.
    (** Given matrix is skew-symmetric matrices *)
    Definition is_skew (m : mat 2 2) : Prop := (- m)%M == m\T.

    Lemma is_skew_spec : forall m : mat 2 2,
        is_skew m -> let '((a11,a12),(a21,a22)) := m2t_2_2 m in
                     (a11 = 0) /\ (a22 = 0) /\ (a12 = -a21)%A.
    Proof.
      intros. destruct m as [m]; simpl in *. cbv in H. split_intro.
      - epose proof (H 0 0 _ _)%nat. ra.
      - epose proof (H 1 1 _ _)%nat. ra.
      - epose proof (H 0 1 _ _)%nat. ra.
        Unshelve. all: ra.
    Qed.

    (** Convert a value to its corresponding skew-symmetric matrix *)
    Definition skew (a : A) : mat 2 2 := l2m _ _ [[0; -a];[a; 0]]%R.

    (** Convert a skew-symmetric matrix to its corresponding value *)
    Definition vex (m : mat 2 2) : option A := Some (m $ 1 $ 0).

    Lemma skew_vex_id : forall (m : mat 2 2), is_skew m -> 
                                         match vex m with
                                         | Some a => skew a == m
                                         | _ => False
                                         end.
    Proof. intros [m]. simpl. intros. apply is_skew_spec in H. lma. Qed.

    Lemma vex_skew_id : forall (a : A), vex (skew a) = Some a.
    Proof. intros. cbv. auto. Qed.
  End skew.

End SO2.


(** * Pose in 2-Dimensions *)
Module SE2.

  (* Compute m2l (mappr (@mat1 3) (@mat1 3)).  *)
  (* Compute m2l (mappc (@mat1 3) (@mat1 3)).  *)

  (** Special Euclidean Group of dimension 3: T ∈ SE(2) ⊂ R^(3x3) *)
  (* Record SE2 := { *)
  (*     SE2R :> mat 3 3; *)
  (*     _ : orthonormal2 SO2R *)
  (*   }. *)

  (** 2D homogeneous transformation, to represent relative pose *)
  Definition T (θ : R) (x y : R) : mat 3 3 :=
    l2m _ _
      [[cos θ; - sin θ; x];
       [sin θ; cos θ; y];
       [0; 0; 1]]%R.

  (** create a relative pose with a finite translation but zero rotation *)
  Definition transl2 (P : cvec 2) : mat 3 3 := T 0 (P$0) (P$1).

  (** create a relative pose with a finite rotation but zero translation *)
  Definition trot2 (θ : angle) : mat 3 3 := T (angle_radian θ) 0 0.

  Example ex_T1 := transl2 (mk_cvec2 1 2) * trot2(30 'deg).

  (** Convert Euclidean coordinates to homogeneous coordinates *)
  Definition e2h (v : cvec 2) : cvec 3 :=
    let '(a0,a1) := cv2t_2 v in
    mk_cvec3 a0 a1 1.

  (** Convert homogeneous coordinates to Euclidean coordinates *)
  Definition h2e (v : cvec 3) : cvec 2 :=
    let '(a0,a1,a2) := cv2t_3 v in
    mk_cvec2 (a0/a2) (a1/a2).

  (** A transformation to rotate about point C *)
  Definition trot2center (C : cvec 2) (θ : angle) : mat 3 3 :=
    transl2 C * trot2 θ * transl2 (-C).

End SE2.


(** * Orientation in 3-Dimensions *)
Module SO3.

  (** A 3D square matrix is orthonormal *)
  Definition orthonormal3 (m : smat 3) :=
    let c0 := mat2col m 0 in
    let c1 := mat2col m 1 in
    let c2 := mat2col m 2 in
    cvunit c0 /\ cvunit c1 /\ cvunit c2 /\
      (cvorthogonal c0 c1) /\
      (cvorthogonal c0 c2) /\
      (cvorthogonal c1 c2).

  (** Special Orthogonal Group of dimension 3: R ∈ SO(3) ⊂ R^(3x3) *)
  Record SO3 := {
      SO3R :> mat 3 3;
      _ : orthonormal3 SO3R
    }.
  

  (* Orthogormal rotation matrices for rotation of θ aobout 
     the x-,y- and z- axes *)
  Definition Rx (θ : R) : mat 3 3 :=
    l2m _ _
      [[1; 0; 0];
       [0; cos θ; - sin θ];
       [0; sin θ; cos θ]]%R.

  Definition Ry (θ : R) : mat 3 3 :=
    l2m _ _
      [[cos θ; 0; sin θ];
       [0; 1; 0];
       [- sin θ; 0; cos θ]]%R.

  Definition Rz (θ : R) : mat 3 3 :=
    l2m _ _
      [[cos θ; - sin θ; 0];
       [sin θ; cos θ; 0];
       [0; 0; 1]]%R.

  Lemma Rx_orthonormal : forall θ, orthonormal3 (Rx θ).
  Proof. intros. cbv. split_intro; autorewrite with R; ra. Qed.

  Lemma Rx_det1 : forall θ, det (Rx θ) = 1.
  Proof. intros. cbv. autorewrite with R. auto. Qed.

  Lemma Rx_inv_eq_trans : forall θ, minv3 (Rx θ) == (Rx θ)\T.
  Proof. lma; try rewrite det3_eq_det, Rx_det1; ra. autorewrite with R; ra. Qed.

  (** Create a rotation matrix of dimension 3 about the x-axis *)
  Definition rotx (θ : angle) : mat 3 3 := Rx (angle_radian θ).

  (** Create a rotation matrix of dimension 3 about the y-axis *)
  Definition roty (θ : angle) : mat 3 3 := Ry (angle_radian θ).

  (** Create a rotation matrix of dimension 3 about the z-axis *)
  Definition rotz (θ : angle) : mat 3 3 := Rz (angle_radian θ).

  Example ex1 : rotx((PI/2) 'rad) * roty((PI/2) 'rad) ==
                  l2m 3 3 [[0;0;1];[1;0;0];[0;1;0]].
  Proof. lma; try autorewrite with R; ra. Qed.

  Example ex2 : roty((PI/2) 'rad) * rotx((PI/2) 'rad) ==
                  l2m 3 3 [[0;1;0];[0;0;-1];[-1;0;0]].
  Proof. lma; try autorewrite with R; ra. Qed.

  
  (** ** The angle representations *)

  (** 欧拉定理要求对三个轴的相继旋转，并且相邻两次使用不同的轴。有两种类型的旋转顺序：
      (1) Eulerian: 有重复，但不是相继的重复。包括：XYX,XZX,YXY,YZY,ZXZ,ZYZ
      (2) Cardanian: 没有重复。XYZ,XZY,YXZ,YZX,ZXY,ZYX
      共有12种类型。
      实际的顺序在特定技术领域有不同的惯例。
      (1) ZYZ, 航空和机械力学中，也是toolbox的顺序。欧拉角是3D向量 Γ=(ϕ,θ,ψ).
      (2) Cardan angles: roll, pitch, yaw. 
          教科书上有两个版本，取决于是否有移动机器人:
          (a) ZYX: 描述车辆的姿态，例如轮船，飞机，汽车。
              x轴指向前进方向；z轴向上或向下。
              yaw是行进方向，pitch是头部关于水平方向的抬升，roll是关于前进轴的旋转。
              Roll-pitch-yaw angles also known as Tait-Bryan angles or nautical angles,
              and for aeronautical application they can be called bank, attitude and 
              heading angles respectively.
          (b) XYZ: 描述机械手的姿态。
              z轴指向前进方向；x轴向上或向下。
          这种方式使得所有的角都可以有任意的符号，当θ_pitch = ±π/2 时发生奇异。
      (3) 用于航天器导航的机械陀螺仪，使用 Cardanian YZX 顺序。
          x轴指向向上的推力轴，z轴指向前面，y轴指向右侧。
   *)

  Module EulerAngle24.

  End EulerAngle24.

  Module ZYZ.

    Definition R (ϕ θ ψ : R) : mat 3 3 := Rz ϕ * Ry θ * Rz ψ.
    
    (** Convert Euler angles to equivalent rotation matrix. *)
    Definition eul2r (Γ : cvec 3) : mat 3 3 :=
      let ϕ := Γ$0 in
      let θ := Γ$1 in
      let ψ := Γ$2 in
      R ϕ θ ψ.

    (** If θ = 0, then ϕ and ψ can not be uniquely decided *)
    (* The author's convension choice is : let ϕ = 0 *)
    Lemma R_theta0 : forall (ϕ θ ψ : Real), θ = 0 -> R ϕ θ ψ == Rz (ϕ + ψ).
    Proof. lma; rewrite H; autorewrite with R; ra. Qed.

    (** Convert rotation matrix to equivalent Euler angles. *)
    (* Definition r2eul (m : mat 3 3) : cvec 3 := ? *)

  End ZYZ.

  Module ZYX.

    Definition R (roll pitch yaw : Real) : mat 3 3 := Rz yaw * Ry pitch * Rx roll.

    Definition rpy2r (roll pitch yaw : Real) : mat 3 3 := R yaw pitch roll.

    (* Definition r2rpy (m : mat 3 3) : cvec 3. *)

  End ZYX.

  Module XYZ.

    Definition R (roll pitch yaw : Real) : mat 3 3 := Rx yaw * Ry pitch * Rz roll.

    Definition rpy2r (roll pitch yaw : Real) : mat 3 3 := R yaw pitch roll.
    
    (* Definition r2rpy (m : mat 3 3) : cvec 3. *)
  End XYZ.

  Module YZX.

    Definition R (roll pitch yaw : Real) : mat 3 3 := Ry pitch * Rz roll * Rx yaw.

    (** If θ_roll = ±π/2, then {pitch,yaw} can not be uniquely decided *)
    Lemma R_roll_pi2 : forall (roll pitch yaw : Real),
        (* (roll = PI/2 \/ roll = - PI/2) -> *)
        (roll = PI/2) ->
        R roll pitch yaw == Rz (PI/2) * Rx (pitch + yaw).
    Proof. lma;
             (* destruct H as [H | H]; *)
             rewrite H; autorewrite with R; ra; try easy.
    Qed.
    (** 丢失了一个自由度，在数学上意味着我们无法反转这个变换，只能建立两个角的线性关系 *)
    (** 本例中，我们只能得到pitch和yaw这两个角的和。*)

  End YZX.

  (** 奇异性问题：在所有三个角的表示中都有y这样的问题。
      问题发生的条件：当两个相继的轴变得对齐时 ？？
      对于 ZYZ Euler angles: 当θ=kπ, k∈Z 时
      对于 roll-pitch-yaw angles：当 pitch = ±(2k+1)π/2 时
      
      作者建议：精心的选择坐标系和角度顺序，使得交通工具的正常操作中不发生奇异
      参考全权老师的书中的算法：应该能够避免奇异性问题i。
   *)
  Section Singularities.

    (** Rotations obey the cyclic rotation rules *)
    Lemma Ry_Rz : forall θ, Rx (PI/2) * Ry θ * (Rx (PI/2))\T == Rz θ.
    Proof. lma; autorewrite with R; ra. Qed.

    Lemma Rz_Rx : forall θ, Ry (PI/2) * Rz θ * (Ry (PI/2))\T == Rx θ.
    Proof. lma; autorewrite with R; ra. Qed.

    Lemma Rx_Ry : forall θ, Rz (PI/2) * Rx θ * (Rz (PI/2))\T == Ry θ.
    Proof. lma; autorewrite with R; ra. Qed.

    (** Rotations obey the anti-cyclic rotation rules *)
    Lemma Rz_Ry : forall θ, (Rx (PI/2))\T * Rz θ * Rx (PI/2) == Ry θ.
    Proof. lma; autorewrite with R; ra. Qed.

    Lemma Rx_Rz : forall θ, (Ry (PI/2))\T * Rx θ * Ry (PI/2) == Rz θ.
    Proof. lma; autorewrite with R; ra. Qed.

    Lemma Ry_Rx : forall θ, (Rz (PI/2))\T * Ry θ * Rz (PI/2) == Rx θ.
    Proof. lma; autorewrite with R; ra. Qed.

  End Singularities.

  (** Skew-symmetric matrix of 3-dimensions *)
  Section skew.
    
    (** Given matrix is skew-symmetric matrices *)
    Definition is_skew (m : mat 3 3) : Prop := (- m)%M == m\T.

    Lemma is_skew_spec : forall m : mat 3 3,
        is_skew m ->
        let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := m2t_3_3 m in
        (a11 = 0) /\ (a22 = 0) /\ (a33 = 0) /\
          (a12 = -a21)%A /\ (a13 = -a31)%A /\ (a23 = -a32)%A.
    Proof.
      intros. destruct m as [m]; simpl in *. cbv in H. split_intro.
      - epose proof (H 0 0 _ _)%nat. ra.
      - epose proof (H 1 1 _ _)%nat. ra.
      - epose proof (H 2 2 _ _)%nat. ra.
      - epose proof (H 0 1 _ _)%nat. ra.
      - epose proof (H 0 2 _ _)%nat. ra.
      - epose proof (H 1 2 _ _)%nat. ra.
        Unshelve. all: ra.
    Qed.

    (** Convert a vector to its corresponding skew-symmetric matrix *)
    Definition skew (v : cvec 3) : mat 3 3 :=
      let x := v$0 in
      let y := v$1 in
      let z := v$2 in
      l2m _ _ [[0; -z; y]; [z; 0; -x]; [-y; x; 0]]%R.

    (** Convert a skew-symmetric matrix to its corresponding vector *)
    Definition vex (m : mat 3 3) : option (cvec 3) :=
      Some (l2cv 3 [m$2$1; m$0$2; m$1$00]).

    Lemma skew_vex_id : forall (m : mat 3 3), is_skew m -> 
                                         match vex m with
                                         | Some v => skew v == m
                                         | _ => False
                                         end.
    Proof.
      intros [m]. simpl. intros. apply is_skew_spec in H.
      do 5 destruct H as [? H]. lma. ra.
    Qed.

    Lemma vex_skew_id : forall (v : cvec 3),
        match vex (skew v) with
        | Some v' => v == v'
        | _ => False
        end.
    Proof.
      intros. cvec_to_fun. cbv. intros.
      assert (j = 0%nat) by lia. rewrite H1.
      destruct i; try easy.
      destruct i; try easy.
      destruct i; try easy. lia.
    Qed.
    
  End skew.


  (** Rotation about an Arbitrary Vector *)
  Section Rotation_about_arbitrary_vector.

    (** The eigenvalue and eigenvectors of an orthonormal rotation matrix always have 
        one real eigenvalue at λ = 1, and a complex pair λ = cos θ ± i * sin θ where
        θ is the rotation angle. *)
    (* Hypotheses eig_of_SO3 : forall (m : mat 3 3), *)
    (*     orthonormal2 m -> *)
    (*     let (x,e) := eig m in *)
    (*     ? *)

    (** determine an angle and some axis (a vector) of a orthonormal rotation matrix *)
    Definition r2angvec (m : mat 3 3) : R * cvec 3 :=
      (* The eigenvalues are returned on the diagonal of the matrix e,
         and the corresponding eigenvectors are the corresponding columns of x *)
      let (x,e) := eig m in
      (* e(idx,idx) = cosθ +i sinθ *)
      let theta_of_idx (idx : nat) := atan ((e $ idx $ idx).b / (e $ idx $ idx).a) in
      (* the idx-th column of x contain the needed vector, which is the real part *)
      let vec_of_idx (idx : nat) := cvecC_to_cvecR (mat2col x idx) (fun c => c.a) in
      (* find the angle and the vector *)
      if x$0$0 ==? 1
      then (theta_of_idx 1%nat, vec_of_idx 0%nat)
      else (if x$1$1 ==? 1
            then (theta_of_idx 2%nat, vec_of_idx 1%nat)
            else (theta_of_idx 1%nat, vec_of_idx 2%nat)).

    (** Converting from angle and a unit vector to a rotation matrix, 
        i.e. Rodrigues' rotation formula. *)
    Definition angvec2r (θ : R) (axis : cvec 3) : mat 3 3 :=
      let ssm := skew axis in
      (mat1 + (sin θ) c* ssm + (1 - cos θ) c* (ssm * ssm))%M.

  End Rotation_about_arbitrary_vector.

  (** Unit Quaternions *)
  Section UnitQuaternion.

    (** rotation matrix to unit quaternion *)
    (* Definition r2q *)
    Parameter r2q : mat 3 3 -> quat.

    (** unit quaternion to rotation matrix *)
    Parameter q2r : quat -> mat 3 3.

  End UnitQuaternion.

End SO3.
