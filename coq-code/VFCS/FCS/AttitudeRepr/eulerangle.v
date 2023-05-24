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
  6. James Diebel, Representing Attitude: Euler Angles, Unit Quaternions, and 
     Rotation Vectors.

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
  1. 小角度变化经常被用来近似描述系统的动态特性，此时系统的响应可通过线性模型来预测和控制。
  2. 角度变化很小(通常认为10度以内)时，可线性化处理，
     sin(α)->α, cos(α)->1, 高阶项sin(α)*sin(β)->0
*)

Require Import Lra.
Require Import VectorR.
Require Import VectorR3.

Open Scope cvec_scope.

(* (* 手性：左手定、和右手定则 *) *)
(* Inductive HandRule := HRLeft | HRRight. *)

(* (* 变换类型：主动变换、被动变换 *) *)
(* Inductive Transformation := TActive | TPassive. *)

(* (* 旋转轴类型：绕机体轴的内旋、绕固定轴的外旋 *) *)
(* Inductive RotateMode := RMIntrinsic | RMExtrinsic. *)
                              

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

  (** 坐标变换的第一种解释：向量不动，坐标系变化。
      Ref: {Dibel - Representing}
      We define the rotation matrix that encodes the attitude of a rigid body to be 
      the matrix that when pre-multiplied by a vector expressed in the body-fixed 
      coordinates yields the same vector expressed in the word coordinates.
      That is, if v\in R^3 is a vector in the body-fixed coordinates and v'\in R^3 is 
      the same vector expressed in the word coordinates, then the following relations 
      hold:
            v' = R v
            v = R\T v'
      These expression apply to {vectors}, relative quantities lacking a position in 
      space. To transform a {point} from one coordinate system to other we must 
      subtract the offset to the origin of the target coordinate system before 
      applying the rotation matrix. *)
  
  (** 坐标变换的第二种解释：同一个坐标系，向量变化
      Orthogormal rotation matrices for rotation of θ aobout the x-,y- and z- axes.

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

  (** 这里的定义与 R3x,R3y,R3z 是一样的 *)
  Lemma Rx_spec : forall θ, Rx θ == R3x θ. Proof. lma. Qed.
  Lemma Ry_spec : forall θ, Ry θ == R3y θ. Proof. lma. Qed.
  Lemma Rz_spec : forall θ, Rz θ == R3z θ. Proof. lma. Qed.

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

  (** 关于0点的线性化 *)
  Section LinearizationCondition_at_Zero.
    Definition LinearizationCondition : Prop :=
      (s1 = θ1 /\ s2 = θ2 /\ s3 = θ3 /\
        c1 = 1 /\ c2 = 1 /\ c3 = 1 /\
         s1 * s2 = 0 /\ s1 * s3 = 0 /\ s2 * s3 = 0 /\
         s2 * s1 = 0 /\ s3 * s1 = 0 /\ s3 * s2 = 0)%R.
  End LinearizationCondition_at_Zero.

  (** 1. Body-three, 123 *)
  Definition B3_123 : mat 3 3 :=
    l2m
      [[c2 * c3; -c2 * s3; s2];
       [s1 * s2 * c3 + s3 * c1; - s1 * s2 * s3 + c3 * c1; - s1 * c2];
       [-c1 * s2 * c3 + s3 * s1; c1 * s2 * s3 + c3 * s1; c1 * c2]]%R.

  Theorem B3_123_ok : B3_123 == Rx θ1 * Ry θ2 * Rz θ3.
  Proof. lma. Qed.

  (* Linearation *)
  
  (* 这里只证明这一个例子，其余例子可以仿照此处做法 *)
  Definition B3_123_L : mat 3 3 :=
    l2m
      [[1; -θ3; θ2];
       [θ3; 1; -θ1];
       [-θ2; θ1; 1]]%R.

  Theorem B3_123_L_spec : LinearizationCondition -> B3_123 == B3_123_L.
  Proof.
    intros.
    destruct H as [Hs1 [Hs2 [Hs3 [Hc1 [Hc2 [Hc3 [H12 [H13 [H23 [H21 [H31 H32]]]]]]]]]]].
    unfold B3_123, B3_123_L.
    lma;
      (* 去掉 cos，并调整形式 *)
      rewrite ?Hc1,?Hc2,?Hc3; ring_simplify;
      (* 去掉 s * s *)
      rewrite ?H12,?H13,?H23,?H21,?H31,?H32; ring_simplify; try easy;
      (* 一步改写若能解决则执行 *)
      try (rewrite ?Hs1,?Hs2,?Hs3; reflexivity).
    (* 最后的都是因负号导致的重写失败 *)
    rewrite Rmult_assoc;
      rewrite ?H12,?H13,?H23,?H21,?H31,?H32; ring_simplify; try easy.
  Qed.
  

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

    (** 奇异性问题的存在性 *)
    Section singularity.

      (** Claim: If θ = kπ+π/2, then we can not uniquely determine ϕ and ψ. *)

      (* Let's prove some simpler goals first. *)

      (** If θ = -π/2, then the rotation matrix has following form. *)
      Lemma B3_123_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
          θ = -PI/2 ->
          B3_123 ϕ θ ψ ==
            l2m [[0; 0; -1];
                 [sin (ψ - ϕ); cos (ψ - ϕ); 0];
                 [cos (ψ - ϕ); - sin (ψ - ϕ); 0]].
      Proof.
        intros; rewrite H.
        lma; autounfold with T; autorewrite with R; auto; try field.
      Qed.
      
      (** If θ = π/2, then the rotation matrix has following form. *)
      Lemma B3_123_θ_eq_pi2 : forall (ϕ θ ψ : R),
          θ = PI/2 ->
          B3_123 ϕ θ ψ ==
            l2m [[0; 0; 1];
                 [sin (ϕ + ψ); cos (ϕ + ψ); 0];
                 [- cos (ϕ + ψ); sin (ϕ + ψ); 0]].
      Proof.
        intros; rewrite H.
        lma; autounfold with T; autorewrite with R; auto; try field.
      Qed.

      (** If θ = -π/2, then there are infinite ϕ can generate a same matrix. *)
      Theorem B3_123_singularity_ϕ_when_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
        θ = -PI/2 -> forall ϕ', (exists ψ', B3_123 ϕ' θ ψ' == B3_123 ϕ θ ψ).
      Proof.
        intros. eexists. rewrite !B3_123_θ_eq_pi2_neg; auto.
        lma. instantiate (1:=ψ - ϕ + ϕ'). all: f_equiv; try field. f_equiv. field.
      Qed.

      (** If θ = -π/2, then there are infinite ψ can generate a same matrix. *)
      Theorem B3_123_singularity_ψ_when_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
        θ = -PI/2 -> forall ψ', (exists ϕ', B3_123 ϕ' θ ψ' == B3_123 ϕ θ ψ).
      Proof.
        intros. eexists. rewrite !B3_123_θ_eq_pi2_neg; auto.
        lma. instantiate (1:=-ψ + ϕ + ψ'). all: f_equiv; try field. f_equiv. field.
      Qed.

      (** If θ = π/2, then there are infinite ϕ can generate a same matrix. *)
      Theorem B3_123_singularity_ϕ_when_θ_eq_pi2 : forall (ϕ θ ψ : R),
        θ = PI/2 -> forall ϕ', (exists ψ', B3_123 ϕ' θ ψ' == B3_123 ϕ θ ψ).
      Proof.
        intros. eexists. rewrite !B3_123_θ_eq_pi2; auto.
        lma. instantiate (1:=ψ + ϕ - ϕ'). all: f_equiv; try field. f_equiv. field.
      Qed.

      (** If θ = π/2, then there are infinite ψ can generate a same matrix. *)
      Theorem B3_123_singularity_ψ_when_θ_eq_pi2 : forall (ϕ θ ψ : R),
        θ = PI/2 -> forall ψ', (exists ϕ', B3_123 ϕ' θ ψ' == B3_123 ϕ θ ψ).
      Proof.
        intros. eexists. rewrite !B3_123_θ_eq_pi2; auto.
        lma. instantiate (1:=ψ + ϕ - ψ'). all: f_equiv; try field. f_equiv. field.
      Qed.
      
    End singularity.

    (* 算法1：避开奇异点，小机动范围，即 roll,pitch,yaw ∈ (-π/2,π/2) *)
    Module alg1.
      Section sec.
        (* Let's have a rotation matrix *)
        Variable C : smat 3.
        
        (* calculate the euler-angles *)
        Definition ϕ' := atan (- C.23 / C.33).
        Definition θ' := asin (C.13).
        Definition ψ' := atan (- C.12 / C.11).
        Definition euler_angles : cvec 3 := l2cv [ϕ'; θ'; ψ'].

        Lemma ϕ_spec : forall (ϕ θ ψ : R),
            - PI / 2 < ϕ < PI / 2 ->
            - PI / 2 < θ < PI / 2 ->
            - PI / 2 < ψ < PI / 2 ->
            C == B3_123 ϕ θ ψ -> ϕ' = ϕ.
        Proof. intros. cbv. rewrite !H2; auto. cbv. autorewrite with R; ra. Qed.

        Lemma θ_spec : forall (ϕ θ ψ : R),
            - PI / 2 < ϕ < PI / 2 ->
            - PI / 2 < θ < PI / 2 ->
            - PI / 2 < ψ < PI / 2 ->
            C == B3_123 ϕ θ ψ -> θ' = θ.
        Proof. intros. cbv. rewrite !H2; auto. cbv. autorewrite with R; ra. Qed.

        Lemma ψ_spec : forall (ϕ θ ψ : R),
            - PI / 2 < ϕ < PI / 2 ->
            - PI / 2 < θ < PI / 2 ->
            - PI / 2 < ψ < PI / 2 ->
            C == B3_123 ϕ θ ψ -> ψ' = ψ.
        Proof. intros. cbv. rewrite !H2; auto. cbv. autorewrite with R; ra. Qed.
      End sec.
      
    End alg1.

    (* 算法2：避开奇异点，大机动范围，即 pitch ∈ (-π/2,π/2), roll,yaw ∈ (-π,π) *)
    Module alg2.
      Section sec.
        (* Let's have a rotation matrix *)
        Variable C : smat 3.
        
        (* calculate the euler-angles *)
        Definition ϕ' := atan2 (- C.23) (C.33).
        Definition θ' := asin (C.13).
        Definition ψ' := atan2 (- C.12) (C.11).
        Definition euler_angles : cvec 3 := l2cv [ϕ'; θ'; ψ'].

        (** An equation about atan2 will be used in the later proof *)
        Lemma atan2_sin_cos_eq1 : forall a k : R,
            - PI < a < PI -> k > 0 ->
            atan2 (sin a * k) (cos a * k) = a.
        Proof.
          intros.
          apply Rsplit_neg_pi_to_pi in H.
          repeat match goal with | H: _ \/ _ |- _ => destruct H as [? | H] end; 
            subst; autorewrite with R.
          - rewrite atan2_spec5; ra.
          - rewrite atan2_spec1; ra.
            replace (0 / k) with 0; ra. apply atan_0.
          - rewrite atan2_spec4; ra.
          - assert (sin a < 0). { apply sin_lt_0_var; lra. }
            assert (cos a < 0).
            { rewrite <- RealFunction.cos_2PI_add. apply cos_lt_0; ra. }
            rewrite atan2_spec2; ra.
            rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw.
            rewrite <- Rtrigo_facts.tan_pi_plus; ra. rewrite atan_tan; ra.
          - assert (sin a < 0). { apply sin_lt_0_var; lra. }
            assert (0 < cos a). { apply cos_gt_0; ra. }
            rewrite atan2_spec1; ra.
            rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw. rewrite atan_tan; ra.
          - assert (0 < sin a). { apply sin_gt_0; lra. }
            assert (0 < cos a). { apply cos_gt_0; ra. }
            rewrite atan2_spec1; ra.
            rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw. rewrite atan_tan; ra.
          - assert (0 < sin a). { apply sin_gt_0; lra. }
            assert (cos a < 0). { apply cos_lt_0; ra. }
            rewrite atan2_spec3; ra.
            rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw.
            rewrite <- RealFunction.tan_sub_PI. rewrite atan_tan; ra.
        Qed.

        Lemma ϕ_spec : forall (ϕ θ ψ : R),
            - PI < ϕ < PI ->
            - PI / 2 < θ < PI / 2 ->
            - PI < ψ < PI ->
            C == B3_123 ϕ θ ψ -> ϕ' = ϕ.
        Proof.
          Opaque atan2.
          intros. cbv. rewrite !H2; auto. cbv. autorewrite with R.
          assert (0 < cos θ). { apply cos_gt_0; try lra. }
          (* atan2 (sin ϕ * cos θ) (cos ϕ * cos θ) = ϕ *)
          rewrite atan2_sin_cos_eq1; auto.
        Qed.

        Lemma θ_spec : forall (ϕ θ ψ : R),
            - PI < ϕ < PI ->
            - PI / 2 < θ < PI / 2 ->
            - PI < ψ < PI ->
            C == B3_123 ϕ θ ψ -> θ' = θ.
        Proof. intros; cbv. rewrite !H2; auto. cbv; autorewrite with R; ra. Qed.
        
        Lemma ψ_spec : forall (ϕ θ ψ : R),
            - PI < ϕ < PI ->
            - PI / 2 < θ < PI / 2 ->
            - PI < ψ < PI ->
            C == B3_123 ϕ θ ψ -> ψ' = ψ.
        Proof.
          Opaque atan2.
          intros. cbv. rewrite !H2; auto. cbv. autorewrite with R.
          assert (0 < cos θ). { apply cos_gt_0; try lra. }
          (* atan2 (cos θ * sin ψ) (cos θ * cos ψ) = ψ *)
          rewrite (Rmult_comm (cos θ)). rewrite (Rmult_comm (cos θ)).
          rewrite atan2_sin_cos_eq1; auto.
        Qed.
      End sec.
      
    End alg2.
      
    (* 算法2：保留奇异点，完整的机动范围，即 roll,pitch,yaw ∈ [-π,π] *)
    Module alg3.
      (* 该算法来自于 QQ's book, page94.
         1. 当θ=±π/2时(此时 r11=r21=0)，ϕ和ψ不唯一，可以人为规定 ϕ = 0
         2. 当ϕ,ψ为边界时，即当 r11=r33=1, r21=r31=r32=0, 有两种可能
            (ϕ,θ,ψ) = (0,0,0);(π,π,π)，此时根据与上次的值相近的结果
         3. 其余情况，可在 alg2 的基础上改进，以便θ从(-π/2,π/2)扩展到(-π,π)
            具体做法：
            (1) 计算出6个欧拉角，ϕ0,θ0,ψ0,ϕ1,θ1,ψ1，它们的组合有8种。
            (2) 计算这8种组合下的旋转矩阵与输入矩阵的差的范数（没有说是哪一种）
            (3) 范数最小时的那个组合就是所要求的欧拉角

         思考"步骤3"的原理：
         1. 为何旋转矩阵之差异矩阵的范数最小时对应了所需的欧拉角？
       *)
      
      (** sign of a real number *)
      Definition Rsign (r : R) : R := if r <? 0 then -1 else 1.
      
      Section sec.
        (* Let's have a rotation matrix *)
        Variable C : smat 3.

        (* (5.13) When r11=r21=0, this is the answer *)
        Definition case1_cond : bool := (C.11 =? 0) && (C.21 =? 0).

        (* ϕ, θ, ψ = v.1, v.2, v.3 *)
        Definition case1_values : cvec 3 :=
          l2cv [0; (Rsign (-C.31)) * (PI / 2); atan2 (-C.12) (C.22)].

        (* (5.15) possible euler angles *)
        
        (* 
           ϕ_0, θ_0, ψ_0 = m.11, m.21, m.31 
           ϕ_1, θ_1, ψ_1 = m.12, m.22, m.32 
         *)
        Definition case2_params : mat 3 2 :=
          let θ_0 := asin (-C.31) in
          l2m [[atan2 (C.32) (C.33); atan2 (-C.32) (-C.33)];
               [θ_0; Rsign θ_0 * PI - θ_0];
               [atan2 (C.21) (C.11); atan2 (-C.21) (-C.11)]].

        (* (5.14) best composition of euler angles *)
        Definition find_best : (R*R*R*R) :=
          let gen_val (ϕ θ ψ : R) : R*R*R*R := (ϕ, θ, ψ, mnormF (C - B3_123 ϕ θ ψ)%M) in
          let m := case2_params in
          let a111 := gen_val (m.11) (m.21) (m.31) in
          let a112 := gen_val (m.11) (m.21) (m.32) in
          let a121 := gen_val (m.11) (m.22) (m.31) in
          let a122 := gen_val (m.11) (m.22) (m.32) in
          let a211 := gen_val (m.12) (m.21) (m.31) in
          let a212 := gen_val (m.12) (m.21) (m.32) in
          let a221 := gen_val (m.12) (m.22) (m.31) in
          let a222 := gen_val (m.12) (m.22) (m.32) in
          let l := [a111;a112;a121;a122;a211;a212;a221;a222] in
          list_min a111
            (fun x y => match x, y with (_,_,_,x1),(_,_,_,y1) => x1 <? y1 end)
            l.

        Definition case2_values : cvec 3 :=
          let '(ϕ,θ,ψ,_) := find_best in
          l2cv [ϕ; θ; ψ].

        (** If the matrix is identity matrix, there are two possible solutions *)
        Definition case3_cond : bool :=
          (C.11 =? 1) && (C.33 =? 1) && (C.21 =? 0) && (C.32 =? 0) && (C.31 =? 0).
        
        Definition case3_opts : mat 3 2 :=
          l2m [[0; PI]; [0; PI]; [0; PI]].

        (** If the euler angles is option 1 or 2, then the matrix is identity matrix *)
        Lemma case3_opts_1_eq_mat1 :
          let ea := mcol case3_opts 0 in
          B3_123 (ea.1) (ea.2) (ea.3) == mat1.
        Proof. lma; autorewrite with R; easy. Qed.
        
        Lemma case3_opts_2_eq_mat1 :
          let ea := mcol case3_opts 1 in
          B3_123 (ea.1) (ea.2) (ea.3) == mat1.
        Proof. lma; autorewrite with R; cbv; ring. Qed.

        Definition case3_values (old : cvec 3) : cvec 3 :=
          (* 根据历史值，与之接近的是正解 *)
          let closest (old opt1 opt2 : R) : R :=
            if Rabs (old - opt1) <? Rabs (old - opt2) then opt1 else opt2 in
          let m := case3_opts in
          l2cv [
              closest (old.1) (m.11) (m.12);
              closest (old.2) (m.21) (m.22);
              closest (old.3) (m.31) (m.32)
            ].

        (** final algorithm *)
        Definition euler_angles (old : cvec 3) : cvec 3 :=
          if case1_cond
          then case1_values
          else if case3_cond
               then case3_values old
               else case2_values.

        (** This algorithm havn't been verified yet. *)
        
      End sec.
    End alg3.
    
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
