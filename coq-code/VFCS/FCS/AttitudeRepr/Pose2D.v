(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Rotation in 2D space
  author    : ZhengPu Shi
  date      : Mar, 2023

  reference :
  1. Peter Corke, Robotics Vision and Control
  
  remark    :
  1. Specify positive direction
     In 2D, (when locking from your eyes to the screen (or paper) ), the 
     counterclockwise direction is defined as positive direction, which is 
     consistent with the usual angle definition.
  2. 旋转矩阵 R2 的说明
  (1) 列向量表示该新坐标系的坐标轴在参考坐标系中的单位向量
  (2) 主动旋转（即，同一个坐标系下，物体的向量在变化）时的旋转矩阵
  (3) 列向量和行向量的不同用法：
  a. 给一个在该坐标系下的列向量 v1，正向旋转该向量 θ 角得到新的向量 v1'，按如下公式
     v1' = R2(θ) * v1
     v1  = R2(θ)\T * v1'
  b. 给一个在该坐标系下的行向量 v2，正向旋转该向量 θ 角得到新的向量 v2'，按如下公式
     v2' = v2 * (R2(θ))\T
  c. 如果进行了连续两次旋转，即，先旋转θ1，然后在此基础上再旋转θ2，则
     按照列向量：v' = R(θ2) * R(θ1) * v，其中 R 是 R2
     按照行向量：v' = v * R(θ1) * R(θ2)，其中 R 是 R2\T
  3. R2的一些特性
  (1). pure rotation is commutative in 2D, but noncommutative in 3D
 *)

Require Export Math.
Require Export VectorR2.

Open Scope nat_scope.
Open Scope R_scope.
Open Scope vec_scope.
Open Scope mat_scope.

(**
   Naming convention:
   1. "o2n" means transformation from old vector to new vector.
   2. "n2o" means transformation from new vector to old vector.
*)


(* ======================================================================= *)
(** ** Rotation matrix in 2D *)

(** Rotation matrix in 2D *)
Definition R2 (theta : R) : smat 2 :=
  (mkmat_2_2
    (cos theta) (- sin theta)
    (sin theta) (cos theta))%R.


(** 从几何作图的角度来证明 R2 的正确性 *)
Module spec1.

  (* 二维向量执行旋转操作的转换矩阵。
     已知向量a=(ax,ay)，长度为l，与+x夹角为alpha，绕原点按正方向旋转beta角后
     得到b=(bx,by)，求出旋转矩阵Rab(beta),Rba(beta)，使得：
     b=R2(beta)a，
     a=R2'(beta)b.
   *)
  
  Lemma R2_spec : forall a (beta : R),
      let l := vlen a in
      let alpha := v2angle v2i a in
      let b_x := (l * cos (alpha + beta))%R in
      let b_y := (l * sin (alpha + beta))%R in
      let b : vec 2 := l2v [b_x;b_y] in
      a <> vzero -> b = cv2v (R2 beta * (v2cv a)).
  Proof.
    intros. unfold b,b_x,b_y. apply v2l_inj. rewrite v2l_l2v; auto.
    replace (v2l (cv2v (R2 beta * v2cv a)))
      with [a.x * (cos beta) + a.y * (- sin beta);
            a.x * (sin beta) + a.y * (cos beta)]%R.
    2:{ cbv. list_eq; Req. }
    list_eq.
    (* core work *)
    - rewrite cos_add. unfold alpha, Rminus, l. ring_simplify.
      rewrite v2len_mul_cos_v2angle_i; auto.
      rewrite v2len_mul_sin_v2angle_i; auto. lra.
    - rewrite sin_add. unfold alpha, l. ring_simplify.
      rewrite v2len_mul_cos_v2angle_i; auto.
      rewrite v2len_mul_sin_v2angle_i; auto. lra.
  Qed.
  
  Lemma R2'_spec : forall a (beta : R),
      let l := vlen a in
      let alpha := v2angle v2i a in
      let b_x := (l * cos (alpha + beta))%R in
      let b_y := (l * sin (alpha + beta))%R in
      let b : vec 2 := l2v [b_x;b_y] in
      a <> vzero -> a = cv2v ((R2 beta)\T * (v2cv b)).
  Proof.
    intros. unfold b,b_x,b_y. apply v2l_inj.
    replace (v2l a) with [a.x; a.y]; [|cbv; auto].
    replace (v2l
               (cv2v
                  ((R2 beta)\T *
                     v2cv (l2v [(l * cos (alpha + beta))%R;
                                (l * sin (alpha + beta))%R]))))
      with [
        (cos beta) * l * cos (alpha + beta) +
          (sin beta) * l * sin (alpha + beta);
        - (sin beta) * l * cos (alpha + beta) +
          (cos beta) * l * sin (alpha + beta)]%R.
    2:{ Local Opaque cos sin vlen v2angle. cbv; list_eq; Req. }
    (* core work *)
    (* Tips: `a.x` and `a.y` is A type, making `ring` will fail. *)
    remember ((a (nat2finS 0)) : R) as a_x.
    remember ((a (nat2finS 1)) : R) as a_y.
    rewrite cos_add, sin_add; unfold alpha, Rminus, l.
    list_eq.
    - ring_simplify. rewrite associative. rewrite v2len_mul_cos_v2angle_i; auto.
      rewrite cos2'. ra.
    - ring_simplify.
      replace ((||a||) * cos beta ^ 2 * sin (v2i /2_ a))%R
        with (cos beta ^ 2 * (||a|| * sin (v2i /2_ a)))%R; ra.
      rewrite associative. rewrite v2len_mul_sin_v2angle_i; auto.
      rewrite sin2'. ra.
  Qed.
End spec1.

(** 根据 RVC 书中 2.1.1.1 节的方法来证明 R2 的正确性 *)
Module spec2.
  Section sec_2_1_1_1.
    Variable pv : vec 2.        (* P点在 {V} 下的向量 *)
    Variable pb : vec 2.        (* P点在 {B} 下的向量 *)
    Hypotheses pv_eq_pb : pv = pb. (* P点在 {V} 和 {B} 下是同一个向量 *)
    
    Variable xv' yv' : vec 2.   (* 坐标系 {V} 的坐标轴x和y的单位向量 *)
    Hypotheses xv'yv'_orth : morth (cvl2m [xv';yv']). (* 确保 xv' 和 yv' 正交 *)
    Variable xv yv : R.         (* P点在 {V} 下以 {xv',yv'} 表示的坐标 *)
    Hypotheses Hpv : pv = (xv \.* xv' + yv \.* yv')%V.
    
    Variable xb' yb' : vec 2.   (* 坐标系 {B} 的坐标轴x和y的单位向量 *)
    Hypotheses xb'yb'_orth : morth (cvl2m [xb';yb']). (* 确保 xb' 和 yb' 正交 *)
    Variable xb yb : R.         (* P点在 {B} 下以 {xb',yb'} 表示的坐标 *)
    Hypotheses Hpb : pb = (xb \.* xb' + yb \.* yb')%V.
    
    Variable theta : R.         (* 坐标系{V}旋转该角度后到达{B} *)
    Hypotheses Hxb' :           (* 单位向量xb'可由角度θ和{xv,yv}表示 *)
      xb' = (cos theta \.* xv' + sin theta \.* yv')%V.
    Hypotheses Hyb' :           (* 单位向量yb'可由角度θ和{xv,yv}表示 *)
      yb' = ((- sin theta)%R \.* xv' + cos theta \.* yv')%V.

    (* pv的矩阵形式 *)
    Fact pvM : pv = cv2v (@cvl2m 2 2 [xv';yv'] * v2cv (l2v [xv;yv])).
    Proof. rewrite Hpv. veq; Req. Qed.
    
    (* pb的矩阵形式 *)
    Fact pbM : pb = cv2v (@cvl2m 2 2 [xb';yb'] * v2cv (l2v [xb;yb])).
    Proof. rewrite Hpb. veq; Req. Qed.
      
    (* Hxb' 和 Hyb' 组合起来的矩阵形式，公式(2.4) *)
    Fact xb'yb'M : cvl2m [xb';yb'] = (cvl2m [xv';yv']) * R2 theta.
    Proof. subst. meq; Req. Qed.
      
    (* pb改用{xv',yv'}的表达形式，公式(2.5) *)
    Fact pb_eq : pb = cv2v ((cvl2m [xv';yv'] * R2 theta) * (v2cv (l2v [xb;yb]))).
    Proof. rewrite pbM. f_equal. f_equal. apply xb'yb'M. Qed.
    
    (* 当坐标系{B}旋转theta角到达{V}时，{B}中的点(xb,yb)如何转换到{V}中 *)
    Theorem R2_spec : @l2v 2 [xv;yv] = cv2v (R2 theta * v2cv (l2v [xb;yb])).
    Proof.
      pose proof (pb_eq). rewrite <- pv_eq_pb in H.
      rewrite pvM in H. apply cv2v_inj in H.
      rewrite mmul_assoc in H. apply mmul_cancel_l in H.
      - apply v2cv_inj. rewrite v2cv_cv2v. auto.
      - apply morth_invertible; auto.
    Qed.
  End sec_2_1_1_1.
End spec2.

(** 预乘和后乘旋转矩阵的关系，即: u1 ~ u2 -> R * u1 ~ u2 * R\T *)
Lemma R2_pre_post : forall (u : vec 2) (θ : R),
    let u1 : cvec 2 := v2cv u in         (* u1是u的列向量形式 *)
    let u2 : rvec 2 := v2rv u in         (* u2是u的行向量形式 *)
    let v1 : cvec 2 := (R2 θ) * u1 in      (* v1是用列向量形式计算的结果 *)
    let v2 : rvec 2 := u2 * ((R2 θ)\T) in  (* v2是用行向量形式计算的结果 *)
    let v1' : vec 2 := cv2v v1 in           (* v1再转为普通向量 *)
    let v2' : vec 2 := rv2v v2 in           (* v2再转为普通向量 *)
    v1' = v2'. (* 结果应该相同 *)
Proof. intros. veq; Req. Qed.


(* ======================================================================= *)
(** ** Properties of R2 *)

(** R2 is orthogonal matrix *)
Lemma R2_orth : forall (θ : R), morth (R2 θ).
Proof. intros; meq; Req_more. Qed.

(** R2 is invertible *)
Lemma R2_invertible : forall (θ : R), minvertible (R2 θ).
Proof. intros. apply morth_invertible. apply R2_orth. Qed.

(** The determinant of R2 is 1 *)
Lemma R2_det1 : forall (θ : R), mdet (R2 θ) = 1.
Proof. intros; cbv; Req_more. Qed.

(** R2 is a member of SO2 *)
Definition R2_SO2 (θ : R) : SO2 :=
  Build_SOn (Build_GOn (R2 θ) (R2_orth _)) (R2_det1 _).

(** R(θ)\-1 = R(θ)\T *)
Lemma R2_inv_eq_trans : forall θ : R, (R2 θ)\-1 = (R2 θ)\T.
Proof.
  (* method 1 : prove by computing (slow) *)
  (* intros; meq; Req_more. *)
  (* method 2 : prove by reasoning *)
  intros; apply (SOn_inv_eq_trans (R2_SO2 θ)).
Qed.

(** R(-θ) = R(θ)\T *)
Lemma R2_neg_eq_trans : forall θ : R, R2 (-θ) = (R2 θ)\T.
Proof. intros; meq; Req_more. Qed.

(** R(-θ) * R(θ) = I *)
Lemma R2_neg_R2_inv : forall θ : R, R2 (- θ) * R2 θ = mat1.
Proof.
  intros; rewrite R2_neg_eq_trans, <- R2_inv_eq_trans, mmul_minv_l; auto.
  apply R2_invertible.
Qed.

(** R(θ) * R(-θ) = I *)
Lemma R2_R2_neg_inv : forall θ : R, R2 θ * R2 (- θ) = mat1.
Proof.
  intros; rewrite R2_neg_eq_trans, <- R2_inv_eq_trans, mmul_minv_r; auto.
  apply R2_invertible.
Qed.

(** R的乘法等价于对参数的加法: R(θ1) * R(θ2) = R(θ1 + θ2) *)
Lemma R2_mul_eq_add : forall (θ1 θ2 : R), (R2 θ1) * (R2 θ2) = R2 (θ1 + θ2).
Proof. intros; meq; Req_more. Qed.

(** R的乘法是交换的: R(θ1) * R(θ2) = R(θ2) * R(θ1) *)
Lemma R2_mul_comm : forall (θ1 θ2 : R), (R2 θ1) * (R2 θ2) = (R2 θ2) * (R2 θ1).
Proof. intros; meq; Req. Qed.


(* ======================================================================= *)
(** ** Skew-symmetric matrix in 2-dimensions *)
Section skew2.
  
  (** Equivalent form of skew2 *)
  Lemma skewP2_eq : forall M : smat 2,
      skewP M <->
      (M.11 = 0) /\ (M.22 = 0) /\ (M.12 = -M.21)%R.
  Proof.
    intros. split; intros.
    - hnf in H. assert (m2l (- M) = m2l (M\T)). rewrite H; auto.
      cbv in H0. list_eq. cbv in *. ra.
    - apply m2l_inj. cbv in *. list_eq; ra.
  Qed.

  (** Create a skew-symmetric matrix in 2D with a value *)
  Definition skew2 (a : R) : mat 2 2 := l2m [[0; -a];[a; 0]]%R.

  Lemma skew2_spec : forall a, skewP (skew2 a).
  Proof. intros. rewrite skewP2_eq. cbv. lra. Qed.

  (** Convert a skew-symmetric matrix in 2D to its corresponding value *)
  Definition vex2 (M : mat 2 2) : R := M.21.

  Lemma skew2_vex2 : forall (M : mat 2 2), skewP M -> skew2 (vex2 M) = M.
  Proof. intros. rewrite skewP2_eq in H. cbv in H. meq; ra. Qed.

  Lemma vex2_skew2 : forall (a : R), vex2 (skew2 a) = a.
  Proof. intros. cbv. auto. Qed.
End skew2.


(* ======================================================================= *)
(** ** Orientation in 2D *)
Section Orien2D.
  
  (* Give friendly name for user, avoiding low-level matrix operation.
     为了避免旋转矩阵使用错误，命名一些操作 *)
  
  (** 2D中主动旋转（即，坐标系不动，对象旋转）。
      对象在坐标系下的初始向量为v，旋转θ角后在该坐标系下的向量值 *)
  Definition Rot2A (θ : R) (v : vec 2) : vec 2 := cv2v ((R2 θ) * v2cv v).

  (** 旋转两次，等价于一次旋转两个角度之和: Rot(θ2,Rot(θ1,v)) = Rot(θ1+θ2,v) *)
  Lemma Rot2A_twice : forall (θ1 θ2 : R) (v : vec 2),
      Rot2A θ2 (Rot2A θ1 v) = Rot2A (θ1+θ2) v.
  Proof.
    intros. unfold Rot2A. rewrite v2cv_cv2v. rewrite <- mmul_assoc.
    rewrite R2_mul_eq_add. rewrite Rplus_comm. auto.
  Qed.

  (** 2D旋转时，旋转次序无关 *)
  Lemma Rot2A_any_order : forall (θ1 θ2 : R) (v : vec 2),
      Rot2A θ2 (Rot2A θ1 v) = Rot2A θ1 (Rot2A θ2 v).
  Proof. intros. rewrite !Rot2A_twice. f_equal. ring. Qed.
  
  (** 2D中被动旋转（即，对象不动，坐标系旋转）。
      对象在初始坐标系下的向量为v，坐标系旋转θ角后在，对象在新新坐标系下的向量值 *)
  Definition Rot2P (θ : R) (v : vec 2) : vec 2 := rv2v (v2rv v * (R2 θ)\T).

  (* 主动旋转等于被动旋转，为什么？*)
  Lemma Rot2A_eq_Rot2P : forall (θ : R) (v : vec 2), Rot2A θ v = Rot2P θ v.
  Proof. intros. veq; Req_more. Qed.

End Orien2D.


(* ======================================================================= *)
(** ** Pose in 2D *)
Section Pose2D.

  (** Special Euclidean Group of dimension 3: T ∈ SE(2) ⊂ R^(3x3) *)
  (* Record SE2 := { *)
  (*     SE2R :> mat 3 3; *)
  (*     _ : orthonormal2 SO2R *)
  (*   }. *)

  (** 2D homogeneous transformation, to represent relative pose *)
  Definition T2 (θ : R) (x y : R) : mat 3 3 :=
    l2m [[cos θ; - sin θ; x];
         [sin θ; cos θ; y];
         [0; 0; 1]]%R.

  (** create a relative pose with a finite translation but zero rotation *)
  Definition transl2 (P : vec 2) : mat 3 3 := T2 0 (P.1) (P.2).

  (** create a relative pose with a finite rotation but zero translation *)
  Definition trot2 (θ : angle) : mat 3 3 := T2 (angle_radian θ) 0 0.

  Example ex_T1 := transl2 (mkvec2 1 2) * trot2 (30 'deg).

  (** Convert Euclidean coordinates to homogeneous coordinates *)
  Definition e2h (v : vec 2) : vec 3 := mkvec3 (v.x) (v.y) 1.

  (** Convert homogeneous coordinates to Euclidean coordinates *)
  Definition h2e (v : vec 3) : vec 2 := mkvec2 (v.x/v.z) (v.y/v.z).
  
  (** A transformation to rotate about point C *)
  Definition trot2center (C : vec 2) (θ : angle) : mat 3 3 :=
    transl2 C * trot2 θ * transl2 (- C)%V.

End Pose2D.


