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
  2. 本文的约定：使用列向量，以及预乘。
  3. 旋转操作rot2和rot2'的构成，及其理解。
  (1) 列向量由该旋转后的坐标系的坐标轴在原来参考坐标系中的单位向量构成。
      可以利用线性表示来帮助理解：
      * 矩阵R=[x̂,ŷ]，列向量v=[v.x,v.y]^T，而 R*v = v.x*x̂ + v.y*ŷ，表示了某向量
        用坐标轴单位向量及其坐标的线性组合。
  4. 旋转矩阵的3个用途
  (1) 可表示两个坐标系的相对朝向。
      坐标系{0}旋转θ1到坐标系{1}，则坐标系{1}相对于{0}的朝向是 R(0->1) = rot2(θ1)；
      坐标系{1}旋转θ2到坐标系{2}，则坐标系{2}相对于{1}的朝向是 R(1->2) = rot2(θ2)；
      此时，坐标系{2}相对于坐标系{0}的朝向是 R(0->2) = R(0->1) * R(1->2)
  (2) 可用于计算：在同一个坐标系下向量主动旋转导致的坐标变化。
      在一个坐标系中，某向量的坐标是v，该向量旋转 θ 角后的坐标为 v'，则
      v' = rot2(θ) * v
      v  = rot2(θ)\T * v'
      通俗的说：
            A点旋转后的世界坐标 = 旋转矩阵 * A点旋转前的世界坐标
  (3) 可用于计算：由于坐标系的旋转而导致同一个向量被动旋转时的坐标。
      坐标系{0}旋转 θ 角至坐标系{1}，某向量在{0} 和 {1}下的坐标分别是 v0 和 v1，则
      v0 = rot2(θ) * v1          其中，rot2(θ) 表示 {1} 相对于 {0} 的旋转矩阵。
      v1 = rot2(θ)\T * v0
      通俗的说：
            由于坐标系的旋转相当于“向量主动旋转”的逆过程。因此，
            A点变换后的摄像机坐标 = 旋转矩阵的逆 * A点变换前的世界坐标。所以，
            A点变换前的世界坐标 = 旋转矩阵 * A点变换后的摄像机坐标。
      用更流行的上下标记号：假设某矢量X在坐标系{B}中的坐标为(X)^B，在坐标系{A}中的坐标为
      (X)^A，而坐标系{B}相对于{A}的旋转矩阵为 R_B^A，那么这三者之间满足如下关系：
            (X)^A = R_B^A * (X)^B
  5. 其他说明
  (1) pure rotation is commutative in 2D, making the sequence is not important.
      but noncommutative in 3D. But when working on pose (rotation + translation), 
      the operation is not commutative
  (2) 如果进行了连续两次旋转，即，先旋转θ1，然后在此基础上再旋转θ2，则
      总的相对位姿是 R(θ2) * R(θ1)，或者 R(θ1) * R(θ2)
 *)

Require Export Math.
Require Export VectorR2.

Open Scope nat_scope.
Open Scope R_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ########################################################################### *)
(** * Preliminary math *)

(** Transformation by SOn matrix will keep v2cross. *)
Lemma SOn_keep_v2cross : forall (M : smat 2) (u v : vec 2),
    SOnP M -> (cv2v (M * v2cv u)) \x (cv2v (M * v2cv v)) = u \x v.
Proof.
  intros. cbv. ring_simplify.
  assert (M.11 * M.22 - M.12 * M.21 = 1)%R.
  { destruct H as [Horth Hdet1]. cbv in Hdet1. ring_simplify in Hdet1. cbv. lra. }
  assert (M.11 * u.1 * M.22 * v.2 - M.11 * u.2 * v.1 * M.22 -
            u.1 * M.12 * M.21 * v.2 + M.12 * u.2 * M.21 * v.1 =
            (u.1 * v.2 - u.2 * v.1) * (M.11 * M.22 - M.12 * M.21))%R. lra.
  assert (M.11 * u.1 * M.22 * v.2 - M.11 * u.2 * v.1 * M.22 -
            u.1 * M.12 * M.21 * v.2 + M.12 * u.2 * M.21 * v.1 =
            u.1 * v.2 - u.2 * v.1)%R; auto.
  rewrite H1. rewrite H0. lra.
Qed.

(** Transformation by SOn matrix will keep v2angle. *)
Lemma SOn_keep_v2angle : forall (M : smat 2) (u v : vec 2),
    SOnP M -> (cv2v (M * v2cv u)) /2_ (cv2v (M * v2cv v)) = u /2_ v.
Proof.
  intros. unfold v2angle.
  pose proof (SOn_keep_v2cross M u v H).
  destruct H as [Horth Hdet1]. pose proof (morth_keep_angle M u v Horth).
  rewrite H0. rewrite H. auto.
Qed.

(* (** <col(m1,i), col(m2,j)> = (m1\T * m2)[i,j] *) *)
(* Lemma vdot_col_col : forall {n} (m : smat n) i j, *)
(*     <mcol m i, mcol m j> = (m\T * m) $ i $ j. *)
(* Proof. intros. apply seqsum_eq. intros; auto. Qed. *)

(* (** <row(m1,i), row(m2,j)> = (m1 * m2\T)[i,j] *) *)
(* Lemma vdot_row_row : forall {n} (m : smat n) i j, *)
(*     <mrow m i, mrow m j> = (m * m\T) $ i $ j. *)
(* Proof. intros. apply seqsum_eq. intros; auto. Qed. *)

(* ======================================================================= *)
(** ** Skew-symmetric matrix in 2-dimensions *)
Section skew2.
  
  (** Equivalent form of skewP of 2D vector *)
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


(* ########################################################################### *)
(** * Rotation matrix in 2D *)

(* ======================================================================= *)
(** ** Definition of 2D rotation matrix *)

(** 创建一个2D旋转矩阵。说明：
   1. 该矩阵是标准正交的，即行向量相互正交，列向量相互正交，并且长度都是1.
   2. 其列向量是旋转后的坐标系的坐标轴关于原坐标系的单位向量
   3. 它属于SO(2)，这表明任意两个这样的矩阵相乘，以及逆都在SO(2)中。
   4. 行列式是1，这表明，一个向量被变换后其长度不改变。
   5. 逆矩阵是其转置。
   6. 该矩阵的四个元素并不独立，实际上只有一个参数theta。这是非最小表示的一个例子，
      缺点是占用更多存储空间，优点是可组合性(composability)
   7. 如何使用该矩阵来变换向量？见 rot2
 *)
Definition R2 (theta : R) : smat 2 :=
  (mkmat_2_2
     (cos theta) (- sin theta)
     (sin theta) (cos theta))%R.


(* ======================================================================= *)
(** ** Properties of 2D rotation matrix *)

Section R2.
  (** R2 is orthogonal matrix *)
  Lemma R2_orth : forall (θ : R), morth (R2 θ).
  Proof. intros; meq; Req_more. Qed.

  (** The determinant of R2 is 1 *)
  Lemma R2_det1 : forall (θ : R), mdet (R2 θ) = 1.
  Proof. intros; cbv; Req_more. Qed.

  (** R2 satisfies SOnP *)
  Lemma R2_SOnP : forall (θ : R), SOnP (R2 θ).
  Proof. intros. hnf. split. apply R2_orth. apply R2_det1. Qed.
  
  (** R2 is a member of SO2 *)
  Definition R2_SO2 (θ : R) : SO2 := mkSOn (R2 θ) (R2_SOnP θ).

  (** R2 is invertible *)
  Lemma R2_invertible : forall (θ : R), minvertible (R2 θ).
  Proof. intros. apply morth_invertible. apply R2_orth. Qed.

  (** R(θ)\-1 = R(θ)\T *)
  Lemma R2_inv_eq_trans : forall θ : R, (R2 θ)\-1 = (R2 θ)\T.
  Proof.
    (* method 1 : prove by computing (slow) *)
    (* intros; meq; Req_more. *)
    (* method 2 : prove by reasoning *)
    intros; apply (SOn_inv_eq_trans (R2_SO2 θ)).
  Qed.

  (** R(θ) * R(θ)\-1 = I *)
  Lemma R2_mul_R2_inv : forall θ : R, R2 θ * ((R2 θ)\-1) = mat1.
  Proof. intros. apply mmul_minv_r. apply R2_invertible. Qed.

  (** R(θ)\-1 * R(θ) = I *)
  Lemma R2_inv_mul_R2 : forall θ : R, (R2 θ)\-1 * (R2 θ) = mat1.
  Proof. intros. apply mmul_minv_l. apply R2_invertible. Qed.

  (** R(θ) * R(θ)\T = I *)
  Lemma R2_mul_R2_trans : forall θ : R, R2 θ * ((R2 θ)\T) = mat1.
  Proof. intros. rewrite <- R2_inv_eq_trans. apply R2_mul_R2_inv. Qed.

  (** R(θ)\T * R(θ) = I *)
  Lemma R2_trans_mul_R2 : forall θ : R, (R2 θ)\T * (R2 θ) = mat1.
  Proof. intros. rewrite <- R2_inv_eq_trans. apply R2_inv_mul_R2. Qed.
  
  (** R(θ1) * R(θ2) = R(θ1 + θ2) *)
  Lemma R2_mul_eq_add : forall (θ1 θ2 : R), (R2 θ1) * (R2 θ2) = R2 (θ1 + θ2).
  Proof. intros; meq; Req_more. Qed.

  (** R(θ1) * R(θ2) = R(θ2) * R(θ1) *)
  Lemma R2_mul_comm : forall (θ1 θ2 : R), (R2 θ1) * (R2 θ2) = (R2 θ2) * (R2 θ1).
  Proof. intros; meq; Req. Qed.
  
End R2.

Section R2_neg.
  
  (** R(-θ) = R(θ)\-1 *)
  Lemma R2_neg_eq_inv : forall θ : R, R2 (-θ) = (R2 θ)\-1.
  Proof. intros; meq; Req_more. Qed.

  (** R(-θ) = R(θ)\T *)
  Lemma R2_neg_eq_trans : forall θ : R, R2 (-θ) = (R2 θ)\T.
  Proof. intros; meq; Req_more. Qed.
  
End R2_neg.


(* ########################################################################### *)
(** * Orientation in 2D (rotation) *)

(* ======================================================================= *)
(** ** Definition of 2D rotation operations *)

?
(** create a relative pose with a finite rotation *)
Definition rot2 (theta : R) : smat 2 := (R2 theta).

Definition rot2' (theta : R) (v : vec 2) : vec 2 := cv2v ((R2 theta)\T * (v2cv v)).

(* ======================================================================= *)
(** ** Specifications for 2D rotation operations *)

(** 规范1：证明在同一个坐标系下向量旋转前后的坐标变化 *)
Section spec1.

  (* 命题：
     任意二维平面中的非零点P，给定某坐标系{0:OXY}，向量OP在{0}下的坐标为a，
     当将OP绕正方向旋转theta角后到达OP'，OP'在{0}下的坐标为b，证明：
     b = rot2(theta,a) 以及  a = rot2'(theta,b) *)

  Context (a : vec 2). (* 任给OP在{0}下的坐标a *)
  Context (theta : R). (* 任给旋转角theta *)
  Hypotheses Hneq0 : a <> vzero. (* 假定OP是非零向量 *)
  Let l := ||a||.        (* OP的长度 *)
  Let alpha := v2i /2_ a.       (* x轴正方向到OP的角度, [0, 2PI) *)
  Let b_x := (l * cos (alpha + theta))%R.   (* OP'的横坐标 *)
  Let b_y := (l * sin (alpha + theta))%R.   (* OP'的纵坐标 *)
  Let b : vec 2 := l2v [b_x;b_y].           (* OP'的坐标 *)

  Lemma rot2_spec1 : b = rot2 theta a.
  Proof.
    (* convert the equality of matrix to element-wise equalities *)
    intros. unfold b,b_x,b_y,rot2. apply v2l_inj. rewrite v2l_l2v; auto.
    replace (v2l (cv2v (R2 theta * v2cv a)))
      with [a.x * (cos theta) + a.y * (- sin theta);
            a.x * (sin theta) + a.y * (cos theta)]%R.
    2:{ cbv. list_eq; Req. } list_eq.
    (* proof equality of element *)
    - rewrite cos_add. unfold alpha, Rminus, l. ring_simplify.
      rewrite v2len_mul_cos_v2angle_i; auto.
      rewrite v2len_mul_sin_v2angle_i; auto. lra.
    - rewrite sin_add. unfold alpha, l. ring_simplify.
      rewrite v2len_mul_cos_v2angle_i; auto.
      rewrite v2len_mul_sin_v2angle_i; auto. lra.
  Qed.

  Lemma rot2'_spec1 : a = rot2' theta b.
  Proof.
    (* convert the equality of matrix to element-wise equalities *)
    intros. unfold b,b_x,b_y,rot2'. apply v2l_inj.
    replace (v2l a) with [a.x; a.y]; [|cbv; auto].
    replace (v2l
               (cv2v
                  ((R2 theta)\T *
                     v2cv (l2v [(l * cos (alpha + theta))%R;
                                (l * sin (alpha + theta))%R]))))
      with [
        (cos theta) * l * cos (alpha + theta) +
          (sin theta) * l * sin (alpha + theta);
        - (sin theta) * l * cos (alpha + theta) +
          (cos theta) * l * sin (alpha + theta)]%R.
    2:{ Local Opaque cos sin vlen v2angle. cbv; list_eq; Req. } list_eq.
    (* proof equality of element *)
    - (* Tips: `a.x` and `a.y` is A type, making `ring` will fail. *)
      remember ((a (nat2finS 0)) : R) as a_x.
      rewrite cos_add, sin_add; unfold alpha, Rminus, l. ring_simplify.
      rewrite associative. rewrite v2len_mul_cos_v2angle_i; auto.
      rewrite cos2'. ra.
    - remember ((a (nat2finS 1)) : R) as a_y.
      rewrite cos_add, sin_add; unfold alpha, Rminus, l. ring_simplify.
      replace ((||a||) * cos theta ^ 2 * sin (v2i /2_ a))%R
        with (cos theta ^ 2 * (||a|| * sin (v2i /2_ a)))%R; ra.
      rewrite associative. rewrite v2len_mul_sin_v2angle_i; auto.
      rewrite sin2'. ra.
  Qed.
End spec1.

(** 规范1：证明坐标系旋转前后(即，两个坐标系)时同一个向量的坐标变化 *)
Section method2.
  (* 参考了 RVC 书中 2.1.1.1 节的方法 *)

  (* 命题：
     任意二维平面中的原点重合的两个坐标系{V}和{B}，{V}旋转theta后到达{B}而来，
     任意向量 OP 在 {V} 和 {B} 下的坐标分别为 v 和 b，证明：
     v = rot2(theta,b) 以及  b = rot2'(theta,v) *)
  
    Variable xv' yv' : vec 2.   (* 坐标系 {V} 的坐标轴单位向量 *)
    Hypotheses xv'yv'_orth : morth (cvl2m [xv';yv']). (* {V}的坐标轴是正交的 *)
    Variable xb' yb' : vec 2.   (* 坐标系 {B} 的坐标轴单位向量 *)
    Hypotheses xb'yb'_orth : morth (cvl2m [xb';yb']). (* {B}的坐标轴是正交的 *)
    Variable theta : R.         (* 坐标系{V}旋转theta角后到{B} *)
    Hypotheses Hxb' :           (* xb'由 theta 和 {xv,yv} 表示 *)
      xb' = (cos theta \.* xv' + sin theta \.* yv')%V.
    Hypotheses Hyb' :           (* yb'由 theta 和 {xv,yv} 表示 *)
      yb' = ((- sin theta)%R \.* xv' + cos theta \.* yv')%V.
    
    Variable p : vec 2.         (* 任意P点 *)
    Variable v : vec 2.         (* P点在 {V} 下的坐标 *)
    Variable b : vec 2.         (* P点在 {B} 下坐标 *)
    Hypotheses Hpv : p = (v.x \.* xv' + v.y \.* yv')%V. (* P点在{V}中的表示 *)
    Hypotheses Hpb : p = (b.x \.* xb' + b.y \.* yb')%V. (* P点在{B}中的表示 *)

    (* Hxb' 和 Hyb' 的矩阵形式，公式(2.4) *)
    Fact Hxb'Hyb' : cvl2m [xb';yb'] = (cvl2m [xv';yv']) * R2 theta.
    Proof. subst. meq; Req. Qed.
    
    (* Hxv' 和 Hyv' 的矩阵形式 *)
    Fact Hxv'Hyv' : @cvl2m 2 2 [xv';yv'] = (cvl2m [xb';yb']) * (R2 theta)\T.
    Proof.
      assert (cvl2m [xb'; yb'] * (R2 theta)\T =
                cvl2m [xv'; yv'] * R2 theta * (R2 theta)\T).
      { rewrite Hxb'Hyb'. auto. }
      rewrite mmul_assoc in H. rewrite R2_mul_R2_trans, mmul_1_r in H. auto.
    Qed.

    (* Hpv 的矩阵形式 *)
    Fact HpvM : p = cv2v (@cvl2m 2 2 [xv';yv'] * v2cv v).
    Proof. rewrite Hpv. veq; Req. Qed.
    
    (* Hpb 的矩阵形式 *)
    Fact HpbM : p = cv2v (@cvl2m 2 2 [xb';yb'] * v2cv b).
    Proof. rewrite Hpb. veq; Req. Qed.
      
    (* p 用 {xv',yv'} 和 b 的矩阵乘法表示，公式(2.5) *)
    Fact p_v_b : p = cv2v ((cvl2m [xv';yv'] * R2 theta) * v2cv b).
    Proof. rewrite HpbM. f_equal. f_equal. apply Hxb'Hyb'. Qed.
      
    (* p 用 {xb',yb'} 和 v 的矩阵乘法表示 *)
    Fact p_b_v : p = cv2v ((cvl2m [xb';yb'] * (R2 theta)\T) * v2cv v).
    Proof. rewrite HpvM. f_equal. f_equal. apply Hxv'Hyv'. Qed.
    
    Lemma rot2_spec2 : v = rot2 theta b.
    Proof.
      unfold rot2.
      assert (cv2v (@cvl2m 2 2 [xv';yv'] * v2cv v) =
                cv2v ((cvl2m [xv';yv'] * R2 theta) * v2cv b)).
      { rewrite <- HpvM. rewrite <- p_v_b. auto. }
      apply cv2v_inj in H. rewrite mmul_assoc in H. apply mmul_cancel_l in H.
      - apply v2cv_inj. rewrite v2cv_cv2v. auto.
      - apply morth_invertible; auto.
    Qed.
    
    Lemma rot2'_spec2 : b = rot2' theta v.
    Proof.
      unfold rot2'.
      assert (cv2v (@cvl2m 2 2 [xb';yb'] * v2cv b) =
                cv2v ((cvl2m [xb';yb'] * (R2 theta)\T) * v2cv v)).
      { rewrite <- HpbM. rewrite <- p_b_v. auto. }
      apply cv2v_inj in H. rewrite mmul_assoc in H. apply mmul_cancel_l in H.
      - apply v2cv_inj. rewrite v2cv_cv2v. auto.
      - apply morth_invertible; auto.
    Qed.
End method2.


(* ======================================================================= *)
(** ** Properties for 2D rotation operations *)

(** 旋转两次，等价于一次旋转两个角度之和: Rot(θ2,Rot(θ1,v)) = Rot(θ1+θ2,v) *)
Lemma rot2_twice : forall (θ1 θ2 : R) (v : vec 2),
    rot2 θ2 (rot2 θ1 v) = rot2 (θ1+θ2) v.
Proof.
  intros. unfold rot2. rewrite v2cv_cv2v. rewrite <- mmul_assoc.
  rewrite R2_mul_eq_add. rewrite Rplus_comm. auto.
Qed.

(** 2D旋转时，旋转次序无关 *)
Lemma rot2_any_order : forall (θ1 θ2 : R) (v : vec 2),
    rot2 θ2 (rot2 θ1 v) = rot2 θ1 (rot2 θ2 v).
Proof. intros. rewrite !rot2_twice. f_equal. ring. Qed.


(* ########################################################################### *)
(** * Pose in 2D *)

(* ======================================================================= *)
(** ** Definition of 2D rotation operations *)

(** Convert Euclidean coordinates to homogeneous coordinates *)
Definition e2h (v : vec 2) : vec 3 := mkvec3 (v.x) (v.y) 1.

(** Convert homogeneous coordinates to Euclidean coordinates *)
Definition h2e (v : vec 3) : vec 2 := mkvec2 (v.x/v.z) (v.y/v.z).

Lemma h2e_e2h : forall (v : vec 2), h2e (e2h v) = v.
Proof. intros. veq; Req. Qed.

Lemma e2h_h2e : forall (v : vec 3), v.z = 1 -> e2h (h2e v) = v.
Proof. intros. cbv in H. veq; rewrite H; Req. Qed.

(** 2D homogeneous transformation. It represents translation and orientation,
    or relative pose. This is oftern referred to as a rigid-body motion. *)
(* T2 ∈ SE(2) ⊂ R^(3x3), SE: special Euclidean group *)

(* 坐标系{0} 先平移 t，再旋转 θ 后的相对位姿 *)
Definition T2 (θ : R) (t : vec 2) : mat 3 3 :=
  l2m [[cos θ; - sin θ; t.x];
       [sin θ; cos θ;   t.y];
       [0;     0;       1  ]]%R.

(* Notes:
   1. 相对位姿可用3个参数(t.x, t.y, θ)，或齐次矩阵 T2 来表示 
   2. 由于平移和旋转操作不可交换，所以我们总是使用两个分开的操作
 *)

(** create a relative pose with a finite translation but zero rotation *)
Definition Transl2 (t : vec 2) : mat 3 3 := T2 0 t.

(** translate a vector `v` by offset `t` *)
Definition transl2 (t : vec 2) (v : vec 2) : mat 3 3 := T2 0 t.

(* 在同一个坐标系中，任给向量 v，平移 t 后，得到的向量是 transl2(t,v) *)
Lemma transl2_spec : forall (t : vec 2) (v : vec 2),
    (v + t)%V = h2e (cv2v (((transl2 t) * (v2cv (e2h v))))).
Proof. intros. veq; Req_more. Qed.

(** create a relative pose with a finite rotation but zero translation *)
Definition trot2 (theta : R) : mat 3 3 := T2 theta vzero.

(* 在同一个坐标系中，任给向量 v，旋转 theta 后，得到的向量是 trot2(theta,v) *)
Lemma transl2_spec : forall (theta : R) (v : vec 2),
    rot2 theta v = (trot2 theta) v.
    (v + t)%V = h2e (cv2v (((transl2 t) * (v2cv (e2h v))))).
Proof. intros. veq; Req_more. Qed.
(* Lemma T2_spec : forall (θ : R) (t : vec 2) (v : vec 2), *)

Example ex_T1 := transl2 (mkvec2 1 2) * trot2 (0.5). (* 30 'deg). *)

(** A transformation to rotate about point C *)
Definition trot2center (C : vec 2) (theta : R) : mat 3 3 :=
  transl2 C * trot2 theta * transl2 (- C)%V.


(* ########################################################################### *)
(** * Others *)

(** 预乘和后乘旋转矩阵的关系，即: u1 ~ u2 -> R * u1 ~ u2 * R' *)
Lemma R2_pre_post : forall (u : vec 2) (θ : R),
    let u1 : cvec 2 := v2cv u in         (* u1是u的列向量形式 *)
    let u2 : rvec 2 := v2rv u in         (* u2是u的行向量形式 *)
    let v1 : cvec 2 := (R2 θ) * u1 in      (* v1是用列向量形式计算的结果 *)
    let v2 : rvec 2 := u2 * (R2' θ) in  (* v2是用行向量形式计算的结果 *)
    let v1' : vec 2 := cv2v v1 in           (* v1再转为普通向量 *)
    let v2' : vec 2 := rv2v v2 in           (* v2再转为普通向量 *)
    v1' = v2'. (* 结果应该相同 *)
Proof. intros. veq; Req. Qed.

(** Special Euclidean Group of dimension 3: T ∈ SE(2) ⊂ R^(3x3) *)
(* Record SE2 := { *)
(*     SE2R :> mat 3 3; *)
(*     _ : orthonormal2 SO2R *)
(*   }. *)
