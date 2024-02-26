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
Import V2Notations.

Open Scope nat_scope.
Open Scope R_scope.
Open Scope mat_scope.
Open Scope vec_scope.


(* ########################################################################### *)
(** * Preliminary math *)

(** Transformation by SOn matrix will keep v2cross. *)
Lemma SOn_keep_v2cross : forall (M : smat 2) (u v : vec 2),
    SOnP M -> (M * u) \x (M * v) = u \x v.
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

(** Transformation by SOn matrix will keep vangle2. *)
Lemma SOn_keep_vangle2 : forall (M : smat 2) (u v : vec 2),
    SOnP M -> (M * u) /2_ (M * v) = u /2_ v.
Proof.
  intros. unfold vangle2. rewrite SOn_keep_v2cross; auto.
  rewrite morth_keep_angle; auto. apply H.
Qed.

(* ########################################################################### *)
(** * Skew-symmetric matrix in 2-D *)

(** Equivalent form of skewP of 2D vector *)
Lemma skewP2_eq : forall M : smat 2,
    skewP M <->
      (M.11 = 0) /\ (M.22 = 0) /\ (M.12 = -M.21)%R.
Proof.
  intros. split; intros.
  - hnf in H. assert (m2l (- M) = m2l (M\T))%M. rewrite H; auto.
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


(* ########################################################################### *)
(** * Orientation in 2D (pure rotation) *)

(* ======================================================================= *)
(** ** 2-D Rotation matrix *)

Open Scope mat_scope.

(** 创建一个2D旋转矩阵。说明：
   1. 该矩阵是标准正交的，即行向量相互正交，列向量相互正交，并且长度都是1.
   2. 其列向量是旋转后的坐标系的坐标轴关于原坐标系的单位向量
   3. 它属于SO(2)，这表明任意两个这样的矩阵相乘，以及逆都在SO(2)中。
   4. 行列式是1，这表明，一个向量被变换后其长度不改变。
   5. 逆矩阵是其转置。
   6. 该矩阵的四个元素并不独立，实际上只有一个参数theta。这是非最小表示的一个例子，
      缺点是占用更多存储空间，优点是可组合性(composability)
   7. 如何使用该矩阵来变换向量？见 operations
 *)
Definition rot2 (theta : R) : smat 2 :=
  (mkmat_2_2
     (cos theta) (- sin theta)
     (sin theta) (cos theta))%R.

(** rot2 is orthogonal matrix *)
Lemma rot2_orth : forall (θ : R), morth (rot2 θ).
Proof. intros; meq; req. Qed.

(** The determinant of rot2 is 1 *)
Lemma rot2_det1 : forall (θ : R), mdet (rot2 θ) = 1.
Proof. intros; cbv; req. Qed.

(** rot2 satisfies SOnP *)
Lemma rot2_SOnP : forall (θ : R), SOnP (rot2 θ).
Proof. intros. hnf. split. apply rot2_orth. apply rot2_det1. Qed.

(** rot2 is a member of SO2 *)
Definition rot2_SO2 (θ : R) : SO2 := mkSOn (rot2 θ) (rot2_SOnP θ).

(** rot2 is invertible *)
Lemma rot2_invertible : forall (θ : R), minvertible (rot2 θ).
Proof. intros. apply morth_invertible. apply rot2_orth. Qed.

(** rot2\-1 = rot2\T *)
Lemma rot2_inv_eq_trans : forall θ : R, (rot2 θ)\-1 = (rot2 θ)\T.
Proof.
  (* method 1 : prove by computing (slow) *)
  (* intros; meq; req. *)
  (* method 2 : prove by reasoning *)
  intros; apply (SOn_inv_eq_trans (rot2_SO2 θ)).
Qed.

(** rot2 * rot2\-1 = I *)
Lemma rot2_mul_rot2_inv : forall θ : R, rot2 θ * ((rot2 θ)\-1) = mat1.
Proof. intros. apply mmul_minv_r. apply rot2_invertible. Qed.

(** rot2\-1 * rot2 = I *)
Lemma rot2_inv_mul_rot2 : forall θ : R, (rot2 θ)\-1 * (rot2 θ) = mat1.
Proof. intros. apply mmul_minv_l. apply rot2_invertible. Qed.

(** rot2 * rot2\T = I *)
Lemma rot2_mul_rot2_trans : forall θ : R, rot2 θ * ((rot2 θ)\T) = mat1.
Proof. intros. rewrite <- rot2_inv_eq_trans. apply rot2_mul_rot2_inv. Qed.

(** rot2\T * rot2 = I *)
Lemma rot2_trans_mul_rot2 : forall θ : R, (rot2 θ)\T * (rot2 θ) = mat1.
Proof. intros. rewrite <- rot2_inv_eq_trans. apply rot2_inv_mul_rot2. Qed.

(** rot2(θ1) * rot2(θ2) = rot2(θ1 + θ2) *)
Lemma rot2_eq_add : forall (θ1 θ2 : R), (rot2 θ1) * (rot2 θ2) = rot2 (θ1 + θ2).
Proof. intros; meq; req. Qed.

(** rot2(θ1) * rot2(θ2) = rot2(θ2) * rot2(θ1) *)
Lemma rot2_comm : forall (θ1 θ2 : R), (rot2 θ1) * (rot2 θ2) = (rot2 θ2) * (rot2 θ1).
Proof. intros; meq; ra. Qed.

(** rot2(-θ) = rot2(θ)\-1 *)
Lemma rot2_neg_eq_inv : forall θ : R, rot2 (-θ) = (rot2 θ)\-1.
Proof. intros; meq; req. Qed.

(** rot2(-θ) = rot2(θ)\T *)
Lemma rot2_neg_eq_trans : forall θ : R, rot2 (-θ) = (rot2 θ)\T.
Proof. intros; meq; req. Qed.


(* ======================================================================= *)
(** ** Definition of 2D rotation operations *)

Open Scope vec_scope.

(* Given two coordinate frames, the world frame {W} and the body frame
   {B}, where {B} is rotated by an angle of theta relative to {W}, the
   coordinates of a vector v in these two coordinate frames are w and
   b, respectively. The following relationship holds:
      w = rot2(theta) * b
      b = rot2(theta)^T * w

  假定有两个坐标系，世界坐标系{W}和物体坐标系{B}，并且{B}相对于{W}旋转
  了theta角，某个向量v在这两个坐标系下的坐标分别为w和b，则满足如下关系
  式：w = rot2(theta)*b, b = rot2(theta)' * w. *)
Definition world4rot (theta : R) (b : vec 2) : vec 2 := rot2 theta * b.
Definition body4rot (theta : R) (w : vec 2) : vec 2 := (rot2 theta)\T * w.

(* In a coordinate frame, if the coordinates of a vector are `a` and
   the vector is rotated by an angle of `theta`, the coordinates after
   rotation are `b`. The following relationship holds:
      b = rot2(theta) * a
      a = rot2(theta)^T * b

  在一个坐标系中，某个向量的坐标是v1，该向量旋转了theta角，旋转后的坐
  标是v2，则有以下关系式：b = rot2(theta) * a, a = rot2'(theta) * b *)
Definition afterRot (theta : R) (a : vec 2) : vec 2 := rot2 theta * a.
Definition beforeRot (theta : R) (b : vec 2) : vec 2 := (rot2 theta)\T * b.


(* ======================================================================= *)
(** ** Properties for 2D rotation operations *)

(** world4rot . body4rot = id *)
Lemma world4rot_body4rot : forall theta w, world4rot theta (body4rot theta w) = w.
Proof.
  intros. unfold world4rot, body4rot. rewrite <- mmulv_assoc.
  rewrite rot2_mul_rot2_trans, mmulv_1_l. auto.
Qed.

(** body4rot . world4rot = id *)
Lemma body4rot_world4rot : forall theta b, body4rot theta (world4rot theta b) = b.
Proof.
  intros. unfold world4rot, body4rot. rewrite <- mmulv_assoc.
  rewrite rot2_trans_mul_rot2, mmulv_1_l. auto.
Qed.

(** world4rot (-θ) = body4rot(θ) *)
Lemma world4rot_neg_eq_body4rot : forall theta v,
    world4rot (-theta) v = body4rot theta v.
Proof.
  intros. unfold world4rot, body4rot. rewrite rot2_neg_eq_trans. auto.
Qed.

(** Two 2-D rotations equal to once with the addition of the angles *)
Lemma world4rot_twice : forall (theta1 theta2 : R) (v : vec 2),
    world4rot theta2 (world4rot theta1 v) =
      world4rot (theta1 + theta2) v.
Proof.
  intros. unfold world4rot. rewrite <- mmulv_assoc.
  rewrite rot2_eq_add. rewrite Rplus_comm. auto.
Qed.

(** The order of two 2-D rotations does not matter *)
Lemma world4rot_anyOrder : forall (θ1 θ2 : R) (v : vec 2),
    world4rot θ2 (world4rot θ1 v) = world4rot θ1 (world4rot θ2 v).
Proof. intros. rewrite !world4rot_twice. f_equal. ring. Qed.

(* we can easily prove the similiarly properties for other operations *)


(* ======================================================================= *)
(** ** Specifications for 2-D rotation operations *)

(** 两个坐标系中同一个向量的坐标变化 *)
Section spec_TwoFrame.
  Open Scope mat_scope.
  
  (* 参考了 RVC 书中 2.1.1.1 节的方法 *)

  (* 命题：
     任意二维平面中的原点重合的两个坐标系{W}和{B}，{W}旋转theta后到达{B}，
     某向量 OP 在 {W} 和 {B} 下的坐标分别为 w 和 b，证明：
     w = world4rot(theta,b) 以及 b=body4rot(theta,w) *)
  
  Variable xw' yw' : vec 2.   (* 坐标系 {W} 的坐标轴单位向量 *)
  Hypotheses xw'yw'_orth : morth (cvl2m [xw';yw']). (* {W}的坐标轴是正交的 *)
  Variable xb' yb' : vec 2.   (* 坐标系 {B} 的坐标轴单位向量 *)
  Hypotheses xb'yb'_orth : morth (cvl2m [xb';yb']). (* {B}的坐标轴是正交的 *)
  Variable theta : R.         (* 坐标系{W}旋转theta角后到{B} *)
  Hypotheses Hxb' :           (* xb'由 theta 和 {xw,yw} 表示 *)
    xb' = (cos theta \.* xw' + sin theta \.* yw')%V.
  Hypotheses Hyb' :           (* yb'由 theta 和 {xw,yw} 表示 *)
    yb' = ((- sin theta)%R \.* xw' + cos theta \.* yw')%V.
  
  Variable p : vec 2.        (* 任意P点 *)
  Variable w : vec 2.        (* P点在 {W} 下的坐标 *)
  Variable b : vec 2.        (* P点在 {B} 下坐标 *)
  Hypotheses Hpw : p = (w.x \.* xw' + w.y \.* yw')%V. (* P点在{W}中的表示 *)
  Hypotheses Hpb : p = (b.x \.* xb' + b.y \.* yb')%V. (* P点在{B}中的表示 *)

  (* Hxb' 和 Hyb' 的矩阵形式，公式(2.4) *)
  Fact Hxb'Hyb' : cvl2m [xb';yb'] = (cvl2m [xw';yw']) * rot2 theta.
  Proof. subst. meq; ra. Qed.
  
  (* Hxw' 和 Hyw' 的矩阵形式 *)
  Fact Hxw'Hyw' : @cvl2m 2 2 [xw';yw'] = (cvl2m [xb';yb']) * (rot2 theta)\T.
  Proof.
    assert (cvl2m [xb'; yb'] * (rot2 theta)\T =
              cvl2m [xw'; yw'] * rot2 theta * (rot2 theta)\T).
    { rewrite Hxb'Hyb'. auto. }
    rewrite mmul_assoc in H. rewrite rot2_mul_rot2_trans, mmul_1_r in H. auto.
  Qed.

  (* Hpv 的矩阵形式 *)
  Fact HpwM : p = (@cvl2m 2 2 [xw';yw'] * w)%V.
  Proof. rewrite Hpw. veq; ra. Qed.
  
  (* Hpb 的矩阵形式 *)
  Fact HpbM : p = (@cvl2m 2 2 [xb';yb'] * b)%V.
  Proof. rewrite Hpb. veq; ra. Qed.
  
  (* p 用 {xw',yw'} 和 b 的矩阵乘法表示，公式(2.5) *)
  Fact p_w_b : p = ((cvl2m [xw';yw'] * rot2 theta)%M * b)%V.
  Proof. rewrite HpbM. f_equal. f_equal. apply Hxb'Hyb'. Qed.
  
  (* p 用 {xb',yb'} 和 w 的矩阵乘法表示 *)
  Fact p_b_w : p = ((cvl2m [xb';yb'] * (rot2 theta)\T)%M * w)%V.
  Proof. rewrite HpwM. f_equal. f_equal. apply Hxw'Hyw'. Qed.
  
  Lemma world4rot_spec : w = world4rot theta b.
  Proof.
    unfold world4rot.
    assert (@cvl2m 2 2 [xw';yw'] * w =
              (cvl2m [xw';yw'] * rot2 theta)%M * b)%V.
    { rewrite <- HpwM. rewrite <- p_w_b. auto. }
    rewrite mmulv_assoc in H. apply mmulv_cancel_l in H; auto.
    apply morth_invertible; auto.
  Qed.
  
  Lemma body4rot_spec : b = body4rot theta w.
  Proof.
    unfold body4rot.
    assert (@cvl2m 2 2 [xb';yb'] * b =
              (cvl2m [xb';yb'] * (rot2 theta)\T)%M * w)%V.
    { rewrite <- HpbM. rewrite <- p_b_w. auto. }
    rewrite mmulv_assoc in H. apply mmulv_cancel_l in H; auto.
    apply morth_invertible; auto.
  Qed.
End spec_TwoFrame.

(** 证明在同一个坐标系下向量旋转前后的坐标变化 *)
Section spec_OneFrame.

  (* 命题：
     任给二维平面及坐标系{0}，坐标原点为O，某非零点P，向量OP的坐标为a，
     当将OP绕正方向旋转theta角后到达OP'，OP'坐标为b，证明：
     b = afterRot(theta,a) 以及  a = beforeRot(theta,b) *)

  Context (a : vec 2). (* 任给OP在{0}下的坐标a *)
  Context (theta : R). (* 任给旋转角theta *)
  Hypotheses Hneq0 : a <> vzero. (* 假定OP是非零向量 *)
  Let l := ||a||.        (* OP的长度 *)
  Let alpha := v2i /2_ a.       (* x轴正方向到OP的角度, [0, 2PI) *)
  Let b_x := (l * cos (alpha + theta))%R.   (* OP'的横坐标 *)
  Let b_y := (l * sin (alpha + theta))%R.   (* OP'的纵坐标 *)
  Let b : vec 2 := l2v [b_x;b_y].           (* OP'的坐标 *)

  Lemma afterRot_spec : b = afterRot theta a.
  Proof.
    (* convert the equality of matrix to element-wise equalities *)
    intros. unfold b,b_x,b_y,afterRot. apply v2l_inj. rewrite v2l_l2v; auto.
    replace (v2l (rot2 theta * a))
      with [a.x * (cos theta) + a.y * (- sin theta);
            a.x * (sin theta) + a.y * (cos theta)]%R.
    2:{ cbv. list_eq; ra. } list_eq.
    (* proof equality of element *)
    - rewrite cos_add. unfold alpha, Rminus, l. ring_simplify.
      rewrite v2len_mul_cos_vangle2_i; auto.
      rewrite v2len_mul_sin_vangle2_i; auto. lra.
    - rewrite sin_add. unfold alpha, l. ring_simplify.
      rewrite v2len_mul_cos_vangle2_i; auto.
      rewrite v2len_mul_sin_vangle2_i; auto. lra.
  Qed.

  Lemma beforeRot_spec : a = beforeRot theta b.
  Proof.
    (* convert the equality of matrix to element-wise equalities *)
    intros. unfold b,b_x,b_y,beforeRot. apply v2l_inj.
    replace (v2l a) with [a.x; a.y]; [|cbv; auto].
    replace (v2l (((rot2 theta)\T *
                     (l2v [(l * cos (alpha + theta))%R;
                           (l * sin (alpha + theta))%R]))))
      with [
        (cos theta) * l * cos (alpha + theta) +
          (sin theta) * l * sin (alpha + theta);
        - (sin theta) * l * cos (alpha + theta) +
          (cos theta) * l * sin (alpha + theta)]%R.
    2:{ Local Opaque cos sin vlen vangle2. cbv; list_eq; ra. } list_eq.
    (* proof equality of element *)
    - (* Tips: `a.x` and `a.y` is A type, making `ring` will fail. *)
      remember ((a (nat2finS 0)) : R) as a_x.
      rewrite cos_add, sin_add; unfold alpha, Rminus, l. ring_simplify.
      rewrite associative. rewrite v2len_mul_cos_vangle2_i; auto.
      rewrite cos2'. ra.
    - remember ((a (nat2finS 1)) : R) as a_y.
      rewrite cos_add, sin_add; unfold alpha, Rminus, l. ring_simplify.
      replace ((||a||) * cos theta ^ 2 * sin (v2i /2_ a))%R
        with (cos theta ^ 2 * (||a|| * sin (v2i /2_ a)))%R; ra.
      rewrite associative. rewrite v2len_mul_sin_vangle2_i; auto.
      rewrite sin2'. ra.
  Qed.
End spec_OneFrame.


(* ########################################################################### *)
(** * Pose in 2-D *)

(* ======================================================================= *)
(** ** Convert between Euclidean coordinates and homogeneous coordinates *)

(** Convert Euclidean coordinates to homogeneous coordinates *)
Definition e2h (v : vec 2) : vec 3 := mkvec3 (v.x) (v.y) 1.

(** Convert homogeneous coordinates to Euclidean coordinates *)
Definition h2e (v : vec 3) : vec 2 := mkvec2 (v.x/v.z) (v.y/v.z).

Lemma h2e_e2h : forall (v : vec 2), h2e (e2h v) = v.
Proof. intros. veq; ra. Qed.

Lemma e2h_h2e : forall (v : vec 3), v.z = 1 -> e2h (h2e v) = v.
Proof. intros. cbv in H. veq; rewrite H; ra. Qed.

(* Lemma e2h_vadd : forall (u v : vec 2), e2h (u + v) = e2h u + e2h v. *)
(* Proof. intros. veq; req. Qed. *)


(* ======================================================================= *)
(** ** 2-D homogeneous transformation matrix *)

Open Scope mat_scope.

(** Create a 2-D homogeneous transformation matrix:
    1. It represents translation and orientation, or relative pose. 
       This is often referred to as a rigid-body motion.
    2. 它表示坐标系先平移 t，再旋转 θ 后的相对位姿
    3. trans2 ∈ SE(2) ⊂ R^(3x3), SE: special Euclidean group
    4. 相对位姿可用3个参数(t.x, t.y, θ)，或齐次矩阵来表示，前者省空间，后者有组合性
    5. 由于平移和旋转操作不可交换，所以我们总是使用两个分开的操作
    6. 如何使用该矩阵来变换向量？见 operations *)
Definition trans2 (t : vec 2) (θ : R) : mat 3 3 :=
  l2m
    [[cos θ; - sin θ; t.x];
     [sin θ; cos θ;   t.y];
     [0;     0;       1  ]]%R.


(* ======================================================================= *)
(** ** 2-D transformation operations *)

(** Create a 2-D relative pose with pure translate of offset `t` *)
Definition transl2 (t : vec 2) : mat 3 3 := trans2 t 0.

(** Create a 2-D relative pose with a pure rotation of angle `theta` *)
Definition trot2 (theta : R) : mat 3 3 := trans2 vzero theta.

(** A transformation to rotate about point C *)
Definition trot2center (C : vec 2) (theta : R) : mat 3 3 :=
  transl2 C * trot2 theta * transl2 (- C)%V.

(* 示例：构造一个相对位姿，坐标系先平移(1,2)，再旋转30度 *)
Example trans_example1 := transl2 (mkvec2 1 2) * trot2 (0.5). (* 30 'deg). *)

(* 任给坐标系中的坐标为v的向量，平移 t 后的新坐标是 transl2(t)*v *)
Lemma transl2_spec : forall (t : vec 2) (v : vec 2),
    (transl2 t * e2h v)%V = e2h (v + t)%V.
Proof. intros. veq; req. Qed.

(* 任给坐标系中的坐标为v的向量，旋转 theta 后的新坐标是 trot2(theta)*v *)
Lemma trot2_spec : forall (theta : R) (v : vec 2),
    (trot2 theta * e2h v)%V = e2h (rot2 theta * v)%V.
Proof. intros. veq; req. Qed.

(* 任给坐标系中的坐标为v的向量，先平移 t 再旋转 theta，得到的新坐标是 trans2(theta,t)*v *)
Lemma trans2_spec : forall (t : vec 2) (theta : R) (v : vec 2),
    (* ((trot2 theta) * e2h (v + t))%V = (trans2 t theta * e2h v)%V. *)
    (h2e (trot2 theta * e2h v) + t = h2e (trans2 t theta * e2h v))%V.
Proof. intros. veq; req. Qed.
  

(* ########################################################################### *)
(** * Others *)

(** 预乘和后乘旋转矩阵的关系，即: R * u = u * R' *)
Lemma rot2_pre_post : forall (u : vec 2) (θ : R),
    let v1 : vec 2 := (rot2 θ * u)%V in      (* v1是用列向量形式计算的结果 *)
    let v2 : vec 2 := rv2v (v2rv u * (rot2 θ)\T) in  (* v2是用行向量形式计算的结果 *)
    v1 = v2. (* 结果应该相同 *)
Proof. intros. veq; ra. Qed.

(** Special Euclidean Group of dimension 3: T ∈ SE(2) ⊂ R^(3x3) *)
  (* Record SE2 := { *)
  (*     SE2R :> mat 3 3; *)
  (*     _ : orthonormal2 SO2R *)
  (*   }. *)
