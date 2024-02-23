(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on R.
  author    : ZhengPu Shi
  date      : 2021.12

  reference :
  1. 《高等数学学习手册》徐小湛，p173
  2. 《高等数学》 第七版，同济大学数学系，第八章，向量代数与空间解析几何
  3. Vector Calculus - Michael Corral
  4. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     Note that, there are concepts related to geometry including point, parallel, 
     colinear.

  remark    :
  一. 关于零向量的平行和垂直问题
  1. 来自《高等数学》的理论：
  (1) 零向量的起点和终点重合，它的方向可看做是任意的。
  (2) 如果∠a,b = 0 or π，则称它们平行，记做 a//b。
      当两向量平行时，若将起点放在同一点，则终点和公共起点应在同一条直线，故
      两向量平行也称两向量共线。
  (3) 如果∠a,b = π/2，称它们垂直，记做 a⟂b。
  (4) 由于零向量与另一向量的夹角可以是[0,π]中的任意值，可认为零向量与任何向量
      都平行，也可认为零向量与任何向量都垂直。
  2. 网络上的观点
  (1) There are two choices to handling zero-vector
      a. The mainstream approach is that the zero vector is parallel and
         perpendicular to any vector.
      b. Only consider the non-zero vector, one reason of it is that the 
         transitivity is broken after including zero-vector.
         (因为包含了零向量以后，平行的传递性被破坏了）
  (2) https://www.zhihu.com/question/489006373
      a. “平行”或“不平行”是对两个可以被识别的方向的比较，对于零向量，“方向”是不可
         识别的，或说，是不确定的。从这个角度讲，“平行”这个概念不该被用到评价两个
         零向量的关系上的。
      b. 不过，两个零向量是“相等”的，对于向量而言，“相等”这件事包含了大小和方向
         的相等，这么说来，说两个零向量“方向”相等，也就是“平行”或也是说得通的。
  3. 使用向量运算的做法
  (1) 使用向量的运算来定义平行和垂直，这样无须三角函数就能判定。
      两向量点乘为零，则它们垂直；两向量叉乘为零向量，则它们平行。
  (2) 在严格证明中，都加上非零向量这一假设条件。
  4. 本文的做法
  (1) vnonzero 类型：表示非零向量。
      在这个类型上定义平行、垂直、角度等。
      换言之，零向量上未定义几何关系。

  二、一些观点
  1. 在三维向量空间中：空间点M <-> 原点O指向M的向量 r⃗=OM=xi+yj+zk <-> 有序数(x,y,z)

  三、额外内容
  1. {R^n, standard-inner-product} is called Euclidean space
     |v| = √<v, v>

 *)

Require Export Ratan2.
Require Export VectorModule.
(* Require Export RowColVectorModule. *)

(* ######################################################################### *)
(** * Vector theory come from common implementations *)

(* Export NormedOrderedFieldElementTypeR. *)
Module Export VectorTheoryR :=
  NormedOrderedFieldVectorTheory NormedOrderedFieldElementTypeR.

Open Scope R_scope.
Open Scope vec_scope.


(* ######################################################################### *)
(** * Vector theory applied to this type *)

(** Aabs a = Rabs a *)
Lemma Aabs_eq_Rabs : forall a : A, | a |%A = | a |.
Proof.
  intros. unfold Aabs. destruct (leb_reflect 0 a); autounfold with A in *; ra.
  rewrite Rabs_left; ra.
Qed.


  
(* ======================================================================= *)
(** ** 去掉 a2r 以及 Aabs 的一些引理 *)

(** <v, v> = ||v||² *)
Lemma vdot_same : forall {n} (v : vec n), <v,v> = (||v||)².
Proof. intros. rewrite <- vdot_same. auto. Qed.


(* ======================================================================= *)
(** ** Vector normalization (only valid in R type) *)
Section vnorm.

  (** Normalization of a non-zero vector v.
      That is, make a unit vector that in the same directin as v. *)
  Definition vnorm {n} (v : vec n) : vec n := (1 / ||v||) \.* v.

  (** The component of a normalized vector is equivalent to its original component 
      divide the vector's length *)
  Lemma vnth_vnorm : forall {n} (v : vec n) i, v <> vzero -> (vnorm v) $ i = (v $ i) / ||v||.
  Proof.
    intros. unfold vnorm. rewrite vnth_vcmul; auto.
    autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** Unit vector is fixpoint of vnorm operation *)
  Lemma vnorm_vunit_eq : forall {n} (v : vec n), vunit v -> vnorm v = v.
  Proof.
    intros. unfold vnorm. rewrite (vunit_spec v) in H. rewrite H.
    autorewrite with R. apply vcmul_1_l.
  Qed.

  (** Normalized vector is non-zero  *)
  Lemma vnorm_vnonzero : forall {n} (v : vec n), v <> vzero -> vnorm v <> vzero.
  Proof.
    intros. unfold vnorm. intro.
    apply vcmul_eq0_imply_k0_or_v0 in H0. destruct H0; auto.
    apply vlen_neq0_iff_neq0 in H. unfold Rdiv in H0.
    rewrite Rmult_1_l in H0. apply Rinv_neq_0_compat in H. easy.
  Qed.

  (** The length of a normalized vector is one *)
  Lemma vnorm_len1 : forall {n} (v : vec n), v <> vzero -> ||vnorm v|| = 1.
  Proof.
    intros. unfold vnorm. rewrite vlen_vcmul. unfold a2r, id. rewrite Aabs_eq_Rabs.
    pose proof (vlen_gt0 v H). rewrite Rabs_right; ra. field; ra.
  Qed.

  (** Normalized vector are unit vector *)
  Lemma vnorm_is_unit : forall {n} (v : vec n), v <> vzero -> vunit (vnorm v).
  Proof. intros. apply vunit_spec. apply vnorm_len1; auto. Qed.

  (** Normalized vector is parallel to original vector *)
  Lemma vnorm_vpara : forall {n} (v : vec n), v <> vzero -> (vnorm v) // v.
  Proof.
    intros. repeat split; auto.
    - apply vnorm_vnonzero; auto.
    - exists (||v||). unfold vnorm. rewrite vcmul_assoc.
      apply vcmul_same_if_k1_or_v0. left.
      autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
  Qed.

  Lemma vnorm_spec : forall {n} (v : vec n),
      v <> vzero -> (||vnorm v|| = 1 /\ (vnorm v) // v).
  Proof. intros. split. apply vnorm_len1; auto. apply vnorm_vpara; auto. Qed.

  (** Normalization is idempotent *)
  Lemma vnorm_idem : forall {n} (v : vec n),
      v <> vzero -> vnorm (vnorm v) = vnorm v.
  Proof. intros. apply vnorm_vunit_eq. apply vnorm_is_unit; auto. Qed.

  (** k <> 0 -> vnorm (k \.* v) = (sign k) \.* (vnorm v) *)
  Lemma vnorm_vcmul : forall {n} k (v : vec n),
      k <> 0 -> v <> vzero -> vnorm (k \.* v) = sign k \.* (vnorm v).
  Proof.
    intros. unfold vnorm. rewrite vlen_vcmul. rewrite !vcmul_assoc.
    f_equal. unfold sign. autounfold with A. apply vlen_neq0_iff_neq0 in H0.
    unfold a2r,id. rewrite Aabs_eq_Rabs.
    bdestruct (0 <? k).
    - rewrite Rabs_right; ra. field. split; auto.
    - bdestruct (k =? 0). easy. rewrite Rabs_left; ra. field. auto.
  Qed.

  (** k > 0 -> vnorm (k \.* v) = vnorm v *)
  Lemma vnorm_vcmul_k_gt0 : forall {n} k (v : vec n),
      k > 0 -> v <> vzero -> vnorm (k \.* v) = vnorm v.
  Proof.
    intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_gt0; auto.
    apply vcmul_1_l.
  Qed.

  (** k < 0 -> vnorm (k \.* v) = vnorm v *)
  Lemma vnorm_vcmul_k_lt0 : forall {n} k (v : vec n),
      k < 0 -> v <> vzero -> vnorm (k \.* v) = - vnorm v.
  Proof.
    intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_lt0; auto.
    rewrite (vcmul_opp 1). f_equal. apply vcmul_1_l.
  Qed.
  
  (* -1 <= (vnorm v)[i] <= 1 *)
  Lemma vnth_vnorm_bound : forall {n} (v : vec n) (i : fin n),
      v <> vzero -> -1 <= vnorm v i <= 1.
  Proof.
    intros. rewrite vnth_vnorm; auto. pose proof (vnth_le_vlen v i H).
    apply Rabs_le_rev. rewrite Aabs_eq_Rabs in *. unfold a2r,id in *.
    apply Rdiv_abs_le_1. apply vlen_neq0_iff_neq0; auto.
    apply le_trans with (||v||); auto.
    rewrite Rabs_right. apply le_refl.
    apply Rle_ge. apply vlen_ge0.
  Qed.

  (* -1 <= v.i / ||v|| <= 1 *)
  Lemma vnth_div_vlen_bound : forall {n} (v : vec n) i,
      v <> vzero -> -1 <= v i / (|| v ||) <= 1.
  Proof.
    intros. pose proof (vnth_vnorm_bound v i H). unfold vnorm in H0.
    rewrite vnth_vcmul in H0. autounfold with A in *. ra.
  Qed.

  (** <vnorm u, vnorm v> = <u, v> / (||u|| * ||v||) *)
  Lemma vdot_vnorm : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero ->
      <vnorm u, vnorm v> = <u, v> / (||u|| * ||v||).
  Proof.
    intros. unfold vnorm. rewrite vdot_vcmul_l, vdot_vcmul_r.
    autounfold with A. field. split; apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** <vnorm u, vnorm v>² = <u, v>² / (<u, u> * <v, v>) *)
  Lemma sqr_vdot_vnorm : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero ->
      <vnorm u, vnorm v>² = <u, v>² / (<u, u> * <v, v>).
  Proof.
    intros. rewrite vdot_vnorm; auto.
    rewrite Rsqr_div'. f_equal. rewrite Rsqr_mult. rewrite !vdot_same. auto.
  Qed.

  (** sqrt (1 - <u, v>²) = sqrt (<u, u> * <v, v> - <u, v>²) / (||u|| * ||v||) *)
  Lemma sqrt_1_minus_sqr_vdot : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero ->
      sqrt (1 - <vnorm u, vnorm v>²) = sqrt (((<u,u> * <v,v>) - <u,v>²) / (||u|| * ||v||)²).
  Proof.
    intros.
    unfold vnorm. rewrite vdot_vcmul_l, vdot_vcmul_r.
    autounfold with A.
    replace (1 - (1 / (||u||) * (1 / (||v||) * (<u,v>)))²)%R
      with (((<u, u> * <v, v>) - <u,v>²) / (||u|| * ||v||)²); auto.
    rewrite !Rsqr_mult, !Rsqr_div'. rewrite <- !vdot_same. field_simplify_eq.
    - autorewrite with R. auto.
    - split; apply vdot_same_neq0_if_vnonzero; auto.
  Qed.

  
  (** vnorm u _|_ v <-> u _|_ v *)
  Lemma vorth_vnorm_l : forall {n} (u v : vec n), u <> vzero -> vnorm u _|_ v <-> u _|_ v.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l. autounfold with A.
    assert (1 * / (||u||) <> 0)%R; ra.
    apply Rmult_integral_contrapositive_currified; ra.
    apply Rinv_neq_0_compat; auto.
    apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** u _|_ vnorm v <-> u _|_ v *)
  Lemma vorth_vnorm_r : forall {n} (u v : vec n), v <> vzero -> u _|_ vnorm v -> u _|_ v.
  Proof.
    intros. apply vorth_comm. apply vorth_comm in H0. apply vorth_vnorm_l; auto.
  Qed.
  
End vnorm.


(* ======================================================================= *)
(** ** Angle between two vectors *)

(** The angle from vector u to vector v, Here, θ ∈ [0,π] *)
Definition vangle {n} (u v : vec n) : R := acos (<vnorm u, vnorm v>).

Infix "/_" := vangle : vec_scope.

Section vangle.

  (** The angle of between any vector and itself is 0 *)
  Lemma vangle_self_eq0 : forall {n} (v : vec n), v <> vzero -> v /_ v = 0.
  Proof.
    intros. unfold vangle. rewrite vdot_same.
    rewrite vnorm_len1; auto. autorewrite with R. apply acos_1.
  Qed.

  (** Angle is commutative *)
  Lemma vangle_comm : forall {n} (u v : vec n), u /_ v = v /_ u.
  Proof. intros. unfold vangle. rewrite vdot_comm. auto. Qed.
  
  (** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
  (* Remark: Here, we can finish a demo proof with a special value π/4,
     but actual cases maybe have any value, it is hard to finished in Coq.
     Because the construction of {sqrt, acos, PI, etc} is complex. *)
  Fact vangle_pi4 : (@l2v 3 [1;0;0]) /_ (l2v [1;1;0]) = PI/4.
  Proof.
    rewrite <- acos_inv_sqrt2. unfold vangle. f_equal.
    compute. autorewrite with R. auto.
  Qed.

  (** 单位向量的点积介于[-1,1] *)
  Lemma vdot_unit_bound : forall {n} (u v : vec n),
      vunit u -> vunit v -> -1 <= <u, v> <= 1.
  Proof.
    intros.
    pose proof (vdot_abs_le u v).
    pose proof (vdot_ge_mul_vlen_neg u v).
    unfold a2r,id in *.
    apply vunit_spec in H, H0. rewrite H,H0 in H1,H2.
    unfold Rabs in H1. destruct Rcase_abs; ra.
  Qed.

  (** 单位化后的非零向量的点积介于 [-1,1] *)
  Lemma vdot_vnorm_bound : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> -1 <= <vnorm u, vnorm v> <= 1.
  Proof. intros. apply vdot_unit_bound; apply vnorm_is_unit; auto. Qed.

  (** <u, v> = ||u|| * ||v|| * cos (u /_ v) *)
  Lemma vdot_eq_cos_angle : forall {n} (u v : vec n), <u, v> = (||u|| * ||v|| * cos (u /_ v))%R.
  Proof.
    intros. destruct (Aeqdec u vzero).
    - subst. rewrite vdot_0_l, vlen_vzero. rewrite Rmult_0_l. auto.
    - destruct (Aeqdec v vzero).
      + subst. rewrite vdot_0_r, vlen_vzero. rewrite Rmult_0_l,Rmult_0_r. auto.
      + unfold vangle. rewrite cos_acos.
        * unfold vnorm. rewrite <- vdot_vcmul_r. rewrite <- vdot_vcmul_l.
          rewrite !vcmul_assoc. autounfold with A.
          replace ((||u||) * (1 / ||u||)) with 1;
            [|field; apply vlen_neq0_iff_neq0; auto].
          replace ((||v||) * (1 / ||v||)) with 1;
            [|field; apply vlen_neq0_iff_neq0; auto].
          rewrite !vcmul_1_l. auto.
        * apply vdot_vnorm_bound; auto.
  Qed.
  
  (** The cosine law *)
  Theorem CosineLaw : forall {n} (u v : vec n),
      ||(u - v)||² = (||u||² + ||v||² - 2 * ||u|| * ||v|| * cos (u /_ v))%R.
  Proof.
    intros. rewrite vlen_sqr_vsub. f_equal. f_equal.
    rewrite vdot_eq_cos_angle. auto.
  Qed.

  (* A variant form *)
  Theorem CosineLaw_var : forall {n} (u v : vec n),
      ||(u + v)||² = (||u||² + ||v||² + 2 * ||u|| * ||v|| * cos (u /_ v))%R.
  Proof.
    intros. rewrite vlen_sqr_vadd. f_equal. f_equal.
    rewrite vdot_eq_cos_angle. auto.
  Qed.
  
  (** The relation between dot product and the cosine of angle *)
  Lemma vdot_eq_cos_angle_by_CosineLaw : forall {n} (u v : vec n),
      <u, v> = (||u|| * ||v|| * cos (u /_ v))%R.
  Proof.
    intros.
    pose proof (vlen_sqr_vsub u v).
    pose proof (CosineLaw u v).
    unfold a2r,id in *.
    ra.
  Qed.

  (** 0 <= u /_ v <= PI *)
  Lemma vangle_bound : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> 0 <= u /_ v <= PI.
  Proof. intros. unfold vangle. apply acos_bound. Qed.
  
  (** u /_ v = 0 <-> (<u, v> = ||u|| * ||v||) *)
  Lemma vangle_0_iff : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> (u /_ v = 0 <-> <u, v> = ||u|| * ||v||).
  Proof.
    intros. rewrite (vdot_eq_cos_angle u v).
    rewrite <- associative. rewrite <- (Rmult_1_r (||u|| * ||v||)) at 2.
    split; intros.
    - apply Rmult_eq_compat_l. rewrite H1. ra.
    - apply Rmult_eq_reg_l in H1.
      * apply (cos_1_period _ 0) in H1. ra.
      * apply vlen_neq0_iff_neq0 in H,H0. ra.
  Qed.
  
  (** u /_ v = π <-> (<u, v> = -||u|| * ||v||) *)
  Lemma vangle_PI_iff : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> (u /_ v = PI <-> <u, v> = (-||u|| * ||v||)%R).
  Proof.
    intros. rewrite (vdot_eq_cos_angle u v).
    rewrite <- !associative.
    replace (- (||u|| * ||v||))%R with ((||u|| * ||v||) * (-1)); ra.
    split; intros.
    - apply Rmult_eq_compat_l. rewrite H1. ra.
    - apply Rmult_eq_reg_l in H1.
      * apply (cos_neg1_period _ 0) in H1. ra.
      * apply vlen_neq0_iff_neq0 in H,H0. ra.
  Qed.

  (** (<u, v>² = <u, u> * <v, v>) <-> (u /_ v = 0) \/ (u /_ v = π) *)
  Lemma vdot_sqr_eq_iff_vangle_0_or_PI : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero ->
      (<u, v>² = <u, u> * <v, v>) <-> (u /_ v = 0) \/ (u /_ v = PI).
  Proof.
    intros. split; intros.
    - rewrite !vdot_same in H1. rewrite <- Rsqr_mult in H1.
      apply Rsqr_eq in H1. destruct H1.
      + apply vangle_0_iff in H1; auto.
      + apply vangle_PI_iff in H1; auto.
    - destruct H1.
      + apply vangle_0_iff in H1; auto. rewrite H1, !vdot_same. ra.
      + apply vangle_PI_iff in H1; auto. rewrite H1, !vdot_same. ra.
  Qed.

  (** u /_ v = π/2 <-> (<u, v> = 0) *)
  Lemma vangle_PI2_iff : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> (u /_ v = PI/2 <-> (<u, v> = 0)).
  Proof.
    intros. rewrite (vdot_eq_cos_angle u v). split; intros.
    - rewrite H1. rewrite cos_PI2. ra.
    - assert (cos (u /_ v) = 0).
      + apply vlen_neq0_iff_neq0 in H,H0. apply Rmult_integral in H1; ra.
      + apply (cos_0_period _ 0) in H2. ra.
  Qed.

  (** 0 <= sin (u /_ v) *)
  Lemma sin_vangle_ge0 : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> 0 <= sin (u /_ v).
  Proof. intros. apply sin_ge_0; apply vangle_bound; auto. Qed.
  
  (** θ ≠ 0 -> θ ≠ π -> 0 < sin (u /_ v) *)
  Lemma sin_vangle_gt0 : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> u /_ v <> 0 -> u /_ v <> PI -> 0 < sin (u /_ v).
  Proof. intros. pose proof (vangle_bound u v H H0). apply sin_gt_0; ra. Qed.
 
  (** a > 0 -> (a \.* u) /_ v = u /_ v *)
  Lemma vangle_vcmul_l_gt0 : forall {n} (u v : vec n) (a : R),
      a > 0 -> u <> vzero -> v <> vzero -> (a \.* u) /_ v = u /_ v.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_l. unfold sign. bdestruct (0 <? a); ra.
    - rewrite !Rmult_1_l. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a < 0 -> (a \.* u) /_ v = PI - u /_ v *)
  Lemma vangle_vcmul_l_lt0 : forall {n} (u v : vec n) (a : R),
      a < 0 -> u <> vzero -> v <> vzero -> (a \.* u) /_ v = (PI - (u /_ v))%R.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_l. unfold sign. bdestruct (0 <? a); ra.
    - bdestruct (a =? 0); ra. rewrite Rmult_neg1_l. rewrite acos_opp. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a > 0 -> u /_ (a \.* v) = u /_ v *)
  Lemma vangle_vcmul_r_gt0 : forall {n} (u v : vec n) (a : R),
      a > 0 -> u <> vzero -> v <> vzero -> u /_ (a \.* v) = u /_ v.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_r. unfold sign. bdestruct (0 <? a); ra.
    - rewrite !Rmult_1_l. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a < 0 -> u /_ (a \.* v) = PI - u /_ v *)
  Lemma vangle_vcmul_r_lt0 : forall {n} (u v : vec n) (a : R),
      a < 0 -> u <> vzero -> v <> vzero -> u /_ (a \.* v) = (PI - (u /_ v))%R.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_r. unfold sign. bdestruct (0 <? a); ra.
    - bdestruct (a =? 0); ra. rewrite Rmult_neg1_l. rewrite acos_opp. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** (vnorm u) /_ v = u /_ v *)
  Lemma vangle_vnorm_l : forall {n} (u v : vec n),
      u <> vzero -> vnorm u /_ v = u /_ v.
  Proof. intros. unfold vangle. rewrite vnorm_idem; auto. Qed.

  (** u /_ (vnorm v) = u /_ v *)
  Lemma vangle_vnorm_r : forall {n} (u v : vec n),
      v <> vzero -> u /_ vnorm v = u /_ v.
  Proof. intros. unfold vangle. rewrite vnorm_idem; auto. Qed.

  (* 0 < k -> (k * u) /_ u = 0 *)
  Lemma vangle_vcmul_same_l_gt0 : forall {n} (u : vec n) k,
      u <> vzero -> 0 < k -> (k \.* u) /_ u = 0.
  Proof.
    intros. rewrite vangle_vcmul_l_gt0; auto. apply vangle_self_eq0; auto.
  Qed.

  (* 0 < k -> u /_ (k * u) = 0 *)
  Lemma vangle_vcmul_same_r_gt0 : forall {n} (u : vec n) k,
      u <> vzero -> 0 < k -> u /_ (k \.* u) = 0.
  Proof.
    intros. rewrite vangle_vcmul_r_gt0; auto. apply vangle_self_eq0; auto.
  Qed.

  (* k < 0 -> (k * u) /_ u = π *)
  Lemma vangle_vcmul_same_l_lt0 : forall {n} (u : vec n) k,
      u <> vzero -> k < 0 -> (k \.* u) /_ u = PI.
  Proof.
    intros. rewrite vangle_vcmul_l_lt0; auto. rewrite vangle_self_eq0; auto. ring.
  Qed.

  (* k < 0 -> u /_ (k * u) = π *)
  Lemma vangle_vcmul_same_r_lt0 : forall {n} (u : vec n) k,
      u <> vzero -> k < 0 -> u /_ (k \.* u) = PI.
  Proof.
    intros. rewrite vangle_vcmul_r_lt0; auto. rewrite vangle_self_eq0; auto. ring.
  Qed.

  (* I can't prove it now *)
  Axiom vdot_eq_mul_vlen_imply_vnorm_eq : forall {n} (u v : vec n),
      <u,v> = (||u|| * ||v||)%R -> vnorm u = vnorm v.
  Axiom vdot_eq_mul_vlen_imply_vnorm_eq_neg : forall {n} (u v : vec n),
      <u,v> = (- (||u|| * ||v||))%R -> vnorm u = - vnorm v.

  (* u // v -> (u /_ v = 0 \/ u /_ v = π) *)
  Lemma vpara_imply_vangle_0_or_PI : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> u // v -> (u /_ v = 0 \/ u /_ v = PI).
  Proof.
    intros. apply vdot_sqr_eq_iff_vangle_0_or_PI; auto.
    apply vpara_imply_uniqueK in H1. destruct H1 as [k [H1 _]]. rewrite <- H1.
    unfold Rsqr. rewrite vdot_vcmul_l, vdot_vcmul_r.
    autounfold with A. ring.
  Qed.

  (* u /_ v = 0 -> u // v *)
  Lemma vangle_0_imply_vpara : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> u /_ v = 0 -> u // v.
  Proof.
    intros. unfold vpara. repeat split; auto.
    apply vangle_0_iff in H1; auto.
    apply vdot_eq_mul_vlen_imply_vnorm_eq in H1.
    unfold vnorm in H1. exists (||v|| * / ||u||). rewrite <- vcmul_assoc.
    rewrite !Rdiv_1_l in H1. rewrite H1. rewrite vcmul_assoc.
    rewrite Rinv_r. apply vcmul_1_l. apply vlen_neq0_iff_neq0; auto.
  Qed.
    
  (* u /_ v = π -> u // v *)
  Lemma vangle_PI_imply_vpara : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> u /_ v = PI -> u // v.
  Proof.
    intros. unfold vpara. repeat split; auto.
    apply vangle_PI_iff in H1; auto.
    apply vdot_eq_mul_vlen_imply_vnorm_eq_neg in H1.
    unfold vnorm in H1. exists ((- ||v||) * / ||u||)%R. rewrite <- vcmul_assoc.
    rewrite !Rdiv_1_l in H1. rewrite H1. rewrite <- vcmul_opp. rewrite vcmul_assoc.
    rewrite <- Rinv_opp. rewrite Rinv_r. apply vcmul_1_l.
    apply Ropp_neq_0_compat. apply vlen_neq0_iff_neq0; auto.
  Qed.

  (* (u /_ v = 0 \/ u /_ v = π) -> u // v *)
  Lemma vangle_0_or_PI_imply_vpara : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> (u /_ v = 0 \/ u /_ v = PI -> u // v).
  Proof.
    intros. destruct H1.
    apply vangle_0_imply_vpara; auto. apply vangle_PI_imply_vpara; auto.
  Qed.

  
  (* u // v <-> (u /_ v = 0 \/ u /_ v = π) *)
  Lemma vpara_iff_vangle_0_or_PI : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> (u // v <-> u /_ v = 0 \/ u /_ v = PI).
  Proof.
    intros. split; intros.
    apply vpara_imply_vangle_0_or_PI; auto.
    apply vangle_0_or_PI_imply_vpara; auto.
  Qed.

  (** u /_ v = 0 <-> u and v 同向平行 *)
  Lemma vangle_eq0_sameDir : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero ->
      (u /_ v = 0 <-> (exists k : R, k > 0 /\ k \.* u = v)).
  Proof.
    intros. split; intros.
    - apply vangle_0_iff in H1; auto.
      apply vdot_eq_mul_vlen_imply_vnorm_eq in H1.
      unfold vnorm in H1. exists (||v|| * / ||u||). split.
      + apply Rdiv_pos_pos; apply vlen_gt0; auto.
      + rewrite <- vcmul_assoc. rewrite !Rdiv_1_l in H1. rewrite H1.
        rewrite vcmul_assoc. rewrite Rinv_r. apply vcmul_1_l.
        apply vlen_neq0_iff_neq0; auto.
    - unfold vangle.
      destruct H1 as [k [H11 H12]]. rewrite <- H12.
      rewrite <- acos_1. f_equal. unfold vnorm.
      rewrite vcmul_assoc, !vdot_vcmul_l, !vdot_vcmul_r.
      rewrite vlen_vcmul. rewrite vdot_same.
      unfold a2r,id in *. rewrite Aabs_eq_Rabs.
      rewrite Rabs_right; ra.
      autounfold with A. field. apply vlen_neq0_iff_neq0 in H,H0. ra.
  Qed.

  (** u /_ w = (u /_ v) + (v /_ w) *)
  Lemma vangle_add : forall {n} (u v w : vec n), u /_ w = ((u /_ v) + (v /_ w))%R.
  Proof.
    (* 由于目前 vangle 只是夹角，没有区分起始和结束向量，所以该性质不成立。
       在2D和3D中有带方向的 vangle2, vangle3。并且在3D中，还需要共面条件。 *)
  Abort.

  (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*)
  Lemma vangle_vadd : forall {n} (u v u' v' : vec n),
      u <> vzero -> v <> vzero ->
      ||u|| = ||u'|| -> ||v|| = ||v'|| ->
      u /_ v = u' /_ v' ->
      (u + v) /_ (u' + v') = u /_ u'.
  Proof.
  Abort.
 
End vangle.

Hint Resolve vdot_vnorm_bound : vec.


(* ======================================================================= *)
(** ** Orthogonal set 正交向量组（集） *)
Section vorthset.

(*
  (** A set of vectors in an inner product space is called pairwise orthogonal if 
      each pairing of them is orthogonal. Such a set is called an orthogonal set.
      Note: each pair means {(vi, vj)|i≠j}  *)
  Definition vorthset {r c} (M : mat r c) : Prop :=
    forall j1 j2, (j1 < c)%nat -> (j2 < c)%nat -> (j1 <> j2) -> <mcol m j1, mcol m j2> = Azero.

  (** (bool version) *)
  Definition vorthsetb {r c} (m : mat r c) : bool :=
    (* two column vectors is orthogonal *)
    let orth (i j : nat) : bool := (<mcol m i, mcol m j> =? Azero)%R in
    (* remain column indexes after this column *)
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    (* the column is orthogonal to right-side remain columns *)
    let allcols (j : nat) : bool := and_blist (map (fun k => orth j k) (cids j)) in
    (* all columns is mutually orthogonal (Note orthogonal is commutative) *)
    and_blist (map (fun j => allcols j) (seq 0 c)).

  Lemma vorthsetb_true_iff : forall {r c} (m : mat r c),
      vorthsetb m <-> vorthset m.
  Abort.

  Example vorthset_ex1 :
    vorthset (@l2m 3 3 [[1;1;1];[0;sqrt 2; -(sqrt 2)];[-1;1;1]])%A.
  Proof.
    apply vorthsetb_true_iff. cbv.
    (** Auto solve equality contatin "Req_EM_T" *)
    repeat
      match goal with
      | |- context[ Req_EM_T ?a ?b] => destruct Req_EM_T; ra
      end.
    autorewrite with R sqrt in *; ra.
  Qed.
 *)
End vorthset.


(* ======================================================================= *)
(** ** Orthonormal vectors 标准正交的向量组 *)
Section mcolsOrthonormal.

(*
  (** All (different) column-vectors of a matrix are orthogonal each other.
      For example: [v1;v2;v3] => u_|_v2 && u_|_v3 && v_|_v3. *)
  Definition mcolsorth {r c} (m : mat r c) : Prop :=
    forall j1 j2, (j1 < c)%nat -> (j2 < c)%nat -> j1 <> j2 -> mcol m j1 _|_ mcol m j2.

  (** bool version *)
  Definition mcolsorthb {r c} (m : mat r c) : bool :=
    let is_orth (i j : nat) : bool := (<mcol m i, mcol m j> =? Azero)%R in
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    let chk_col (j : nat) : bool := and_blist (map (fun k => is_orth j k) (cids j)) in
    and_blist (map (fun j => chk_col j) (seq 0 c)).

  Lemma mcolsorthb_spec : forall {r c} (m : mat r c),
      mcolsorthb m <-> mcolsorth m.
  Proof.
  Abort.

  Section test.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.
    Let m1 : mat 1 3 := l2m [[a11;a12;a13];[a21;a22;a23]].
    Let m2 : mat 3 1 := l2m [[a11;a12];[a21;a22];[a31;a32]].

    (* Compute mcolsorthb m1. *)
    (* Compute mcolsorthb m2. (* because only one column, needn't be check *) *)
  End test.

  (** All column-vectors of a matrix are unit vector.
      For example: [v1;v2;v3] => unit u && unit v && unit v3 *)
  Definition mcolsUnit {r c} (m : mat r c) : Prop :=
    forall j, (j < c)%nat -> vunit (mcol m j).

  (** bool version *)
  Definition mcolsUnitb {r c} (m : mat r c) : bool :=
    and_blist (map (fun i => vunitb (mcol m i)) (seq 0 c)).

  Lemma mcolsUnitb_spec : forall {r c} (m : mat r c),
      mcolsUnitb m <-> mcolsUnit m.
  Proof.
  Abort.

  (** The columns of a matrix is orthogomal *)
  Definition mcolsOrthonormal {r c} (m : mat r c) : Prop :=
    mcolsorth m /\ mcolsUnit m.

 *)
End mcolsOrthonormal.


(* ======================================================================= *)
(** ** Orthogonal matrix *)
Section morth.

  (* (** matrix m is orthogonal <-> columns of m are orthogomal *) *)
  (* Lemma morth_iff_mcolsOrthonormal : forall {n} (m : smat n), *)
  (*     morth m <-> mcolsOrthonormal m. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold morth,mcolsOrthonormal. *)
  (*   unfold mcolsorth, mcolsUnit. *)
  (*   unfold vorth, vunit. *)
  (*   split; intros. *)
  (*   - split; intros. *)
  (*     + rewrite vdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_diff; auto. *)
  (*     + rewrite vdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_same; auto. *)
  (*   - destruct H as [H1 H2]. hnf. intros. rewrite <- vdot_col_col; auto. *)
  (*     bdestruct (i =? j)%nat. *)
  (*     + subst. rewrite mnth_mat1_same; auto. apply H2; auto. *)
  (*     + rewrite mnth_mat1_diff; auto. apply H1; auto. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep inner-product *) *)
  (* Theorem morth_keep_dot : forall {n} (m : smat n) (u v : vec n), *)
  (*     morth m -> <m * u, m * v> = <v1, v>. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite vdot_eq_mul_trans. *)
  (*   unfold scalar_of_mat, Matrix.scalar_of_mat. *)
  (*   rewrite (m2f_mor _ (v1\T * v)); auto. *)
  (*   rewrite mtrans_mmul. rewrite mmul_assoc. rewrite <- (mmul_assoc _ m). *)
  (*   rewrite morth_iff_mul_trans_l in H. rewrite H. *)
  (*   rewrite mmul_1_l. easy. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep length. *) *)
  (* Corollary morth_keep_length : forall {n} (m : smat n) (v : vec n), *)
  (*     morth m -> ||m * v|| = ||v||. *)
  (* Proof. *)
  (*   intros. rewrite vlen_eq_iff_dot_eq. apply morth_keep_dot. auto. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep normalization. *) *)
  (* keep unit?? or keep norm?? or both *)
  (* Corollary morth_keep_normalize : forall {n} (m : smat n) (v : vec n), *)
  (*     morth m -> vnorm (m * v) = m * (vnorm v). *)
  (* Proof. *)
  (*   intros. unfold vnorm. *)
  (*   rewrite morth_keep_length; auto. apply mcmul_mmul_assoc_r. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep angle. *) *)
  (* Corollary morth_keep_angle : forall {n} (m : smat n) (u v : vec n), *)
  (*     morth m -> m * u /_ m * v = u /_ v. *)
  (* Proof. *)
  (*   intros. unfold vangle. f_equal. rewrite !morth_keep_normalize; auto. *)
  (*   rewrite morth_keep_dot; auto. *)
  (* Qed. *)

(** 由于正交矩阵可保持变换向量的长度和角度，它可保持坐标系的整体结构不变。
      因此，正交矩阵仅可用于旋转变换和反射变换或二者的组合变换。
      当正交矩阵的行列式为1，表示一个旋转，行列式为-1，表示一个反射。*)
End morth.


(* ======================================================================= *)
(** ** Exercise in textbook *)
Section exercise.
  (** 习题8.2第12题, page 23, 高等数学，第七版 *)
  (** 利用向量来证明不等式，并指出等号成立的条件 *)
  Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R,
      sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= |a1*b1 + a2*b2 + a3*b3|.
  Proof.
    intros.
    pose (u := mkvec3 a1 a2 a3).
    pose (v := mkvec3 b1 b2 b3).
    replace (sqrt (a1² + a2² + a3²)) with (vlen u); [|cbv; f_equal; ring].
    replace (sqrt (b1² + b2² + b3²)) with (vlen v); [|cbv; f_equal; ring].
    replace (a1 * b1 + a2 * b2 + a3 * b3)%R with (<u, v>); [|cbv; f_equal; ring].
    pose proof (vdot_abs_le u v). ra.
  Qed.

End exercise.


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let u := @l2v 3 [1;2;3].
  Let v := @f2v 3 (fun i => 2 + nat2R i)%R.
  
  (* Compute v2l u. *)
  (* Compute v2l v. *)
  (* Compute u$fin0. *)
  (* Compute v2l (vmap u Ropp). *)
  (* Compute v2l (vmap2 u v Rplus). *)
  (* Compute @Vector.v2l _ _ (@Vector.vmap2 _ _ _ pair _ u v). *)
  (* Compute vsum u Rplus 0. *)
  (* Compute v2l (u + v). *)

  (* Compute v2l (u - v). *)
  (* Compute v2l (3 \.* u). *)
  (* Compute <u, v>. *)
  (* Compute vunitb u. *)
  (* Compute vnorm u. *)
  (* Compute vorthb u v. *)
End test.
