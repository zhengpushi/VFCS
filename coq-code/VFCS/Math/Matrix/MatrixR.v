(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on R.
  author    : ZhengPu Shi
  date      : 2023.12

  reference :
  1. 《高等数学学习手册》徐小湛，p173
  2. 《高等数学》 第七版，同济大学数学系，第八章，向量代数与空间解析几何
  3. Vector Calculus - Michael Corral
  4. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     Note that, there are concepts related to geometry including point, parallel, 
     colinear.
  5. https://wuli.wiki/online/Cross.html
  6. https://en.wikipedia.org/wiki/Cross_product

  remark    :
  1. 在三维向量空间中：空间点M <-> 原点O指向M的向量 r⃗=OM=xi+yj+zk <-> 有序数(x,y,z)
  2. {R^n, standard-inner-product} is called Euclidean space
     |v| = √<v, v>
 *)

Require Export RExt.
Require Export Ratan2.
Require Export MatrixModule.


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryR :=
  NormedOrderedFieldMatrixTheory NormedOrderedFieldElementTypeR.

Open Scope R_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)

Open Scope vec_scope.

(* ======================================================================= *)
(** ** Extension for R *)
Lemma Rsqrt_1_minus_x_eq_y : forall x y : R,
    (x² + y²)%R <> 0 -> sqrt (1 - (x / sqrt (x² + y²))²) = |y| / sqrt (x² + y²).
Proof.
  intros.
  replace (1 - (x / sqrt (x² + y²))²)%R with (y² / (x² + y²))%R.
  - rewrite sqrt_div_alt; ra. f_equal. apply sqrt_square_abs.
  - rewrite Rsqr_div'. autorewrite with sqrt; ra. field. ra.
Qed.

Lemma Rsqrt_1_minus_y_eq_x : forall x y : R,
    (x² + y²)%R <> 0 -> sqrt (1 - (y / sqrt (x² + y²))²) = |x| / sqrt (x² + y²).
Proof.
  intros.
  rewrite Rplus_comm at 1. rewrite Rsqrt_1_minus_x_eq_y; ra.
  f_equal. rewrite Rplus_comm. auto.
Qed.

(* ======================================================================= *)
(** ** 去掉 a2r 以及 Aabs 的一些引理 *)

(** Aabs a = Rabs a *)
Lemma Aabs_eq_Rabs : forall a : A, | a |%A = | a |.
Proof.
  intros. unfold Aabs. destruct (leb_reflect 0 a); autounfold with A in *; ra.
  rewrite Rabs_left; ra.
Qed.

(** <v, v> = ||v||² *)
Lemma vdot_same : forall {n} (v : vec n), <v,v> = (||v||)².
Proof. intros. rewrite <- vdot_same. auto. Qed.

(* ======================================================================= *)
(** ** Vector normalization (only valid in R type) *)

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
Lemma vnorm_vpara : forall {n} (v : vec n), v <> vzero -> (vnorm v) //+ v.
Proof.
  intros. repeat split; auto.
  - apply vnorm_vnonzero; auto.
  - exists (||v||). split.
    + apply vlen_gt0; auto.
    + unfold vnorm. rewrite vcmul_assoc. apply vcmul_same_if_k1_or_v0.
      left. autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
Qed.

Lemma vnorm_spec : forall {n} (v : vec n),
    v <> vzero -> (||vnorm v|| = 1 /\ (vnorm v) //+ v).
Proof. intros. split. apply vnorm_len1; auto. apply vnorm_vpara; auto. Qed.

(** Normalization is idempotent *)
Lemma vnorm_idem : forall {n} (v : vec n), v <> vzero -> vnorm (vnorm v) = vnorm v.
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
  intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_gt0; auto. apply vcmul_1_l.
Qed.

(** k < 0 -> vnorm (k \.* v) = vnorm v *)
Lemma vnorm_vcmul_k_lt0 : forall {n} k (v : vec n),
    k < 0 -> v <> vzero -> vnorm (k \.* v) = - vnorm v.
Proof.
  intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_lt0; auto.
  rewrite (vcmul_opp 1). f_equal. apply vcmul_1_l.
Qed.

(** -1 <= (vnorm v)[i] <= 1 *)
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

(** -1 <= v.i / ||v|| <= 1 *)
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
  intros. rewrite vdot_vnorm; auto. rewrite Rsqr_div'. f_equal.
  rewrite Rsqr_mult. rewrite !vdot_same. auto.
Qed.

(** sqrt (1 - <u, v>²) = sqrt (<u, u> * <v, v> - <u, v>²) / (||u|| * ||v||) *)
Lemma sqrt_1_minus_sqr_vdot : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero ->
    sqrt (1 - <vnorm u, vnorm v>²) = sqrt (((<u,u> * <v,v>) - <u,v>²) / (||u|| * ||v||)²).
Proof.
  intros. unfold vnorm. rewrite vdot_vcmul_l, vdot_vcmul_r. autounfold with A.
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
  apply Rinv_neq_0_compat; auto. apply vlen_neq0_iff_neq0; auto.
Qed.

(** u _|_ vnorm v <-> u _|_ v *)
Lemma vorth_vnorm_r : forall {n} (u v : vec n), v <> vzero -> u _|_ vnorm v -> u _|_ v.
Proof.
  intros. apply vorth_comm. apply vorth_comm in H0. apply vorth_vnorm_l; auto.
Qed.

(* ======================================================================= *)
(** ** Angle between two vectors *)

(** The angle from vector u to vector v, Here, θ ∈ [0,π] *)
Definition vangle {n} (u v : vec n) : R := acos (<vnorm u, vnorm v>).
Infix "/_" := vangle : vec_scope.

(** The angle of between any vector and itself is 0 *)
Lemma vangle_self : forall {n} (v : vec n), v <> vzero -> v /_ v = 0.
Proof.
  intros. unfold vangle. rewrite vdot_same.
  rewrite vnorm_len1; auto. autorewrite with R. apply acos_1.
Qed.

(** Angle is commutative *)
Lemma vangle_comm : forall {n} (u v : vec n), u /_ v = v /_ u.
Proof. intros. unfold vangle. rewrite vdot_comm. auto. Qed.

(* Tips: Here, we can finish a demo proof with a special value π/4,
   but actual cases maybe have any value, it is hard to finished in Coq.
   Because the construction of {sqrt, acos, PI, etc} is complex. *)
(** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
Fact vangle_pi4 : (@l2v 3 [1;0;0]) /_ (l2v [1;1;0]) = PI/4.
Proof.
  rewrite <- acos_inv_sqrt2. unfold vangle. f_equal.
  compute. autorewrite with R. auto.
Qed.

(** 单位向量的点积介于[-1,1] *)
Lemma vdot_unit_bound : forall {n} (u v : vec n),
    vunit u -> vunit v -> -1 <= <u, v> <= 1.
Proof.
  intros. pose proof (vdot_abs_le u v). pose proof (vdot_ge_mul_vlen_neg u v).
  unfold a2r,id in *. apply vunit_spec in H, H0. rewrite H,H0 in H1,H2.
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
        replace ((||u||) * (1 / ||u||))%R with 1;
          [|field; apply vlen_neq0_iff_neq0; auto].
        replace ((||v||) * (1 / ||v||))%R with 1;
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

(** A variant form of cosine law *)
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
  intros. pose proof (vlen_sqr_vsub u v). pose proof (CosineLaw u v).
  unfold a2r,id in *. ra.
Qed.

(** 0 <= u /_ v <= PI *)
Lemma vangle_bound : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> 0 <= u /_ v <= PI.
Proof. intros. unfold vangle. apply acos_bound. Qed.

(** u /_ v = 0 <-> (<u, v> = ||u|| * ||v||) *)
Lemma vangle_0_iff : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> (u /_ v = 0 <-> <u, v> = (||u|| * ||v||)%R).
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
  intros. rewrite (vdot_eq_cos_angle u v). rewrite <- !associative.
  replace (- (||u|| * ||v||))%R with ((||u|| * ||v||) * (-1))%R; ra.
  split; intros.
  - apply Rmult_eq_compat_l. rewrite H1. ra.
  - apply Rmult_eq_reg_l in H1.
    * apply (cos_neg1_period _ 0) in H1. ra.
    * apply vlen_neq0_iff_neq0 in H,H0. ra.
Qed.

(** u /_ v = 0 -> <u, v>² = <u, u> * <v, v> *)
Lemma vangle_0_imply_vdot_sqr_eq : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero ->
    u /_ v = 0 -> <u, v>² = (<u, u> * <v, v>)%R.
Proof. intros. apply vangle_0_iff in H1; auto. rewrite H1, !vdot_same. ra. Qed.

(** u /_ v = π -> <u, v>² = <u, u> * <v, v> *)
Lemma vangle_PI_imply_vdot_sqr_eq : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero ->
    u /_ v = PI -> <u, v>² = (<u, u> * <v, v>)%R.
Proof. intros. apply vangle_PI_iff in H1; auto. rewrite H1, !vdot_same. ra. Qed.

(** (<u, v>² = <u, u> * <v, v>) -> (u /_ v = 0) \/ (u /_ v = π) *)
Lemma vdot_sqr_eq_imply_vangle_0_or_PI : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero ->
    <u, v>² = (<u, u> * <v, v>)%R -> (u /_ v = 0) \/ (u /_ v = PI).
Proof.
  intros. rewrite !vdot_same in H1. rewrite <- Rsqr_mult in H1.
  apply Rsqr_eq in H1. destruct H1.
  - apply vangle_0_iff in H1; auto.
  - apply vangle_PI_iff in H1; auto.
Qed.

(** (u /_ v = 0) \/ (u /_ v = π) -> <u, v>² = <u, u> * <v, v> *)
Lemma vangle_0_or_PI_imply_vdot_sqr_eq : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero ->
    (u /_ v = 0) \/ (u /_ v = PI) -> <u, v>² = (<u, u> * <v, v>)%R. 
Proof.
  intros. destruct H1.
  - apply vangle_0_imply_vdot_sqr_eq; auto.
  - apply vangle_PI_imply_vdot_sqr_eq; auto.
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

(** 0 < k -> (k * u) /_ u = 0 *)
Lemma vangle_vcmul_same_l_gt0 : forall {n} (u : vec n) k,
    u <> vzero -> 0 < k -> (k \.* u) /_ u = 0.
Proof.
  intros. rewrite vangle_vcmul_l_gt0; auto. apply vangle_self; auto.
Qed.

(** 0 < k -> u /_ (k * u) = 0 *)
Lemma vangle_vcmul_same_r_gt0 : forall {n} (u : vec n) k,
    u <> vzero -> 0 < k -> u /_ (k \.* u) = 0.
Proof.
  intros. rewrite vangle_vcmul_r_gt0; auto. apply vangle_self; auto.
Qed.

(** k < 0 -> (k * u) /_ u = π *)
Lemma vangle_vcmul_same_l_lt0 : forall {n} (u : vec n) k,
    u <> vzero -> k < 0 -> (k \.* u) /_ u = PI.
Proof.
  intros. rewrite vangle_vcmul_l_lt0; auto. rewrite vangle_self; auto. ring.
Qed.

(** k < 0 -> u /_ (k * u) = π *)
Lemma vangle_vcmul_same_r_lt0 : forall {n} (u : vec n) k,
    u <> vzero -> k < 0 -> u /_ (k \.* u) = PI.
Proof.
  intros. rewrite vangle_vcmul_r_lt0; auto. rewrite vangle_self; auto. ring.
Qed.

(** u //+ v -> u /_ v = 0 *)
Lemma vpara_imply_vangle_0 : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> u //+ v -> u /_ v = 0.
Proof.
  intros. apply vpara_imply_uniqueK in H1. destruct H1 as [k [[H1 H2] _]].
  rewrite <- H2. rewrite vangle_vcmul_r_gt0; auto. apply vangle_self; auto.
Qed.

(** u //- v -> u /_ v = π *)
Lemma vantipara_imply_vangle_PI : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> u //- v -> u /_ v = PI.
Proof.
  intros. apply vantipara_imply_uniqueK in H1. destruct H1 as [k [[H1 H2] _]].
  rewrite <- H2. rewrite vangle_vcmul_r_lt0; auto. rewrite vangle_self; auto. lra.
Qed.

(** u // v -> (u /_ v = 0 \/ u /_ v = π) *)
Lemma vcoll_imply_vangle_0_or_PI : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> u // v -> (u /_ v = 0 \/ u /_ v = PI).
Proof.
  intros. apply vcoll_imply_vpara_or_vantipara in H1. destruct H1.
  - apply vpara_imply_vangle_0 in H1; auto.
  - apply vantipara_imply_vangle_PI in H1; auto.
Qed.

(* u /_ v = 0 -> u //+ v *)
Lemma vangle_0_imply_vpara : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> u /_ v = 0 -> u //+ v.
Proof.
  intros.
  apply vangle_0_iff in H1; auto.
  unfold vpara. repeat split; auto.
Abort.

(* u /_ v = π -> u //- v *)
Lemma vangle_PI_imply_vantipara : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> u /_ v = PI -> u //- v.
Proof.
  intros. unfold vpara. repeat split; auto.
  apply vangle_PI_iff in H1; auto.
Abort.

(* (u /_ v = 0 \/ u /_ v = π) -> u // v *)
Lemma vangle_0_or_PI_imply_vcoll : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> (u /_ v = 0 \/ u /_ v = PI -> u // v).
Proof.
  intros. destruct H1.
  (* apply vangle_0_imply_vpara; auto. apply vangle_PI_imply_vpara; auto. *)
  (* Qed. *)
Abort.

(* u // v <-> (u /_ v = 0 \/ u /_ v = π) *)
Lemma vcoll_iff_vangle_0_or_PI : forall {n} (u v : vec n),
    u <> vzero -> v <> vzero -> (u // v <-> u /_ v = 0 \/ u /_ v = PI).
Proof.
  intros. split; intros.
  apply vcoll_imply_vangle_0_or_PI; auto.
  (*   apply vangle_0_or_PI_imply_vpara; auto. *)
  (* Qed. *)
Abort.

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

Hint Resolve vdot_vnorm_bound : vec.

(* ======================================================================= *)
(** ** The cross product of 2D vectors *)

(* 2维向量的叉积的结果若为正，则夹角小于180度。 *)
(** u × v *)
Definition v2cross (u v : vec 2) : R := u.x * v.y - u.y * v.x.

Module Export V2Notations.
  Infix "\x" := v2cross : vec_scope.
End V2Notations.

(** u × v = - (v × u) *)
Lemma v2cross_comm : forall (u v : vec 2), u \x v = (- (v \x u))%R.
Proof. intros. cbv; ra. Qed.

(** 0 <= u × v -> u × v = √((u⋅u)(v⋅v) - (u⋅v)²) *)
Lemma v2cross_ge0_eq : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> 0 <= u \x v ->
    u \x v = sqrt ((<u, u> * <v, v>) - <u, v>²).
Proof.
  intros. apply Rsqr_inj. ra. ra. rewrite !Rsqr_sqrt.
  - cbv. v2f 0. field.
  - pose proof (vdot_sqr_le u v). autounfold with A in *. ra.
Qed.

(** u × v < 0 -> u × v = - √((u⋅u)(v⋅v) - (u⋅v)²) *)
Lemma v2cross_lt0_eq : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> u \x v < 0 ->
    u \x v = (- sqrt ((<u, u> * <v, v>) - <u, v>²))%R.
Proof.
  intros. rewrite v2cross_comm. rewrite (vdot_comm u v).
  rewrite v2cross_ge0_eq; ra.
  - f_equal. f_equal. ring.
  - rewrite v2cross_comm; ra.
Qed.

(* u × v = 0 <-> (<u, v> = ||u|| * ||v||) *)
Lemma v2cross_eq0_iff_vdot_sqr_eq : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> (u \x v = 0 <-> (<u, v>² = <u, u> * <v, v>)%R).
Proof.
  intros. bdestruct (0 <=? u \x v).
  - pose proof (vdot_sqr_le u v).
    pose proof (v2cross_ge0_eq u v H H0 H1). autounfold with A in *.
    rewrite H3. split; intros.
    + apply sqrt_eq_0 in H4; ra.
    + rewrite H4. autorewrite with R. auto.
  - split; intros; ra.
    assert (u \x v < 0); ra.
    pose proof (v2cross_lt0_eq u v H H0 H3).
    rewrite <- H2 in H4. autorewrite with R in H4. ra.
Qed.

(** (u × v = 0) <-> (u /_ v = 0) \/ (u /_ v = π) *)
Lemma v2cross_eq0_iff_vangle : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> (u \x v = 0 <-> ((u /_ v = 0) \/ (u /_ v = PI))).
Proof.
  intros. rewrite v2cross_eq0_iff_vdot_sqr_eq; auto. split; intros.
  - apply vdot_sqr_eq_imply_vangle_0_or_PI; auto.
  - apply vangle_0_or_PI_imply_vdot_sqr_eq; auto.
Qed.

(** (u × v <> 0) <-> 0 < (u /_ v) < π) *)
Lemma v2cross_neq0_iff_vangle : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> (u \x v <> 0 <-> (0 < (u /_ v) < PI)).
Proof.
  intros. rewrite v2cross_eq0_iff_vangle; auto.
  pose proof (vangle_bound u v H H0). ra.
Qed.


(* ======================================================================= *)
(** ** 2D vector theory *)

(** The length of 2D vector has a equal form *)
Lemma v2len_eq : forall v : vec 2, ||v|| = sqrt (v.x² + v.y²).
Proof. intros. cbv. f_equal. ra. Qed.

(** (v.x / ||v||)² = 1 - (v.y / ||v||)² *)
Lemma sqr_x_div_vlen : forall (v : vec 2),
    v <> vzero -> (v.x / ||v||)² = (1 - (v.y / ||v||)²)%R.
Proof.
  intros. rewrite !Rsqr_div'. rewrite <- !vdot_same. field_simplify_eq.
  cbv; field. apply vdot_same_neq0_if_vnonzero; auto.
Qed.
    
(** (v.y / ||v||)² = 1 - (v.x / ||v||)² *)
Lemma sqr_y_div_vlen : forall (v : vec 2),
    v <> vzero -> (v.y / ||v||)² = (1 - (v.x / ||v||)²)%R.
Proof.
  intros. rewrite !Rsqr_div'. rewrite <- !vdot_same. field_simplify_eq.
  cbv; field. apply vdot_same_neq0_if_vnonzero; auto.
Qed.

(** 0 < <u, v> ->
    acos (<u, v> / (||u|| * ||v||)) =
    atan (sqrt (<u, u> * <v, v> - <u, v>²) / <u, v>) *)
Lemma acos_div_dot_gt0_eq : forall (u v : vec 2),
    (0 < <u, v>) ->
    acos (<u, v> / (||u|| * ||v||)) =
      atan (sqrt ((<u, u> * <v, v>) - <u, v>²) / <u, v>).
Proof.
  intros.
  assert (<u, v> <> 0); ra.
  pose proof (vdot_neq0_imply_neq0_l u v H0).
  pose proof (vdot_neq0_imply_neq0_r u v H0).
  pose proof (vlen_gt0 _ H1). pose proof (vlen_gt0 _ H2).
  pose proof (vdot_gt0 _ H1). pose proof (vdot_gt0 _ H2).
  pose proof (vdot_sqr_le u v). pose proof (vdot_sqr_le_form2 u v H1 H2).
  autounfold with A in *.
  rewrite acos_atan; [|ra]. f_equal. apply Rsqr_inj. ra. ra.
  rewrite !Rsqr_div', !Rsqr_mult, <- !vdot_same. field_simplify_eq; [|ra].
  rewrite Rsqr_sqrt; [|ra]. rewrite Rsqr_sqrt; [|ra].
  autorewrite with R. field. split; apply vdot_same_neq0_if_vnonzero; auto.
Qed.

(** <u, v> < 0 ->
    acos (<u, v> / (||u|| * ||v||)) =
    atan (sqrt (<u, u> * <v, v> - <u, v>²) / <u, v>) + PI *)
Lemma acos_div_dot_lt0_eq : forall (u v : vec 2),
    (<u, v> < 0) ->
    acos (<u, v> / (||u|| * ||v||)) =
      (atan (sqrt ((<u, u> * <v, v>) - <u, v>²) / <u, v>) + PI)%R.
Proof.
  intros.
  assert (<u, v> <> 0); ra.
  pose proof (vdot_neq0_imply_neq0_l u v H0).
  pose proof (vdot_neq0_imply_neq0_r u v H0).
  pose proof (vlen_gt0 _ H1). pose proof (vlen_gt0 _ H2).
  pose proof (vdot_gt0 _ H1). pose proof (vdot_gt0 _ H2).
  pose proof (vdot_sqr_le u v). pose proof (vdot_sqr_le_form2 u v H1 H2).
  autounfold with A in *.
  rewrite acos_atan_neg; [|ra]. f_equal. f_equal. apply Rsqr_inj_neg. ra. ra.
  rewrite !Rsqr_div', !Rsqr_mult, <- !vdot_same. field_simplify_eq; [|ra].
  unfold a2r, id.
  rewrite Rsqr_sqrt; [|ra]. rewrite Rsqr_sqrt; [|ra].
  autorewrite with R. field. split; apply vdot_same_neq0_if_vnonzero; auto.
Qed.

(* ======================================================================= *)
(** ** Standard base of 2-D vectors *)
Definition v2i : vec 2 := mkvec2 1 0.
Definition v2j : vec 2 := mkvec2 0 1.

(** 任意向量都能写成该向量的坐标在标准基向量下的线性组合 *)
Lemma v2_linear_composition : forall (v : vec 2), v = v.x \.* v2i + v.y \.* v2j.
Proof. intros. apply v2eq_iff. cbv. ra. Qed.

(** 标准基向量的长度为 1 *)
Lemma v2i_len1 : ||v2i|| = 1.
Proof. cbv. autorewrite with R; auto. Qed.

Lemma v2j_len1 : ||v2j|| = 1.
Proof. cbv. autorewrite with R; auto. Qed.

#[export] Hint Resolve v2i_len1 v2j_len1  : vec.

(** 标准基向量都是单位向量 *)
Lemma v2i_vunit : vunit v2i.
Proof. apply vunit_spec. apply v2i_len1. Qed.

Lemma v2j_vunit : vunit v2j.
Proof. apply vunit_spec. apply v2j_len1. Qed.

(** 标准基向量都是非零向量 *)
Lemma v2i_nonzero : v2i <> vzero.
Proof. intro. apply v2eq_iff in H. inv H. ra. Qed.

Lemma v2j_nonzero : v2j <> vzero.
Proof. intro. apply v2eq_iff in H. inv H. ra. Qed.

#[export] Hint Resolve v2i_nonzero v2j_nonzero : vec.

(** 标准基向量的规范化 *)
Lemma v2i_vnorm : vnorm v2i = v2i.
Proof. apply vnorm_vunit_eq. apply v2i_vunit. Qed.

Lemma v2j_vnorm : vnorm v2j = v2j.
Proof. apply vnorm_vunit_eq. apply v2j_vunit. Qed.

(** 标准基向量与任意向量 v 的点积等于 v 的各分量 *)
Lemma vdot_i_l : forall (v : vec 2), <v2i, v> = v.x. Proof. intros. cbv; ra. Qed.
Lemma vdot_i_r : forall (v : vec 2), <v, v2i> = v.x. Proof. intros. cbv; ra. Qed.
Lemma vdot_j_l : forall (v : vec 2), <v2j, v> = v.y. Proof. intros. cbv; ra. Qed.
Lemma vdot_j_r : forall (v : vec 2), <v, v2j> = v.y. Proof. intros. cbv; ra. Qed.

(** 标准基向量的夹角 *)
Lemma v2angle_i_j : v2i /_ v2j = PI/2.
Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

(** 标准基向量的叉乘 *)
Lemma v2cross_i_l : forall (v : vec 2), v2i \x v = v.y.
Proof. intros. cbv. ring. Qed.
Lemma v2cross_i_r : forall (v : vec 2), v \x v2i = (- v.y)%R.
Proof. intros. cbv. ring. Qed.
Lemma v2cross_j_l : forall (v : vec 2), v2j \x v = (- v.x)%R.
Proof. intros. cbv. ring. Qed.
Lemma v2cross_j_r : forall (v : vec 2), v \x v2j = v.x.
Proof. intros. cbv. ring. Qed.


(* ======================================================================= *)
(** ** vangle2: exact angle for 2D vector (-π,π] *)

(* 
  1. vangle2 的动机：
  * vangle表示两个向量a和b的夹角θ，并未考虑两个向量的前后顺序。
    同时其值域是[0,π]，并未充满整个圆周，这将失去一些方位信息。
  * 可以规定从a到b逆时针旋转为正方向，从而将其值域扩展到 (-π,π] 或 [0,2π)。
    如果得到了 (-π, π]，则只需要当 θ∈(-π,0)时，加上2π即可。
  * 一个现有的模型是 atan2 函数。
  3. 有多种具体做法来实现这种扩展
  (1) 方法一 vangle2A
  * 做法
    由于 a⋅b = |a| |b| cos(θ) = ax*bx + ay*by
         a×b = |a| |b| sin(θ) = ax*by - ay*bx
    所以，tan(θ) = (a×b) / (a⋅b), θ = atan ((a×b) / (a⋅b))
    但是 atan 的值域是 (-π/2, π/2)。
    所以，使用 atan2 (a⋅b) (a×b)，其值域是 (-π, π]
  * 特点
    计算简单，应该是计算机软件中的常见做法。
    但是，因为 atan2 的构造有多个判断分支，也许证明不太方便。
  (2) 方法二 vangle2B
  * 做法
    首先分别得到a和b相对于x轴正方向的角度θa,θb,则所求结果是 θb-θa。
    也就是说，避开了点积和叉积运算。
  * 特点
    理解起来比较直观。但是要计算两次 atan2 运算，计算和证明都会复杂。
  (3) 方法三 vangle2C (取名为 vangle2)
  * 做法
    对之前用 acos 定义的夹角做直接的扩展。
    记夹角 vangle(a,b) 为 α，记叉积 a×b 为 Δ。定义所求的 θ 如下
    当 Δ >= 0,  θ = α  ∈ [0,π]，仅当 Δ = 0时，θ = π
    当 Δ < 0,   θ = -α ∈ (-π,0)
  * 特点
    复用了 vangle，避免了 atan2，可简化证明。
    另外，由于 vangle 的定义只在非零向量有效，所以该方法不支持零向量。
  4. 可证明这三种做法是等价的。我们选择便于证明的“方法三”。
 *)

Definition vangle2A (u v : vec 2) : R := atan2 (u \x v) (<u, v>).

Definition vangle2B (u v : vec 2) : R := atan2 (v.y) (v.x) - atan2 (u.y) (u.x).

(* Note that, vangle2C is the default choice, we will call it vangle2 for short *)
Definition vangle2 (u v : vec 2) : R :=
  let alpha := u /_ v in
  if 0 ??<= u \x v then alpha else (-alpha)%R.

Infix "/2_" := vangle2 : vec_scope.

Lemma vangle2B_vangle2A_equiv : forall (u v : vec 2), vangle2B u v = vangle2A u v.
Proof.
  intros. cbv. pose proof (atan2_minus_eq). unfold Rminus in H. rewrite H.
  f_equal; ra.
Qed.

Lemma vangle2C_vangle2A_equiv : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> vangle2 u v = vangle2A u v.
Proof.
  intros. unfold vangle2A,vangle2,vangle,vnorm.
  rewrite !vdot_vcmul_l,!vdot_vcmul_r.
  pose proof (vlen_gt0 u H). pose proof (vlen_gt0 v H0).
  pose proof (vdot_gt0 u H). pose proof (vdot_gt0 v H0).
  autounfold with A.
  replace (1 / (||u||) * (1 / (||v||) * (<u, v>)))%R with ((<u, v>)/ (||u|| * ||v||)).
  2:{ field. split; apply vlen_neq0_iff_neq0; auto. }
  destruct (<u, v> ??= 0).
  - (* <u, v> = 0 *)
    rewrite e. autorewrite with R; ra.
    rewrite acos_0. destruct (0 ??<= u \x v).
    + rewrite atan2_X0_Yge0; ra.
    + rewrite atan2_X0_Ylt0; ra.
  - (* <u, v> <> 0 *)
    destruct (0 ??< <u, v>).
    + (* 0 < <u, v> *)
      rewrite acos_div_dot_gt0_eq; ra.
      rewrite atan2_Xgt0; ra. 
      destruct (0 ??<= u \x v).
      * (* 0 <= u × v *)
        rewrite v2cross_ge0_eq; ra.
      * (* u × v < 0*)
        rewrite v2cross_lt0_eq; ra.
        rewrite Rdiv_opp_l. rewrite atan_opp. auto.
    + (* <u, v> < 0 *)
      rewrite acos_div_dot_lt0_eq; ra.
      destruct (0 ??<= u \x v).
      * (* 0 <= u × v *)
        rewrite atan2_Xlt0_Yge0; ra. rewrite v2cross_ge0_eq; ra.
      * (* u × v < 0*)
        rewrite atan2_Xlt0_Ylt0; ra. rewrite v2cross_lt0_eq; ra.
        rewrite Rdiv_opp_l. rewrite atan_opp. ring.
Qed.

(* u /2_ v ∈ (-π,π] *)
Lemma vangle2_bound : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> - PI < u /2_ v <= PI.
Proof.
  intros. unfold vangle2.
  pose proof PI_bound.
  pose proof (vangle_bound u v H H0).
  pose proof (v2cross_neq0_iff_vangle u v H H0).
  destruct (0 ??<= u \x v); ra.
Qed.

(** u × v = 0 -> (u /2_ v) = (v /2_ u) *)
Lemma vangle2_comm_cross_eq0 : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> u \x v = 0 -> u /2_ v = v /2_ u.
Proof.
  intros. remember H1 as H2. clear HeqH2.
  apply v2cross_eq0_iff_vangle in H1; auto. destruct H1.
  - unfold vangle2. rewrite (vangle_comm v u). rewrite H1.
    destruct (_??<=_), (_??<=_); ra.
  - unfold vangle2. rewrite (vangle_comm v u). rewrite H1.
    rewrite (v2cross_comm v u). rewrite H2.
    autorewrite with R. auto.
Qed.

(** u × v <> 0 -> u /2_ v = - (v /2_ u) *)
Lemma vangle2_comm_cross_neq0 : forall (u v : vec 2),
    u <> vzero -> v <> vzero -> u \x v <> 0 -> u /2_ v = (- (v /2_ u))%R.
Proof.
  intros. remember H1 as H2. clear HeqH2.
  apply v2cross_neq0_iff_vangle in H1; auto.
  unfold vangle2. rewrite (vangle_comm v u).
  rewrite (v2cross_comm v u). destruct (_??<=_),(_??<=_); ra.
Qed.

(** i /2_ j = π/2 *)
Fact vangle2_i_j : v2i /2_ v2j = PI/2.
Proof.
  rewrite vangle2C_vangle2A_equiv; auto with vec. cbv. apply atan2_X0_Yge0; ra.
Qed.

(** j /2_ j = - π/2 *)
Fact vangle2_j_i : v2j /2_ v2i = - PI/2.
Proof.
  rewrite vangle2C_vangle2A_equiv; auto with vec. cbv. apply atan2_X0_Ylt0; ra.
Qed.

(** cos (u /2_ v) = cos (u /_ v) *)
Lemma cos_vangle2_eq : forall (u v : vec 2), cos (u /2_ v) = cos (u /_ v).
Proof. intros. unfold vangle2. destruct (_??<=_); ra. Qed.

(** sin (u /2_ v) = (0 <= u \x v) ? sin (v /_ v) : (- sin (u /_ v)) *)
Lemma sin_vangle2_eq : forall (u v : vec 2),
    sin (u /2_ v) = if 0 ??<= u \x v then sin (u /_ v) else (- sin (u /_ v))%R.
Proof. intros. unfold vangle2. destruct (_??<=_); ra. Qed.

(** i与任意非零向量v的夹角的余弦等于其横坐标除以长度 *)
Lemma cos_vangle2_i : forall (v : vec 2), v <> vzero -> cos (v2i /2_ v) = (v.x / ||v||)%R.
Proof.
  intros. rewrite cos_vangle2_eq. unfold vangle. rewrite cos_acos; auto with vec.
  rewrite v2i_vnorm. rewrite vdot_i_l. rewrite vnth_vnorm; auto.
Qed.
  
(** i与任意非零向量v的夹角的正弦等于其纵坐标除以长度 *)
Lemma sin_vangle2_i : forall (v : vec 2), v <> vzero -> sin (v2i /2_ v) = (v.y / ||v||)%R.
Proof.
  intros. unfold vangle2. unfold vangle. rewrite v2i_vnorm. rewrite vdot_i_l.
  rewrite vnth_vnorm; auto. pose proof (vlen_gt0 v H).
  rewrite v2cross_i_l. destruct (_??<=_).
  - rewrite sin_acos; auto with vec.
    + rewrite <- sqr_y_div_vlen; auto. ra.
    + apply vnth_div_vlen_bound; auto.
  - rewrite sin_neg. rewrite sin_acos; auto with vec.
    + rewrite <- sqr_y_div_vlen; auto. rewrite sqrt_Rsqr_abs. rewrite Rabs_left; ra.
    + apply vnth_div_vlen_bound; auto.
Qed.

(** j与任意非零向量v的夹角的余弦等于其纵坐标除以长度 *)
Lemma cos_vangle2_j : forall (v : vec 2), v <> vzero -> cos (v2j /2_ v) = (v.y / ||v||)%R.
Proof.
  intros. rewrite cos_vangle2_eq. unfold vangle. rewrite cos_acos.
  - rewrite v2j_vnorm. rewrite vdot_j_l. rewrite vnth_vnorm; auto.
  - apply vdot_vnorm_bound; auto. apply v2j_nonzero.
Qed.

(** j与任意非零向量v的夹角的正弦等于其横坐标取负除以长度 *)
Lemma sin_vangle2_j : forall (v : vec 2),
    v <> vzero -> sin (v2j /2_ v) = (- v.x / ||v||)%R.
Proof.
  intros. unfold vangle2. unfold vangle. rewrite v2j_vnorm. rewrite vdot_j_l.
  rewrite vnth_vnorm; auto. pose proof (vlen_gt0 v H).
  rewrite v2cross_j_l. destruct (_??<=_).
  - assert (v.x <= 0); ra. rewrite sin_acos; auto with vec.
    + rewrite <- sqr_x_div_vlen; auto. rewrite sqrt_Rsqr_abs. rewrite Rabs_left1; ra.
      assert (0 < / (||v||)); ra.
    + apply vnth_div_vlen_bound; auto.
  - assert (v.x > 0); ra. rewrite sin_neg. rewrite sin_acos; auto with vec.
    + rewrite <- sqr_x_div_vlen; auto.
      rewrite sqrt_Rsqr_abs. rewrite Rabs_right; ra.
    + apply vnth_div_vlen_bound; auto.
Qed.

(** ||a|| * cos (i /2_ a) = a.x *)
Lemma v2len_mul_cos_vangle2_i : forall (a : vec 2),
    a <> vzero -> (||a|| * cos (v2i /2_ a) = a.x)%R.
Proof.
  intros. rewrite cos_vangle2_i; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * sin (i /2_ a) = a.y *)
Lemma v2len_mul_sin_vangle2_i : forall (a : vec 2),
    a <> vzero -> (||a|| * sin (v2i /2_ a) = a.y)%R.
Proof.
  intros. rewrite sin_vangle2_i; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * cos (j /2_ a) = a.y *)
Lemma v2len_mul_cos_vangle2_j : forall (a : vec 2),
    a <> vzero -> (||a|| * cos (v2j /2_ a) = a.y)%R.
Proof.
  intros. rewrite cos_vangle2_j; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * sin (j /2_ a) = - a.x *)
Lemma v2len_mul_sin_vangle2_j : forall (a : vec 2),
    a <> vzero -> (||a|| * sin (v2j /2_ a) = - a.x)%R.
Proof.
  intros. rewrite sin_vangle2_j; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(* ======================================================================= *)
(** ** Properties about parallel, orthogonal of 3D vectors *)

(* 与两个不共线的向量都垂直的向量是共线的 *)
Lemma vcoll_if_vorth_both : forall {n} (u v w1 w2 : vec n),
    ~(u // v) -> u _|_ w1 -> v _|_ w1 -> u _|_ w2 -> v _|_ w2 -> w1 // w2.
Proof.
Abort.

(** 两个平行向量u和v若长度相等，则 u = v *)
Lemma vpara_and_same_len_imply : forall {n} (u v : vec n),
    u //+ v -> ||u|| = ||v|| -> u = v.
Proof.
  intros. destruct H as [H1 [H2 [k [H3 H4]]]].
  destruct (Aeqdec u vzero), (Aeqdec v vzero); try easy.
  assert (k = 1).
  { rewrite <- H4 in H0. rewrite vlen_vcmul in H0. unfold a2r,id in H0.
    symmetry in H0. apply Rmult_eq_r_reg in H0; auto.
    autounfold with A in *. unfold Aabs in H0. destruct (_<=?_); lra.
    apply vlen_neq0_iff_neq0; auto. }
  rewrite H in H4. rewrite vcmul_1_l in H4; auto.
Qed.

(** 两个反平行向量u和v若长度相等，则 u = - v *)
Lemma vantipara_and_same_len_imply : forall {n} (u v : vec n),
    u //- v -> ||u|| = ||v|| -> u = -v.
Proof.
  intros. destruct H as [H1 [H2 [k [H3 H4]]]].
  destruct (Aeqdec u vzero), (Aeqdec v vzero); try easy.
  assert (k = - (1))%R.
  { rewrite <- H4 in H0. rewrite vlen_vcmul in H0. unfold a2r,id in H0.
    symmetry in H0. apply Rmult_eq_r_reg in H0; auto.
    autounfold with A in *. unfold Aabs in H0. destruct (_<=?_); lra.
    apply vlen_neq0_iff_neq0; auto. }
  rewrite H in H4. rewrite vcmul_neg1_l in H4. rewrite <- H4, vopp_vopp. auto.
Qed.

(** 两个共线向量u和v若长度相等，则 u = ± v *)
Lemma vcoll_and_same_len_imply : forall {n} (u v : vec n),
    u // v -> ||u|| = ||v|| -> u = v \/ u = -v.
Proof.
  intros. destruct (vcoll_imply_vpara_or_vantipara u v H).
  - left. apply vpara_and_same_len_imply; auto.
  - right. apply vantipara_and_same_len_imply; auto.
Qed.

(* ======================================================================= *)
(** ** The cross product (vector product) of two 3-dim vectors *)
(* 1. 外积的几何学(三角学)意义  ||P×Q|| = ||P|| * ||Q|| * sin α
   2. 外积若不为零，则其与这两个向量都垂直。有两个向量，方向相反。
      根据所选左/右手系来确定方向。
   3. 3D坐标系中的x,y,z轴正方向用 i,j,k 表示，并按 i,j,k 顺序组成一个循环，则：
   (1) 相邻两个向量按相同次序的外积为第三个向量，即 i×j=k, j×k=i, k×i=j。
   (2) 相邻两个向量按相反次序的外积为第三个向量的取反，即 j×i=-k, etc. *)

(** u \x v *)
Definition v3cross (u v : vec 3) : vec 3 :=
  mkvec3
    (u.2 * v.3 - u.3 * v.2)%R
    (u.3 * v.1 - u.1 * v.3)%R
    (u.1 * v.2 - u.2 * v.1)%R.
Infix "\x" := v3cross : vec_scope.

(* functional style, for C-code generation *)
Definition v3crossFun (u v : vec 3) : vec 3 :=
  f2v (fun i =>
         match i with
         | 0 => u.2*v.3 - u.3*v.2
         | 1 => u.3*v.1 - u.1*v.3
         | 2 => u.1*v.2 - u.2*v.1
         | _=> 0
         end)%R.

(* These two definitions should equiv *)
Lemma v3cross_v3crossFun_equiv : forall u v : vec 3, v3cross u v = v3crossFun u v.
Proof. intros. apply v3eq_iff. auto. Qed.

(** v × v = 0 *)
Lemma v3cross_self : forall v : vec 3, v \x v = vzero.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** u × v = - (v × u) *)
Lemma v3cross_anticomm : forall u v : vec 3, u \x v = -(v \x u).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (u + v) × w = (u × w) + (v × w) *)
Lemma v3cross_add_distr_l : forall u v w : vec 3,
    (u + v) \x w = (u \x w) + (v \x w).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** u × (v + w) = (u × v) + (u × w) *)
Lemma v3cross_add_distr_r : forall u v w : vec 3,
    u \x (v + w) = (u \x v) + (u \x w).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (- u) × v = - (u × v) *)
Lemma v3cross_vopp_l : forall u v : vec 3, (-u) \x v = - (u \x v).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** u × (- v) = - (u × v) *)
Lemma v3cross_vopp_r : forall u v : vec 3, u \x (-v) = - (u \x v).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (u - v) × w = (u × w) - (v × w) *)
Lemma v3cross_sub_distr_l : forall u v w : vec 3,
    (u - v) \x w = (u \x w) - (v \x w).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** u × (v - w) = (u × v) - (u × w) *)
Lemma v3cross_sub_distr_r : forall u v w : vec 3,
    u \x (v - w) = (u \x v) - (u \x w).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (k \.* u) × v = k \.* (u × v) *)
Lemma v3cross_vcmul_assoc_l : forall (k : R) (u v : vec 3),
    (k \.* u) \x v = k \.* (u \x v).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** u × (a \.* v) = a \.* (u × v) *)
Lemma v3cross_vcmul_assoc_r : forall (a : R) (u v : vec 3),
    u \x (a \.* v) = a \.* (u \x v).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** <u × v, w> = <w × u, v> *)
Lemma v3cross_vdot_l : forall u v w : vec 3, <u \x v, w> = <w \x u, v>.
Proof. intros. cbv. field. Qed.

(** <u × v, w> = <v × w, u> *)
Lemma v3cross_dot_r : forall u v w : vec 3, <u \x v, w> = <v \x w, u>.
Proof. intros. cbv. field. Qed.

(** <u × v, u> = 0 *)
Lemma v3cross_vdot_same_l : forall u v : vec 3, <u \x v, u> = 0.
Proof. intros. cbv. field. Qed.

(** <u × v, v> = 0 *)
Lemma v3cross_vdot_same_r : forall u v : vec 3, <u \x v, v> = 0.
Proof. intros. cbv. field. Qed.

(** u × (v × u) = (u × v) × u = *)
Lemma v3cross_u_vu : forall u v : vec 3, u \x (v \x u) = (u \x v) \x u.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (u × u) × v = - (u × (v × u)) *)
Lemma v3cross_u_uv : forall u v : vec 3, u \x (u \x v) = - ((u \x v) \x u).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (u × v) × u = <u,u> \.* v - <u,v> \.* u *)
Lemma v3cross_uv_u_eq_minus : forall u v : vec 3,
    (u \x v) \x u = <u,u> \.* v - <u,v> \.* u.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** u × (v × u) = <u,u> \.* v - <u,v> \.* u *)
Lemma v3cross_u_vu_eq_minus : forall u v : vec 3,
    u \x (v \x u) = <u,u> \.* v - <u,v> \.* u.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** u × (u × v) = <u,v> \.* u - <u,u> \.* v *)
Lemma v3cross_u_uv_eq_minus : forall u v : vec 3,
    u \x (u \x v) = <u,v> \.* u - <u,u> \.* v.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** <a×b, c×d> = <a,c> * <b,d> - <a,d> * <b,c> *)
Lemma v3cross_dot_v3cross : forall (a b c d : vec 3),
    (<a \x b, c \x d > = (<a, c> * <b, d>) - (<a, d> * <b, c>))%R.
Proof.
  (* 我尚未完成推理，先暴力证明 *)
  intros. cbv; ra.
Qed.

(** (u × v) ⟂ u *)
Lemma v3cross_orth_l : forall u v : vec 3, (u \x v) _|_ u.
Proof. intros. unfold vorth. apply v3cross_vdot_same_l. Qed.

(** (u × v) ⟂ v *)
Lemma v3cross_orth_r : forall u v : vec 3, (u \x v) _|_ v.
Proof. intros. unfold vorth. apply v3cross_vdot_same_r. Qed.

(** || u × v ||² = ||u||² * ||v||² - <u,v>² *)
Lemma vlen_v3cross_form1 : forall u v : vec 3,
    || u \x v ||² = ((||u||² * ||v||²) - (<u,v>)²)%R.
Proof. intros. rewrite <- !vdot_same. cbv; ra. Qed.

(** || u × v || = ||u|| * ||v|| * |sin (vangle u v)| *)
Lemma vlen_v3cross : forall u v : vec 3,
    u <> vzero -> v <> vzero -> || u \x v || = (||u|| * ||v|| * sin (u /_ v))%R.
Proof.
  intros. pose proof (vlen_v3cross_form1 u v).
  rewrite vdot_eq_cos_angle in H1. rewrite !Rsqr_mult in H1. rewrite cos2 in H1.
  apply Rsqr_inj; ra. apply vlen_ge0.
  apply Rmult_le_pos. apply vlen_ge0.
  apply Rmult_le_pos. apply vlen_ge0. apply sin_vangle_ge0; auto.
Qed.

(** ||u × v|| = 0 <-> (θ = 0 \/ θ = PI) *)
Lemma vlen_v3cross_eq0_iff_angle_0_pi : forall (u v : vec 3),
    u <> vzero -> v <> vzero -> ||u \x v|| = 0 <-> (u /_ v = 0 \/ u /_ v = PI).
Proof.
  intros. rewrite vlen_v3cross; auto.
  pose proof (vangle_bound u v H H0).
  apply vlen_neq0_iff_neq0 in H,H0.
  split; intros.
  - apply Rmult_integral in H2; destruct H2; ra.
    apply Rmult_integral in H2; destruct H2; ra.
    apply sin_eq_O_2PI_0 in H2; ra.
  - apply Rmult_eq_0_compat. right.
    apply Rmult_eq_0_compat. right.
    apply sin_eq_O_2PI_1; ra.
Qed.

(** u × v = vzero <-> (θ = 0 \/ θ = PI) *)
Lemma v3cross_eq0_iff_angle_0_pi : forall (u v : vec 3),
    u <> vzero -> v <> vzero -> (u \x v = vzero <-> (u /_ v = 0 \/ u /_ v = PI)).
Proof.
  intros. rewrite <- vlen_v3cross_eq0_iff_angle_0_pi; auto.
  rewrite vlen_eq0_iff_eq0. easy.
Qed.

(** u × v = vzero <-> u // v *)
Lemma v3cross_eq0_iff_vcoll : forall (u v : vec 3),
    u <> vzero -> v <> vzero -> (u \x v = vzero <-> u // v).
Proof.
  intros. rewrite v3cross_eq0_iff_angle_0_pi; auto. split; intros.
  2:{ apply vcoll_imply_vangle_0_or_PI; auto. }
  -
Abort.

(** u × v = (sin (u ∠ v) * ||u|| * ||v||) \.* vnorm (u × v) *)
Lemma v3cross_eq_vcmul : forall (u v : vec 3),
    u <> vzero -> v <> vzero ->
    u /_ v <> 0 -> u /_ v <> PI ->
    u \x v = ((sin (u /_ v) * ||u|| * ||v||)%R \.* vnorm (u \x v)).
Proof.
  intros. unfold vnorm. rewrite vlen_v3cross; auto.
  rewrite vcmul_assoc.
  match goal with |- context [?a \.* _] => replace a with 1 end.
  rewrite vcmul_1_l; easy.
  autounfold with A. field. repeat split.
  - pose proof (sin_vangle_gt0 u v H H0). ra.
  - apply vlen_neq0_iff_neq0; auto.
  - apply vlen_neq0_iff_neq0; auto.
Qed.

(** If u ∠ v ∈ (0,π) (that is they are Linear-Independent), then u × v is nonzero. *)
Lemma v3cross_neq0_if_vangle_in_0_pi : forall (u v : vec 3),
    u <> vzero -> v <> vzero -> 0 < u /_ v < PI -> u \x v <> vzero.
Proof.
  intros. apply vlen_neq0_iff_neq0.
  intro. apply vlen_v3cross_eq0_iff_angle_0_pi in H2; auto. ra.
Qed.


(* ======================================================================= *)
(** ** Skew-symmetric matrix of 3-dimensions *)

(** Equivalent form of skewP of 3D vector *)
Lemma skewP3_eq : forall M : mat 3 3,
    skewP M <->
      (M.11 = 0) /\ (M.22 = 0) /\ (M.33 = 0) /\
        (M.12 = -M.21 /\ M.13 = -M.31 /\ M.23 = -M.32)%R.
Proof.
  intros. split; intros.
  - hnf in H. assert (m2l (- M)%M = m2l (M\T)). rewrite H. auto.
    cbv in H0. list_eq. cbv. ra.
  - hnf. cbv in H. meq; ra.
Qed.

(** Convert a vector to its corresponding skew-symmetric matrix *)
Definition skew3 (v : vec 3) : mat 3 3 :=
  l2m [[0; -v.3; v.2];
       [v.3; 0; -v.1];
       [-v.2; v.1; 0]]%R.
Notation "`| v |x" := (skew3 v) : vec_scope.

Lemma skew3_spec : forall a, skewP (skew3 a).
Proof. intros. rewrite skewP3_eq. cbv. lra. Qed.

(** Convert a skew-symmetric matrix to its corresponding vector *)
Definition vex3 (M : mat 3 3) : vec 3 := l2v [M.32; M.13; M.21].

Lemma skew3_vex3 : forall (m : mat 3 3), skewP m -> skew3 (vex3 m) = m.
Proof. intros. apply skewP3_eq in H. cbv in H. meq; ra. Qed.

Lemma vex3_skew3 : forall (v : vec 3), vex3 (skew3 v) = v.
Proof. intros. veq. Qed.

Lemma v3cross_eq_skew_mul_vec : forall (u v : vec 3),
    u \x v = `|u|x * v.
Proof. intros; veq; ra. Qed.

Lemma v3cross_eq_skew_mul_cvec : forall (u v : cvec 3),
    cv2v u \x (cv2v v) = cv2v ((`|cv2v u|x * v)%M).
Proof. intros; veq; ra. Qed.

Section examples.
  
  (** Example 4, page 19, 高等数学，第七版 *)
  Example v3cross_example1 : (l2v [2;1;-1]) \x (l2v [1;-1;2]) = l2v [1;-5;-3].
  Proof. veq; ra. Qed.

  (** Example 5, page 19, 高等数学，第七版 *)
  (** 根据三点坐标求三角形面积 *)
  Definition area_of_triangle (A B C : vec 3) :=
    let AB := B - A in
    let AC := C - A in
    ((1/2) * ||AB \x AC||)%R.

  (** Example 6, page 20, 高等数学，第七版 *)
  (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*)
  Definition v3_rotation_model (ω r v : vec 3) := v = ω \x r.
  
End examples.

(* ======================================================================= *)
(** ** 3D vector theory *)

(** vdot in 3D has given form *)
Lemma v3dot_eq : forall u v : vec 3, <u, v> = (u.1 * v.1 + u.2 * v.2 + u.3 * v.3)%R.
Proof. intros. cbv. ring. Qed.

(** A 3D unit vector satisfy these algebraic equations *)

Lemma v3unit_sqr_xyz : forall (v : vec 3), vunit v -> (v.x² + v.y² + v.z² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_xzy : forall (v : vec 3), vunit v -> (v.x² + v.z² + v.y² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_yzx : forall (v : vec 3), vunit v -> (v.y² + v.z² + v.x² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_yxz : forall (v : vec 3), vunit v -> (v.y² + v.x² + v.z² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_zxy : forall (v : vec 3), vunit v -> (v.z² + v.x² + v.y² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_zyx : forall (v : vec 3), vunit v -> (v.z² + v.y² + v.x² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_x : forall (v : vec 3), vunit v -> v.x² = (1 - v.y² - v.z²)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_y : forall (v : vec 3), vunit v -> v.y² = (1 - v.x² - v.z²)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_z : forall (v : vec 3), vunit v -> v.z² = (1 - v.x² - v.y²)%R.
Proof. intros. cbv in *. ra. Qed.

(** vnorm v = (v.1 / |v|, v.2 / |v|, v.3 / |v|) *)
Lemma v3norm_eq : forall (v : vec 3),
    let v' := vnorm v in
    v <> vzero -> (v'.1 = v.1 / ||v||) /\ (v'.2 = v.2 / ||v||) /\ (v'.3 = v.3 / ||v||).
Proof.
  intros. unfold v', vnorm. rewrite !vnth_vcmul. autounfold with A.
  repeat split; ra.
Qed.

Lemma v3norm_sqr_eq1 : forall (v : vec 3),
    v <> vzero -> ((v.1 / ||v||)² + (v.2 / ||v||)² + (v.3 / ||v||)² = 1)%R.
Proof.
  intros. pose proof (vdot_same_neq0_if_vnonzero v H).
  rewrite !Rsqr_div'. rewrite <- !vdot_same. cbv. field. cbv in H0. ra.
Qed.

(** Projection component of vector in 3D : 投影分量 *)
(*
  (** The matrix form of vproj in 3-dim *)
  Definition v3proj (u v : vec 3) : vec 3 :=
    let x := v.1 in
    let y := v.2 in
    let z := v.3 in
    let M : mat 3 3 :=
      l2m [[x * x; x * y; x * z];
           [y * x; y * y; y * z];
           [z * x; z * y; z * z]]%R in
    (1 / <v,v>) \.* (M * u).

  Lemma v3proj_spec : forall u v : vec 3, v3proj u v = vproj u v.
  Proof. apply v3eq_iff; cbv; ra. Qed.

  (** v × (proj u v) = 0 *)
  Lemma v3cross_v3proj_eq0 : forall u v : vec 3, v \x v3proj u v = vzero.
  Proof. apply v3eq_iff; cbv; ra. Qed.
 *)

(** Perpendicular component of vector in 3D : 垂直分量 *)

(** The perpendicular vector can be get from cross product.
    ref: https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula.
    利用两次叉乘得到垂直分量的表示。此式在几何上容易理解，但代数上不是很显然。*)
Definition v3perp (u v : vec 3) : vec 3 := - ((u \x v) \x v).

Lemma v3perp_spec : forall (u v : vec 3), vunit v -> v3perp u v = vperp u v.
Proof.
  intros.
  pose proof (v3unit_sqr_xyz v H) as H0; cbv in H0; v2f 0.
  apply v3eq_iff. repeat split; cbv; v2f 0; field_simplify; try lra.
  - pose proof (v3unit_sqr_xzy v H) as H1; cbv in H1; v2f 0;
      ring_simplify in H1; rewrite H1; clear H1. field.
  - pose proof (v3unit_sqr_yxz v H) as H1; cbv in H1; v2f 0;
      ring_simplify in H1; rewrite H1; clear H1. field.
  - pose proof (v3unit_sqr_zyx v H) as H1; cbv in H1; v2f 0;
      ring_simplify in H1; rewrite H1; clear H1. field.
Qed.

(** Two vectors in 3D are parallel, can be determined by cross-product.
      That is: u // v <-> u × v = 0 *)
Definition v3para (u v : vec 3) : Prop := u \x v = vzero.

Lemma v3para_spec : forall (u v : vec 3),
    u <> vzero -> v <> vzero -> (u // v <-> v3para u v).
Proof.
  intros. unfold v3para. rewrite v3cross_eq0_iff_angle_0_pi; auto.
  (*   apply vpara_iff_vangle_0_or_PI; auto. *)
  (* Qed. *)
Abort.


(* ======================================================================= *)
(** ** Standard base for Euclidean space (3-D vectors) *)

Definition v3i : vec 3 := mkvec3 1 0 0.
Definition v3j : vec 3 := mkvec3 0 1 0.
Definition v3k : vec 3 := mkvec3 0 0 1.

(** 任意向量都能写成该向量的坐标在标准基向量下的线性组合 *)
Lemma v3_linear_composition : forall (v : vec 3),
    v = v.x \.* v3i + v.y \.* v3j + v.z \.* v3k.
Proof. intros. apply v3eq_iff. cbv. ra. Qed.

(** 标准基向量的长度为 1 *)
Lemma v3i_len1 : ||v3i|| = 1. Proof. cbv. autorewrite with R; auto. Qed.
Lemma v3j_len1 : ||v3j|| = 1. Proof. cbv. autorewrite with R; auto. Qed.
Lemma v3k_len1 : ||v3k|| = 1. Proof. cbv. autorewrite with R; auto. Qed.

(** 标准基向量都是单位向量 *)
Lemma v3i_vunit : vunit v3i. Proof. apply vunit_spec. apply v3i_len1. Qed.
Lemma v3j_vunit : vunit v3j. Proof. apply vunit_spec. apply v3j_len1. Qed.
Lemma v3k_vunit : vunit v3k. Proof. apply vunit_spec. apply v3k_len1. Qed.

(** 标准基向量都是非零向量 *)
Lemma v3i_nonzero : v3i <> vzero.
Proof. intro. apply v3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.

Lemma v3j_nonzero : v3j <> vzero.
Proof. intro. apply v3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.

Lemma v3k_nonzero : v3k <> vzero.
Proof. intro. apply v3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.

(** 标准基向量的规范化 *)
Lemma v3i_vnorm : vnorm v3i = v3i.
Proof. apply vnorm_vunit_eq. apply v3i_vunit. Qed.

Lemma v3j_vnorm : vnorm v3j = v3j.
Proof. apply vnorm_vunit_eq. apply v3j_vunit. Qed.

Lemma v3k_vnorm : vnorm v3k = v3k.
Proof. apply vnorm_vunit_eq. apply v3k_vunit. Qed.

(** 标准基向量与任意向量v的点积等于v的各分量 *)
Lemma v3dot_i_l : forall v : vec 3, <v3i, v> = v.x. Proof. intros. cbv; ring. Qed.
Lemma v3dot_j_l : forall v : vec 3, <v3j, v> = v.y. Proof. intros. cbv; ring. Qed.
Lemma v3dot_k_l : forall v : vec 3, <v3k, v> = v.z. Proof. intros. cbv; ring. Qed.
Lemma v3dot_i_r : forall v : vec 3, <v, v3i> = v.x. Proof. intros. cbv; ring. Qed.
Lemma v3dot_j_r : forall v : vec 3, <v, v3j> = v.y. Proof. intros. cbv; ring. Qed.
Lemma v3dot_k_r : forall v : vec 3, <v, v3k> = v.z. Proof. intros. cbv; ring. Qed.

(** i × j = k, j × k = i, k × i = j *)
Lemma v3cross_ij : v3i \x v3j = v3k. Proof. apply v3eq_iff; cbv; ra. Qed.
Lemma v3cross_jk : v3j \x v3k = v3i. Proof. apply v3eq_iff; cbv; ra. Qed.
Lemma v3cross_ki : v3k \x v3i = v3j. Proof. apply v3eq_iff; cbv; ra. Qed.

(** j × i = -k, k × j = -i, i × k = -j *)
Lemma v3cross_ji : v3j \x v3i = - v3k. Proof. apply v3eq_iff; cbv; ra. Qed.
Lemma v3cross_kj : v3k \x v3j = - v3i. Proof. apply v3eq_iff; cbv; ra. Qed.
Lemma v3cross_ik : v3i \x v3k = - v3j. Proof. apply v3eq_iff; cbv; ra. Qed.

(** 矩阵乘以标准基向量得到列向量 *)
Lemma mmulv_v3i : forall (M : smat 3), M * v3i = M&1. Proof. intros; veq; ra. Qed.
Lemma mmulv_v3j : forall (M : smat 3), M * v3j = M&2. Proof. intros; veq; ra. Qed.
Lemma mmulv_v3k : forall (M : smat 3), M * v3k = M&3. Proof. intros; veq; ra. Qed.

(** 矩阵的列向量等于矩阵乘以标准基向量 *)
Lemma mcol_eq_mul_v3i : forall (M : smat 3), M&1 = M * v3i. Proof. intros; veq; ra. Qed.
Lemma mcol_eq_mul_v3j : forall (M : smat 3), M&2 = M * v3j. Proof. intros; veq; ra. Qed.
Lemma mcol_eq_mul_v3k : forall (M : smat 3), M&3 = M * v3k. Proof. intros; veq; ra. Qed.

(** 矩阵的行向量等于矩阵乘以标准基向量 *)
Lemma mrow_eq_mul_v3i : forall (M : smat 3), M.1 = M\T * v3i. Proof. intros; veq; ra. Qed.
Lemma mrow_eq_mul_v3j : forall (M : smat 3), M.2 = M\T * v3j. Proof. intros; veq; ra. Qed.
Lemma mrow_eq_mul_v3k : forall (M : smat 3), M.3 = M\T * v3k. Proof. intros; veq; ra. Qed.

(** 标准基向量的夹角 *)
Lemma v3angle_i_j : v3i /_ v3j = PI/2.
Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

Lemma v3angle_j_k : v3j /_ v3k = PI/2.
Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

Lemma v3angle_k_i : v3k /_ v3i = PI/2.
Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

(* ======================================================================= *)
(** ** Direction cosine of 3-D vectors *)

(* ToDo:
   ref: https://en.wikipedia.org/wiki/Euclidean_vector
   关于方向余弦矩阵，这里有更多的工作要做，不仅仅是三维，
   它可用于表示在不同的笛卡尔基之间的变换。
   
   以三维为例，给定两组基{e1,e2,e3}和{n1,n2,n3}，
   任意向量a可以被表示为 a = pe1 + qe2 + re3 = un1 + vn2 + wn3，
   而每个系数可这样获得 p = a⋅e1, q = a⋅e2, 依次类推。

   于是我们可以根据第一组基下的坐标来计算第二组基下的坐标
   u = (pe1 + qe2 + re3)⋅n1 = pe1⋅n1 + qe2⋅n1 + re3⋅n1,
   v = (pe1 + qe2 + re3)⋅n2 = pe1⋅n2 + qe2⋅n2 + re3⋅n2,
   w = (pe1 + qe2 + re3)⋅n3 = pe1⋅n3 + qe2⋅n3 + re3⋅n3.

   将每个点积用一个唯一的标量代替后得到
   u = c11p + c12q + c13r,
   v = c21p + c22q + c23r,
   w = c31p + c32q + c33r.
   
   这些方程表示为单个矩阵等式
   [u]   [c11 c12 c13] [p]
   [v] = [c21 c22 c23] [q]. 
   [w]   [c31 c32 c33] [r]

   该矩阵等式关联了向量a在基n下的坐标(u,v,w)和在基e下的奏表(p,q,r)。
   每个矩阵元素cjk是nj和ek的方向余弦，（即，两个向量夹角的余弦，也等于点积）。
   因此，
   c11 = n1⋅e1, c12 = n1⋅e2, c13 = n1⋅e3
   c21 = n2⋅e1, c12 = n2⋅e2, c13 = n2⋅e3
   c31 = n3⋅e1, c12 = n3⋅e2, c13 = n3⋅e3

   上述包含了所有cjk的矩阵称为“从e到n的变换矩阵”，或“从e到n的旋转矩阵”，或“从e到n的
   方向余弦矩阵”。
 *)

(** Direction cosine of a vector relative to standard basis.
      That is : (cos α, cos β, cos γ) *)
Definition v3dc (v : vec 3) : vec 3 :=
  mkvec3 (v.1 / ||v||) (v.2 / ||v||) (v.3 / ||v||). 

(** The original (lower level) definition as its spec. *)
Lemma v3dc_spec : forall (v : vec 3),
    let v' := v3dc v in
    let r := ||v|| in 
    (v'.1 = <v,v3i> / r) /\ v'.2 = (<v,v3j> / r) /\ v'.3 = (<v,v3k> / r).
Proof. intros. rewrite v3dot_i_r, v3dot_j_r, v3dot_k_r; auto. Qed.

(** dc of a nonzero vector is a unit vector *)
Lemma v3dc_unit : forall (v : vec 3), v <> vzero -> vunit (v3dc v).
Proof.
  intros. unfold vunit,Vector.vunit. cbn. autorewrite with R.
  apply v3norm_sqr_eq1; auto.
Qed.


(* ======================================================================= *)
(** ** The triple scalar product (or called Mixed products) of 3-D vectors *)

(** [u v w] = <u×v, w>
    几何意义：绝对值表示以向量a,b,c为棱的平行六面体的体积，另外若a,b,c组成右手系，
    则混合积的符号为正；若组成左手系，则符号为负。*)
Definition v3mixed (u v w : vec 3) : R := <u \x v, w>.
Notation "`[ u v w ]" :=
  (v3mixed u v w) (at level 1, u, v at level 9, format "`[ u  v  w ]") : vec_scope.

(* alternate definition of v3mixed *)
Lemma v3mixed_swap_op : forall (u v w : vec 3), <u, v \x w> = <u \x v, w>.
Proof. intros. cbv. ring. Qed.

(** The mixed product with columns is equal to the determinant *)
Lemma v3mixed_eq_det_cols : forall u v w : vec 3, `[u v w] = mdet (cvl2m [u;v;w]).
Proof. intros. cbv. ring. Qed.

(** The mixed product with rows is equal to the determinant *)
Lemma v3mixed_eq_det_rows : forall u v w : vec 3, `[u v w] = mdet (rvl2m [u;v;w]).
Proof. intros. cbv. ring. Qed.

(** [u v w] = [v w u] *)
Lemma v3mixed_comm : forall (u v w : vec 3), `[u v w] = `[v w u].
Proof. intros. cbv. ring. Qed.

(** 若混合积≠0，则三向量可构成平行六面体，即三向量不共面，反之也成立。
    所以：三向量共面的充要条件是混合积为零。*)
Definition v3coplanar (u v w : vec 3) : Prop := `[u v w] = 0.

(** (u,v)的法向量和(v,v3)的法向量相同，则u,v,v3共面 *)
Lemma v3cross_same_v3coplanar : forall u v w : vec 3,
    u \x v = v \x w -> v3coplanar u v w.
Proof.
  intros. unfold v3coplanar, v3mixed. rewrite H. apply v3cross_vdot_same_r.
Qed.

(** Example 7, page 22, 高等数学，第七版 *)
(** 根据四顶点的坐标，求四面体的体积：四面体ABCD的体积等于AB,AC,AD为棱的平行六面体
    的体积的六分之一 *)
Definition v3_volume_of_tetrahedron (A B C D : vec 3) :=
  let AB := B - A in
  let AC := C - A in
  let AD := D - A in
  ((1/6) * `[AB AC AD])%R.

(** u,v,w ∈ one-plane, u ∠ w = (u ∠ v) + (v ∠ w) *)
Lemma v3angle_add : forall (u v w : vec 3),
    u /_ v < PI ->
    v /_ w < PI ->
    v3coplanar u v w ->
    u /_ w = ((u /_ v) + (v /_ w))%R.
Proof.
  (* 由于 u /_ v 和 v /_ u 并没有区分，所以该性质不成立。*)
  (* intros. unfold vangle. unfold vnorm. unfold vlen. *)
  (* unfold vcmul. unfold vdot. unfold Vector.vdot. *)
  (* vec2fun. unfold Tmul,Tadd,T0,T. *)
  (* autorewrite with R. *)
Abort.


(* ======================================================================= *)
(** ** Standard base for 4-D vectors *)

Definition v4i : vec 4 := mkvec4 1 0 0 0.
Definition v4j : vec 4 := mkvec4 0 1 0 0.
Definition v4k : vec 4 := mkvec4 0 0 1 0.
Definition v4l : vec 4 := mkvec4 0 0 0 1.


(* ======================================================================= *)
(** ** matrix norm *)

Open Scope mat_scope.

(** norm space *)
Class Norm `{Ring} (f : A -> R) (cmul : R -> A -> A) := {
    Norm_pos : forall a : A, 0 <= f a;
    Norm_eq0_iff : forall a : A, f a = 0 <-> a = Azero;
    Norm_cmul_compat : forall (c : R) (a : A), f (cmul c a) = ((Rabs c) * f a)%A
  }.

(* Equivalent form of matrix norm *)
Definition mnorm_spec_pos {r c} (mnorm : mat r c -> R) : Prop :=
  forall M : mat r c,
    (M <> mat0 -> mnorm M > 0) /\ (M = mat0 -> mnorm M = 0).

Definition mnorm_spec_mcmul {r c} (mnorm : mat r c -> R) : Prop :=
  forall (M : mat r c) (k : R),
    mnorm (k \.* M) = ((Rabs k) * (mnorm M))%R.

Definition mnorm_spec_trig {r c} (mnorm : mat r c -> R) : Prop :=
  forall (M N : mat r c),
    mnorm (M + N) <= mnorm M + mnorm N.

(* ======================================================================= *)
(** ** matrix F norm *)

(* F-norm (M) := √(∑∑M(i,j)²) *)
Definition mnormF {r c} (M : mat r c) : R :=
  sqrt (vsum (fun i => vsum (fun j => (M$i$j)²))).

(** mnormF m = √ tr (M\T * M) *)
Lemma mnormF_eq_trace : forall {r c} (M : mat r c),
    mnormF M = sqrt (tr (M\T * M)).
Proof.
  intros. unfold mnormF. f_equal. unfold mtrace, Matrix.mtrace, vsum.
  rewrite fseqsum_fseqsum_exchg. apply fseqsum_eq. intros j.
  apply fseqsum_eq. intros i. cbv. auto.
Qed.

Lemma mnormF_spec_pos : forall r c, mnorm_spec_pos (@mnormF r c).
Proof.
  intros. hnf. intros. split; intros.
  - unfold mnormF. apply sqrt_lt_R0. apply vsum_gt0.
    + intros. apply vsum_ge0. intros. apply sqr_ge0.
    + apply mneq_iff_exist_mnth_neq in H. destruct H as [i [j H]].
      exists i. intro. apply vsum_eq0_rev with (i:=j) in H0; auto.
      * rewrite mnth_mat0 in H. cbv in H. ra.
      * intros. cbv. ra.
  - rewrite H. unfold mnormF.
    apply sqrt_0_eq0. apply vsum_eq0; intros. apply vsum_eq0; intros.
    rewrite mnth_mat0. ra.
Qed.

Lemma mnormF_spec_mcmul : forall r c, mnorm_spec_mcmul (@mnormF r c).
Proof.
Admitted.

Lemma mnormF_spec_trig : forall r c, mnorm_spec_trig (@mnormF r c).
Proof.
Admitted.

(* ======================================================================= *)
(** ** Orthogonal matrix *)

(** orthogonal M -> |M| = ± 1 *)
Lemma morth_mdet : forall {n} (M : smat n), morth M -> (mdet M = 1 \/ mdet M = -1).
Proof.
  intros. rewrite morth_iff_mul_trans_l in H.
  assert (mdet (M\T * M) = mdet (@mat1 n)). rewrite H. auto.
  rewrite mdet_mmul, mdet_mtrans, mdet_mat1 in H0. apply Rsqr_eq1 in H0. easy.
Qed.

(** Transformation by orthogonal matrix will keep normalization. *)
Lemma morth_keep_norm : forall {n} (M : smat n) (v : vec n),
    morth M -> vnorm (M * v)%V = (M * vnorm v)%V.
Proof.
  intros. unfold vnorm.
  pose proof (morth_keep_length M). unfold vlen. rewrite H0; auto.
  rewrite <- mmulv_vcmul. auto.
Qed.

(** Transformation by orthogonal matrix will keep angle. *)
Lemma morth_keep_angle : forall {n} (M : smat n) (u v : vec n),
    morth M -> (M * u)%V /_ (M * v)%V = u /_ v.
Proof.
  intros. unfold vangle. f_equal. rewrite !morth_keep_norm; auto.
  apply morth_keep_dot; auto.
Qed.

(** if M is orthogonal, then M&i <> vzero *)
Lemma morth_imply_col_neq0 : forall {n} (M : smat n) i, morth M -> mcol M i <> vzero.
Proof.
  intros. apply morth_iff_mcolsOrthonormal in H. destruct H as [H1 H2].
  specialize (H2 i). apply vunit_neq0; auto.
Qed.

(** if M is orthogonal, then ||M&i||=1 *)
Lemma morth_imply_vlen_col : forall {n} (M : smat n) i, morth M -> || mcol M i || = 1.
Proof.
  intros. apply morth_iff_mcolsOrthonormal in H. destruct H as [H1 H2].
  apply vlen_eq1_iff_vdot1. apply H2.
Qed.

(** if M is orthogonal, then ||M.i||=1 *)
Lemma morth_imply_vlen_row : forall {n} (M : smat n) i, morth M -> || mrow M i || = 1.
Proof.
  intros. apply morth_iff_mrowsOrthonormal in H. destruct H as [H1 H2].
  apply vlen_eq1_iff_vdot1. apply H2.
Qed.

(** if M is orthogonal, then <M&i, M&j> = 0 *)
Lemma morth_imply_vdot_cols_diff : forall {n} (M : smat n) i j,
    morth M -> i <> j -> <mcol M i, mcol M j> = 0.
Proof.
  intros. apply morth_iff_mcolsOrthonormal in H. destruct H as [H1 H2].
  apply H1; auto.
Qed.

(** if M is orthogonal, then M&i _|_ &j *)
Lemma morth_imply_orth_cols_diff : forall {n} (M : smat n) i j,
    morth M -> i <> j -> mcol M i _|_ mcol M j.
Proof.
  intros. apply morth_iff_mcolsOrthonormal in H. destruct H as [H1 H2].
  apply H1; auto.
Qed.

(** if M is orthogonal, then M&i /_ &j = π/2 *)
Lemma morth_imply_vangle_cols_diff : forall {n} (M : smat n) i j,
    morth M -> i <> j -> mcol M i /_ mcol M j = PI/2.
Proof.
  intros. apply vangle_PI2_iff; try apply morth_imply_col_neq0; auto.
  apply morth_imply_vdot_cols_diff; auto.
Qed.

(** if M is orthogonal, then sin (M&i /_ &j) = 1 *)
Lemma morth_imply_sin_vangle_cols_diff : forall {n} (M : smat n) i j,
    morth M -> i <> j -> sin (mcol M i /_ mcol M j) = 1.
Proof. intros. rewrite (morth_imply_vangle_cols_diff); auto. ra. Qed.

(** if M is orthogonal, then ||M&i×M&j||=1 *)
Lemma morth_imply_vlen_v3cross_cols_diff : forall (M : smat 3) i j,
    morth M -> i <> j -> || mcol M i \x mcol M j || = 1.
Proof.
  intros. rewrite vlen_v3cross; try apply morth_imply_col_neq0; auto.
  rewrite !morth_imply_vlen_col; auto.
  rewrite morth_imply_sin_vangle_cols_diff; auto. ra.
Qed.

(* https://en.wikipedia.org/wiki/Cross_product#Algebraic&02AProperties   *)
Goal forall (M : smat 3) (u v : vec 3),
    mdet M <> 0 -> (M * u)%V \x (M * v)%V = ((mdet M) \.* (M\-1\T * (u \x v)))%V.
Proof.
  intros. rewrite <- mmulv_mcmul.
  (* rewrite <- mcomat_eq; auto. *)
  (* rewrite !v3cross_eq_skew_mul_vec. *)
  (* rewrite <- !mmulv_assoc. f_equal. *)
  (* apply meq_iff_mnth; intros. *)
  (* rewrite !mnth_mmul. *)
Abort.

(** if M is orthogonal, then M&1×M&2 //+ M&3 *)
Lemma morth_imply_vpara_v3cross_12 : forall (M : smat 3),
    morth M -> M&1 \x M&2 //+ M&3.
Proof.
  intros.
  pose proof (v3cross_eq0_iff_angle_0_pi (M&1 \x M&2) (M&3)).
  assert (M&1 \x M&2 /_ M&3 = 0 \/ M&1 \x M&2 /_ M&3 = PI). admit.
  apply H0 in H1.
Abort.

Section SO3_keep_v3cross.
  (* 参考了 stackexchange, user1551 的证明思路 *)
  (* https://math.stackexchange.com/questions/2534923/does-so3-preserve-the-cross-product *)
  Open Scope vec_scope.

  (** morth(M) -> det(M) = 1 -> [Mu Mv Mw] = <Mu, M(v×w)> *)
  Lemma morth_keep_v3cross_det1_aux : forall (M : smat 3) (u v w : vec 3),
      morth M -> mdet M = 1 ->
      `[(M*u) (M*v) (M*w)] = <M*u, M*(v\x w)>.
  Proof.
    intros.
    rewrite morth_keep_dot; auto. rewrite v3mixed_swap_op. fold (v3mixed u v w).
    rewrite !v3mixed_eq_det_cols.
    replace (@cvl2m 3 3 [M * u; M * v; M * w])
      with (M * @cvl2m 3 3 [u;v;w])%M by meq.
    rewrite mdet_mmul. rewrite H0. autounfold with A. ring.
  Qed.

  (** morth(M) -> det(M) = -1 -> [Mu Mv Mw] = -<Mu, M(v×w)> *)
  Lemma morth_keep_v3cross_detNeg1_aux : forall (M : smat 3) (u v w : vec 3),
      morth M -> mdet M = (-1)%R ->
      `[(M*u) (M*v) (M*w)] = (- (<M*u, M*(v\x w)>)%V)%R.
  Proof.
    intros.
    rewrite morth_keep_dot; auto. rewrite v3mixed_swap_op. fold (v3mixed u v w).
    rewrite !v3mixed_eq_det_cols.
    replace (@cvl2m 3 3 [M * u; M * v; M * w])
      with (M * @cvl2m 3 3 [u;v;w])%M by meq.
    rewrite mdet_mmul. rewrite H0. autounfold with A. ring.
  Qed.
    
  (** morth(M) -> det(M) = 1 -> Mu × Mv = M(u×v) *)
  (** orthogonal matrix keep v3cross *)
  Lemma morth_keep_v3cross_det1 : forall (M : smat 3) (u v : vec 3),
      morth M -> mdet M = 1 -> (M * u) \x (M * v) = (M * (u \x v)).
  Proof.
    intros.
    pose proof (morth_keep_v3cross_det1_aux M).
    apply vdot_cancel_l; intros.
    rewrite !v3mixed_swap_op. fold (v3mixed c (M*u) (M*v)).
    specialize (H1 (M\T*c) u v H H0).
    replace (M * (M \T * c)) with c in H1; auto.
    rewrite <- mmulv_assoc. rewrite morth_iff_mul_trans_r in H.
    rewrite H; auto. rewrite mmulv_1_l. auto.
  Qed.

  (** SO(3) keep v3cross *)
  Corollary SO3_keep_v3cross : forall (M : smat 3) (u v : vec 3),
      SOnP M -> (M * u) \x (M * v) = M * (u \x v).
  Proof. intros. hnf in H. destruct H. apply morth_keep_v3cross_det1; auto. Qed.

  (** morth(M) -> det(M) = -1 -> Mu × Mv = -M(u×v) *)
  Lemma morth_keep_v3cross_detNeg1 : forall (M : smat 3) (u v : vec 3),
      morth M -> mdet M = (-1)%R -> (M * u) \x (M * v) = -(M * (u \x v)).
  Proof.
    intros.
    pose proof (morth_keep_v3cross_detNeg1_aux M).
    apply vdot_cancel_l; intros.
    rewrite !v3mixed_swap_op. fold (v3mixed c (M*u) (M*v)).
    specialize (H1 (M\T*c) u v H H0).
    replace (M * (M \T * c)) with c in H1; auto.
    - rewrite H1. rewrite vdot_vopp_r. auto.
    - rewrite <- mmulv_assoc. rewrite morth_iff_mul_trans_r in H.
      rewrite H; auto. rewrite mmulv_1_l. auto.
  Qed.
  
  (** Cross product invariant for columns of SO(3) : M&1 × M&2 = M&3 *)
  Lemma SO3_v3cross_c12 : forall (M : smat 3), SOnP M -> M&1 \x M&2 = M&3.
  Proof.
    intros. rewrite mcol_eq_mul_v3i, mcol_eq_mul_v3j, mcol_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_ij.
  Qed.
  
  (** Cross product invariant for columns of SO(3) : M&2 × M&3 = M&1 *)
  Lemma SO3_v3cross_c23 : forall (M : smat 3), SOnP M -> M&2 \x M&3 = M&1.
  Proof.
    intros. rewrite mcol_eq_mul_v3i, mcol_eq_mul_v3j, mcol_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_jk.
  Qed.
  
  (** Cross product invariant for columns of SO(3) : M&3 × M&1 = M&2 *)
  Lemma SO3_v3cross_c31 : forall (M : smat 3), SOnP M -> M&3 \x M&1 = M&2.
  Proof.
    intros. rewrite mcol_eq_mul_v3i, mcol_eq_mul_v3j, mcol_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_ki.
  Qed.

  (** Cross product invariant for rows of SO(3) : M.1 × M.2 = M.3 *)
  Lemma SO3_v3cross_r12 : forall (M : smat 3), SOnP M -> M.1 \x M.2 = M.3.
  Proof.
    intros. rewrite mrow_eq_mul_v3i, mrow_eq_mul_v3j, mrow_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_ij. apply SOnP_mtrans; auto.
  Qed.
  
  (** Cross product invariant for rows of SO(3) : M.2 × M.3 = M.1 *)
  Lemma SO3_v3cross_r23 : forall (M : smat 3), SOnP M -> M.2 \x M.3 = M.1.
  Proof.
    intros. rewrite mrow_eq_mul_v3i, mrow_eq_mul_v3j, mrow_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_jk. apply SOnP_mtrans; auto.
  Qed.
  
  (** Cross product invariant for rows of SO(3) : M.3 × M.1 = M.2 *)
  Lemma SO3_v3cross_r31 : forall (M : smat 3), SOnP M -> M.3 \x M.1 = M.2.
  Proof.
    intros. rewrite mrow_eq_mul_v3i, mrow_eq_mul_v3j, mrow_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_ki. apply SOnP_mtrans; auto.
  Qed.

  (* 其他证明思路，暂时走不通
     https://math.stackexchange.com/questions/279173/rotational-invariance-of-cross-product *)

End SO3_keep_v3cross.


(* https://en.wikipedia.org/wiki/Cross_product 
   当 a = c, b = d 时，这就是叉乘直接分量形式，即
             [ î  ĵ  k̂ ]
   a×b = det [ a1 a2 a3]
             [ b1 b2 b3]
   这是 Binet–Cauchy identity 的 n = 3 的情形，需要先证明一般情形，但比较复杂。
   见 https://en.wikipedia.org/wiki/Binet%E2%80%93Cauchy_identity。
 *)

(* ======================================================================= *)
(** ** SO2 and SO3 *)

(** SO2 *)
Notation SO2 := (@SOn 2).

(** SO3 *)
Notation SO3 := (@SOn 3).

Example SO3_example1 : forall M : SO3, M\-1 = M\T.
Proof. apply SOn_inv_eq_trans. Qed.


(* ######################################################################### *)
(** * Modules for notations to avoid name pollution *)
Module V3Notations.
  Infix "\x" := v3cross : vec_scope.
  Notation "`| v |x" := (skew3 v) : vec_scope.
End V3Notations.


(* ######################################################################### *)
(** * Usage demo *)

(* ======================================================================= *)
(** ** Exercise in textbook *)

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

Section test.
  Let m1 := @l2m 2 2 [[1;2];[3;4]].
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Ropp m1). *)
  (* Compute m2l (m1 * m1). *)
End test.

Section Example4CoordinateSystem.
  Variable ψ θ φ: R.
  Let Rx := (mkmat_3_3 1 0 0 0 (cos φ) (sin φ) 0 (-sin φ) (cos φ))%R.
  Let Ry := (mkmat_3_3 (cos θ) 0 (-sin θ) 0 1 0 (sin θ) 0 (cos θ))%R.
  Let Rz := (mkmat_3_3 (cos ψ) (sin ψ) 0 (-sin ψ) (cos ψ) 0 0 0 1)%R.
  Let Rbe := (mkmat_3_3
                (cos θ * cos ψ) (cos ψ * sin θ * sin φ - sin ψ * cos φ)
                (cos ψ * sin θ * cos φ + sin φ * sin ψ) (cos θ * sin ψ)
                (sin ψ * sin θ * sin φ + cos ψ * cos φ)
                (sin ψ * sin θ * cos φ - cos ψ * sin φ)
                (-sin θ) (sin φ * cos θ) (cos φ * cos θ))%R.
  Lemma Rbe_ok : (Rbe = Rz\T * Ry\T * Rx\T).
  Proof. apply m2l_inj; cbv; list_eq; lra. Qed.
    
End Example4CoordinateSystem.


(** example for symbol matrix *)
Module Exercise_Ch1_Symbol.

  (* for better readibility *)
  Notation "0" := R0.
  Notation "1" := R1.
  Notation "2" := (R1 + R1)%R.
  Notation "3" := (R1 + (R1 + R1))%R.
  Notation "4" := ((R1 + R1) * (R1 + R1))%R.
  
  Example ex6_1 : forall a b : R,
      (let m := mkmat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1 in
      mdet m = (a - b)^3)%R.
  Proof. intros; cbv; lra. Qed.
  
  Example ex6_2 : forall a b x y z : R,
      (let m1 := mkmat_3_3
                   (a*x+b*y) (a*y+b*z) (a*z+b*x)
                   (a*y+b*z) (a*z+b*x) (a*x+b*y)
                   (a*z+b*x) (a*x+b*y) (a*y+b*z) in
       let m2 := mkmat_3_3 x y z y z x z x y in
       mdet m1 = (a^3 + b^3) * mdet m2)%R.
  Proof. intros; cbv; lra. Qed.
  
  Example ex6_3 : forall a b e d : A,
      (let m := mkmat_4_4
                 (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
                 (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
                 (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
                 (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2) in
      mdet m = 0)%R.
  Proof. intros. cbv. lra. Qed.
  
  Example ex6_4 : forall a b e d : A,
      let m := mkmat_4_4
                 1 1 1 1
                 a b e d
                 (a^2) (b^2) (e^2) (d^2)
                 (a^4) (b^4) (e^4) (d^4) in
      (mdet m = (a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%R.
  Proof. intros; cbv; lra. Qed.
  
  (** 6.(5), it is an infinite structure, need more work, later... *)

End Exercise_Ch1_Symbol.
