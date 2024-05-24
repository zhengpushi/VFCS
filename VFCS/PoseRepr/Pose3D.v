(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Pose in 3D
  author    : ZhengPu Shi
  date      : 2024.01

  remark    :
  1. Specify positive direction
     In 3D, the right-hand rule is used to specify the positive direction.
  2. R3x,R3y,R3z 是主动旋转时的旋转矩阵。参考 Pose2D 中的说明。
*)

From FinMatrix Require Export MatrixR.
Import V3Notations.


(* ########################################################################### *)
(** * Preliminary math *)


(* ########################################################################### *)
(** * Axis-angle representation *)
Section AxisAngle.

  (** 推导绕任意轴 n̂ 旋转 θ 角度的矩阵 R(n̂,θ)，使得 a' = R(n̂,θ) * a *)

  (* https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula *)
  
  (** Rotate one vector a in R^3 by an axis described with a unit vector n and 
      an angle θ according to right handle rule, we got the rotated vector as
      follows. This formula is known as Rodrigues formula. *)
  Definition rotaa (θ : R) (n : vec 3) (a : vec 3) : vec 3 :=
    ((cos θ) \.* (a - <a,n> \.* n) + (sin θ) \.* (n \x a) + <a,n> \.* n)%V.

  (** The correctness of `rotaa` by geometry *)
  Theorem rotaa_spec : forall (θ : R) (n : vec 3) (a : vec 3),
      let a_para : vec 3 := vproj a n in
      let a_perp : vec 3 := vperp a n in
      let b : vec 3 := n \x a_perp in
      let a_perp' : vec 3 := ((cos θ) \.* a_perp + (sin θ) \.* b)%V in
      let a' : vec 3 := (a_perp' + a_para)%V in
      vunit n -> a' = rotaa θ n a.
  Proof.
    intros. unfold rotaa.
    assert (a_para = <a,n> \.* n)%V as H1.
    { unfold a_para. unfold vproj, Vector.vproj. unfold vunit, Vector.vunit in H.
      rewrite H. unfold vcmul. f_equal. unfold vdot. autounfold with A. field. }
    assert (a_perp = (a - <a,n> \.* n)%V) as H2.
    { unfold a_perp. rewrite <- H1. auto. }
    assert (b = n \x a) as H3.
    { unfold b. rewrite H2.
      rewrite v3cross_add_distr_r. rewrite v3cross_vopp_r.
      rewrite v3cross_vcmul_assoc_r. rewrite v3cross_self. rewrite vcmul_0_r.
      rewrite vopp_vzero. rewrite vadd_0_r. auto. }
    unfold a'. unfold a_perp'. rewrite H1. rewrite H2. rewrite H3. auto.
  Qed.

  (** Another form of the formula *)
  Lemma rotaa_form1 : forall (θ : R) (n : vec 3) (a : vec 3),
      rotaa θ n a =
        ((cos θ) \.* a + (sin θ) \.* (n \x a) + (<a,n> * (1 - cos θ))%R \.* n)%V.
  Proof.
    pose proof (vadd_AGroup 3) as HAGroup.
    intros. unfold rotaa. rewrite vcmul_vsub. agroup.
    unfold Rminus. rewrite Rmult_plus_distr_l. rewrite identityRight at 1.
    rewrite vcmul_add. agroup. rewrite vcmul_assoc.
    rewrite <- vcmul_opp. f_equal. autounfold with A. ring.
  Qed.

  (** Matrix formula of roation with axis-angle *)
  Definition aa2mat (θ : R) (n : vec 3) : smat 3 :=
    let K := skew3 n in
    mat1 + (sin θ) \.* K + (1 - cos θ)%R \.* (K * K).

  (** `aa2mat` has the same behavior as `rotaa` *)
  Lemma aa2mat_spec : forall (θ : R) (n : vec 3) (a : vec 3),
      vunit n -> aa2mat θ n *v a = rotaa θ n a.
  Proof.
    pose proof (vadd_AGroup 3) as HAGroup.
    intros. rewrite rotaa_form1. unfold aa2mat.
    rewrite !mmulv_madd. rewrite mmulv_1_l.
    rewrite !mmulv_mcmul. rewrite mmulv_assoc.
    rewrite <- !v3cross_eq_skew_mul_vec.
    move2h (sin θ \.* (n \x a))%V. symmetry. move2h (sin θ \.* (n \x a))%V. agroup.
    rewrite (commutative (<a,n>)). rewrite <- vcmul_assoc.
    rewrite v3cross_a_ab_eq_minus.
    rewrite H. rewrite vdot_comm.
    rewrite vcmul_vadd. agroup. unfold Rminus.
    rewrite vcmul_add. rewrite !vcmul_1_l.
    rewrite vcmul_opp, vcmul_vopp. rewrite group_opp_opp at 1.
    agroup.
  Qed.
  
  (** The direct form aa2mat. *)
  Definition aa2matM (θ : R) (n : vec 3) : mat 3 3 :=
    let x := n.1 in
    let y := n.2 in
    let z := n.3 in
    let C := cos θ in
    let S := sin θ in
    l2m
      [[C + x * x * (1 - C); x * y * (1 - C) - z * S; x * z * (1 - C) + y * S];
       [y * x * (1 - C) + z * S; C + y * y * (1 - C); y * z * (1 - C) - x * S];
       [z * x * (1 - C) - y * S; z * y * (1 - C) + x * S; C + z * z * (1 - C)]]%R.

  (** `aa2matM` is equal to `aa2mat` *)
  Theorem aa2matM_eq_aa2mat : forall (θ : R) (n : vec 3),
      vunit n -> aa2matM θ n = aa2mat θ n.
  Proof.
    intros. meq; rewrite <- !nth_v2f; ra.
    - pose proof (v3unit_sqr_x n H).
      cbv in H0; rewrite <- !nth_v2f in H0; rewrite H0; ra.
    - pose proof (v3unit_sqr_y n H).
      cbv in H0; rewrite <- !nth_v2f in H0; rewrite H0; ra.
    - pose proof (v3unit_sqr_z n H).
      cbv in H0; rewrite <- !nth_v2f in H0; rewrite H0; ra.
  Qed.

  (** `aa2matM` is orthogonal matrix *)
  Lemma aa2matM_orth : forall (θ : R) (n : vec 3), vunit n -> morth (aa2matM θ n).
  Proof.
    intros.
    pose proof (v3unit_sqr_x n H).
    pose proof (v3unit_sqr_y n H).
    pose proof (v3unit_sqr_z n H). cbv in H0,H1,H2.
    ring_simplify in H0.
    ring_simplify in H1.
    ring_simplify in H2.
    meq.
    all: ring_simplify; simp_pow; try (rewrite H0; rewrite sin2'; lra).
  Qed.

  (** det (`aa2matM`) = 1 *)
  Lemma aa2matM_det1 : forall (θ : R) (n : vec 3),
      vunit n -> mdet (aa2matM θ n) = 1.
  Proof.
    intros.
    pose proof (v3unit_sqr_x n H).
    pose proof (v3unit_sqr_y n H).
    pose proof (v3unit_sqr_z n H). cbv in H0,H1,H2.
    ring_simplify in H0.
    ring_simplify in H1.
    ring_simplify in H2.
    cbv.
    ring_simplify. simp_pow. rewrite H0. rewrite sin2'. lra.
  Qed.

  (** `aa2matM` satisfying SO3 *)
  Lemma aa2matM_SOnP (θ : R) (n : vec 3) (H : vunit n) : SOnP (aa2matM θ n).
  Proof. hnf. split. apply aa2matM_orth; auto. apply aa2matM_det1; auto. Qed.
    
  (** `aa2matM` is SO3 *)
  Definition aa2matM_SO3 (θ : R) (n : vec 3) (H : vunit n) : SO3 :=
    mkSOn (aa2matM θ n) (aa2matM_SOnP θ n H).

  (** R(-θ) = R(θ)\T *)
  Lemma aa2mat_neg_eq_trans : forall (θ : R) (n : vec 3), aa2mat (-θ) n = (aa2mat θ n)\T.
  Proof. intros. meq; req. Qed.

  (** R(θ) * R(θ)\T = I *)
  Lemma aa2mat_mul_aa2mat_trans : forall (θ : R) (n : vec 3),
      vunit n -> aa2mat θ n * (aa2mat θ n)\T = mat1.
  Proof.
    intros. rewrite <- aa2matM_eq_aa2mat; auto.
    apply (SOn_mul_trans_r_eq1 (aa2matM_SO3 θ n H)).
  Qed.

End AxisAngle.


(* ########################################################################### *)
(** * Rotation matrix in 3D *)

Open Scope mat_scope.

(* ======================================================================= *)
(** ** Definition of basic rotation matrices in 3D *)

Definition R3x (θ : R) : mat 3 3 :=
  l2m
    [[1;   0;       0      ];
     [0;   cos θ;   - sin θ];
     [0;   sin θ;   cos θ  ]]%R.

Definition R3y (θ : R) : mat 3 3 :=
  l2m
    [[cos θ;    0;   sin θ];
     [0;        1;   0    ];
     [- sin θ;  0;   cos θ]]%R.

Definition R3z (θ : R) : mat 3 3 :=
  l2m
    [[cos θ;    - sin θ;  0];
     [sin θ;    cos θ;    0];
     [0;        0;        1]]%R.

(* ======================================================================= *)
(** ** Properties of basic rotation matrices in 3D *)

(** R3x,R3y,R3z are the special case of aa2mat. *)
Theorem aa2mat_eq_Rx : forall θ : R, aa2mat θ v3i = R3x θ.
Proof. intros; meq; ra. Qed.

Theorem aa2mat_eq_Ry : forall θ : R, aa2mat θ v3j = R3y θ.
Proof. intros; meq; ra. Qed.

Theorem aa2mat_eq_Rz : forall θ : R, aa2mat θ v3k = R3z θ.
Proof. intros; meq; ra. Qed.

(** R3x,R3y,R3z are orthogonal matrix *)
Lemma R3x_orth : forall (θ : R), morth (R3x θ).
Proof. intros; meq; req. Qed.

Lemma R3y_orth : forall (θ : R), morth (R3y θ).
Proof. intros; meq; req. Qed.

Lemma R3z_orth : forall (θ : R), morth (R3z θ).
Proof. intros; meq; req. Qed.

(** R3x,R3y,R3z are invertible matrix *)
Lemma R3x_minvtble : forall (θ : R), minvtble (R3x θ).
Proof. intros. apply morth_minvtble. apply R3x_orth. Qed.

Lemma R3y_minvtble : forall (θ : R), minvtble (R3y θ).
Proof. intros. apply morth_minvtble. apply R3y_orth. Qed.

Lemma R3z_minvtble : forall (θ : R), minvtble (R3z θ).
Proof. intros. apply morth_minvtble. apply R3z_orth. Qed.

(** The determinant of R3x,R3y,R3z are 1 *)
Lemma R3x_det1 : forall (θ : R), mdet (R3x θ) = 1.
Proof. intros; cbv; req. Qed.

Lemma R3y_det1 : forall (θ : R), mdet (R3y θ) = 1.
Proof. intros; cbv; autorewrite with R; auto. Qed.

Lemma R3z_det1 : forall (θ : R), mdet (R3z θ) = 1.
Proof. intros; cbv; autorewrite with R; auto. Qed.

(** R3x,R3y,R3z are member of SO3 *)
Lemma R3x_SOnP : forall θ : R, SOnP (R3x θ).
Proof. intros. hnf. split. apply R3x_orth. apply R3x_det1. Qed.
Lemma R3y_SOnP : forall θ : R, SOnP (R3y θ).
Proof. intros. hnf. split. apply R3y_orth. apply R3y_det1. Qed.
Lemma R3z_SOnP : forall θ : R, SOnP (R3z θ).
Proof. intros. hnf. split. apply R3z_orth. apply R3z_det1. Qed.

Definition R3x_SO3 (θ : R) : SO3 := mkSOn (R3x θ) (R3x_SOnP θ).
Definition R3y_SO3 (θ : R) : SO3 := mkSOn (R3y θ) (R3y_SOnP θ).
Definition R3z_SO3 (θ : R) : SO3 := mkSOn (R3z θ) (R3z_SOnP θ).

(** 使用群 SOn 可以直接证明逆矩阵、旋转矩阵等有关的性质，并且比计算式证明的速度快 *)

(** R(θ)⁻¹ = R(θ)\T *)

Lemma R3x_inv_eq_trans : forall θ : R, (R3x θ)\-1 = (R3x θ)\T.
Proof.
  (* method 1 : prove by computing (too slow, 0.4s) *)
  (* because the computation "determinant <> 0" prevents the computation,
     we should use minvNoCheck. Maybe we should use it as default method *)
  (*
  intros.
  unfold minv; unfold OrthAM.AM.Minv_inst.minv.
  rewrite <- minvNoCheck_spec.
  meq; ra; field_simplify_eq.
  *)
  (* method 2 : prove by reasoning *)
  intros. apply (SOn_minv_eq_trans (R3x_SO3 θ)).
Qed.

Lemma R3y_inv_eq_trans : forall θ : R, (R3y θ)\-1 = (R3y θ)\T.
Proof. intros; apply (SOn_minv_eq_trans (R3y_SO3 θ)). Qed.

Lemma R3z_inv_eq_trans : forall θ : R, (R3z θ)\-1 = (R3z θ)\T.
Proof. intros; apply (SOn_minv_eq_trans (R3z_SO3 θ)). Qed.

(** R(-θ) = R(θ)\T *)
Lemma R3x_neg_eq_trans : forall θ : R, R3x (-θ) = (R3x θ)\T.
Proof. intros; meq; req. Qed.

Lemma R3y_neg_eq_trans : forall θ : R, R3y (-θ) = (R3y θ)\T.
Proof. intros; meq; req. Qed.

Lemma R3z_neg_eq_trans : forall θ : R, R3z (-θ) = (R3z θ)\T.
Proof. intros; meq; req. Qed.

(** R(-θ) * R(θ) = I *)
Lemma R3x_neg_mul_R3x : forall θ : R, R3x (- θ) * R3x θ = mat1.
Proof.
  (* intros; meq; ra. Qed. *)
  intros; rewrite R3x_neg_eq_trans, <- R3x_inv_eq_trans, mmul_minv_l; auto.
  apply R3x_minvtble.
Qed.

Lemma R3y_neg_mul_R3y : forall θ : R, R3y (- θ) * R3y θ = mat1.
Proof.
  intros; rewrite R3y_neg_eq_trans, <- R3y_inv_eq_trans, mmul_minv_l; auto.
  apply R3y_minvtble.
Qed.

Lemma R3z_neg_mul_R3z : forall θ : R, R3z (- θ) * R3z θ = mat1.
Proof.
  intros; rewrite R3z_neg_eq_trans, <- R3z_inv_eq_trans, mmul_minv_l; auto.
  apply R3z_minvtble.
Qed.

(** R(θ) * R(-θ) = I *)
Lemma R3x_mul_R3x_neg : forall θ : R, R3x θ * R3x (- θ) = mat1.
Proof.
  intros; rewrite R3x_neg_eq_trans, <- R3x_inv_eq_trans, mmul_minv_r; auto.
  apply R3x_minvtble.
Qed.

Lemma R3y_mul_R3y_neg : forall θ : R, R3y θ * R3y (- θ) = mat1.
Proof.
  intros; rewrite R3y_neg_eq_trans, <- R3y_inv_eq_trans, mmul_minv_r; auto.
  apply R3y_minvtble.
Qed.

Lemma R3z_mul_R3z_neg : forall θ : R, R3z θ * R3z (- θ) = mat1.
Proof.
  intros; rewrite R3z_neg_eq_trans, <- R3z_inv_eq_trans, mmul_minv_r; auto.
  apply R3z_minvtble.
Qed.



(* ########################################################################### *)
(** * 3D rotation operations *)

(* ======================================================================= *)
(** ** Definition of 3D rotation operations *)


(** *** Specifications for 3D rotation operations *)

(** v' = Rx(θ) * v *)
Lemma R3x_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3i v = cv2v ((R3x θ) * v2cv v).
Proof. intros; veq; ra. Qed.

Lemma R3y_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3j v = cv2v ((R3y θ) * v2cv v).
Proof. intros; veq; ra. Qed.

Lemma R3z_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3k v = cv2v ((R3z θ) * v2cv v).
Proof. intros; veq; ra. Qed.

(** v = R(-θ) * v' *)
Lemma R3x_spec2 : forall (v : vec 3) (θ : R),
    v = cv2v ((R3x (-θ)) * v2cv (rotaa θ v3i v)).
Proof.
  intros. rewrite R3x_spec1. rewrite v2cv_cv2v.
  rewrite <- mmul_assoc, R3x_neg_mul_R3x, mmul_1_l. rewrite cv2v_v2cv; auto.
Qed.

Lemma R3y_spec2 : forall (v : vec 3) (θ : R),
    v = cv2v ((R3y (-θ)) * v2cv (rotaa θ v3j v)).
Proof.
  intros. rewrite R3y_spec1. rewrite v2cv_cv2v.
  rewrite <- mmul_assoc, R3y_neg_mul_R3y, mmul_1_l. rewrite cv2v_v2cv; auto.
Qed.

Lemma R3z_spec2 : forall (v : vec 3) (θ : R),
    v = cv2v ((R3z (-θ)) * v2cv (rotaa θ v3k v)).
Proof.
  intros. rewrite R3z_spec1. rewrite v2cv_cv2v.
  rewrite <- mmul_assoc, R3z_neg_mul_R3z, mmul_1_l. rewrite cv2v_v2cv; auto.
Qed.

(** v = R(θ)\T * v' *)
Lemma R3x_spec3 : forall (v : vec 3) (θ : R),
    v = cv2v ((R3x θ)\T * v2cv (rotaa θ v3i v)).
Proof. intros. rewrite <- R3x_neg_eq_trans, <- R3x_spec2; auto. Qed.

Lemma R3y_spec3 : forall (v : vec 3) (θ : R),
    v = cv2v ((R3y θ)\T * v2cv (rotaa θ v3j v)).
Proof. intros. rewrite <- R3y_neg_eq_trans, <- R3y_spec2; auto. Qed.

Lemma R3z_spec3 : forall (v : vec 3) (θ : R),
    v = cv2v ((R3z θ)\T * v2cv (rotaa θ v3k v)).
Proof. intros. rewrite <- R3z_neg_eq_trans, <- R3z_spec2; auto. Qed.

(** 预乘和后乘旋转矩阵的关系，即: u1 ~ u2 -> R * u1 ~ u2 * R\T *)
Lemma R3x_spec4 : forall (u : vec 3) (θ : R),
    let u1 : cvec 3 := v2cv u in         (* u1是u的列向量形式 *)
    let u2 : rvec 3 := v2rv u in         (* u2是u的行向量形式 *)
    let v1 : cvec 3 := (R3x θ) * u1 in      (* v1是用列向量形式计算的结果 *)
    let v2 : rvec 3 := u2 * ((R3x θ)\T) in  (* v2是用行向量形式计算的结果 *)
    let v1' : vec 3 := cv2v v1 in           (* v1再转为普通向量 *)
    let v2' : vec 3 := rv2v v2 in           (* v2再转为普通向量 *)
    v1' = v2'. (* 结果应该相同 *)
Proof. intros. veq; ra.  Qed.



(** *** Specifications for 3D rotation operations *)

(* 方法一：模仿 Pose2D 中的做法，暂未进行。 *)

(* 3D向量绕x轴旋转的转换矩阵。
   已知向量oa=[a1 a2 a3]^T，其绕x轴旋转到达ob=[b1 b2 b3]，此时x坐标不变，
   而y,z坐标等价于将其投影到yz平面上进行逆时针旋转。
   求出旋转矩阵A(beta),B(beta)，使得：
   [b1 b2 b3]^T=A(beta)[a1 a2 a3]^T，
   [a1 a2 a3]^T=B(beta)[b1 b2 b3]^T
 *)

(* 方法二：使用 rotaa 来验证 *)

