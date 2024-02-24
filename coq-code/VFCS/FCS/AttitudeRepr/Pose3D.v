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
  2. 

*)

Require Export Math.
Require Export VectorR3.

Open Scope nat_scope.
Open Scope R_scope.
Open Scope mat_scope.
Open Scope vec_scope.


(* ======================================================================= *)
(** Skew-symmetric matrix of 3-dimensions *)
Section v3skew.

  (** Given matrix is skew-symmetric matrices *)
  Definition v3skewP (m : mat 3 3) : Prop := (- m)%M = m\T.

  (* Equivalent form of v3skewP *)
  Lemma v3skewP_eq : forall m : mat 3 3,
      v3skewP m ->
      (m.11 = 0) /\ (m.22 = 0) /\ (m.33 = 0) /\
        (m.12 = -m.21 /\ m.13 = -m.31 /\ m.23 = -m.32)%R.
  Proof.
    intros. hnf in H.
    assert (m2l (- m)%M = m2l (m\T)).
    { rewrite H. auto. }
    cbv in H0. list_eq. cbv. ra.
  Qed.

  (** Convert a vector to its corresponding skew-symmetric matrix *)
  Definition v3skew (v : vec 3) : mat 3 3 :=
    l2m [[0; -v.3; v.2];
         [v.3; 0; -v.1];
         [-v.2; v.1; 0]]%R.
  
  Notation "`| v |ₓ" := (v3skew v).

  (** Convert a skew-symmetric matrix to its corresponding vector *)
  Definition v3vex (m : mat 3 3) : vec 3 := l2v [m.32; m.13; m.21].

  Lemma v3skew_v3vex_id : forall (m : mat 3 3), v3skewP m -> v3skew (v3vex m) = m.
  Proof. intros. apply v3skewP_eq in H. cbv in H. meq; Req. Qed.

  Lemma v3vex_v3skew_id : forall (v : vec 3), v3vex (v3skew v) = v.
  Proof. intros. veq. Qed.

  Lemma v3cross_eq_skew_mul_vec : forall (u v : vec 3),
      u \x v = cv2v (`|u|ₓ * (v2cv v)).
  Proof. intros; veq; ra. Qed.

  Lemma v3cross_eq_skew_mul_cvec : forall (u v : vec 3),
      v2cv (u \x v) = `|u|ₓ * (v2cv v).
  Proof. intros; meq; ra. Qed.

  (** Example 4, page 19, 高等数学，第七版 *)
  Example v3cross_example1 : (l2v [2;1;-1]) \x (l2v [1;-1;2]) = l2v [1;-5;-3].
  Proof. veq; Req. Qed.

  (** Example 5, page 19, 高等数学，第七版 *)
  (** 根据三点坐标求三角形面积 *)
  Definition v3_area_of_triangle (A B C : vec 3) :=
    let AB := B - A in
    let AC := C - A in
    ((1/2) * ||AB \x AC||)%R.

  (** Example 6, page 20, 高等数学，第七版 *)
  (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*)
  Definition v3_rotation_model (ω r v : vec 3) := v = ω \x r.

End v3skew.

Notation "`| v |ₓ" := (v3skew v).


(* ======================================================================= *)
(** Axis-angle representation *)
Section AxisAngle.

  (** 推导绕任意轴 n̂ 旋转 θ 角度的矩阵 R(n̂,θ)，使得 a' = R(n̂,θ) * a *)

  (** Rotate one vector a in R^3 by an axis described with a unit vector n and 
      an angle θ according to right handle rule, we got the rotated vector as
      follows. This formula is known as Rodrigues formula. *)
  Definition rotaa (θ : R) (n : vec 3) (a : vec 3) : vec 3 :=
    (cos θ) \.* (a - <a,n> \.* n) + (sin θ) \.* (n \x a) + <a,n> \.* n.

  (** Proof its correctness *)
  Theorem rotaa_spec : forall (θ : R) (n : vec 3) (a : vec 3),
      let a_para : vec 3 := vproj a n in
      let a_perp : vec 3 := vperp a n in
      let b : vec 3 := n \x a_perp in
      let a_perp' : vec 3 := (cos θ) \.* a_perp + (sin θ) \.* b in
      let a' : vec 3 := (a_perp' + a_para)%V in
      vunit n ->
      a' = rotaa θ n a.
  Proof.
    intros. unfold rotaa.
    assert (a_para = <a,n> \.* n) as H1.
    { unfold a_para. unfold vproj, Vector.vproj. unfold vunit, Vector.vunit in H.
      rewrite H. unfold vcmul. f_equal. unfold vdot. autounfold with A. field. }
    assert (a_perp = a - <a,n> \.* n) as H2.
    { unfold a_perp. rewrite <- H1. auto. }
    assert (b = n \x a) as H3.
    { unfold b. rewrite H2. unfold vsub. 
      rewrite v3cross_add_distr_r. rewrite v3cross_vopp_r.
      rewrite v3cross_vcmul_assoc_r. rewrite v3cross_self. rewrite vcmul_0_r.
      rewrite vopp_vzero. rewrite vadd_0_r. auto. }
    unfold a'. unfold a_perp'. rewrite H1. rewrite H2. rewrite H3. auto.
  Qed.

  (** Another form of the formula *)
  Lemma rotaa_form1 : forall (θ : R) (n : vec 3) (a : vec 3),
      rotaa θ n a =
        (cos θ) \.* a + (sin θ) \.* (n \x a) + (<a,n> * (1 - cos θ))%R \.* n.
  Proof.
    intros. unfold rotaa. rewrite vcmul_vsub. unfold vsub. asemigroup.
    unfold Rminus. rewrite Rmult_plus_distr_l. rewrite identityRight at 1.
    rewrite vcmul_add. asemigroup. rewrite vcmul_assoc.
    rewrite <- vcmul_opp. f_equal. autounfold with A. ring.
  Qed.

  (** Matrix formula of roation with axis-angle *)
  (* https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula *)
  Definition aa2mat (θ : R) (n : vec 3) : smat 3 :=
    let N := v3skew n in
    (mat1 + (sin θ) \.* N + (1 - cos θ)%R \.* N * N)%M.

  Lemma aa2mat_spec : forall (θ : R) (n : vec 3) (a : vec 3),
      vunit n -> cv2v ((aa2mat θ n) * (v2cv a)) = rotaa θ n a.
  Proof.
    intros.
    (* simplify the cv2v and v2cv *)
    rewrite rotaa_form1. unfold aa2mat.
    rewrite !mmul_madd_distr_r. rewrite mmul_1_l. rewrite !cv2v_madd.
    rewrite !mmul_mcmul_l, !cv2v_mcmul, mmul_assoc.
    rewrite <- !v3cross_eq_skew_mul_cvec. rewrite !cv2v_v2cv.
    (* final steps *)
    move2h (sin θ \.* (n \x a)). symmetry. move2h (sin θ \.* (n \x a)). elimh.
    rewrite (commutative (<a,n>)). rewrite <- vcmul_assoc.
    rewrite v3cross_u_uv_eq_minus.
    rewrite H. rewrite vdot_comm. unfold vsub.
    rewrite vcmul_vadd. asemigroup. unfold Rminus.
    rewrite vcmul_add. rewrite !vcmul_1_l.
    rewrite vcmul_opp, vcmul_vopp. rewrite group_opp_opp at 1.
    asemigroup. group.
  Qed.
  
  (** The direct form aa2mat. *)
  Definition aa2matM (θ : R) (k : vec 3) : mat 3 3 :=
    let x := k.x in
    let y := k.y in
    let z := k.z in
    let C := cos θ in
    let S := sin θ in
    l2m
      [[C + x * x * (1 - C); x * y * (1 - C) - z * S; x * z * (1 - C) + y * S];
       [y * x * (1 - C) + z * S; C + y * y * (1 - C); y * z * (1 - C) - x * S];
       [z * x * (1 - C) - y * S; z * y * (1 - C) + x * S; C + z * z * (1 - C)]]%R.

  Theorem aa2matM_eq_aa2mat : forall (θ : R) (k : vec 3),
      vunit k -> aa2matM θ k = aa2mat θ k.
  Proof.
    intros. meq; ra.
    - pose proof (v3unit_sqr_x k H). cbv in H0; rewrite H0; ra.
    - pose proof (v3unit_sqr_y k H). cbv in H0; rewrite H0; ra.
    - pose proof (v3unit_sqr_z k H). cbv in H0; rewrite H0; ra.
  Qed.

  Lemma aa2matM_orth : forall (θ : R) (k : vec 3), vunit k -> morth (aa2matM θ k).
  Proof.
    intros.
    pose proof (v3unit_sqr_x k H).
    pose proof (v3unit_sqr_y k H).
    pose proof (v3unit_sqr_z k H). cbv in H0,H1,H2.
    ring_simplify in H0.
    ring_simplify in H1.
    ring_simplify in H2.
    meq.
    all: ring_simplify; simp_pow; try (rewrite H0; rewrite sin2'; lra).
  Qed.
  
  Lemma aa2matM_det1 : forall (θ : R) (k : vec 3),
      vunit k -> mdet (aa2matM θ k) = 1.
  Proof.
    intros.
    pose proof (v3unit_sqr_x k H).
    pose proof (v3unit_sqr_y k H).
    pose proof (v3unit_sqr_z k H). cbv in H0,H1,H2.
    ring_simplify in H0.
    ring_simplify in H1.
    ring_simplify in H2.
    cbv.
    ring_simplify. simp_pow. rewrite H0. rewrite sin2'. lra.
  Qed.

  (* aa2matM is SO3 *)
  Definition aa2matM_SO3 (θ : R) (k : vec 3) (H : vunit k) : SO3 :=
    Build_SOn (Build_GOn (aa2matM θ k) (aa2matM_orth _ k H)) (aa2matM_det1 _ k H).

  (** R(-θ) = R(θ)\T *)
  Lemma aa2mat_neg_eq_trans : forall (θ : R) (n : vec 3), aa2mat (-θ) n = (aa2mat θ n)\T.
  Proof. intros. meq; Req_more. Qed.

  (** R(θ) * R(θ)\T = I *)
  Lemma aa2mat_aa2mat_neg_inv : forall (θ : R) (n : vec 3),
      vunit n -> aa2mat θ n * ((aa2mat θ n)\T) = mat1.
  Proof.
    intros. rewrite <- aa2matM_eq_aa2mat; auto.
    apply (SOn_mul_trans_r_eq1 (aa2matM_SO3 θ n H)).
  Qed.

End AxisAngle.



(* ======================================================================= *)
(** ** Rotation matrix in 3D *)
Section RotationMatrix3D.
  
  (** 主动旋转，逆时针正向(或顺时针负向)时，旋转矩阵 *)

  (** 注意列向量和行向量的不同用法：
     1. 给一个在该坐标系下的列向量 u，正向旋转该向量 θ 角得到新的向量 u'，按如下公式
          u' = R(θ) * u
          u  = R(θ)\T * u'
     2. 给一个在该坐标系下的行向量 v，正向旋转该向量 θ 角得到新的向量 v'，按如下公式
          v' = v * (R(θ))\T
     3. 如果进行了连续两次旋转，即，先旋转θ1，然后在此基础上再旋转θ2，则
        按照列向量：v' = R(θ2) * R(θ1) * v，
        按照行向量：v' = v * R(θ1) * R(θ2)，其中 R 是 R\T
   *)

  (** Basic rotation matrices in 3D *)
  
  Definition R3x (θ : R) : mat 3 3 :=
    l2m
      [[1; 0; 0];
       [0; cos θ; - sin θ];
       [0; sin θ; cos θ]]%R.
  
  Definition R3y (θ : R) : mat 3 3 :=
    l2m
      [[cos θ; 0; sin θ];
       [0; 1; 0];
       [- sin θ; 0; cos θ]]%R.

  Definition R3z (θ : R) : mat 3 3 :=
    l2m
      [[cos θ; - sin θ; 0];
       [sin θ; cos θ; 0];
       [0; 0; 1]]%R.


  Section ReasoningRotation3D.

  (* 3D向量绕x轴旋转的转换矩阵。
    已知向量oa=[a1 a2 a3]^T，其绕x轴旋转到达ob=[b1 b2 b3]，此时x坐标不变，
    而y,z坐标等价于将其投影到yz平面上进行逆时针旋转。
    求出旋转矩阵A(beta),B(beta)，使得：
    [b1 b2 b3]^T=A(beta)[a1 a2 a3]^T，
    [a1 a2 a3]^T=B(beta)[b1 b2 b3]^T
   *)
  End ReasoningRotation3D.

  
  (** R3x,R3y,R3z are orthogonal matrix *)
  Lemma R3x_orth : forall (θ : R), morth (R3x θ).
  Proof. intros; meq; Req_more. Qed.
  
  Lemma R3y_orth : forall (θ : R), morth (R3y θ).
  Proof. intros; meq; Req_more. Qed.
  
  Lemma R3z_orth : forall (θ : R), morth (R3z θ).
  Proof. intros; meq; Req_more. Qed.

  (** R3x,R3y,R3z are invertible matrix *)
  Lemma R3x_invertible : forall (θ : R), minvertible (R3x θ).
  Proof. intros. apply morth_invertible. apply R3x_orth. Qed.
  
  Lemma R3y_invertible : forall (θ : R), minvertible (R3y θ).
  Proof. intros. apply morth_invertible. apply R3y_orth. Qed.
  
  Lemma R3z_invertible : forall (θ : R), minvertible (R3z θ).
  Proof. intros. apply morth_invertible. apply R3z_orth. Qed.

  (** The determinant of R3x,R3y,R3z are 1 *)
  Lemma R3x_det1 : forall (θ : R), mdet (R3x θ) = 1.
  Proof. intros; cbv; Req_more. Qed.

  Lemma R3y_det1 : forall (θ : R), mdet (R3y θ) = 1.
  Proof. intros; cbv; autorewrite with R; auto. Qed.

  Lemma R3z_det1 : forall (θ : R), mdet (R3z θ) = 1.
  Proof. intros; cbv; autorewrite with R; auto. Qed.

  (** R3x,R3y,R3z are member of SO3 *)
  Definition R3x_SO3 (θ : R) : SO3 :=
    Build_SOn (Build_GOn (R3x θ) (R3x_orth _)) (R3x_det1 _).

  Definition R3y_SO3 (θ : R) : SO3 :=
    Build_SOn (Build_GOn (R3y θ) (R3y_orth _)) (R3y_det1 _).

  Definition R3z_SO3 (θ : R) : SO3 :=
    Build_SOn (Build_GOn (R3z θ) (R3z_orth _)) (R3z_det1 _).

  (** 以下示例说明了使用群 SOn 可以解决一批问题(SO2, SO3等），并且比暴力证明的速度快 *)
  
  (** R(θ)⁻¹ = R(θ)\T *)
  
  Lemma R3x_inv_eq_trans : forall θ : R, (R3x θ)\-1 = (R3x θ)\T.
  Proof.
    (* method 1 : prove by computing (too slow, 0.4s) *)
    (* Time intros; meq; Req. *)
    (* method 2 : prove by reasoning *)
    intros. apply (SOn_inv_eq_trans (R3x_SO3 θ)).
  Qed.

  Lemma R3y_inv_eq_trans : forall θ : R, (R3y θ)\-1 = (R3y θ)\T.
  Proof. intros; apply (SOn_inv_eq_trans (R3y_SO3 θ)). Qed.

  Lemma R3z_inv_eq_trans : forall θ : R, (R3z θ)\-1 = (R3z θ)\T.
  Proof. intros; apply (SOn_inv_eq_trans (R3z_SO3 θ)). Qed.
  
  (** R(-θ) = R(θ)\T *)
  Lemma R3x_neg_eq_trans : forall θ : R, R3x (-θ) = (R3x θ)\T.
  Proof. intros; meq; Req_more. Qed.
  
  Lemma R3y_neg_eq_trans : forall θ : R, R3y (-θ) = (R3y θ)\T.
  Proof. intros; meq; Req_more. Qed.
  
  Lemma R3z_neg_eq_trans : forall θ : R, R3z (-θ) = (R3z θ)\T.
  Proof. intros; meq; Req_more. Qed.

  (** R(-θ) * R(θ) = I *)
  Lemma R3x_neg_mul_R3x : forall θ : R, R3x (- θ) * R3x θ = mat1.
  Proof.
    (* intros; meq; Req. Qed. *)
    intros; rewrite R3x_neg_eq_trans, <- R3x_inv_eq_trans, mmul_minv_l; auto.
    apply R3x_invertible.
  Qed.
  
  Lemma R3y_neg_mul_R3y : forall θ : R, R3y (- θ) * R3y θ = mat1.
  Proof.
    intros; rewrite R3y_neg_eq_trans, <- R3y_inv_eq_trans, mmul_minv_l; auto.
    apply R3y_invertible.
  Qed.
  
  Lemma R3z_neg_mul_R3z : forall θ : R, R3z (- θ) * R3z θ = mat1.
  Proof.
    intros; rewrite R3z_neg_eq_trans, <- R3z_inv_eq_trans, mmul_minv_l; auto.
    apply R3z_invertible.
  Qed.

  (** R(θ) * R(-θ) = I *)
  Lemma R3x_mul_R3x_neg : forall θ : R, R3x θ * R3x (- θ) = mat1.
  Proof.
    intros; rewrite R3x_neg_eq_trans, <- R3x_inv_eq_trans, mmul_minv_r; auto.
    apply R3x_invertible.
  Qed.
  
  Lemma R3y_mul_R3y_neg : forall θ : R, R3y θ * R3y (- θ) = mat1.
  Proof.
    intros; rewrite R3y_neg_eq_trans, <- R3y_inv_eq_trans, mmul_minv_r; auto.
    apply R3y_invertible.
  Qed.
  
  Lemma R3z_mul_R3z_neg : forall θ : R, R3z θ * R3z (- θ) = mat1.
  Proof.
    intros; rewrite R3z_neg_eq_trans, <- R3z_inv_eq_trans, mmul_minv_r; auto.
    apply R3z_invertible.
  Qed.
  
  (** R3x,R3y,R3z are the special case of aa2mat. *)
  Theorem aa2mat_eq_Rx : forall θ : R, aa2mat θ v3i = R3x θ.
  Proof. intros; meq; Req. Qed.

  Theorem aa2mat_eq_Ry : forall θ : R, aa2mat θ v3j = R3y θ.
  Proof. intros; meq; Req. Qed.

  Theorem aa2mat_eq_Rz : forall θ : R, aa2mat θ v3k = R3z θ.
  Proof. intros; meq; Req. Qed.
  
  (** v' = Rx(θ) * v *)
  Lemma R3x_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3i v = cv2v ((R3x θ) * v2cv v).
  Proof. intros; veq; Req. Qed.
  
  Lemma R3y_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3j v = cv2v ((R3y θ) * v2cv v).
  Proof. intros; veq; Req. Qed.
  
  Lemma R3z_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3k v = cv2v ((R3z θ) * v2cv v).
  Proof. intros; veq; Req. Qed.

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
  Proof. intros. veq; Req.  Qed.

End RotationMatrix3D.
