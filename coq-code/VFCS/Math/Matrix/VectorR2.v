(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 3-dimensional vector on R.
  author    : ZhengPu Shi
  date      : 2023.01

  reference :
  remark    :
 *)

Require Import VectorR.
Open Scope cvec_scope.


(* ======================================================================= *)
(** * Extension for R *)
Section RExt.

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
  
End RExt.


(* ======================================================================= *)
(** * 2D vector theory *)

(** ** General properties *)
Section general.

  (** The equality of 2D vector *)
  Lemma cv2eq_iff : forall v1 v2 : cvec 2, v1 == v2 <-> v1.x = v2.x /\ v1.y = v2.y.
  Proof.
    intros. split; intros; try lma. split.
    - specialize (H 0 0)%nat; apply H; auto.
    - specialize (H 1 0)%nat; apply H; auto.
  Qed.

  (** The length of 2D vector *)
  Lemma cv2len_eq : forall v : cvec 2, ||v|| = sqrt (v.x² + v.y²).
  Proof. intros. cbv. cvec2fun. autorewrite with R. ra. Qed.

End general.


(** ** 标准基向量 *)
Section basis.
  Definition cv2i : cvec 2 := mk_cvec2 1 0.
  Definition cv2j : cvec 2 := mk_cvec2 0 1.

  (** 任意向量都能写成该向量的坐标在标准基向量下的线性组合 *)
  Lemma cv2_linear_composition : forall (v : cvec 2), v == v.x c* cv2i + v.y c* cv2j.
  Proof. lma. Qed.

  (** 标准基向量的长度为 1 *)
  Lemma cv2i_len1 : ||cv2i|| = 1.
  Proof. cbv. autorewrite with R; auto. Qed.
  
  Lemma cv2j_len1 : ||cv2j|| = 1.
  Proof. cbv. autorewrite with R; auto. Qed.

  (** 标准基向量都是单位向量 *)
  Lemma cv2i_vunit : cvunit cv2i.
  Proof. apply cvunit_spec. apply cv2i_len1. Qed.
  
  Lemma cv2j_vunit : cvunit cv2j.
  Proof. apply cvunit_spec. apply cv2j_len1. Qed.

  (** 标准基向量都是非零向量 *)
  Lemma cv2i_nonzero : cvnonzero cv2i.
  Proof. intro. apply cv2eq_iff in H. inv H. ra. Qed.

  Lemma cv2j_nonzero : cvnonzero cv2j.
  Proof. intro. apply cv2eq_iff in H. inv H. ra. Qed.

  (** 标准基向量是规范化操作的不动点 *)
  Lemma cv2i_cvnormalize_fixpoint : cvnormalize cv2i == cv2i.
  Proof. apply cvnormalize_vunit_fixpoint. apply cv2i_vunit. Qed.

  Lemma cv2j_cvnormalize_fixpoint : cvnormalize cv2j == cv2j.
  Proof. apply cvnormalize_vunit_fixpoint. apply cv2j_vunit. Qed.
  
  (** 标准基向量与任意向量v的点积等于v的各分量 *)
  Lemma cv2dot_i_l : forall (v : cvec 2), <cv2i, v> = v.x. Proof. intros. cbv; ring. Qed.
  Lemma cv2dot_i_r : forall (v : cvec 2), <v, cv2i> = v.x. Proof. intros. cbv; ring. Qed.
  Lemma cv2dot_j_l : forall (v : cvec 2), <cv2j, v> = v.y. Proof. intros. cbv; ring. Qed.
  Lemma cv2dot_j_r : forall (v : cvec 2), <v, cv2j> = v.y. Proof. intros. cbv; ring. Qed.

End basis.


(** ** cv2angle *)
Section cv2angle.

  (** ToDo: 判断2D向量的夹角是否超过180度？
      将2D向量扩展到3D，并根据第三个分量的符号来判断，原理我还是不理解 *)

  (* (** 用于判别2D向量夹角是否超过π的判别式Δ, *)
   (*     当 Δ > 0,  θ ∈ [0,π) *)
   (*     当 Δ = 0,  θ = π *)
   (*     当 Δ < 0,  θ ∈ (π,2π) *) *)
  (* Definition cv2angleDet (v1 v2 : cvec 2) : R := v1.x * v2.y - v2.x * v1.y. *)

  (* (** 2D向量间角度的范围 *) *)
  (* Inductive Cv2AngleRange := *)
  (* | CA2_ltPI  (* θ ∈ [0,π) *) *)
  (* | CA2_eqPI  (* θ = π *) *)
  (* | CA2_gtPI  (* θ ∈ (π,2π) *) *)
  (* . *)

  (* (** 计算2D向量间角度的范围 *) *)
  (* Definition cv2angleRange (v1 v2 : cvec 2) : Cv2AngleRange := *)
  (*   let delta := cv2angleDet v1 v2 in *)
  (*   if delta >? 0 *)
  (*   then CA2_ltPI *)
  (*   else (if delta =? 0 then CA2_eqPI else CA2_gtPI). *)

  (** 2D向量间角度是否大于π *)
  Definition cv2angleGtPI (v1 v2 : cvec 2) : bool := (v1.x * v2.y - v2.x * v1.y <? 0)%R.

  (* (** ∠(v1,v2) <? π = ~ (∠(v1,v2) >? π) *) *)
  (* Lemma cv2angleLtPI_negb_GtPI : forall (v1 v2 : cvec 2), *)
  (*     cv2angleLtPI v1 v2 = negb (cv2angleGtPI v1 v2). *)
  (* Proof. *)
  (*   intros. unfold cv2angleLtPI, cv2angleGtPI. *)
  (*   remember (v1.x * v2.y - v2.x * v1.y)%R as r. *)
  (*   bdestruct (0 <? r); bdestruct (r <? 0); auto; try lra. *)
  (*   rewrite Rminus_ltb0_comm. auto. *)
  (* Qed. *)
  
  (* (** ∠(v1,v2) <? π = ∠(v2,v1) >? π *) *)
  (* Lemma cv2angleLtPI_GtPI_comm : forall (v1 v2 : cvec 2), *)
  (*     cv2angleLtPI v1 v2 = cv2angleGtPI v2 v1. *)
  (* Proof. *)
  (*   intros. unfold cv2angleLtPI, cv2angleGtPI. rewrite Rminus_ltb0_comm. auto. *)
  (* Qed. *)

  (** The angle from i to v is > π, if and only if v.y is negative *)
  Lemma cv2angleGtPI_i_true : forall (v : cvec 2), cv2angleGtPI cv2i v = true <-> v.y < 0.
  Proof.
    intros. cvec2fun. cbv. autorewrite with R. destruct Rlt_le_dec; auto.
    split; intros; auto; try easy. lra.
  Qed.
  
  (** The angle from i to v is <= π, if and only if v.y is non negative *)
  Lemma cv2angleGtPI_i_false : forall (v : cvec 2), cv2angleGtPI cv2i v = false <-> 0 <= v.y.
  Proof.
    intros. cvec2fun. cbv. autorewrite with R. destruct Rlt_le_dec; auto.
    split; intros; auto; try easy. lra.
  Qed.
  
  (** The angle from j to v is > π, if and only if v.x is positive *)
  Lemma cv2angleGtPI_j_true : forall (v : cvec 2), cv2angleGtPI cv2j v = true <-> 0 < v.x.
  Proof.
    intros. cvec2fun. cbv. autorewrite with R. destruct Rlt_le_dec; auto.
    split; intros; auto; try easy. lra.
    split; intros; auto; try easy. lra.
  Qed.
  
  (** The angle from j to v is <= π, if and only if v.x is non positive *)
  Lemma cv2angleGtPI_j_false : forall (v : cvec 2), cv2angleGtPI cv2j v = false <-> v.x <= 0.
  Proof.
    intros. cvec2fun. cbv. autorewrite with R. destruct Rlt_le_dec; auto.
    split; intros; auto; try easy. lra.
    split; intros; auto; try easy. lra.
  Qed.

  (** The angle from vector v1 to vector v2, θ ∈ [0,2π) *)
  Definition cv2angle (v1 v2 : cvec 2) : R :=
    let angle := cvangle v1 v2 in
    if cv2angleGtPI v1 v2
    then 2 * PI - angle
    else angle.

  (** ∠(i,j) = π/2 *)
  Example cv2angle_ex1 : cv2angle cv2i cv2j = PI/2.
  Proof.
    unfold cv2angle. unfold cv2angleGtPI. simpl.
    autorewrite with R. bdestruct (1 <? 0); try lra.
    unfold cvangle.
    match goal with |- context[acos ?a] => replace a with 0 end. apply acos_0.
    cbv. ra.
  Qed.

  (** ∠(j,i) = 3π/2 *)
  Example cv2angle_ex2 : cv2angle cv2j cv2i = 3*PI/2.
  Proof.
    unfold cv2angle. unfold cv2angleGtPI. simpl.
    autorewrite with R. bdestruct (0 - 1 <? 0); try lra.
    unfold cvangle.
    match goal with |- context[acos ?a] => replace a with 0 end. rewrite acos_0. lra.
    cbv. ra.
  Qed.

  (* (** ∠(v1,v2) + ∠(v2,v1) = 2*π *) *)
  (* Lemma cv2angle_anticomm : forall (v1 v2 : cvec 2), *)
  (*     ((cv2angle v1 v2) + (cv2angle v2 v1) = 2 * PI)%R. *)
  (* Proof. *)
  (*   intros. unfold cv2angle. ? *)
  (*   rewrite cv2angleLtPI_GtPI_comm.  *)
  
  (*   ? *)

  (** cos (cv2angle x y) = cos (cvangle x y) *)
  Lemma cos_cv2angle_eq_cos_cvangle : forall (x y : cvec 2),
      cos (cv2angle x y) = cos (cvangle x y).
  Proof.
    intros. unfold cv2angle. destruct (cv2angleGtPI x y); auto.
    unfold Rminus. rewrite RealFunction.cos_2PI_add. apply cos_neg.
  Qed.

  (** i与任意非零向量v的夹角的余弦等于其横坐标除以长度 *)
  Lemma cos_cv2angle_i : forall (v : cvec 2),
      cvnonzero v -> cos (cv2angle cv2i v) = (v.x / ||v||)%R.
  Proof.
    intros. rewrite cos_cv2angle_eq_cos_cvangle.
    unfold cvangle. rewrite cos_acos.
    - rewrite cv2i_cvnormalize_fixpoint. rewrite cv2dot_i_l.
      rewrite cvnormalize_nth; auto.
    - apply cvdot_vnormalize_bound; auto. apply cv2i_nonzero.
  Qed.

  (** i与任意非零向量v的夹角的正弦等于其纵坐标除以长度 *)
  Lemma sin_cv2angle_i : forall (v : cvec 2),
      cvnonzero v -> sin (cv2angle cv2i v) = (v.y / ||v||)%R.
  Proof.
    intros. unfold cv2angle. destruct (cv2angleGtPI cv2i v) eqn:E1.
    - unfold Rminus. rewrite RealFunction.sin_2PI_add. rewrite sin_neg.
      apply cv2angleGtPI_i_true in E1. unfold cvangle. rewrite sin_acos.
      + rewrite cv2i_cvnormalize_fixpoint. rewrite cv2dot_i_l.
        rewrite cvnormalize_nth; auto. rewrite cv2len_eq.
        rewrite Rsqrt_1_minus_x_eq_y. field_simplify. f_equal.
        rewrite Rabs_left; auto. lra.
        all: try apply cvlen_neq0_iff_neq0 in H; rewrite cv2len_eq in H; auto.
        apply sqrt_neq0_iff in H. lra.
      + apply cvdot_vnormalize_bound; auto. apply cv2i_nonzero.
    - apply cv2angleGtPI_i_false in E1. unfold cvangle. rewrite sin_acos.
      + rewrite cv2i_cvnormalize_fixpoint. rewrite cv2dot_i_l.
        rewrite cvnormalize_nth; auto. rewrite cv2len_eq.
        rewrite Rsqrt_1_minus_x_eq_y.
        * f_equal. rewrite Rabs_right; auto. ra.
        * apply cvlen_neq0_iff_neq0 in H. rewrite cv2len_eq in H.
          apply sqrt_neq0_iff in H. lra.
      + apply cvdot_vnormalize_bound; auto. apply cv2i_nonzero.
  Qed.

  (** j与任意非零向量v的夹角的余弦等于其纵坐标除以长度 *)
  Lemma cos_vangle_j : forall (v : cvec 2),
      cvnonzero v -> cos (cv2angle cv2j v) = (v.y / ||v||)%R.
  Proof.
    intros. rewrite cos_cv2angle_eq_cos_cvangle.
    unfold cvangle. rewrite cos_acos.
    - rewrite cv2j_cvnormalize_fixpoint. rewrite cv2dot_j_l.
      rewrite cvnormalize_nth; auto.
    - apply cvdot_vnormalize_bound; auto. apply cv2j_nonzero.
  Qed.
  
  (** j与任意非零向量v的夹角的正弦等于其横坐标取负除以长度 *)
  Lemma sin_vangle_j : forall (v : cvec 2),
      cvnonzero v -> sin (cv2angle cv2j v) = (- v.x / ||v||)%R.
  Proof.
    intros. unfold cv2angle. destruct (cv2angleGtPI cv2j v) eqn:E1.
    - unfold Rminus. rewrite RealFunction.sin_2PI_add. rewrite sin_neg.
      apply cv2angleGtPI_j_true in E1. unfold cvangle. rewrite sin_acos.
      + rewrite cv2j_cvnormalize_fixpoint. rewrite cv2dot_j_l.
        rewrite cvnormalize_nth; auto. rewrite cv2len_eq.
        rewrite Rsqrt_1_minus_y_eq_x.
        field_simplify. f_equal. rewrite Rabs_right; auto. lra.
        all: try apply cvlen_neq0_iff_neq0 in H; rewrite cv2len_eq in H; auto.
        apply sqrt_neq0_iff in H. lra.
      + apply cvdot_vnormalize_bound; auto. apply cv2j_nonzero.
    - apply cv2angleGtPI_j_false in E1. unfold cvangle. rewrite sin_acos.
      + rewrite cv2j_cvnormalize_fixpoint. rewrite cv2dot_j_l.
        rewrite cvnormalize_nth; auto. rewrite cv2len_eq.
        rewrite Rsqrt_1_minus_y_eq_x. f_equal; auto with R.
        apply cvlen_neq0_iff_neq0 in H; rewrite cv2len_eq in H;
          apply sqrt_neq0_iff in H. lra.
      + apply cvdot_vnormalize_bound; auto. apply cv2j_nonzero.
  Qed.

End cv2angle.


(** ** Rotation matrix in 2D *)
Section RotationMatrix2D.

  (** 主动旋转，逆时针正向(或顺时针负向)时，旋转矩阵 *)

  (** 注意列向量和行向量的不同用法：
     1. 给一个在该坐标系下的列向量 v1，正向旋转该向量 θ 角得到新的向量 v1'，按如下公式
          v1' = R2(θ) * v1
          v1  = R2(θ)\T * v1'
     2. 给一个在该坐标系下的行向量 v2，正向旋转该向量 θ 角得到新的向量 v2'，按如下公式
          v2' = v2 * (R2(θ))\T
     3. 如果进行了连续两次旋转，即，先旋转θ1，然后在此基础上再旋转θ2，则
        按照列向量：v' = R(θ2) * R(θ1) * v，其中 R 是 R2
        按照行向量：v' = v * R(θ1) * R(θ2)，其中 R 是 R2\T
   *)

  (** Rotation matrix in 2D *)
  Definition R2 (θ : R) : smat 2 :=
    let c := cos θ in
    let s := sin θ in
    l2m [[c;-s];[s;c]]%R.

  (** R2 is orthogonal matrix *)
  Lemma R2_orthogonal : forall (θ : R), morthogonal (R2 θ).
  Proof. lma; autorewrite with R; easy. Qed.

  (** The determinant of R2 is 1 *)
  Lemma R2_det1 : forall (θ : R), mdet (R2 θ) = 1.
  Proof. intros. cbv. autorewrite with R; easy. Qed.

  (** R2 is a member of SO2 *)
  Definition R2_SO2 (θ : R) : SO2.
    refine (Build_SOn _ (R2 θ) _). split.
    apply R2_orthogonal. apply R2_det1.
  Defined.

  (** R(θ)⁻¹ = R(θ)\T *)
  
  Lemma R2_inv_eq_trans : forall θ : R, (R2 θ)⁻¹ == (R2 θ)\T.
  Proof.
    (* method 1 : prove by computing (slow) *)
    (* lma; autounfold with A; autorewrite with R; try easy. *)
    (* method 2 : prove by reasoning *)
    intros; apply (SOn_imply_inv_eq_trans (R2_SO2 θ)).
  Qed.

  (** R(-θ) = R(θ)\T *)
  Lemma R2_neg_eq_trans : forall θ : R, R2 (-θ) == (R2 θ)\T.
  Proof. lma; autorewrite with R; try easy. Qed.

  (** R(-θ) * R(θ) = I *)
  Lemma R2_neg_R2_inv : forall θ : R, R2 (- θ) * R2 θ == mat1.
  Proof.
    (* lma; autounfold with A; autorewrite with R; auto; ring. *)
    intros; rewrite R2_neg_eq_trans, <- R2_inv_eq_trans, mmul_minv_l; easy.
  Qed.

  (** R(θ) * R(-θ) = I *)
  Lemma R2_R2_neg_inv : forall θ : R, R2 θ * R2 (- θ) == mat1.
  Proof.
    (* lma; autounfold with A; autorewrite with R; auto; ring. *)
    intros; rewrite R2_neg_eq_trans, <- R2_inv_eq_trans, mmul_minv_r; easy.
  Qed.

  (** v' = R(θ) * v *)
  Lemma R2_spec1 : forall (v : cvec 2) (θ : R),
      let l := cvlen v in
      let α := cv2angle cv2i v in
      let vx' := (l * cos (α + θ))%R in
      let vy' := (l * sin (α + θ))%R in
      let v' : cvec 2 := mk_cvec2 vx' vy' in
      cvnonzero v -> v' == R2 θ * v.
  Proof.
    lma.
    - unfold vx'. unfold l. unfold α.
      rewrite cos_plus. unfold Rminus. rewrite Rmult_plus_distr_l.
      rewrite cos_cv2angle_i, sin_cv2angle_i; auto.
      autounfold with A. autorewrite with R. field.
      apply cvlen_neq0_iff_neq0; auto.
    - unfold vy'. unfold l. unfold α.
      rewrite sin_plus. rewrite Rmult_plus_distr_l.
      rewrite cos_cv2angle_i, sin_cv2angle_i; auto.
      autounfold with A. autorewrite with R. field.
      apply cvlen_neq0_iff_neq0; auto.
  Qed.

  (** v = R(-θ) * v' *)
  Lemma R2_spec2 : forall (v : cvec 2) (θ : R),
      let l := cvlen v in
      let α := cv2angle cv2i v in
      let vx' := (l * cos (α + θ))%R in
      let vy' := (l * sin (α + θ))%R in
      let v' : cvec 2 := mk_cvec2 vx' vy' in
      cvnonzero v -> v == (R2 (-θ)) * v'.
  Proof.
    intros.
    pose proof (R2_spec1 v θ). simpl in H0. specialize (H0 H).
    unfold v',vx',vy',l,α. rewrite H0. rewrite <- mmul_assoc.
    rewrite R2_neg_R2_inv. rewrite mmul_1_l. easy.
  Qed.

  (** v = R(θ)\T * v' *)
  Lemma R2_spec3 : forall (v : cvec 2) (θ : R),
      let l := cvlen v in
      let α := cv2angle cv2i v in
      let vx' := (l * cos (α + θ))%R in
      let vy' := (l * sin (α + θ))%R in
      let v' : cvec 2 := mk_cvec2 vx' vy' in
      cvnonzero v -> v == (R2 θ)\T * v'.
  Proof.
    intros.
    pose proof (R2_spec2 v θ). simpl in H0. specialize (H0 H).
    unfold v',vx',vy',l,α. rewrite <- R2_neg_eq_trans. auto.
  Qed.

  (** 预乘和后乘旋转矩阵的关系，即: v ~ v' -> R(θ) * v ~ v' * R(θ) *)
  Lemma R2_spec4 : forall (v1 : cvec 2) (θ : R),
      let v1' : rvec 2 := v1\T in  (* v1和v1'是列向量和行向量形式的同一个向量 *)
      let v2 : cvec 2 := (R2 θ) * v1 in       (* 用列向量形式计算 *)
      let v2' : rvec 2 := v1' * ((R2 θ)\T) in (* 用行向量形式计算 *)
      let v2'' : cvec 2 := v2'\T in           (* v2' 的列向量形式 *)
      v2 == v2''. (* 结果应该相同 *)
  Proof. lma. Qed.

  (** R的乘法是交换的: R(θ1) * R(θ2) = R(θ2) * R(θ1) *)
  Lemma R2_mul_comm : forall (θ1 θ2 : R), (R2 θ1) * (R2 θ2) == (R2 θ2) * (R2 θ1).
  Proof. lma. Qed.

  (** R的乘法等价于对参数的加法: R(θ1) * R(θ2) = R(θ1 + θ2) *)
  Lemma R2_mul_eq_sum : forall (θ1 θ2 : R), (R2 θ1) * (R2 θ2) == R2 (θ1 + θ2).
  Proof. lma; autounfold with A; autorewrite with R; ring. Qed.

End RotationMatrix2D.


(** ** Rotation: Friendly name for user, avoid low-level matrix operation *)
Section Rotation.

  (** 为了避免旋转矩阵使用错误，命名一些操作 *)
  
  (** 2D中旋转一个列向量 *)
  Definition Rot2C (θ : R) (v : cvec 2) : cvec 2 := (R2 θ) * v.

  (** 2D中旋转一个行向量 *)
  Definition Rot2R (θ : R) (v : rvec 2) : rvec 2 := v * ((R2 θ)\T).

  (** 旋转列向量，等效于旋转行向量 *)
  Lemma Rot2C_eq_Rot2R : forall θ (v : cvec 2), Rot2C θ v == (Rot2R θ (v\T))\T.
  Proof. lma. Qed.

  (** 旋转行向量，等效于旋转列向量 *)
  Lemma Rot2R_eq_Rot2C : forall θ (v : rvec 2), Rot2R θ v == (Rot2C θ (v\T))\T.
  Proof. lma. Qed.

  (** 旋转两次，等价于一次旋转两个角度之和: Rot(θ2, Rot(θ1,v)) = Rot(θ1+θ2, v) *)
  Lemma Rot2C_twice : forall (θ1 θ2 : R) (v : cvec 2),
      Rot2C θ2 (Rot2C θ1 v) == Rot2C (θ1+θ2) v.
  Proof.
    intros. unfold Rot2C. rewrite <- mmul_assoc. rewrite R2_mul_eq_sum.
    rewrite Rplus_comm. easy.
  Qed.
  
  Lemma Rot2R_twice : forall (θ1 θ2 : R) (v : rvec 2),
      Rot2R θ2 (Rot2R θ1 v) == Rot2R (θ1+θ2) v.
  Proof.
    intros. unfold Rot2R. rewrite mmul_assoc.
    rewrite <- mtrans_mmul. rewrite R2_mul_eq_sum. rewrite Rplus_comm. easy.
  Qed.
  
End Rotation.
