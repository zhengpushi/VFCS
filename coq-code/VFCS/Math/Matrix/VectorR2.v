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
(** * 2D vector theory *)

(** 2D向量相等的等价形式 *)
Lemma cv2eq_iff : forall v1 v2 : cvec 2, v1 == v2 <-> v1.x = v2.x /\ v1.y = v2.y.
Proof.
  intros. split; intros; try lma. split.
  - specialize (H 0 0)%nat; apply H; auto.
  - specialize (H 1 0)%nat; apply H; auto.
Qed.


(** 标准基向量 *)
Section basis.
  Definition cv2i : cvec 2 := mk_cvec2 1 0.
  Definition cv2j : cvec 2 := mk_cvec2 0 1.

  (** 任意向量都能写成该向量的坐标在标准基向量下的线性组合 *)
  Lemma cv2ij_spec : forall (v : cvec 2), v == v.x c* cv2i + v.y c* cv2j.
  Proof. lma. Qed.

  (** 标准基向量的长度为 1 *)
  Lemma cv2i_len1 : ||cv2i|| = 1.
  Proof. cbv. autorewrite with R; auto. Qed.
  
  Lemma cv2j_len1 : ||cv2j|| = 1.
  Proof. cbv. autorewrite with R; auto. Qed.

  (** 标准基向量都是非零向量 *)
  Lemma cv2i_nonzero : cvnonzero cv2i.
  Proof. intro. apply cv2eq_iff in H. inv H. ra. Qed.

  Lemma cv2j_nonzero : cvnonzero cv2j.
  Proof. intro. apply cv2eq_iff in H. inv H. ra. Qed.

  (** 任意向量v与i的点积等于v的横坐标 *)
  Lemma cv2dot_i_eq_x : forall (v : cvec 2), <v, cv2i> = v.x.
  Proof. intros. cvec2fun. cbv. ring. Qed.

  (** 任意向量v与j的点积等于v的横坐标 *)
  Lemma cv2dot_j_eq_y : forall (v : cvec 2), <v, cv2j> = v.y.
  Proof. intros. cvec2fun. cbv. ring. Qed.

  (** 任意非零向量v与i的夹角的余弦等于其横坐标除以长度 *)
  Lemma cos_vangle_i : forall (v : cvec 2),
      cvnonzero v -> cos (cvangle v cv2i) = (v.x / ||v||)%R.
  Proof.
    intros. unfold cvangle. rewrite cos_acos.
    - unfold cvnormalize. rewrite cv2i_len1. autorewrite with R.
      rewrite cvdot_vcmul_l, cvdot_vcmul_r.
      rewrite cv2dot_i_eq_x. autounfold with A. field.
      apply cvlen_neq0_iff_neq0; auto.
    - apply cvdot_vnormalize_bound; auto. apply cv2i_nonzero.
  Qed.

  (** 任意非零向量v与i的夹角的正弦等于其纵坐标除以长度 *)
  Lemma sin_vangle_i : forall (v : cvec 2),
      cvnonzero v -> sin (cvangle v cv2i) = (v.y / ||v||)%R.
  Proof.
    intros. unfold cvangle. rewrite sin_acos.
    - unfold cvnormalize. rewrite cv2i_len1. autorewrite with R.
      rewrite cvdot_vcmul_l, cvdot_vcmul_r.
      rewrite cv2dot_i_eq_x. autounfold with A.
      autorewrite with R.
      Admitted.
  (*     field. *)
  (*     apply cvlen_neq0_iff_neq0; auto. *)
  (*   - (* -1 <= <cvnormalize v,cvnormalize cv2i> <= 1 *) ? *)
  (*     rewrite cv2dot_cosine. *)
  (*     rewrite ?cvnormalize_len1; auto. *)
  (*     match goal with |- context [cos ?r] => remember r as a end. *)
  (*     pose proof (COS_bound a). lra. apply cv2i_nonzero. *)
  (* Qed. *)

  (** 任意非零向量v与j的夹角的余弦等于其纵坐标除以长度 *)
  Lemma cos_vangle_j : forall (v : cvec 2),
      cvnonzero v -> cos (cvangle v cv2j) = (v.y / ||v||)%R.
  Admitted.
  
  (** 任意非零向量v与j的夹角的正弦等于其横坐标除以长度 *)
  Lemma sin_vangle_j : forall (v : cvec 2),
      cvnonzero v -> sin (cvangle v cv2i) = (v.x / ||v||)%R.
  Admitted.  

End basis.

Section RotationMatrix.
  (** 主动旋转，逆时针正向(或顺时针负向)时，旋转矩阵 *)

  (** 注意列向量和行向量的不同用法：
     1. 给一个在该坐标系下的列向量 v1，正向旋转该向量 θ 角得到新的向量 v1'，按如下公式
          v1' = R2d(θ) * v1
     2. 给一个在该坐标系下的行向量 v2，正向旋转该向量 θ 角得到新的向量 v2'，按如下公式
          v2' = v2 * (R2d(θ))\T
     3. 如果进行了连续两次旋转，即，先旋转θ1，然后在此基础上再旋转θ2，则
        按照列向量：v' = R(θ2) * R(θ1) * v，其中 R 是 R2d
        按照行向量：v' = v * R(θ1) * R(θ2)，其中 R 是 R2d\T
   *)
  Definition R2d (θ : R) : smat 2 :=
    let c := cos θ in
    let s := sin θ in
    l2m [[c;-s];[s;c]]%R.

  (** 利用三角关系来验证旋转矩阵 *)
  Lemma R2d_spec (v : cvec 2) (θ : R) :
    let l := cvlen v in
    let α := cvangle cv2i v in
    let vx' := (l * cos (α + θ))%R in
    let vy' := (l * sin (α + θ))%R in
    let v' : cvec 2 := mk_cvec2 vx' vy' in
    cvnonzero v -> v' == R2d θ * v.
  Proof.
    lma.
    - unfold vx'. unfold l. unfold α.
      rewrite cos_plus. unfold Rminus. rewrite Rmult_plus_distr_l.
      rewrite cvangle_comm. rewrite cos_vangle_i, sin_vangle_i; auto.
      autounfold with A. autorewrite with R. field.
      apply cvlen_neq0_iff_neq0; auto.
    - unfold vy'. unfold l. unfold α.
      rewrite sin_plus. rewrite Rmult_plus_distr_l.
      rewrite cvangle_comm. rewrite cos_vangle_i, sin_vangle_i; auto.
      autounfold with A. autorewrite with R. field.
      apply cvlen_neq0_iff_neq0; auto.
  Qed.

End RotationMatrix.

(** 一个实际的例子来说明该旋转矩阵的用法 *)
Section test.
  Variable θ : R.
  Variable v1 : cvec 2.
  Let v2 : rvec 2 := v1\T. (* v1和v2在数学上相等，只是分别写作列向量和行向量的形式 *)
  Let v1' : cvec 2 := (R2d θ) * v1.     (* 用列向量形式计算 *)
  Let v2' : rvec 2 := v2 * ((R2d θ)\T). (* 用行向量形式计算 *)
  Let v2'' : cvec 2 := v2'\T.  (* 再次写出 v2' 的列向量形式 *)
  Goal v1' == v2''. (* 结果应该相同 *)
  Proof. lma. Qed.

End test.


(** 为了避免旋转矩阵使用错误，命名一些操作 *)

(** 2D中旋转一个列向量 *)
Definition Rot2dC (θ : R) (v : cvec 2) : cvec 2 := (R2d θ) * v.

(** 2D中旋转一个行向量 *)
Definition Rot2dR (θ : R) (v : rvec 2) : rvec 2 := v * ((R2d θ)\T).

(** 旋转列向量，等效于旋转行向量，但需要转换输入和输出的向量形式 *)
Lemma Rot2dC_eq_Rot2dR : forall θ (v : cvec 2), Rot2dC θ v == (Rot2dR θ (v\T))\T.
Proof. lma. Qed.

(** 旋转列向量，等效于旋转行向量，但需要转换输入和输出的向量形式 *)
Lemma Rot2dR_eq_Rot2dC : forall θ (v : rvec 2), Rot2dR θ v == (Rot2dC θ (v\T))\T.
Proof. lma. Qed.


(* (* ==================================== *) *)
(* (** ** Exercise in textbook *) *)
(* Section exercise. *)
(*   (** 习题8.2第12题, page 23, 高等数学，第七版 *) *)
(*   (** 利用向量来证明不等式，并指出等号成立的条件 *) *)
(*   Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R, *)
(*       sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= |a1*b1 + a2*b2 + a3*b3|. *)
(*   Proof. *)
(*     intros. *)
(*     pose (a := t2cv_3 (a1,a2,a3)). *)
(*     pose (b := t2cv_3 (b1,b2,b3)). *)
(*     pose (alen := cvlen a). *)
(*     pose (blen := cvlen b). *)
(*     replace (sqrt _) with alen; [| unfold alen; cbv; f_equal; ring]. *)
(*     replace (sqrt _) with blen; [| unfold blen; cbv; f_equal; ring]. *)
(*     replace (Rabs _) with (|<a,b>|); [| cbv; autorewrite with R; auto]. *)
(*   Abort. *)

(*   (** Example 4, page 19, 高等数学，第七版 *) *)
(*   Goal let a := t2cv_3 (2,1,-1) in *)
(*        let b := t2cv_3 (1,-1,2) in *)
(*        a × b == t2cv_3 (1,-5,-3). *)
(*   Proof. lma. Qed. *)

(*   (** Example 5, page 19, 高等数学，第七版 *) *)
(*   (** 根据三点坐标求三角形面积 *) *)
(*   Definition cv3_area_of_triangle (A B C : cvec 3) := *)
(*     let AB := B - A in *)
(*     let AC := C - A in *)
(*     ((1/2) * ||AB × AC||)%R. *)

(*   (** Example 6, page 20, 高等数学，第七版 *) *)
(*   (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*) *)
(*   Definition cv3_rotation_model (ω r v : cvec 3) := v = ω × r. *)

(* End exercise. *)


(* (* ======================================================================= *) *)
(* (** * Usage demo *) *)
(* Section test. *)
(*   Let l1 := [1;2;3]. *)
(*   Let v1 := @l2rv 2 l1. *)
(*   Let v2 := @l2cv 2 l1. *)
(*   (* Compute rv2l v1. *) *)
(*   (* Compute cv2l v2. *) *)


(*   Variable a1 a2 a3 : A. *)
(*   Variable f : A -> A. *)
(*   Let v3 := t2rv_3 (a1,a2,a3). *)
(*   Let v4 := t2cv_3 (a1,a2,a3). *)
(*   (* Compute rv2l (rvmap v3 f). *) *)
(*   (* Compute cv2l (cvmap v4 f). *) *)
  
(* End test. *)
