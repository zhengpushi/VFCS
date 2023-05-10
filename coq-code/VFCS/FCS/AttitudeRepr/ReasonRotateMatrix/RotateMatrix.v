(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : reasoning the rotation matrix under 2-dim and 3-dim space.
  author    : ZhengPu Shi
  date      : Mar, 2021
*)

Require Export VectorR.

(* Export List. *)
(* Export ListNotations. *)

Open Scope nat_scope.
Open Scope R_scope.
Open Scope mat_scope.


(* (** equality of list, if corresponding elements are equal. *) *)
(* Lemma list_equality : forall (A : Type) (a1 a2 : A) (l1 l2 : list A), *)
(*   a1 = a2 -> l1 = l2 -> a1 :: l1 = a2 :: l2. *)
(* Proof. intros. subst; auto. Qed. *)

(** 
   Specify positive direction
   1. in 2D, the counterclockwise direction is positive, which is consistent with 
      the usual angle definition.
   2. in 3D, the right-hand rule is used to specify the positive direction.
 *)

(**
   Naming convention:
   1. "o2n" means transformation from old vector to new vector.
   2. "n2o" means transformation from new vector to old vector.
*)

Section Rotation2D.

  (* 二维向量执行旋转操作的转换矩阵。
     已知向量a=[ax ay]^T，长度为l，与+x夹角为alpha，绕原点按正方向旋转beta角后
     得到b=[bx by]^T，求出旋转矩阵Rab(beta),Rba(beta)，使得：
     b=Rab(beta)a，
     a=Rba(beta)b.
  *)
  Definition Rab (beta : R) : mat 2 2 :=
    mk_mat_2_2
      (cos beta) (- sin beta)%A
      (sin beta) (cos beta).
  Definition Rba (beta : R) : mat 2 2 :=
    mk_mat_2_2 
      (cos beta) (sin beta)
      (- sin beta)%A (cos beta).

  Lemma Rab_spec (a : cvec 2) (beta : R) :
    let l := cvlen a in
    let alpha := cvangle cv2i atan (a.y / a.x) in
    let b_x := (l * cos (alpha + beta))%R in
    let b_y := (l * sin (alpha + beta))%R in
    let b : cvec 2 := l2cv [b_x;b_y] in
    b == Rab beta * a.
  Proof.
    lma.
    - unfold b_x. autorewrite with R.
      unfold Rminus. rewrite Rmult_plus_distr_l.
      f_equiv. ring_simplify.
      
      rewrite Rmul_
      unfold alpha.
      rewrite cos_atan, sin_atan.
      unfold l. ring_simplify.
    true.
    let p1 := a1 = (l * cos alpha)%R in
    let p2 := a2 = (l * sin alpha)%R in
    let b1 := (l * cos (alpha + beta))%R in
    let b2 := (l * sin (alpha + beta))%R in
    let ob := t2v_2 (b1,b2) in
    let A := rotation_matrix_2d_o2n beta in
      p1 -> p2 ->
      ob == (mmul A oa).
  Proof.
    destruct oa as [oa]. simpl.
    lma; cbv in *; autorewrite with R in *;
      remember (oa 0 0)%nat as a1;
      remember (oa 1 0)%nat as a2.
    - rewrite cos_plus; ring_simplify.
      rewrite <- H, <- H0. ring.
    - rewrite sin_plus; ring_simplify.
      rewrite <- H, <- H0. ring.
  Qed.
  
  Lemma rotation_matrix_2d_n2o_correct (oa : vec 2) (beta : R) :
    let '(a1,a2) := v2t_2 oa in
    let l := vlen oa in 
    let alpha := (atan (a2 / a1))%R in
    let p1 := a1 = (l * cos alpha)%R in
    let p2 := a2 = (l * sin alpha)%R in
    let b1 := (l * cos (alpha + beta))%R in
    let b2 := (l * sin (alpha + beta))%R in
    let ob := t2v_2 (b1,b2) in
    let B := rotation_matrix_2d_n2o beta in
      p1 -> p2 ->
      oa == (mmul B ob).
  Proof.
    destruct oa as [oa]. simpl.
    lma; cbv in *; autorewrite with R in *;
      remember (oa 0 0)%nat as a1;
      remember (oa 1 0)%nat as a2.
    - rewrite cos_plus,sin_plus; ring_simplify.
      rewrite Rmult_assoc. rewrite <- H.
      autorewrite with R.
      replace ((cos beta)² * a1 + a1 * (sin beta)²)%R
        with (((cos beta)² + (sin beta)²) * a1)%R; try ring.
      autorewrite with R. auto.
    - rewrite cos_plus,sin_plus; ring_simplify.
      rewrite Rmult_assoc. rewrite <- H0.
      rewrite Rmult_assoc. rewrite (Rmult_comm _ (sin _)). rewrite <- Rmult_assoc.
      rewrite <- H0.
      autorewrite with R.
      replace ((sin beta)² * a2 + a2 * (cos beta)²)%R
        with (((sin beta)² + (cos beta)²) * a2)%R; try ring.
      autorewrite with R. auto.
  Qed.


  (* 二维向量执行旋转操作的转换矩阵。
    已知向量oa=[a1 a2]^T，长度为l，与ox夹角为alpha，绕原点按正方向旋转beta角后
    得到ob=[b1 b2]^T，求出旋转矩阵A(beta),B(beta)，使得：
    [b1 b2]^T=A(beta)[a1 a2]^T，
    [a1 a2]^T=B(beta)[b1 b2]^T
  *)
  Definition rotation_matrix_2d_o2n (beta : R) : mat 2 2 :=
    mk_mat_2_2
      (cos beta) (- sin beta)%A
      (sin beta) (cos beta).
  Definition rotation_matrix_2d_n2o (beta : R) : mat 2 2 :=
    mk_mat_2_2 
      (cos beta) (sin beta)
      (- sin beta)%A (cos beta).

  Lemma rotation_matrix_2d_o2n_correct (oa : vec 2) (beta : R) :
    let '(a1,a2) := v2t_2 oa in
    let l := vlen oa in 
    let alpha := atan (a2 / a1) in
    let p1 := a1 = (l * cos alpha)%R in
    let p2 := a2 = (l * sin alpha)%R in
    let b1 := (l * cos (alpha + beta))%R in
    let b2 := (l * sin (alpha + beta))%R in
    let ob := t2v_2 (b1,b2) in
    let A := rotation_matrix_2d_o2n beta in
      p1 -> p2 ->
      ob == (mmul A oa).
  Proof.
    destruct oa as [oa]. simpl.
    lma; cbv in *; autorewrite with R in *;
      remember (oa 0 0)%nat as a1;
      remember (oa 1 0)%nat as a2.
    - rewrite cos_plus; ring_simplify.
      rewrite <- H, <- H0. ring.
    - rewrite sin_plus; ring_simplify.
      rewrite <- H, <- H0. ring.
  Qed.
  
  Lemma rotation_matrix_2d_n2o_correct (oa : vec 2) (beta : R) :
    let '(a1,a2) := v2t_2 oa in
    let l := vlen oa in 
    let alpha := (atan (a2 / a1))%R in
    let p1 := a1 = (l * cos alpha)%R in
    let p2 := a2 = (l * sin alpha)%R in
    let b1 := (l * cos (alpha + beta))%R in
    let b2 := (l * sin (alpha + beta))%R in
    let ob := t2v_2 (b1,b2) in
    let B := rotation_matrix_2d_n2o beta in
      p1 -> p2 ->
      oa == (mmul B ob).
  Proof.
    destruct oa as [oa]. simpl.
    lma; cbv in *; autorewrite with R in *;
      remember (oa 0 0)%nat as a1;
      remember (oa 1 0)%nat as a2.
    - rewrite cos_plus,sin_plus; ring_simplify.
      rewrite Rmult_assoc. rewrite <- H.
      autorewrite with R.
      replace ((cos beta)² * a1 + a1 * (sin beta)²)%R
        with (((cos beta)² + (sin beta)²) * a1)%R; try ring.
      autorewrite with R. auto.
    - rewrite cos_plus,sin_plus; ring_simplify.
      rewrite Rmult_assoc. rewrite <- H0.
      rewrite Rmult_assoc. rewrite (Rmult_comm _ (sin _)). rewrite <- Rmult_assoc.
      rewrite <- H0.
      autorewrite with R.
      replace ((sin beta)² * a2 + a2 * (cos beta)²)%R
        with (((sin beta)² + (cos beta)²) * a2)%R; try ring.
      autorewrite with R. auto.
  Qed.

End Rotation2D.

  
Section Rotation3D.

  (* 3D向量绕x轴旋转的转换矩阵。
    已知向量oa=[a1 a2 a3]^T，其绕x轴旋转到达ob=[b1 b2 b3]，此时x坐标不变，
    而y,z坐标等价于将其投影到yz平面上进行逆时针旋转。
    求出旋转矩阵A(beta),B(beta)，使得：
    [b1 b2 b3]^T=A(beta)[a1 a2 a3]^T，
    [a1 a2 a3]^T=B(beta)[b1 b2 b3]^T
  *)
  Definition rotation_matrix_3d_x_o2n (beta : R) : mat 3 3 :=
    mk_mat_3_3
      1 0 0
      0 (cos beta) (- sin beta)%A
      0 (sin beta) (cos beta).

  End Rotation3D.
