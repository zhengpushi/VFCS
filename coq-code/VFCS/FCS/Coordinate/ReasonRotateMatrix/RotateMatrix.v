(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose:    reasoning the rotation matrix under 2-dim and 3-dim space.
  author:     ZhengPu Shi
  date:       Mar 11, 2021
*)

From FCS Require Export VectorR.

Export List.
Export ListNotations.

Open Scope R_scope.
Open Scope mat_scope.


(** equality of list, if corresponding elements are equal. *)
Lemma list_equality : forall (A : Type) (a1 a2 : A) (l1 l2 : list A),
  a1 = a2 -> l1 = l2 -> a1 :: l1 = a2 :: l2.
Proof. intros. subst; auto. Qed.


Section RotationUnder2D.

  (* 二维向量顺时针旋转的转换矩阵。
    已知向量om=[x1 y1]^T，长度为l，与ox夹角为alpha，绕原点顺时针旋转beta角后
    得到on=[x2 y2]^T，求出旋转矩阵A(beta),B(beta)，使得：
    [x2 y2]^T=A(beta)[x1 y1]^T，
    [x1 y1]^T=B(beta)[x2 y2]^T
  *)
  Definition rotation_matrix_clockwise_2d_A (beta : R) : mat 2 2 := mat_2_2 
    (cos beta) (- sin beta)%A
    (sin beta) (cos beta).
  Definition rotation_matrix_clockwise_2d_B (beta : R) : mat 2 2 := mat_2_2 
    (cos beta) (sin beta)
    (- sin beta)%A (cos beta).
  
  Lemma rotation_matrix_clockwise_2d_A_correct (om : vec 2) (beta : R) :
    let '(x1,y1) := v2_to_t2 om in
    let l := v2_len om in 
    let alpha := atan (y1 / x1) in
    let p1 := x1 = l * cos alpha in
    let p2 := y1 = l * sin alpha in
    let x2 := l * cos (alpha + beta) in
    let y2 := l * sin (alpha + beta) in
    let on := t2_to_v2 (x2,y2) in
    let A := rotation_matrix_clockwise_2d_A beta in
      p1 -> p2 ->
      on = (mmul A om).
  Proof.
    destruct om.
    destruct mat_data; simpl in *; try easy.
    destruct mat_data; simpl in *; try easy.
    inversion mat_height. apply length_zero_iff_nil in H0; subst.
    destruct mat_width. destruct a.
    destruct l; simpl in *; try easy.
    destruct l0; simpl in *; try easy.
    inversion e. inversion e0.
    apply length_zero_iff_nil in H0,H1. subst.
    intros.
    apply meq_iff. simpl in *.
    unfold v2_len in *. unfold v2_to_t2 in *. simpl in *.
    rewrite cos_plus, sin_plus.
    rewrite Rmult_plus_distr_l, Rmult_minus_distr_l.
    repeat rewrite <- Rmult_assoc.
    unfold mul in *.
    rewrite <- H. rewrite <- H0.
    repeat apply list_equality; auto;
    unfold RingTypeR.A, add, ListAux.ldot; simpl; trigo_simp.
  Qed.
  
  Lemma rotation_matrix_clockwise_2d_B_correct (om : vec 2) (beta : R) :
    let '(x1,y1) := v2_to_t2 om in
    let l := v2_len om in 
    let alpha := atan (y1 / x1) in
    let p1 := x1 = l * cos alpha in
    let p2 := y1 = l * sin alpha in
    let x2 := l * cos (alpha + beta) in
    let y2 := l * sin (alpha + beta) in
    let on := t2_to_v2 (x2,y2) in
    let B := rotation_matrix_clockwise_2d_B beta in
      p1 -> p2 ->
      om = (mmul B on).
  Proof.
    destruct om.
    destruct mat_data; simpl in *; try easy.
    destruct mat_data; simpl in *; try easy.
    inversion mat_height. apply length_zero_iff_nil in H0; subst.
    destruct mat_width. destruct a.
    destruct l; simpl in *; try easy.
    destruct l0; simpl in *; try easy.
    inversion e. inversion e0.
    apply length_zero_iff_nil in H0,H1. subst.
    intros.
    apply meq_iff. simpl in *.
    unfold v2_len in *. unfold v2_to_t2 in *. simpl in *.
    rewrite cos_plus, sin_plus.
    rewrite Rmult_plus_distr_l, Rmult_minus_distr_l.
    repeat rewrite <- Rmult_assoc.
    rewrite <- H. rewrite <- H0.
    repeat apply list_equality; auto;
    unfold RingTypeR.A, add, mul, ListAux.ldot; simpl; trigo_simp.
    match goal with
    | |- a = ?b => replace b with (a * (cos beta * cos beta + sin beta * sin beta))
    end.
    trigo_simp. ring.
    match goal with
    | |- a0 = ?b => replace b with (a0 * (cos beta * cos beta + sin beta * sin beta))
    end.
    trigo_simp. ring.
  Qed.
  
  
