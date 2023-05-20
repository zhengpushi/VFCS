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

Require Export VectorR.
Require Import VectorR2.


(* ======================================================================= *)
(** * 3D vector theory *)

(** ** General properties *)
Section general.

  (** The equality of 3D vector equal to the equality of its components *)
  Lemma cv3eq_iff : forall (v1 v2 : cvec 3),
      v1 == v2 <-> (v1.1 = v2.1 /\ v1.2 = v2.2 /\ v1.3 = v2.3).
  Proof. intros. split; intros. repeat (split; try apply H; auto). lma. Qed.

  (** The inequality of 3D vector equal to the inequality of its components *)
  Lemma cv3neq_iff : forall (v1 v2 : cvec 3),
      v1 != v2 <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2 \/ v1.3 <> v2.3).
  Proof. intros. unfold not. rewrite cv3eq_iff. lra. Qed.

End general.


(** ** Standard basis vector in Euclidean space of 3-dimensions *)
Section basis.
  
  (* Open Scope rvec_scope. *)
  
  (* Definition rv3i : rvec 3 := mk_rvec3 1 0 0. *)
  (* Definition rv3j : rvec 3 := mk_rvec3 0 1 0. *)
  (* Definition rv3k : rvec 3 := mk_rvec3 0 0 1. *)
  
  (* (** <v,i> = <i,v> = v.1, <v,j> = <j,v> = v.2, <v,k> = <k,v> = v.3 *) *)
  (* Lemma rvdot_v3i_l : forall v : rvec 3, <rv3i, v> = v.1. Proof. intros. cbv; ring. Qed. *)
  (* Lemma rvdot_v3j_l : forall v : rvec 3, <rv3j, v> = v.2. Proof. intros. cbv; ring. Qed. *)
  (* Lemma rvdot_v3k_l : forall v : rvec 3, <rv3k, v> = v.3. Proof. intros. cbv; ring. Qed. *)
  (* Lemma rvdot_v3i_r : forall v : rvec 3, <v, rv3i> = v.1. Proof. intros. cbv; ring. Qed. *)
  (* Lemma rvdot_v3j_r : forall v : rvec 3, <v, rv3j> = v.2. Proof. intros. cbv; ring. Qed. *)
  (* Lemma rvdot_v3k_r : forall v : rvec 3, <v, rv3k> = v.3. Proof. intros. cbv; ring. Qed. *)

  Open Scope cvec_scope.

  Definition cv3i : cvec 3 := mk_cvec3 1 0 0.
  Definition cv3j : cvec 3 := mk_cvec3 0 1 0.
  Definition cv3k : cvec 3 := mk_cvec3 0 0 1.

  (** 任意向量都能写成该向量的坐标在标准基向量下的线性组合 *)
  Lemma cv3_linear_composition : forall (v : cvec 3),
      v == v.x c* cv3i + v.y c* cv3j + v.z c* cv3k.
  Proof. lma. Qed.

  (** 标准基向量的长度为 1 *)
  Lemma cv3i_len1 : ||cv3i|| = 1. Proof. cbv. autorewrite with R; auto. Qed.
  Lemma cv3j_len1 : ||cv3j|| = 1. Proof. cbv. autorewrite with R; auto. Qed.
  Lemma cv3k_len1 : ||cv3k|| = 1. Proof. cbv. autorewrite with R; auto. Qed.

  (** 标准基向量都是单位向量 *)
  Lemma cv3i_vunit : cvunit cv3i. Proof. apply cvunit_spec. apply cv3i_len1. Qed.
  Lemma cv3j_vunit : cvunit cv3j. Proof. apply cvunit_spec. apply cv3j_len1. Qed.
  Lemma cv3k_vunit : cvunit cv3k. Proof. apply cvunit_spec. apply cv3k_len1. Qed.

  (** 标准基向量都是非零向量 *)
  Lemma cv3i_nonzero : cvnonzero cv3i.
  Proof. intro. apply cv3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.
  
  Lemma cv3j_nonzero : cvnonzero cv3j.
  Proof. intro. apply cv3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.
  
  Lemma cv3k_nonzero : cvnonzero cv3k.
  Proof. intro. apply cv3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.

  (** 标准基向量是规范化操作的不动点 *)
  Lemma cv3i_cvnormalize_fixpoint : cvnormalize cv3i == cv3i.
  Proof. apply cvnormalize_cvunit_fixpoint. apply cv3i_vunit. Qed.
  
  Lemma cv3j_cvnormalize_fixpoint : cvnormalize cv3j == cv3j.
  Proof. apply cvnormalize_cvunit_fixpoint. apply cv3j_vunit. Qed.
  
  Lemma cv3k_cvnormalize_fixpoint : cvnormalize cv3k == cv3k.
  Proof. apply cvnormalize_cvunit_fixpoint. apply cv3k_vunit. Qed.

  (** 标准基向量与任意向量v的点积等于v的各分量 *)
  Lemma cv3dot_i_l : forall v : cvec 3, <cv3i, v> = v.x. Proof. intros. cbv; ring. Qed.
  Lemma cv3dot_j_l : forall v : cvec 3, <cv3j, v> = v.y. Proof. intros. cbv; ring. Qed.
  Lemma cv3dot_k_l : forall v : cvec 3, <cv3k, v> = v.z. Proof. intros. cbv; ring. Qed.
  Lemma cv3dot_i_r : forall v : cvec 3, <v, cv3i> = v.x. Proof. intros. cbv; ring. Qed.
  Lemma cv3dot_j_r : forall v : cvec 3, <v, cv3j> = v.y. Proof. intros. cbv; ring. Qed.
  Lemma cv3dot_k_r : forall v : cvec 3, <v, cv3k> = v.z. Proof. intros. cbv; ring. Qed.

End basis.


(** Dot product (inner-product) in 3D *)
Section cv3dot.
  Definition cv3dot (a b : cvec 3) := (a.1*b.1 + a.2*b.2 + a.3*b.3)%R.

  Lemma cv3dot_spec : forall v1 v2 : cvec 3, cv3dot v1 v2 = <v1,v2>.
  Proof. intros. cbv. ring. Qed.
End cv3dot.


(** Unit vector in 3D *)
Section cvunit.

  (** A unit vector has a algebra equation relation *)
  Lemma cv3unit_eq1 : forall (n : cvec 3),
      cvunit n -> (n.x)² = (1 - (n.y)² - (n.z)²)%R.
  Proof. intros. cvec2fun. cbv in *. ring_simplify in H. ring_simplify. lra. Qed.

  Lemma cv3unit_eq2 : forall (n : cvec 3),
      cvunit n -> (n.y)² = (1 - (n.x)² - (n.z)²)%R.
  Proof. intros. cvec2fun. cbv in *. ring_simplify in H. ring_simplify. lra. Qed.

  Lemma cv3unit_eq3 : forall (n : cvec 3),
      cvunit n -> (n.z)² = (1 - (n.x)² - (n.y)²)%R.
  Proof. intros. cvec2fun. cbv in *. ring_simplify in H. ring_simplify. lra. Qed.

End cvunit.


(** Normalization in 3D *)
Section cv3normalize.
  
  (** normalize v = (v.0/|v|, v.1/|v|, v.2/|v|) *)
  Lemma cv3normalize_eq : forall {n} (v : cvec n),
      let v' := cvnormalize v in
      cvnonzero v ->
      (v'.1 = v.1 / ||v||) /\ (v'.2 = v.2 / ||v||) /\ (v'.3 = v.3 / ||v||).
  Proof.
    intros. unfold v', cvnormalize. cvec2fun.
    autounfold with A. repeat split; try field.
    all: apply cvlen_neq0_iff_neq0; auto.
  Qed.

  Lemma cv3normalize_sqr_eq1 : forall (v : cvec 3),
      let r := ||v|| in
      ((v.1 / r)² + (v.2 / r)² + (v.3 / r)² = 1)%R.
  Proof.
    intros. pose proof (cvnormalize_len1 v).
    unfold cvnormalize in H.
    rewrite <- H.
    unfold cvlen.
    unfold cvdot. cbn. autorewrite with R.
  Admitted. (* 可能太复杂了，下次重新证 *)
  
End cv3normalize.


(** Cross product (vector product) of two 3-dim vectors *)
Section cv3cross.
  (**
   1. 外积的几何学(三角学)意义  ||P×Q|| = ||P|| * ||Q|| * sin α
   2. 外积若不为零，则其与这两个向量都垂直。有两个向量，方向相反。
      根据所选左/右手系来确定方向。
   3. 3D坐标系中的x,y,z轴正方向用 i,j,k 表示，并按 i,j,k 顺序组成一个循环，则：
   (1) 相邻两个向量按相同次序的外积为第三个向量，即 i×j=k, j×k=i, k×i=j。
   (2) 相邻两个向量按相反次序的外积为第三个向量的取反，即 j×i=-k, etc.
   *)
  Definition cv3cross (a b : cvec 3) : cvec 3 :=
    l2cv [a.2 * b.3 - a.3 * b.2;
          a.3 * b.1 - a.1 * b.3;
          a.1 * b.2 - a.2 * b.1]%R.

  Infix "×" := cv3cross : cvec_scope.

  #[export] Instance cv3corss_mor : Proper (meq ==> meq ==> meq) cv3cross.
  Proof.
    simp_proper. intros. hnf in *. mat2fun. intros. rewrite !H,!H0; auto. easy.
  Qed.

  (** v × v = 0 *)
  Lemma cv3cross_self : forall v : cvec 3, v × v == cvec0.
  Proof. lma. Qed.

  (** v1 × v2 = - (v2 × v1) *)
  Lemma cv3cross_anticomm : forall v1 v2 : cvec 3, v1 × v2 == -(v2 × v1).
  Proof. lma. Qed.

  (** (v1 + v2) × v3 = (v1 × v3) + (v2 × v3) *)
  Lemma cv3cross_add_distr_l : forall v1 v2 v3 : cvec 3,
      (v1 + v2) × v3 == (v1 × v3) + (v2 × v3).
  Proof. lma. Qed.

  (** v1 × (v2 + v3) = (v1 × v2) + (v1 × v3) *)
  Lemma cv3cross_add_distr_r : forall v1 v2 v3 : cvec 3,
      v1 × (v2 + v3) == (v1 × v2) + (v1 × v3).
  Proof. lma. Qed.

  (** (- v1) × v2 = - (v1 × v2) *)
  Lemma cv3cross_vopp_l : forall v1 v2 : cvec 3, (-v1) × v2 == - (v1 × v2).
  Proof. lma. Qed.

  (** v1 × (- v2) = - (v1 × v2) *)
  Lemma cv3cross_vopp_r : forall v1 v2 : cvec 3, v1 × (-v2) == - (v1 × v2).
  Proof. lma. Qed.

  (** (a c* v1) × v2 = a c* (v1 × v2) *)
  Lemma cv3cross_cmul_assoc_l : forall (a : R) (v1 v2 : cvec 3),
      (a c* v1) × v2 == a c* (v1 × v2).
  Proof. lma. Qed.

  (** v1 × (a c* v2) = a c* (v1 × v2) *)
  Lemma cv3cross_cmul_assoc_r : forall (a : R) (v1 v2 : cvec 3),
      v1 × (a c* v2) == a c* (v1 × v2).
  Proof. lma. Qed.

  (** <v1 × v2, v3> = <v3 × v1, v2> *)
  Lemma cv3cross_dot_l : forall v1 v2 v3 : cvec 3, <v1 × v2, v3> = <v3 × v1, v2>.
  Proof. intros. cbv. field. Qed.

  (** <v1 × v2, v3> = <v2 × v3, v1> *)
  Lemma cv3cross_dot_r : forall v1 v2 v3 : cvec 3, <v1 × v2, v3> = <v2 × v3, v1>.
  Proof. intros. cbv. field. Qed.

  (** <v1 × v2, v1> = 0 *)
  Lemma cv3cross_dot_same_l : forall v1 v2 : cvec 3, <v1 × v2, v1> = 0.
  Proof. intros. cbv. field. Qed.

  (** <v1 × v2, v2> = 0 *)
  Lemma cv3cross_dot_same_r : forall v1 v2 : cvec 3, <v1 × v2, v2> = 0.
  Proof. intros. cbv. field. Qed.

  (** (v1 × v2) × v1 = v1 × (v2 × v1) *)
  Lemma cv3cross_cross_form1 : forall v1 v2 : cvec 3,
      (v1 × v2) × v1 == v1 × (v2 × v1).
  Proof. lma. Qed.

  (** (v1 × v2) × v1 = <v1,v1> c* v2 - <v1,v2> c* v1 *)
  Lemma cv3cross_cross_form2 : forall v1 v2 : cvec 3,
      (v1 × v2) × v1 == <v1,v1> c* v2 - <v1,v2> c* v1.
  Proof. lma. Qed.

  (** i×j=k, j×k=i, k×i=j *)
  Lemma cv3cross_ij : cv3i × cv3j == cv3k. Proof. lma. Qed.
  Lemma cv3cross_jk : cv3j × cv3k == cv3i. Proof. lma. Qed.
  Lemma cv3cross_ki : cv3k × cv3i == cv3j. Proof. lma. Qed.

  (** j×i=-k, k×j=-i, i×k=-j *)
  Lemma cv3cross_ji : cv3j × cv3i == -cv3k. Proof. lma. Qed.
  Lemma cv3cross_kj : cv3k × cv3j == -cv3i. Proof. lma. Qed.
  Lemma cv3cross_ik : cv3i × cv3k == -cv3j. Proof. lma. Qed.


  (** The relation between cross and dot product *)
  (* https://en.wikipedia.org/wiki/Cross_product *)
  Local Open Scope fun_scope.

  (** || v1 × v2 ||² = ||v1||² * ||v2||² - <v1,v2>² *)
  Lemma cvlen_cv3cross_cv3dot : forall v1 v2 : cvec 3,
      || v1 × v2 ||² = ((||v1||² * ||v2||²) - (<v1,v2>)²)%R.
  Proof.
    intros. cvec2fun. cbv. autorewrite with R.
    remember (v1.11) as a1; remember (v1.21) as a2; remember (v1.31) as a3.
    remember (v2.11) as b1; remember (v2.21) as b2; remember (v2.31) as b3.
    rewrite !Rsqr_sqrt; ra.
  Qed.
  
  (** || v1 × v2 || = ||v1|| * ||v2|| * |sin (cvangle v1 v2)| *)
  Lemma cvlen_cv3cross : forall v1 v2 : cvec 3,
      || v1 × v2 || = (||v1|| * ||v2|| * sin (cvangle v1 v2))%R.
  Proof.
    intros. pose proof (cvlen_cv3cross_cv3dot v1 v2).
    rewrite cvdot_eq_cos_angle in H.  rewrite !Rsqr_mult in H. rewrite cos2 in H.
    apply Rsqr_inj; ra. apply cvlen_ge0.
    apply Rmult_le_pos. apply cvlen_ge0.
    apply Rmult_le_pos. apply cvlen_ge0. apply sin_cvangle_ge0.
  Qed.

End cv3cross.
Infix "×" := cv3cross : cvec_scope.


(** Projection component of vector in 3D : 投影分量 *)
Section cv3proj.

  (** The matrix form of cvproj in 3-dim *)
  Definition cv3proj (a b : cvec 3) : cvec 3 :=
    let x := b.1 in
    let y := b.2 in
    let z := b.3 in
    let M : mat 3 3 :=
      l2m [[x * x; x * y; x * z];
           [x * y; y * y; y * z];
           [x * z; y * z; z * z]]%R in
    (1/<b,b>) c* (M * a).

  Lemma cv3proj_spec : forall a b : cvec 3, cv3proj a b == cvproj a b.
  Proof. lma. Qed.

End cv3proj.


(** Perpendicular component of vector in 3D : 垂直分量 *)
Section cv3perp.
  Open Scope fun_scope.

  (** The perpendicular vector can be get from cross product.
    ref: https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula.
    利用两次叉乘得到垂直分量的表示。此式在几何上容易理解，但代数上不是很显然。*)
  Definition cv3perp (a b : cvec 3) : cvec 3 := - ((a × b) × b).

  Lemma cv3perp_spec : forall (a b : cvec 3), cvunit b -> cvperp a b == cv3perp a b.
  Proof.
    intros. unfold cvperp,cvproj,cv3perp. rewrite H. autorewrite with R.
    (* Why it is a correct algebra equation? 
       I'm confused, and it's just a brute proof. *)
    cvec2fun.
    assert (b.11 ^ 2 = R1 - b.21 ^ 2 - b.31 ^ 2)%R as H1.
    { cbv in H. rewrite <- H. field. }
    lma; cbv; ring_simplify; ring_simplify in H1; rewrite H1; field.
  Qed.
  
End cv3perp.


(** Parallel vectors in 3D *)
Section cv3parallel.
  Local Open Scope fun_scope.

  (** Two vectors in 3D are parallel, can be determined by cross-product.
      That is: v1 ∥ v2 <-> v1 × v2 = 0 *)
  Definition cv3parallel (v1 v2 : cvec 3) : Prop := cvzero (v1 × v2).
  
  Lemma cv3parallel_spec : forall (v1 v2 : cvec 3), v1 ∥ v2 <-> cv3parallel v1 v2.
  Proof.
    intros. cvec2fun. unfold cvparallel,cv3parallel. split; intros.
    - destruct H as [k [H1]].
      cbv. intros. rewrite <- !H; auto; simpl.
      repeat (destruct i; cbv; try ring).
    - cbv in *.
  Abort. (* 叉乘为零，则{1:两行线性相关，对应系数成比例; 2.存在零向量}。*)
End cv3parallel.


(** Direction cosine *)
Section direction_cosine.

  (** Direction cosine of a vector relative to standard basis.
      That is : (cos α, cos β, cos γ) *)
  Definition cv3dc (v : cvec 3) : cvec 3 :=
    let r := ||v|| in l2cv [v.1/r; v.2/r; v.3/r].

  (** The original (lower level) definition as its spec. *)
  Lemma cv3dc_spec : forall (v : cvec 3),
      let v' := cv3dc v in
      let r := ||v|| in 
      (v'.1 = <v,cv3i> / r) /\ v'.2 = (<v,cv3j> / r) /\ v'.3 = (<v,cv3k> / r).
  Proof. intros. rewrite cv3dot_i_r, cv3dot_j_r, cv3dot_k_r; auto. Qed.

  (** dc of a nonzero vector is a unit vector *)
  Lemma cv3dc_unit : forall (v : cvec 3), cvnonzero v -> cvunit (cv3dc v).
  Proof.
    intros. unfold cvunit. cbn. autorewrite with R.
    apply cv3normalize_sqr_eq1.
  Qed.
End direction_cosine.


(** Skew-symmetric matrix of 3-dimensions *)
Section skew.
  
  (** Given matrix is skew-symmetric matrices *)
  Definition cv3skewP (m : mat 3 3) : Prop := (- m)%M == m\T.

  Lemma cv3skewP_spec : forall m : mat 3 3,
      cv3skewP m ->
      (m.11 = 0) /\ (m.22 = 0) /\ (m.33 = 0) /\
        (m.12 = -m.21 /\ m.13 = -m.31 /\ m.23 = -m.32)%R.
  Proof.
    intros. destruct m as [m]; simpl in *. cbv in H. split_intro.
    - epose proof (H 0 0 _ _)%nat. ra.
    - epose proof (H 1 1 _ _)%nat. ra.
    - epose proof (H 2 2 _ _)%nat. ra.
    - epose proof (H 0 1 _ _)%nat. ra.
    - epose proof (H 0 2 _ _)%nat. ra.
    - epose proof (H 1 2 _ _)%nat. ra.
      Unshelve. all: ra.
  Qed.

  (** Convert a vector to its corresponding skew-symmetric matrix *)
  Definition cv3skew (v : cvec 3) : mat 3 3 :=
    l2m [[0; -v.3; v.2];
         [v.3; 0; -v.1];
         [-v.2; v.1; 0]]%R.
  
  Notation "`| v |ₓ" := (cv3skew v).

  (** Convert a skew-symmetric matrix to its corresponding vector *)
  Definition cv3vex (m : mat 3 3) : cvec 3 := l2cv [m.32; m.13; m.21].

  Lemma cv3skew_skew2v_id : forall (m : mat 3 3), cv3skewP m -> cv3skew (cv3vex m) == m.
  Proof.
    intros [m]. simpl. intros. apply cv3skewP_spec in H.
    do 5 destruct H as [? H]. lma. autounfold with A. ra.
  Qed.

  Lemma cv3skew2v_skew_id : forall (v : cvec 3), cv3vex (cv3skew v) == v.
  Proof.
    intros. cvec2fun. cbv. intros.
    assert (j = 0%nat) by lia. rewrite H1.
    destruct i; try easy.
    destruct i; try easy.
    destruct i; try easy. lia.
  Qed.
  
  Lemma cv3cross_eq_skew_mul : forall (v1 v2 : cvec 3), v1 × v2 == `|v1|ₓ * v2.
  Proof. lma. Qed.

  (* (** 习题8.2第12题, page 23, 高等数学，第七版 *) *)
  (* (** 利用向量来证明不等式，并指出等号成立的条件 *) *)
  (* Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R, *)
  (*     sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= |a1*b1 + a2*b2 + a3*b3|. *)
  (* Proof. *)
  (*   intros. *)
  (*   pose (a := t2cv_3 (a1,a2,a3)). *)
  (*   pose (b := t2cv_3 (b1,b2,b3)). *)
  (*   pose (alen := cvlen a). *)
  (*   pose (blen := cvlen b). *)
  (*   replace (sqrt _) with alen; [| unfold alen; cbv; f_equal; ring]. *)
  (*   replace (sqrt _) with blen; [| unfold blen; cbv; f_equal; ring]. *)
  (*   replace (Rabs _) with (|<a,b>|); [| cbv; autorewrite with R; auto]. *)
  (* Abort. *)

  (** Example 4, page 19, 高等数学，第七版 *)
  Goal let a := t2cv_3 (2,1,-1) in
       let b := t2cv_3 (1,-1,2) in
       a × b == t2cv_3 (1,-5,-3).
  Proof. lma. Qed.

  (** Example 5, page 19, 高等数学，第七版 *)
  (** 根据三点坐标求三角形面积 *)
  Definition cv3_area_of_triangle (A B C : cvec 3) :=
    let AB := B - A in
    let AC := C - A in
    ((1/2) * ||AB × AC||)%R.

  (** Example 6, page 20, 高等数学，第七版 *)
  (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*)
  Definition cv3_rotation_model (ω r v : cvec 3) := v = ω × r.

End skew.
Notation "`| v |ₓ" := (cv3skew v).


(** The triple scalar product (or called Mixed products of vectors) *)
Section cv3mixed.
  
  (** 几何意义：绝对值表示以向量a,b,c为棱的平行六面体的体积，另外若a,b,c组成右手系，
      则混合积的符号为正；若组成左手系，则符号为负。*)
  Definition cv3mixed (a b c : cvec 3) := <a × b, c>.

  (** The mixed product is equal to the determinant *)
  Lemma cv3mixed_eq_det : forall a b c : cvec 3,
      cv3mixed a b c = mdet3 (mconsc a (mconsc b c)).
  Proof. intros [a] [b] [c]. cbv. ring. Qed.

  (** 若混合积≠0，则三向量可构成平行六面体，即三向量不共面，反之也成立。
    所以：三向量共面的充要条件是混合积为零。*)
  Definition cv3coplanar (a b c : cvec 3) := cv3mixed a b c = 0.

  (** (v1,v2)的法向量和(v2,v3)的法向量相同，则v1,v2,v3共面 *)
  Lemma cv3cross_same_cv3coplanar : forall v1 v2 v3 : cvec 3,
      v1 × v2 == v2 × v3 -> cv3coplanar v1 v2 v3.
  Proof.
    intros. unfold cv3coplanar, cv3mixed. rewrite H. apply cv3cross_dot_same_r.
  Qed.

  (** Example 7, page 22, 高等数学，第七版 *)
  (** 根据四顶点的坐标，求四面体的体积：四面体ABCD的体积等于AB,AC,AD为棱的平行六面体
    的体积的六分之一 *)
  Definition cv3_volume_of_tetrahedron (A B C D : cvec 3) :=
    let AB := B - A in
    let AC := C - A in
    let AD := D - A in
    ((1/6) * (cv3mixed AB AC AD))%R.
  
End cv3mixed.


(** Axis-angle representation *)
Section AxisAngle.

  (** 推导绕任意轴 k̂ 旋转 θ 角度的矩阵 R(n̂,θ)，使得 v' = R(n̂,θ) * v *)

  (** Rotate a vector v in R^3 by an axis described with a unit vector n and 
        an angle θ according to right handle rule, we got the rotated vector as
        follows. This formula is known as Rodrigues formula. *)
  Definition rotAxisAngle (θ : R) (n : cvec 3) (v : cvec 3) : cvec 3 :=
    (cos θ) c* (v - <v,n> c* n) + (sin θ) c* (n×v) + <v,n> c* n.

  (** Proof its correctness *)
  Theorem rotAxisAngle_spec : forall (θ : R) (n : cvec 3) (v : cvec 3),
      let v_para : cvec 3 := cvproj v n in
      let v_perp : cvec 3 := cvperp v n in
      let w : cvec 3 := n × v_perp in
      let v_perp' : cvec 3 := (cos θ) c* v_perp + (sin θ) c* w in
      let v' : cvec 3 := v_perp' + v_para in
      cvunit n ->
      v' == rotAxisAngle θ n v.
  Proof.
    intros.
    unfold rotAxisAngle.
    assert (v_para == <v,n> c* n) as H1.
    { unfold v_para, cvproj. rewrite H. f_equiv. autounfold with A. field. }
    assert (v_perp == v - <v,n> c* n) as H2.
    { unfold v_perp. rewrite <- H1. easy. }
    assert (w == n × v) as H3.
    { unfold w. rewrite H2.
      (* lma. (* auto solvable. But the detail also be shown below. *) *)
      unfold cvsub, Vector.cvsub. rewrite cv3cross_add_distr_r.
      unfold cvcmul. rewrite cvopp_vcmul. rewrite cv3cross_cmul_assoc_r.
      rewrite cv3cross_self. rewrite cvcmul_0_r. rewrite cvadd_0_r. easy. }
    unfold v'. unfold v_perp'. rewrite H1. rewrite H2. rewrite H3. easy.
  Qed.

  (** Another form of the formula *)
  Lemma rotAxisAngle_form1 : forall (θ : R) (n : cvec 3) (v : cvec 3),
      rotAxisAngle θ n v ==
        v *c (cos θ) + (n × v) *c (sin θ) + n *c (<v,n> * (1 - cos θ))%R.
  Proof.
    intros. unfold rotAxisAngle.
    rewrite !cvmulc_eq_vcmul. rewrite cvcmul_vsub. rewrite cvsub_rw.
    rewrite !cvadd_assoc. f_equiv.
    rewrite <- cvadd_assoc. rewrite cvadd_perm. rewrite cvadd_comm. f_equiv.
    unfold Rminus. rewrite Rmult_plus_distr_l. autorewrite with R.
    rewrite cvcmul_add_distr. rewrite cvadd_comm. f_equiv.
    rewrite cvopp_vcmul. rewrite cvcmul_assoc. f_equiv. autounfold with A. ring.
  Qed.

  (** Matrix formula of roation with axis-angle *)
  (* https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula *)
  Definition rotAxisAngleMat (θ : R) (n : cvec 3) : smat 3 :=
    let N := cv3skew n in
    (mat1 + (sin θ) c* N + (1 - cos θ)%R c* N * N)%M.

  Lemma rotAxisAngleMat_spec : forall (θ : R) (n : cvec 3) (v : cvec 3),
      cvunit n -> (rotAxisAngleMat θ n) * v == rotAxisAngle θ n v.
  Proof.
    intros.
    (* unfold rotAxisAngleMat. *)
    rewrite rotAxisAngle_form1.
    (* v * cosθ + (n × v) * sinθ + n *c (<v,n> * (1-cosθ)) *)
    rewrite <- cvmulc_assoc.
    (* v * cosθ + (n × v) * sinθ + (k *c <v,n>) *c (1-cosθ) *)
    remember (cv3skew n) as N.
    assert ((n *c <n,v>) == v + N * (N * v)).
    {
      assert ((n *c <n,v>) == v - cvperp v n).
      { unfold cvperp. unfold cvproj. rewrite H. rewrite cvdot_comm. lma. }
      rewrite H0. rewrite cv3perp_spec; auto. unfold cv3perp.
      rewrite cv3cross_anticomm. rewrite (cv3cross_anticomm v).
      rewrite cv3cross_vopp_r.
      rewrite !cv3cross_eq_skew_mul. rewrite <- HeqN.
      unfold cvsub. rewrite ?cvopp_vopp. easy. }
    rewrite (cvdot_comm v n). rewrite H0.
    (* v * cosθ + (n × v) * sinθ + (v + N * (N * v)) * (1 - cosθ) *)
    rewrite !cvmulc_eq_vcmul.
    rewrite !cvcmul_vadd_distr.
    rewrite cv3cross_eq_skew_mul.
    rewrite !cvcmul_mmul_assoc_l. rewrite <- !mmul_assoc.
    move2h ((1 - cos θ)%R c* v). rewrite <- !associative.
    assert ((1 - cos θ)%R c* v + cos θ c* v == v) by lma. rewrite H1.
    (* right side is ready *)
    unfold rotAxisAngleMat.
    rewrite !mmul_madd_distr_r. rewrite <- HeqN. f_equiv. f_equiv. apply mmul_1_l.
  Qed.

  (** Rodrigues formula. *)
  Section Rodrigues.

    (** The Matrix for rotate by any axis is known as Rodrigues formula. *)
    Definition RrodM := rotAxisAngleMat.
    
    (** The direct form of Rodrigues formula. *)
    Definition Rrod (θ : R) (k : cvec 3) : mat 3 3 :=
      let x := k.x in
      let y := k.y in
      let z := k.z in
      let C := cos θ in
      let S := sin θ in
      l2m
        [[C + x * x * (1 - C); x * y * (1 - C) - z * S; x * z * (1 - C) + y * S];
         [y * x * (1 - C) + z * S; C + y * y * (1 - C); y * z * (1 - C) - x * S];
         [z * x * (1 - C) - y * S; z * y * (1 - C) + x * S; C + z * z * (1 - C)]]%R.

    Theorem Rrod_eq_RrodM : forall (θ : R) (k : cvec 3),
        cvunit k -> Rrod θ k == RrodM θ k.
    Proof.
      intros. lma;
        pose proof (cv3unit_eq1 k H); autounfold with A in *;
        ring_simplify; autorewrite with R; rewrite H0; field.
    Qed.

    (** R(-θ) = R(θ)\T *)
    Lemma Rrod_neg_eq_trans : forall (θ : R) (n : cvec 3), Rrod (-θ) n == (Rrod θ n)\T.
      (* Proof. lma; autounfold with A; autorewrite with R; ring. Qed. *)
    Admitted. (* to speed up the compile process *)

    (** R(θ) * R(θ)\T = I *)
    Lemma Rrod_Rrod_neg_inv : forall (θ : R) (n : cvec 3),
        cvunit n -> Rrod θ n * ((Rrod θ n)\T) == mat1.
    (* Proof. *)
    (*   intros. *)
    (*   pose proof (cv3unit_eq1 n H) as H1. *)
    (*   pose proof (cv3unit_eq2 n H) as H2. *)
    (*   pose proof (cv3unit_eq3 n H) as H3. *)
    (*   lma; autounfold with A in *; cvec2fun; cbv; ring_simplify; autorewrite with R. *)
    (*   - rewrite H1. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (*   - rewrite H3. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (*   - rewrite H2. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (*   - rewrite H3. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (*   - rewrite H2. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (*   - rewrite H1. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (*   - rewrite H2. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (*   - rewrite H1. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (*   - rewrite H3. rewrite RealFunction.cos2_eq. cbv; ring. *)
    (* Qed. *)
    Admitted. (* to speed up the compile process *)

  End Rodrigues.

End AxisAngle.


(** ** Rotation matrix in 3D *)
Section RotationMatrix3D.
  
  (** 主动旋转，逆时针正向(或顺时针负向)时，旋转矩阵 *)

  (** 注意列向量和行向量的不同用法：
     1. 给一个在该坐标系下的列向量 v1，正向旋转该向量 θ 角得到新的向量 v1'，按如下公式
          v1' = R(θ) * v1
          v1  = R(θ)\T * v1'
     2. 给一个在该坐标系下的行向量 v2，正向旋转该向量 θ 角得到新的向量 v2'，按如下公式
          v2' = v2 * (R(θ))\T
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
  
  (** R3x,R3y,R3z are the special case of Rrod. *)
  Theorem Rrod_eq_Rx : forall θ : R, Rrod θ cv3i == R3x θ.
  Proof. lma. Qed.

  Theorem Rrod_eq_Ry : forall θ : R, Rrod θ cv3j == R3y θ.
  Proof. lma. Qed.

  Theorem Rrod_eq_Rz : forall θ : R, Rrod θ cv3k == R3z θ.
  Proof. lma. Qed.
  
  (** R3x,R3y,R3z are orthogonal matrix *)
  Lemma R3x_orthogonal : forall (θ : R), morthogonal (R3x θ).
  Proof. lma; autorewrite with R; easy. Qed.
  
  Lemma R3y_orthogonal : forall (θ : R), morthogonal (R3y θ).
  Proof. lma; autorewrite with R; easy. Qed.
  
  Lemma R3z_orthogonal : forall (θ : R), morthogonal (R3z θ).
  Proof. lma; autorewrite with R; easy. Qed.

  (** The determinant of R3x,R3y,R3z are 1 *)
  Lemma R3x_det1 : forall (θ : R), mdet (R3x θ) = 1.
  Proof. intros; cbv; autorewrite with R; easy. Qed.

  Lemma R3y_det1 : forall (θ : R), mdet (R3y θ) = 1.
  Proof. intros; cbv; autorewrite with R; easy. Qed.

  Lemma R3z_det1 : forall (θ : R), mdet (R3z θ) = 1.
  Proof. intros; cbv; autorewrite with R; easy. Qed.

  (** R3x,R3y,R3z are member of SO3 *)
  Definition R3x_SO3 (θ : R) : SO3.
    refine (Build_SOn _ (R3x θ) _). split. apply R3x_orthogonal. apply R3x_det1.
  Defined.

  Definition R3y_SO3 (θ : R) : SO3.
    refine (Build_SOn _ (R3y θ) _). split. apply R3y_orthogonal. apply R3y_det1.
  Defined.

  Definition R3z_SO3 (θ : R) : SO3.
    refine (Build_SOn _ (R3z θ) _). split. apply R3z_orthogonal. apply R3z_det1.
  Defined.

  (** 以下示例说明了使用群 SOn 可以解决一批问题(SO2, SO3等），并且比暴力证明的速度快 *)
  
  (** R(θ)⁻¹ = R(θ)\T *)
  
  Lemma R3x_inv_eq_trans : forall θ : R, (R3x θ)⁻¹ == (R3x θ)\T.
  Proof.
    (* method 1 : prove by computing (too slow, 0.8s) *)
    (* lma; autounfold with A; autorewrite with R; try easy. *)
    (* method 2 : prove by reasoning *)
    intros; apply (SOn_imply_inv_eq_trans (R3x_SO3 θ)).
  Qed.

  Lemma R3y_inv_eq_trans : forall θ : R, (R3y θ)⁻¹ == (R3y θ)\T.
  Proof. intros; apply (SOn_imply_inv_eq_trans (R3y_SO3 θ)). Qed.

  Lemma R3z_inv_eq_trans : forall θ : R, (R3z θ)⁻¹ == (R3z θ)\T.
  Proof. intros; apply (SOn_imply_inv_eq_trans (R3z_SO3 θ)). Qed.
  
  (** R(-θ) = R(θ)\T *)
  Lemma R3x_neg_eq_trans : forall θ : R, R3x (-θ) == (R3x θ)\T.
  Proof. lma; autorewrite with R; try easy. Qed.
  
  Lemma R3y_neg_eq_trans : forall θ : R, R3y (-θ) == (R3y θ)\T.
  Proof. lma; autorewrite with R; try easy. Qed.
  
  Lemma R3z_neg_eq_trans : forall θ : R, R3z (-θ) == (R3z θ)\T.
  Proof. lma; autorewrite with R; try easy. Qed.

  (** R(-θ) * R(θ) = I *)
  Lemma R3x_neg_R3x_inv : forall θ : R, R3x (- θ) * R3x θ == mat1.
  Proof.
    (* lma; autounfold with A; autorewrite with R; auto; ring. *)
    intros; rewrite R3x_neg_eq_trans, <- R3x_inv_eq_trans, mmul_minv_l; easy.
  Qed.
  
  Lemma R3y_neg_R3y_inv : forall θ : R, R3y (- θ) * R3y θ == mat1.
  Proof. intros; rewrite R3y_neg_eq_trans, <- R3y_inv_eq_trans, mmul_minv_l; easy. Qed.
  
  Lemma R3z_neg_R3z_inv : forall θ : R, R3z (- θ) * R3z θ == mat1.
  Proof. intros; rewrite R3z_neg_eq_trans, <- R3z_inv_eq_trans, mmul_minv_l; easy. Qed.

  (** R(θ) * R(-θ) = I *)
  Lemma R3x_R3x_neg_inv : forall θ : R, R3x θ * R3x (- θ) == mat1.
  Proof. intros; rewrite R3x_neg_eq_trans, <- R3x_inv_eq_trans, mmul_minv_r; easy. Qed.
  
  Lemma R3y_R3y_neg_inv : forall θ : R, R3y θ * R3y (- θ) == mat1.
  Proof. intros; rewrite R3y_neg_eq_trans, <- R3y_inv_eq_trans, mmul_minv_r; easy. Qed.
  
  Lemma R3z_R3z_neg_inv : forall θ : R, R3z θ * R3z (- θ) == mat1.
  Proof. intros; rewrite R3z_neg_eq_trans, <- R3z_inv_eq_trans, mmul_minv_r; easy. Qed.

  (** v' = Rx(θ) * v *)
  Lemma R3x_spec1 : forall (v : cvec 3) (θ : R), rotAxisAngle θ cv3i v == (R3x θ) * v.
  Proof. lma. Qed.
  
  Lemma R3y_spec1 : forall (v : cvec 3) (θ : R), rotAxisAngle θ cv3j v == (R3y θ) * v.
  Proof. lma. Qed.
  
  Lemma R3z_spec1 : forall (v : cvec 3) (θ : R), rotAxisAngle θ cv3k v == (R3z θ) * v.
  Proof. lma. Qed.

  (** v = R(-θ) * v' *)
  Lemma R3x_spec2 : forall (v : cvec 3) (θ : R), v == (R3x (-θ)) * (rotAxisAngle θ cv3i v).
  Proof. intros. rewrite R3x_spec1,<- mmul_assoc,R3x_neg_R3x_inv,mmul_1_l; easy. Qed.
  
  Lemma R3y_spec2 : forall (v : cvec 3) (θ : R), v == (R3y (-θ)) * (rotAxisAngle θ cv3j v).
  Proof. intros. rewrite R3y_spec1,<- mmul_assoc,R3y_neg_R3y_inv,mmul_1_l; easy. Qed.
  
  Lemma R3z_spec2 : forall (v : cvec 3) (θ : R), v == (R3z (-θ)) * (rotAxisAngle θ cv3k v).
  Proof. intros. rewrite R3z_spec1,<- mmul_assoc,R3z_neg_R3z_inv,mmul_1_l; easy. Qed.

  (** v = R(θ)\T * v' *)
  Lemma R3x_spec3 : forall (v : cvec 3) (θ : R), v == (R3x θ)\T * (rotAxisAngle θ cv3i v).
  Proof. intros. rewrite <- R3x_neg_eq_trans. apply R3x_spec2. Qed.

  Lemma R3y_spec3 : forall (v : cvec 3) (θ : R), v == (R3y θ)\T * (rotAxisAngle θ cv3j v).
  Proof. intros. rewrite <- R3y_neg_eq_trans. apply R3y_spec2. Qed.

  Lemma R3z_spec3 : forall (v : cvec 3) (θ : R), v == (R3z θ)\T * (rotAxisAngle θ cv3k v).
  Proof. intros. rewrite <- R3z_neg_eq_trans. apply R3z_spec2. Qed.

  (** 预乘和后乘旋转矩阵的关系，即: v ~ v' -> R(θ) * v ~ v' * R(θ) *)
  Lemma R3x_spec4 : forall (v1 : cvec 3) (θ : R),
      let v1' : rvec 3 := v1\T in  (* v1和v1'是列向量和行向量形式的同一个向量 *)
      let v2 : cvec 3 := (R3x θ) * v1 in       (* 用列向量形式计算 *)
      let v2' : rvec 3 := v1' * ((R3x θ)\T) in (* 用行向量形式计算 *)
      let v2'' : cvec 3 := v2'\T in           (* v2' 的列向量形式 *)
      v2 == v2''. (* 结果应该相同 *)
  Proof. lma. Qed.

End RotationMatrix3D.

