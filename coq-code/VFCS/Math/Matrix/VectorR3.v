(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 3-dimensional vector on R.
  author    : ZhengPu Shi
  date      : 2023.01

  reference :
  1. https://wuli.wiki/online/Cross.html
  2. https://en.wikipedia.org/wiki/Cross_product

  remark    :
  1. 外积的几何学(三角学)意义  ||P×Q|| = ||P|| * ||Q|| * sin α
  2. 外积若不为零，则其与这两个向量都垂直。有两个向量，方向相反。
     根据所选左/右手系来确定方向。
  3. 3D坐标系中的x,y,z轴正方向用 i,j,k 表示，并按 i,j,k 顺序组成一个循环，则：
  (1) 相邻两个向量按相同次序的外积为第三个向量，即 i×j=k, j×k=i, k×i=j。
  (2) 相邻两个向量按相反次序的外积为第三个向量的取反，即 j×i=-k, etc.
 *)

Require Import VectorR.
Open Scope vec_scope.


(* ======================================================================= *)
(** * 3D vector theory *)

(** ** Equality *)
Section v3eq.

  (** The equality of 3D vector equal to the equality of its components *)
  Lemma v3eq_iff : forall (u v : vec 3),
      u = v <-> (u.1 = v.1 /\ u.2 = v.2 /\ u.3 = v.3).
  Proof.
    intros. split; intros; subst; auto.
    unfold nat2finS in H; simpl in H. destruct H as [H1 [H2 H3]].
    apply veq_iff_vnth_nat; intros. unfold nat2fin.
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H1).
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H2).
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H3).
    lia.
  Qed.

  (** The inequality of 3D vector equal to the inequality of its components *)
  Lemma v3neq_iff : forall (u v : vec 3),
      u <> v <-> (u.1 <> v.1 \/ u.2 <> v.2 \/ u.3 <> v.3).
  Proof. intros. unfold not. rewrite v3eq_iff. lra. Qed.

End v3eq.


Section v3dot.
  
  (** vdot in 3D has given form *)
  Lemma v3dot_eq : forall u v : vec 3, <u, v> = (u.1 * v.1 + u.2 * v.2 + u.3 * v.3)%R.
  Proof. intros. cbv. ring. Qed.

End v3dot.


Section v3unit.
  (** A unit vector satisfy these algebraic equations *)

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
End v3unit.


Section v3norm.
  
  (** vnorm v = (v.1 / |v|, v.2 / |v|, v.3 / |v|) *)
  Lemma v3norm_eq : forall (v : vec 3),
      let v' := vnorm v in
      v <> vzero ->
      (v'.1 = v.1 / ||v||) /\ (v'.2 = v.2 / ||v||) /\ (v'.3 = v.3 / ||v||).
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
  
End v3norm.


(** ** The cross product (vector product) of two 3-dim vectors *)
Section v3cross.
  Definition v3cross (u v : vec 3) : vec 3 :=
    mkvec3
      (u.2 * v.3 - u.3 * v.2)%R
      (u.3 * v.1 - u.1 * v.3)%R
      (u.1 * v.2 - u.2 * v.1)%R.

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

  Infix "\x" := v3cross : vec_scope.

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

  (** (u × v) × u = u × (v × u) *)
  Lemma v3cross_v3cross_form1 : forall u v : vec 3, (u \x v) \x u = u \x (v \x u).
  Proof. intros. apply v3eq_iff; cbv; ra. Qed.

  (** (u × v) × u = <u,u> \.* v - <u,v> \.* u *)
  Lemma v3cross_v3cross_form2 : forall u v : vec 3,
      (u \x v) \x u = <u,u> \.* v - <u,v> \.* u.
  Proof. intros. apply v3eq_iff; cbv; ra. Qed.

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
  
  (** || u × v || = ||u|| * ||v|| * |sin (cvangle u v)| *)
  Lemma vlen_v3cross : forall u v : vec 3,
      u <> vzero -> v <> vzero -> || u \x v || = ||u|| * ||v|| * sin (u /_ v).
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

  (** u × v = (sin (u ∠ v) * ||u|| * ||v||) \.* vnorm (u × v) *)
  Lemma v3cross_eq_vcmul : forall (u v : vec 3),
      u <> vzero -> v <> vzero ->
      u /_ v <> 0 -> u /_ v <> PI ->
      u \x v = ((sin (u /_ v) * ||u|| * ||v||)%R \.* vnorm (u \x v))%CV.
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

End v3cross.

Infix "\x" := v3cross : vec_scope.


(** ** Standard basis vector in Euclidean space of 3-dimensions *)
Section basis.
  Open Scope vec_scope.

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
  
  (** 标准基向量的夹角 *)
  Lemma vangle_i_j : v3i /_ v3j = PI/2.
  Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

  Lemma vangle_j_k : v3j /_ v3k = PI/2.
  Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

  Lemma vangle_k_i : v3k /_ v3i = PI/2.
  Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

End basis.


(** Projection component of vector in 3D : 投影分量 *)
Section v3proj.
(*
  (** The matrix form of cvproj in 3-dim *)
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
End v3proj.


(** Perpendicular component of vector in 3D : 垂直分量 *)
Section v3perp.

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
  
End v3perp.


(** Parallel vectors in 3D *)
Section v3para.

  (** Two vectors in 3D are parallel, can be determined by cross-product.
      That is: u //v <-> u × v = 0 *)
  Definition v3para (u v : vec 3) : Prop := u \x v = vzero.
  
  Lemma v3para_spec : forall (u v : vec 3),
      u <> vzero -> v <> vzero -> (u // v <-> v3para u v).
  Proof.
    intros. unfold v3para. rewrite v3cross_eq0_iff_angle_0_pi; auto.
    apply vpara_iff_vangle_0_or_PI; auto.
  Qed.
  
End v3para.


(** Direction cosine *)
Section direction_cosine.

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
End direction_cosine.


(** Skew-symmetric matrix of 3-dimensions *)
(*
Section skew.

  (** Given matrix is skew-symmetric matrices *)
  Definition v3skewP (m : mat 3 3) : Prop := (- m)%M = m\T.

  Lemma v3skewP_spec : forall m : mat 3 3,
      v3skewP m ->
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
  Definition v3skew (v : vec 3) : mat 3 3 :=
    l2m [[0; -v.3; v.2];
         [v.3; 0; -v.1];
         [-v.2; v.1; 0]]%R.
  
  Notation "`| v |ₓ" := (v3skew v).

  (** Convert a skew-symmetric matrix to its corresponding vector *)
  Definition v3vex (m : mat 3 3) : vec 3 := l2cv [m.32; m.13; m.21].

  Lemma v3skew_skew2v_id : forall (m : mat 3 3), v3skewP m -> v3skew (v3vex m) = m.
  Proof.
    intros [m]. simpl. intros. apply v3skewP_spec in H.
    do 5 destruct H as [? H]. apply v3eq_iff; cbv; ra. autounfold with T. ra.
  Qed.

  Lemma v3skew2v_skew_id : forall (v : vec 3), v3vex (v3skew v) = v.
  Proof.
    intros. vec2fun. cbv. intros.
    assert (j = 0%nat) by lia. rewrite H1.
    destruct i; try easy.
    destruct i; try easy.
    destruct i; try easy. lia.
  Qed.
  
  Lemma v3cross_eq_skew_mul : forall (u v : vec 3), u \x v = `|u|ₓ * v.
  Proof. apply v3eq_iff; cbv; ra. Qed.

  (* (** 习题8.2第12题, page 23, 高等数学，第七版 *) *)
  (* (** 利用向量来证明不等式，并指出等号成立的条件 *) *)
  (* Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R, *)
  (*     sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= |a1*b1 + a2*b2 + a3*b3|. *)
  (* Proof. *)
  (*   intros. *)
  (*   pose (a := t2cv_3 (a1,a2,a3)). *)
  (*   pose (b := t2cv_3 (b1,b2,b3)). *)
  (*   pose (alen := vlen a). *)
  (*   pose (blen := vlen b). *)
  (*   replace (sqrt _) with alen; [| unfold alen; cbv; f_equal; ring]. *)
  (*   replace (sqrt _) with blen; [| unfold blen; cbv; f_equal; ring]. *)
  (*   replace (Rabs _) with (|<a,b>|); [| cbv; autorewrite with R; auto]. *)
  (* Abort. *)

  (** Example 4, page 19, 高等数学，第七版 *)
  Goal let a := t2cv_3 (2,1,-1) in
       let b := t2cv_3 (1,-1,2) in
       a \x b = t2cv_3 (1,-5,-3).
  Proof. apply v3eq_iff; cbv; ra. Qed.

  (** Example 5, page 19, 高等数学，第七版 *)
  (** 根据三点坐标求三角形面积 *)
  Definition v3_area_of_triangle (A B C : vec 3) :=
    let AB := B - A in
    let AC := C - A in
    ((1/2) * ||AB \x AC||)%R.

  (** Example 6, page 20, 高等数学，第七版 *)
  (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*)
  Definition v3_rotation_model (ω r v : vec 3) := v = ω \x r.

End skew.
Notation "`| v |ₓ" := (v3skew v).
*)


(** The triple scalar product (or called Mixed products of vectors) *)
Section v3mixed.
  
  (** 几何意义：绝对值表示以向量a,b,c为棱的平行六面体的体积，另外若a,b,c组成右手系，
      则混合积的符号为正；若组成左手系，则符号为负。*)
  Definition v3mixed (u v w : vec 3) := <u \x v, w>.

  (*
  (** The mixed product is equal to the determinant *)
  Lemma v3mixed_eq_det : forall u v w : vec 3,
      v3mixed a b c = mdet3 (mconsc a (mconsc b c)).
  Proof. intros [a] [b] [c]. cbv. ring. Qed.
   *)

  (** 若混合积≠0，则三向量可构成平行六面体，即三向量不共面，反之也成立。
    所以：三向量共面的充要条件是混合积为零。*)
  Definition v3coplanar (u v w : vec 3) := v3mixed u v w = 0.

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
    ((1/6) * (v3mixed AB AC AD))%R.

  (** u,v,w ∈ one-plane, u ∠ w = (u ∠ v) + (v ∠ w) *)
  Lemma v3angle_add : forall (u v w : vec 3),
      u /_ v < PI ->
      v /_ w < PI ->
      v3coplanar u v w ->
      u /_ w = ((u /_ v) + (v /_ w))%R.
  Proof.
    (* 由于 u /_ v 和 v /_ u 并没有区分，所以该性质不成立。*)
    (* intros. unfold cvangle. unfold vnorm. unfold vlen. *)
    (* unfold cvcmul. unfold cvdot. unfold Vector.cvdot. *)
    (* vec2fun. unfold Tmul,Tadd,T0,T. *)
    (* autorewrite with R. *)
    Abort.
End v3mixed.


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
      let a' : vec 3 := a_perp' + a_para in
      vunit n ->
      a' = rotaa θ n a.
  Proof.
    intros. unfold rotaa.
    assert (a_para = <a,n> \.* n) as H1.
    { unfold a_para. unfold vproj, Vector.vproj. unfold vunit, Vector.vunit in H.
      rewrite H. unfold vcmul. f_equal. unfold vdot. autounfold with A. field. }
    assert (a_perp = a - <a,n> \.* n) as H2.
    { unfold a_perp. rewrite <- H1. easy. }
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
        (cos θ) \.* a + (sin θ) \.* (n \x a)  + (<a,n> * (1 - cos θ))%R \.* n.
  Proof.
    intros. unfold rotaa. rewrite vcmul_vsub. unfold vsub. asemigroup.
    unfold Rminus. rewrite Rmult_plus_distr_l.
    rewrite identityRight at 1. rewrite vcmul_add.
    asemigroup. rewrite vcmul_assoc.
    rewrite <- vcmul_opp. f_equal. autounfold with A. ring.
  Qed.

  (** Matrix formula of roation with axis-angle *)
  (* https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula *)
(*  
  Definition aa2mat (θ : R) (n : vec 3) : smat 3 :=
    let N := v3skew n in
    (mat1 + (sin θ) \.* N + (1 - cos θ)%R \.* N * N)%M.

  Lemma aa2mat_spec : forall (θ : R) (n : vec 3) (a : vec 3),
      vunit n -> (aa2mat θ n) * a = rotaa θ n a.
  Proof.
    intros.
    (* unfold aa2mat. *)
    rewrite rotaa_form1.
    (* a * cosθ + (n × a) * sinθ + n \.* (<a,n> * (1-cosθ)) *)
    rewrite <- cvmulc_assoc.
    (* a * cosθ + (n × a) * sinθ + (k \.* <a,n>) \.* (1-cosθ) *)
    remember (v3skew n) as N.
    assert ((n \.* <n,a>) = a + N * (N * a)).
    {
      assert ((n \.* <n,a>) = a - cvperp a n).
      { unfold cvperp. unfold cvproj. rewrite H. rewrite cvdot_comm. apply v3eq_iff; cbv; ra. }
      rewrite H0. rewrite v3perp_spec; auto. unfold v3perp.
      rewrite v3cross_anticomm. rewrite (v3cross_anticomm a).
      rewrite v3cross_vopp_r.
      rewrite !v3cross_eq_skew_mul. rewrite <- HeqN.
      unfold cvsub. rewrite ?cvopp_vopp. easy. }
    rewrite (cvdot_comm a n). rewrite H0.
    (* a * cosθ + (n × a) * sinθ + (a + N * (N * a)) * (1 - cosθ) *)
    rewrite !cvmulc_eq_vcmul.
    rewrite !cvcmul_vadd_distr.
    rewrite v3cross_eq_skew_mul.
    rewrite !cvcmul_mmul_assoc_l. rewrite <- !mmul_assoc.
    move2h ((1 - cos θ)%R \.* a). rewrite <- !associative.
    assert ((1 - cos θ)%R \.* a + cos θ \.* a = a) by apply v3eq_iff; cbv; ra. rewrite H1.
    (* right side is ready *)
    unfold aa2mat.
    rewrite !mmul_madd_distr_r. rewrite <- HeqN. f_equiv. f_equiv. apply mmul_1_l.
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
    intros. apply v3eq_iff; cbv; ra;
      pose proof (v3unit_eq1 k H); autounfold with T in *;
      ring_simplify; autorewrite with R; rewrite H0; field.
  Qed.

  (** R(-θ) = R(θ)\T *)
  Lemma aa2mat_neg_eq_trans : forall (θ : R) (n : vec 3), aa2mat (-θ) n = (aa2mat θ n)\T.
    (* Proof. apply v3eq_iff; cbv; ra; autounfold with T; autorewrite with R; ring. Qed. *)
  Admitted. (* to speed up the compile process *)

  (** R(θ) * R(θ)\T = I *)
  Lemma aa2mat_aa2mat_neg_inv : forall (θ : R) (n : vec 3),
      vunit n -> aa2mat θ n * ((aa2mat θ n)\T) = mat1.
    (* Proof. *)
    (*   intros. *)
    (*   pose proof (v3unit_eq1 n H) as H1. *)
    (*   pose proof (v3unit_eq2 n H) as H2. *)
    (*   pose proof (v3unit_eq3 n H) as H3. *)
    (*   apply v3eq_iff; cbv; ra; autounfold with T in *; vec2fun; cbv; ring_simplify; autorewrite with R. *)
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
*)

End AxisAngle.

(** ** Rotation matrix in 3D *)
(*
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
  
  (** R3x,R3y,R3z are the special case of aa2mat. *)
  Theorem aa2mat_eq_Rx : forall θ : R, aa2mat θ v3i = R3x θ.
  Proof. apply v3eq_iff; cbv; ra. Qed.

  Theorem aa2mat_eq_Ry : forall θ : R, aa2mat θ v3j = R3y θ.
  Proof. apply v3eq_iff; cbv; ra. Qed.

  Theorem aa2mat_eq_Rz : forall θ : R, aa2mat θ v3k = R3z θ.
  Proof. apply v3eq_iff; cbv; ra. Qed.
  
  (** R3x,R3y,R3z are orthogonal matrix *)
  Lemma R3x_orth : forall (θ : R), morth (R3x θ).
  Proof. apply v3eq_iff; cbv; ra; autorewrite with R; easy. Qed.
  
  Lemma R3y_orth : forall (θ : R), morth (R3y θ).
  Proof. apply v3eq_iff; cbv; ra; autorewrite with R; easy. Qed.
  
  Lemma R3z_orth : forall (θ : R), morth (R3z θ).
  Proof. apply v3eq_iff; cbv; ra; autorewrite with R; easy. Qed.

  (** The determinant of R3x,R3y,R3z are 1 *)
  Lemma R3x_det1 : forall (θ : R), mdet (R3x θ) = 1.
  Proof. intros; cbv; autorewrite with R; easy. Qed.

  Lemma R3y_det1 : forall (θ : R), mdet (R3y θ) = 1.
  Proof. intros; cbv; autorewrite with R; easy. Qed.

  Lemma R3z_det1 : forall (θ : R), mdet (R3z θ) = 1.
  Proof. intros; cbv; autorewrite with R; easy. Qed.

  (** R3x,R3y,R3z are member of SO3 *)
  Definition R3x_SO3 (θ : R) : SO3.
    refine (Build_SOn _ (R3x θ) _). split. apply R3x_orth. apply R3x_det1.
  Defined.

  Definition R3y_SO3 (θ : R) : SO3.
    refine (Build_SOn _ (R3y θ) _). split. apply R3y_orth. apply R3y_det1.
  Defined.

  Definition R3z_SO3 (θ : R) : SO3.
    refine (Build_SOn _ (R3z θ) _). split. apply R3z_orth. apply R3z_det1.
  Defined.

  (** 以下示例说明了使用群 SOn 可以解决一批问题(SO2, SO3等），并且比暴力证明的速度快 *)
  
  (** R(θ)⁻¹ = R(θ)\T *)
  
  Lemma R3x_inv_eq_trans : forall θ : R, (R3x θ)⁻¹ = (R3x θ)\T.
  Proof.
    (* method 1 : prove by computing (too slow, 0.8s) *)
    (* apply v3eq_iff; cbv; ra; autounfold with T; autorewrite with R; try easy. *)
    (* method 2 : prove by reasoning *)
    intros; apply (SOn_imply_inv_eq_trans (R3x_SO3 θ)).
  Qed.

  Lemma R3y_inv_eq_trans : forall θ : R, (R3y θ)⁻¹ = (R3y θ)\T.
  Proof. intros; apply (SOn_imply_inv_eq_trans (R3y_SO3 θ)). Qed.

  Lemma R3z_inv_eq_trans : forall θ : R, (R3z θ)⁻¹ = (R3z θ)\T.
  Proof. intros; apply (SOn_imply_inv_eq_trans (R3z_SO3 θ)). Qed.
  
  (** R(-θ) = R(θ)\T *)
  Lemma R3x_neg_eq_trans : forall θ : R, R3x (-θ) = (R3x θ)\T.
  Proof. apply v3eq_iff; cbv; ra; autorewrite with R; try easy. Qed.
  
  Lemma R3y_neg_eq_trans : forall θ : R, R3y (-θ) = (R3y θ)\T.
  Proof. apply v3eq_iff; cbv; ra; autorewrite with R; try easy. Qed.
  
  Lemma R3z_neg_eq_trans : forall θ : R, R3z (-θ) = (R3z θ)\T.
  Proof. apply v3eq_iff; cbv; ra; autorewrite with R; try easy. Qed.

  (** R(-θ) * R(θ) = I *)
  Lemma R3x_neg_R3x_inv : forall θ : R, R3x (- θ) * R3x θ = mat1.
  Proof.
    (* apply v3eq_iff; cbv; ra; autounfold with T; autorewrite with R; auto; ring. *)
    intros; rewrite R3x_neg_eq_trans, <- R3x_inv_eq_trans, mmul_minv_l; easy.
  Qed.
  
  Lemma R3y_neg_R3y_inv : forall θ : R, R3y (- θ) * R3y θ = mat1.
  Proof. intros; rewrite R3y_neg_eq_trans, <- R3y_inv_eq_trans, mmul_minv_l; easy. Qed.
  
  Lemma R3z_neg_R3z_inv : forall θ : R, R3z (- θ) * R3z θ = mat1.
  Proof. intros; rewrite R3z_neg_eq_trans, <- R3z_inv_eq_trans, mmul_minv_l; easy. Qed.

  (** R(θ) * R(-θ) = I *)
  Lemma R3x_R3x_neg_inv : forall θ : R, R3x θ * R3x (- θ) = mat1.
  Proof. intros; rewrite R3x_neg_eq_trans, <- R3x_inv_eq_trans, mmul_minv_r; easy. Qed.
  
  Lemma R3y_R3y_neg_inv : forall θ : R, R3y θ * R3y (- θ) = mat1.
  Proof. intros; rewrite R3y_neg_eq_trans, <- R3y_inv_eq_trans, mmul_minv_r; easy. Qed.
  
  Lemma R3z_R3z_neg_inv : forall θ : R, R3z θ * R3z (- θ) = mat1.
  Proof. intros; rewrite R3z_neg_eq_trans, <- R3z_inv_eq_trans, mmul_minv_r; easy. Qed.

  (** v' = Rx(θ) * v *)
  Lemma R3x_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3i v = (R3x θ) * v.
  Proof. apply v3eq_iff; cbv; ra. Qed.
  
  Lemma R3y_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3j v = (R3y θ) * v.
  Proof. apply v3eq_iff; cbv; ra. Qed.
  
  Lemma R3z_spec1 : forall (v : vec 3) (θ : R), rotaa θ v3k v = (R3z θ) * v.
  Proof. apply v3eq_iff; cbv; ra. Qed.

  (** v = R(-θ) * v' *)
  Lemma R3x_spec2 : forall (v : vec 3) (θ : R), v = (R3x (-θ)) * (rotaa θ v3i v).
  Proof. intros. rewrite R3x_spec1,<- mmul_assoc,R3x_neg_R3x_inv,mmul_1_l; easy. Qed.
  
  Lemma R3y_spec2 : forall (v : vec 3) (θ : R), v = (R3y (-θ)) * (rotaa θ v3j v).
  Proof. intros. rewrite R3y_spec1,<- mmul_assoc,R3y_neg_R3y_inv,mmul_1_l; easy. Qed.
  
  Lemma R3z_spec2 : forall (v : vec 3) (θ : R), v = (R3z (-θ)) * (rotaa θ v3k v).
  Proof. intros. rewrite R3z_spec1,<- mmul_assoc,R3z_neg_R3z_inv,mmul_1_l; easy. Qed.

  (** v = R(θ)\T * v' *)
  Lemma R3x_spec3 : forall (v : vec 3) (θ : R), v = (R3x θ)\T * (rotaa θ v3i v).
  Proof. intros. rewrite <- R3x_neg_eq_trans. apply R3x_spec2. Qed.

  Lemma R3y_spec3 : forall (v : vec 3) (θ : R), v = (R3y θ)\T * (rotaa θ v3j v).
  Proof. intros. rewrite <- R3y_neg_eq_trans. apply R3y_spec2. Qed.

  Lemma R3z_spec3 : forall (v : vec 3) (θ : R), v = (R3z θ)\T * (rotaa θ v3k v).
  Proof. intros. rewrite <- R3z_neg_eq_trans. apply R3z_spec2. Qed.

  (** 预乘和后乘旋转矩阵的关系，即: v ~ v' -> R(θ) * v ~ v' * R(θ) *)
  Lemma R3x_spec4 : forall (u : vec 3) (θ : R),
      let u' : rvec 3 := u\T in  (* u和u'是列向量和行向量形式的同一个向量 *)
      let v : vec 3 := (R3x θ) * u in       (* 用列向量形式计算 *)
      let v' : rvec 3 := u' * ((R3x θ)\T) in (* 用行向量形式计算 *)
      let v'' : vec 3 := v'\T in           (* v' 的列向量形式 *)
      v = v''. (* 结果应该相同 *)
  Proof. apply v3eq_iff; cbv; ra. Qed.

End RotationMatrix3D.
*)
