(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 2-dimensional vector on R.
  author    : ZhengPu Shi
  date      : 2023.01

  reference :
  remark    :
 *)

Require Export VectorR.
Open Scope vec_scope.


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

(** The equality of 2D vector *)
Lemma v2eq_iff : forall u v : vec 2, u = v <-> u.x = v.x /\ u.y = v.y.
Proof.
  intros. split; intros; subst; auto.
  unfold nat2finS in H; simpl in H. destruct H as [Hx Hy].
  apply veq_iff_vnth_nat; intros. unfold nat2fin.
  destruct i; simpl; auto. apply (vnth_sameIdx_imply Hx).
  destruct i; simpl; auto. apply (vnth_sameIdx_imply Hy). lia.
Qed.

(** The length of 2D vector *)
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


(** ** The cross product of 2D vectors *)
Section v2cross.
  (* u × v) *)
  Definition v2cross (u v : vec 2) : R := u.x * v.y - u.y * v.x.
  Infix "\x" := v2cross : vec_scope.

  (* u × v = - (v × u) *)
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
      u <> vzero -> v <> vzero -> (u \x v = 0 <-> (<u, u> * <v, v>) = <u, v>²).
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
      rewrite H2 in H4. autorewrite with R in H4. ra.
  Qed.

  (* (u × v = 0) <-> (u /_ v = 0) \/ (u /_ v = π) *)
  Lemma v2cross_eq0_iff_vangle : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> (u \x v = 0 <-> ((u /_ v = 0) \/ (u /_ v = PI))).
  Proof.
    intros. rewrite v2cross_eq0_iff_vdot_sqr_eq; auto.
    rewrite <- vdot_sqr_eq_iff_vangle_0_or_PI; auto. easy.
  Qed.

  (* (u × v <> 0) <-> 0 < (u /_ v) < π) *)
  Lemma v2cross_neq0_iff_vangle : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> (u \x v <> 0 <-> (0 < (u /_ v) < PI)).
  Proof.
    intros. rewrite v2cross_eq0_iff_vangle; auto.
    pose proof (vangle_bound u v H H0). ra.
  Qed.
  
End v2cross.
Infix "\x" := v2cross : vec_scope.


(** ** 标准基向量 *)
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
Lemma vangle_i_j : v2i /_ v2j = PI/2.
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


(** ** Extended angle for 2D vector (-π,π] *)

(* 
  1. 动机：
  * vangle表示两个向量a和b的夹角θ，并未考虑两个向量的前后顺序。
    同时其值域是[0,π]，并未充满整个圆周，这将失去一些方位信息。
  * 可以规定从a到b逆时针旋转为正方向，从而将其值域扩展到 (-π,π] 或 [0,2π)。
    如果得到了 (-π, π]，则只需要当 θ∈(-π,0)时，加上2π即可。
  * 一个现有的模型是 atan2 函数。
  3. 有多种具体做法来实现这种扩展
  (1) 方法一 v2angleA
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

Definition v2angleA (u v : vec 2) : R := atan2 (u \x v) (<u, v>).

Definition v2angleB (u v : vec 2) : R := atan2 (v.y) (v.x) - atan2 (u.y) (u.x).

(* Note that, v2angleC is the default choice, we will call it v2angle for short *)
Definition v2angle (u v : vec 2) : R :=
  let alpha := u /_ v in
  if 0 ??<= u \x v then alpha else (-alpha)%R.

Infix "/2_" := v2angle : vec_scope.

Section v2angle_props.

  Lemma v2angleB_v2angleA_equiv : forall (u v : vec 2), v2angleB u v = v2angleA u v.
  Proof.
    intros. cbv. pose proof (atan2_minus_eq). unfold Rminus in H. rewrite H.
    f_equal; ra.
  Qed.

  Lemma v2angleC_v2angleA_equiv : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> v2angle u v = v2angleA u v.
  Proof.
    intros. unfold v2angleA,v2angle,vangle,vnorm.
    rewrite !vdot_vcmul_l,!vdot_vcmul_r.
    pose proof (vlen_gt0 u H). pose proof (vlen_gt0 v H0).
    pose proof (vdot_gt0 u H). pose proof (vdot_gt0 v H0).
    autounfold with A.
    replace (1 / (||u||) * (1 / (||v||) * (<u, v>))) with ((<u, v>)/ (||u|| * ||v||)).
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
  Lemma v2angle_bound : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> - PI < u /2_ v <= PI.
  Proof.
    intros. unfold v2angle.
    pose proof PI_bound.
    pose proof (vangle_bound u v H H0).
    pose proof (v2cross_neq0_iff_vangle u v H H0).
    destruct (0 ??<= u \x v); ra.
  Qed.

  (** u × v = 0 -> (u /2_ v) = (v /2_ u) *)
  Lemma v2angle_comm_cross_eq0 : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> u \x v = 0 -> u /2_ v = v /2_ u.
  Proof.
    intros. remember H1 as H2. clear HeqH2.
    apply v2cross_eq0_iff_vangle in H1; auto. destruct H1.
    - unfold v2angle. rewrite (vangle_comm v u). rewrite H1.
      destruct (_??<=_), (_??<=_); ra.
    - unfold v2angle. rewrite (vangle_comm v u). rewrite H1.
      rewrite (v2cross_comm v u). rewrite H2.
      autorewrite with R. auto.
  Qed.

  (** u × v <> 0 -> u /2_ v = - (v /2_ u) *)
  Lemma v2angle_comm_cross_neq0 : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> u \x v <> 0 -> u /2_ v = (- (v /2_ u))%R.
  Proof.
    intros. remember H1 as H2. clear HeqH2.
    apply v2cross_neq0_iff_vangle in H1; auto.
    unfold v2angle. rewrite (vangle_comm v u).
    rewrite (v2cross_comm v u). destruct (_??<=_),(_??<=_); ra.
  Qed.

End v2angle_props.


(** ** More properties  *)

(** i /2_ j = π/2 *)
Fact v2angle_i_j : v2i /2_ v2j = PI/2.
Proof.
  rewrite v2angleC_v2angleA_equiv; auto with vec. cbv. apply atan2_X0_Yge0; ra.
Qed.

(** j /2_ j = - π/2 *)
Fact v2angle_j_i : v2j /2_ v2i = - PI/2.
Proof.
  rewrite v2angleC_v2angleA_equiv; auto with vec. cbv. apply atan2_X0_Ylt0; ra.
Qed.

(** cos (u /2_ v) = cos (u /_ v) *)
Lemma cos_v2angle_eq : forall (u v : vec 2), cos (u /2_ v) = cos (u /_ v).
Proof. intros. unfold v2angle. destruct (_??<=_); ra. Qed.

(** sin (u /2_ v) = (0 <= u \x v) ? sin (v /_ v) : (- sin (u /_ v)) *)
Lemma sin_v2angle_eq : forall (u v : vec 2),
    sin (u /2_ v) = if 0 ??<= u \x v then sin (u /_ v) else (- sin (u /_ v))%R.
Proof. intros. unfold v2angle. destruct (_??<=_); ra. Qed.

(** i与任意非零向量v的夹角的余弦等于其横坐标除以长度 *)
Lemma cos_v2angle_i : forall (v : vec 2), v <> vzero -> cos (v2i /2_ v) = (v.x / ||v||)%R.
Proof.
  intros. rewrite cos_v2angle_eq. unfold vangle. rewrite cos_acos; auto with vec.
  rewrite v2i_vnorm. rewrite vdot_i_l. rewrite vnth_vnorm; auto.
Qed.
  
(** i与任意非零向量v的夹角的正弦等于其纵坐标除以长度 *)
Lemma sin_v2angle_i : forall (v : vec 2), v <> vzero -> sin (v2i /2_ v) = (v.y / ||v||)%R.
Proof.
  intros. unfold v2angle. unfold vangle. rewrite v2i_vnorm. rewrite vdot_i_l.
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
Lemma cos_v2angle_j : forall (v : vec 2), v <> vzero -> cos (v2j /2_ v) = (v.y / ||v||)%R.
Proof.
  intros. rewrite cos_v2angle_eq. unfold vangle. rewrite cos_acos.
  - rewrite v2j_vnorm. rewrite vdot_j_l. rewrite vnth_vnorm; auto.
  - apply vdot_vnorm_bound; auto. apply v2j_nonzero.
Qed.

(** j与任意非零向量v的夹角的正弦等于其横坐标取负除以长度 *)
Lemma sin_v2angle_j : forall (v : vec 2),
    v <> vzero -> sin (v2j /2_ v) = (- v.x / ||v||)%R.
Proof.
  intros. unfold v2angle. unfold vangle. rewrite v2j_vnorm. rewrite vdot_j_l.
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
Lemma v2len_mul_cos_v2angle_i : forall (a : vec 2),
    a <> vzero -> (||a|| * cos (v2i /2_ a) = a.x)%R.
Proof.
  intros. rewrite cos_v2angle_i; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * sin (i /2_ a) = a.y *)
Lemma v2len_mul_sin_v2angle_i : forall (a : vec 2),
    a <> vzero -> (||a|| * sin (v2i /2_ a) = a.y)%R.
Proof.
  intros. rewrite sin_v2angle_i; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * cos (j /2_ a) = a.y *)
Lemma v2len_mul_cos_v2angle_j : forall (a : vec 2),
    a <> vzero -> (||a|| * cos (v2j /2_ a) = a.y)%R.
Proof.
  intros. rewrite cos_v2angle_j; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * sin (j /2_ a) = - a.x *)
Lemma v2len_mul_sin_v2angle_j : forall (a : vec 2),
    a <> vzero -> (||a|| * sin (v2j /2_ a) = - a.x)%R.
Proof.
  intros. rewrite sin_v2angle_j; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

