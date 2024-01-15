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

Require Import VectorR.
Require Import Ratan2.
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
Section general.

  (** The equality of 2D vector *)
  Lemma v2eq_iff : forall u v : vec 2, u = v <-> u.x = v.x /\ u.y = v.y.
  Proof.
    intros. split; intros; subst; auto.
    unfold nat2finS in H; simpl in H. destruct H.
    apply veq_iff_vnth_nat; intros. unfold nat2fin.
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H).
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H0). lia.
  Qed.

  (** The length of 2D vector *)
  Lemma v2len_eq : forall v : vec 2, ||v|| = sqrt (v.x² + v.y²).
  Proof. intros. cbv. f_equal. ra. Qed.

End general.


(** ** 标准基向量 *)
Section basis.
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

  (** 标准基向量是规范化操作的不动点 *)
  Lemma v2i_cvnorm_fixpoint : vnorm v2i = v2i.
  Proof. apply vnorm_vunit_fixpoint. apply v2i_vunit. Qed.

  Lemma v2j_cvnorm_fixpoint : vnorm v2j = v2j.
  Proof. apply vnorm_vunit_fixpoint. apply v2j_vunit. Qed.
  
  (** 标准基向量与任意向量 v 的点积等于 v 的各分量 *)
  Lemma vdot2_i_l : forall (v : vec 2), <v2i, v> = v.x. Proof. intros. cbv; ra. Qed.
  Lemma vdot2_i_r : forall (v : vec 2), <v, v2i> = v.x. Proof. intros. cbv; ra. Qed.
  Lemma vdot2_j_l : forall (v : vec 2), <v2j, v> = v.y. Proof. intros. cbv; ra. Qed.
  Lemma vdot2_j_r : forall (v : vec 2), <v, v2j> = v.y. Proof. intros. cbv; ra. Qed.

  (** 标准基向量的夹角 *)
  Lemma vangle_vec2_i_j : v2i /_ v2j = PI/2.
  Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

End basis.


(** ** The cross product of 2D vectors *)
Section vcross2.
  Definition vcross2 (u v : vec 2) : R := u.x * v.y - u.y * v.x.

  (* u X v = - (v X u) *)
  Lemma vcross2_comm : forall (u v : vec 2), vcross2 u v = (- (vcross2 v u))%R.
  Proof. intros. cbv; ra. Qed.

  (** 0 <= u × v -> u × v = √((u⋅u)(v⋅v) - (u⋅v)²) *)
  Lemma vcross2_ge0_eq : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> 0 <= vcross2 u v ->
      vcross2 u v = sqrt ((<u, u>*<v, v>) - <u, v>²).
  Proof.
    intros. apply Rsqr_inj. ra. ra.
    rewrite !Rsqr_sqrt.
    2:{ pose proof (vdot_sqr_le u v). ra. }
    cbv. v2f 0. field.
  Qed.

  (** u × v < 0 -> u × v = - √((u⋅u)(v⋅v) - (u⋅v)²) *)
  Lemma vcross2_lt0_eq : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> vcross2 u v < 0 ->
      vcross2 u v = (- sqrt ((<u, u>*<v, v>) - <u, v>²))%R.
  Proof.
    intros. rewrite vcross2_comm. rewrite (vdot_comm u v).
    rewrite vcross2_ge0_eq; ra.
    - f_equal. f_equal. ring.
    - rewrite vcross2_comm; ra.
  Qed.
  
End vcross2.


(** ** Extended angle for 2D vector (-π,π] *)
Section vangle2.
  (* 
     1. 动机：
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

  Section vangle2A.
    Definition vangle2A (u v : vec 2) : R := atan2 (vcross2 u v) (<u, v>).
    
  End vangle2A.
  
  Section vangle2B.
    Definition vangle2B (u v : vec 2) : R :=
      atan2 (v.y) (v.x) - atan2 (u.y) (u.x).

    Lemma vangle2B_vangle2A_equiv : forall (u v : vec 2), vangle2B u v = vangle2A u v.
    Proof.
      intros. cbv. pose proof (atan2_minus_eq). unfold Rminus in H. rewrite H.
      f_equal; ra.
    Qed.
    
  End vangle2B.
  
  Section vangle2C.
    
    (* Note that, vangle2 is the short name of vangle2C *)
    Definition vangle2 (u v : vec 2) : R :=
      let d := vcross2 u v in
      let alpha := u /_ v in
      if d >=? 0 then alpha else (-alpha)%R.
    
    Infix "/2_" := vangle2 (at level 60) : vec_scope.

    (** 0 < <u, v> ->
       acos (<u, v> / (||u|| * ||v||)) =
       atan (sqrt (<u, u> * <v, v> - <u, v>²) / <u, v>) *)
    Lemma acos_div_dot_gt0_eq : forall (u v : vec 2),
        0 < <u, v> ->
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
      autorewrite with R. field. split; apply vdot_neq0_iff_vnonzero; auto.
    Qed.

    (** <u, v> < 0 ->
       acos (<u, v> / (||u|| * ||v||)) =
       atan (sqrt (<u, u> * <v, v> - <u, v>²) / <u, v>) + PI *)
    Lemma acos_div_dot_lt0_eq : forall (u v : vec 2),
        <u, v> < 0 ->
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
      rewrite Rsqr_sqrt; [|ra]. rewrite Rsqr_sqrt; [|ra].
      autorewrite with R. field. split; apply vdot_neq0_iff_vnonzero; auto.
    Qed.
      
    Lemma vangle2C_vangle2A_equiv : forall (u v : vec 2),
        u <> vzero -> v <> vzero ->
        vangle2 u v = vangle2A u v.
    Proof.
      intros. unfold vangle2A,vangle2,vangle,vnorm.
      rewrite !vdot_vcmul_l,!vdot_vcmul_r.
      pose proof (vlen_gt0 u H). pose proof (vlen_gt0 v H0).
      pose proof (vdot_gt0 u H). pose proof (vdot_gt0 v H0).
      autounfold with A.
      replace (1 / (||u||) * (1 / (||v||) * (<u, v>))) with ((<u, v>)/ (||u|| * ||v||)).
      2:{ field. split; apply vlen_neq0_iff_neq0; auto. }
      bdestruct (<u, v> =? 0).
      - (* <u, v> = 0 *)
        rewrite H5. autorewrite with R; ra.
        rewrite acos_0. bdestruct (0 <=? vcross2 u v).
        + rewrite atan2_X0_Yge0; ra.
        + rewrite atan2_X0_Ylt0; ra.
      - (* <u, v> <> 0 *)
        bdestruct (0 <? <u, v>).
        + (* 0 < <u, v> *)
          rewrite acos_div_dot_gt0_eq; ra.
          rewrite atan2_Xgt0; ra. 
          bdestruct (0 <=? vcross2 u v).
          * (* 0 <= u × v *)
            rewrite vcross2_ge0_eq; ra.
          * (* u × v < 0*)
            rewrite vcross2_lt0_eq; ra.
            rewrite Ropp_div. rewrite atan_opp. auto.
        + (* <u, v> < 0 *)
          rewrite acos_div_dot_lt0_eq; ra.
          bdestruct (0 <=? vcross2 u v).
          * (* 0 <= u × v *)
            rewrite atan2_Xlt0_Yge0; ra. rewrite vcross2_ge0_eq; ra.
          * (* u × v < 0*)
            rewrite atan2_Xlt0_Ylt0; ra. rewrite vcross2_lt0_eq; ra.
            rewrite Ropp_div. rewrite atan_opp. ring.
    Qed.

    ?
    Lemma vangle2_bound : forall (u v : vec 2),


  End vangle2C.

  (* The expended angle which is (-π,π] for 2D vectors (alternative version) *)

  (* The `vangle2_alt` is equivalent to `vangle2` *)


  (* Δ = 0, u /2_ v = π *)
  Lemma vangle2_eq_vangle_neg : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> vcross2 u v = 0 -> u /2_ v = PI.
  Proof.
  Abort.

  (* The vangle2 is equal to vangle *)
  Lemma vangle2_eq_vangle : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> vcross2 u v > 0 -> u /2_ v = u /_ v.
  Proof.
    intros. unfold vangle2, vangle.
    assert (<u, u> <> 0) by (apply vdot_neq0_iff_vnonzero; auto).
    assert (<v, v> <> 0) by (apply vdot_neq0_iff_vnonzero; auto).
    bdestruct (0 <? <u, v>).
    - rewrite atan2_Xgt0; auto. rewrite acos_atan; ra.
      + f_equal. unfold vnorm. rewrite !vdot_vcmul_l, !vdot_vcmul_r.
        remember (1 / (||u||)) as r1. remember (1 / (||v||)) as r2.
        remember (<u, v>) as r.
        autounfold with A. autorewrite with R. field_simplify_eq.
        apply Rsqr_inj.
        3:{ rewrite Rsqr_sqrt.
            { rewrite Heqr1,Heqr2,Heqr. autorewrite with R. rewrite !Rsqr_div'.
              rewrite <- !vdot_same. cbv; v2f 0; field. cbv in H2,H3; v2f 0; ra. }
            { rewrite Heqr1,Heqr2,Heqr. rewrite !Rsqr_div'.
              rewrite <- !vdot_same. cbv; v2f 0.
              autorewrite with R.
              (* 应该是成立的，但是分支过多，下次在证 *)
  Abort.

  (* The vangle2 is equal to the negation of vangle *)
  Lemma vangle2_eq_vangle_neg : forall (u v : vec 2),
      u <> vzero -> v <> vzero -> vcross2 u v < 0 -> u /2_ v = (- (u /_ v))%R.
  Proof.
  Abort.

  (** i /2_ j = π/2 *)
  Fact vangle2_i_j : v2i /2_ v2j = PI/2.
  Proof. cbv. apply atan2_X0_Ygt0; ra. Qed.

  (** j /2_ j = - π/2 *)
  Example vangle2_ex2 : v2j /2_ v2i = - PI/2.
  Proof. cbv. apply atan2_X0_Ylt0; ra. Qed.

  (** v /2_ u = - (u /2_ v) *)
  Lemma vangle2_comm : forall (u v : vec 2),
      u <> vzero -> v <> vzero ->
      (0 < <u, v> \/ vcross2 u v <> 0) ->
      v /2_ u = (- (u /2_ v))%R.
  Proof.
    intros. unfold vangle2.
    rewrite vdot_comm. rewrite vcross2_comm. rewrite atan2_y_neg; auto.
  Qed.
  
  (* Lemma vangle2Delta_gt0_imply_ltPI : forall (u v : vec 2), *)
  (*     vangle2Delta u v > 0 -> u /_ v < PI. *)

  (* (** The angle from i to v is > π, if and only if v.y is negative *) *)
  (* Lemma vangle2_i_gt0 : forall (v : vec 2), vangle2Delta v2i v > PI <-> v.y < 0. *)
  (* Proof. *)
  (*   intros. cbv. autorewrite with R. split; intros; ra. ra. destruct R_lt_Dec; auto. *)
  (*   destruct dec; split; intros; ra. *)
  (* Qed. *)
  
  (* (** The angle from i to v is <= π, if and only if v.y is non negative *) *)
  (* Lemma vangle2GtPI_i_false : forall (v : vec 2), vangle2GtPI v2i v = false <-> 0 <= v.y. *)
  (* Proof. *)
  (*   intros. cbv. autorewrite with R. destruct R_lt_Dec; auto. *)
  (*   destruct dec; split; intros; ra. *)
  (* Qed. *)
  
  (* (** The angle from j to v is > π, if and only if v.x is positive *) *)
  (* Lemma vangle2GtPI_j_true : forall (v : vec 2), vangle2GtPI v2j v = true <-> 0 < v.x. *)
  (* Proof. *)
  (*   intros. cbv. autorewrite with R. destruct R_lt_Dec; auto. *)
  (*   destruct dec; split; intros; ra. *)
  (* Qed. *)
  
  (* (** The angle from j to v is <= π, if and only if v.x is non positive *) *)
  (* Lemma vangle2GtPI_j_false : forall (v : vec 2), vangle2GtPI v2j v = false <-> v.x <= 0. *)
  (* Proof. *)
  (*   intros. cbv. autorewrite with R. destruct R_lt_Dec; auto. *)
  (*   destruct dec; split; intros; ra. *)
  (*   intros. vec2fun. cbv. autorewrite with R. destruct Rlt_le_dec; auto. *)
  (*   split; intros; auto; try easy. lra. *)
  (*   split; intros; auto; try easy. lra. *)
  (* Qed. *)

  (* (** ∠(v1, v2) + ∠(v2, v1) = 2*π *) *)
  (* Lemma vangle2_anticomm : forall (v1 v2 : vec 2), *)
  (*     ((vangle2 v1 v2) + (vangle2 v2 v1) = 2 * PI)%R. *)
  (* Proof. *)
  (*   intros. unfold vangle2. ? *)
  (*   rewrite vangle2LtPI_GtPI_comm.  *)
  
  (*   ? *)

  (** cos (x /2_ y) = cos (x /_ y) *)
  Lemma cos_vangle2_eq_cos_cvangle : forall (x y : vec 2),
      cos (vangle2 x y) = cos (vangle x y).
  Proof.
    intros. unfold vangle2,vangle.
  (*   destruct (vangle2GtPI x y); auto. *)
  (*   unfold Rminus. rewrite RealFunction.cos_2PI_add. apply cos_neg. *)
    (* Qed. *)
  Abort.

  (** i与任意非零向量v的夹角的余弦等于其横坐标除以长度 *)
  Lemma cos_vangle2_i : forall (v : vec 2),
      v <> vzero -> cos (vangle2 v2i V) = (v.x / ||v||)%R.
  Proof.
    intros.
?
    
    intros. rewrite cos_vangle2_eq_cos_cvangle.
    unfold vangle. rewrite cos_acos.
    - rewrite v2i_cvnorm_fixpoint. rewrite v2dot_i_l.
      rewrite vnorm_nth; auto.
    - apply vdot_vnormalize_bound; auto. apply v2i_nonzero.
    Qed.
  Abort.

  (** i与任意非零向量v的夹角的正弦等于其纵坐标除以长度 *)
  Lemma sin_vangle2_i : forall (v : vec 2),
      v <> vzero -> sin (vangle2 v2i V) = (v.y / ||v||)%R.
  Proof.
    intros. unfold vangle2. destruct (vangle2GtPI v2i v) eqn:E1.
    - unfold Rminus. rewrite RealFunction.sin_2PI_add. rewrite sin_neg.
      apply vangle2GtPI_i_true in E1. unfold vangle. rewrite sin_acos.
      + rewrite v2i_cvnorm_fixpoint. rewrite v2dot_i_l.
        rewrite vnorm_nth; auto. rewrite v2len_eq.
        rewrite Rsqrt_1_minus_x_eq_y. field_simplify. f_equal.
        rewrite Rabs_left; auto. lra.
        all: try apply vlen_neq0_iff_neq0 in H; rewrite v2len_eq in H; auto.
        apply sqrt_neq0_iff in H. lra.
      + apply vdot_vnormalize_bound; auto. apply v2i_nonzero.
    - apply vangle2GtPI_i_false in E1. unfold vangle. rewrite sin_acos.
      + rewrite v2i_cvnorm_fixpoint. rewrite v2dot_i_l.
        rewrite vnorm_nth; auto. rewrite v2len_eq.
        rewrite Rsqrt_1_minus_x_eq_y.
        * f_equal. rewrite Rabs_right; auto. ra.
        * apply vlen_neq0_iff_neq0 in H. rewrite v2len_eq in H.
          apply sqrt_neq0_iff in H. lra.
      + apply vdot_vnormalize_bound; auto. apply v2i_nonzero.
  Qed.

  (** j与任意非零向量v的夹角的余弦等于其纵坐标除以长度 *)
  Lemma cos_vangle_j : forall (v : vec 2),
      v <> vzero -> cos (vangle2 v2j v) = (v.y / ||v||)%R.
  Proof.
    intros. rewrite cos_vangle2_eq_cos_cvangle.
    unfold vangle. rewrite cos_acos.
    - rewrite v2j_cvnorm_fixpoint. rewrite v2dot_j_l.
      rewrite vnorm_nth; auto.
    - apply vdot_vnormalize_bound; auto. apply v2j_nonzero.
  Qed.
  
  (** j与任意非零向量v的夹角的正弦等于其横坐标取负除以长度 *)
  Lemma sin_vangle_j : forall (v : vec 2),
      v <> vzero -> sin (vangle2 v2j v) = (- v.x / ||v||)%R.
  Proof.
    intros. unfold vangle2. destruct (vangle2GtPI v2j v) eqn:E1.
    - unfold Rminus. rewrite RealFunction.sin_2PI_add. rewrite sin_neg.
      apply vangle2GtPI_j_true in E1. unfold vangle. rewrite sin_acos.
      + rewrite v2j_cvnorm_fixpoint. rewrite v2dot_j_l.
        rewrite vnorm_nth; auto. rewrite v2len_eq.
        rewrite Rsqrt_1_minus_y_eq_x.
        field_simplify. f_equal. rewrite Rabs_right; auto. lra.
        all: try apply vlen_neq0_iff_neq0 in H; rewrite v2len_eq in H; auto.
        apply sqrt_neq0_iff in H. lra.
      + apply vdot_vnormalize_bound; auto. apply v2j_nonzero.
    - apply vangle2GtPI_j_false in E1. unfold vangle. rewrite sin_acos.
      + rewrite v2j_cvnorm_fixpoint. rewrite v2dot_j_l.
        rewrite vnorm_nth; auto. rewrite v2len_eq.
        rewrite Rsqrt_1_minus_y_eq_x. f_equal; auto with R.
        apply vlen_neq0_iff_neq0 in H; rewrite v2len_eq in H;
          apply sqrt_neq0_iff in H. lra.
      + apply vdot_vnormalize_bound; auto. apply v2j_nonzero.
  Qed.

End vangle2.


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
  Lemma R2_orthogonal : forall (θ : R), morth (R2 θ).
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
  
  Lemma R2_inv_eq_trans : forall θ : R, (R2 θ)⁻¹ = (R2 θ)\T.
  Proof.
    (* method 1 : prove by computing (slow) *)
    (* lma; autounfold with A; autorewrite with R; try easy. *)
    (* method 2 : prove by reasoning *)
    intros; apply (SOn_imply_inv_eq_trans (R2_SO2 θ)).
  Qed.

  (** R(-θ) = R(θ)\T *)
  Lemma R2_neg_eq_trans : forall θ : R, R2 (-θ) = (R2 θ)\T.
  Proof. lma; autorewrite with R; try easy. Qed.

  (** R(-θ) * R(θ) = I *)
  Lemma R2_neg_R2_inv : forall θ : R, R2 (- θ) * R2 θ = mat1.
  Proof.
    (* lma; autounfold with A; autorewrite with R; auto; ring. *)
    intros; rewrite R2_neg_eq_trans, <- R2_inv_eq_trans, mmul_minv_l; easy.
  Qed.

  (** R(θ) * R(-θ) = I *)
  Lemma R2_R2_neg_inv : forall θ : R, R2 θ * R2 (- θ) = mat1.
  Proof.
    (* lma; autounfold with A; autorewrite with R; auto; ring. *)
    intros; rewrite R2_neg_eq_trans, <- R2_inv_eq_trans, mmul_minv_r; easy.
  Qed.

  (** v' = R(θ) * v *)
  Lemma R2_spec1 : forall (v : vec 2) (θ : R),
      let l := vlen v in
      let α := vangle2 v2i v in
      let vx' := (l * cos (α + θ))%R in
      let vy' := (l * sin (α + θ))%R in
      let v' : vec 2 := mk_vec2 vx' vy' in
      v <> vzero -> v' = R2 θ * v.
  Proof.
    lma.
    - unfold vx'. unfold l. unfold α.
      rewrite cos_plus. unfold Rminus. rewrite Rmult_plus_distr_l.
      rewrite cos_vangle2_i, sin_vangle2_i; auto.
      autounfold with T. autorewrite with R. field.
      apply vlen_neq0_iff_neq0; auto.
    - unfold vy'. unfold l. unfold α.
      rewrite sin_plus. rewrite Rmult_plus_distr_l.
      rewrite cos_vangle2_i, sin_vangle2_i; auto.
      autounfold with T. autorewrite with R. field.
      apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** v = R(-θ) * v' *)
  Lemma R2_spec2 : forall (v : vec 2) (θ : R),
      let l := vlen v in
      let α := vangle2 v2i v in
      let vx' := (l * cos (α + θ))%R in
      let vy' := (l * sin (α + θ))%R in
      let v' : vec 2 := mk_vec2 vx' vy' in
      v <> vzero -> v = (R2 (-θ)) * v'.
  Proof.
    intros.
    pose proof (R2_spec1 v θ). simpl in H0. specialize (H0 H).
    unfold v',vx',vy',l,α. rewrite H0. rewrite <- mmul_assoc.
    rewrite R2_neg_R2_inv. rewrite mmul_1_l. easy.
  Qed.

  (** v = R(θ)\T * v' *)
  Lemma R2_spec3 : forall (v : vec 2) (θ : R),
      let l := vlen v in
      let α := vangle2 v2i v in
      let vx' := (l * cos (α + θ))%R in
      let vy' := (l * sin (α + θ))%R in
      let v' : vec 2 := mk_vec2 vx' vy' in
      v <> vzero -> v = (R2 θ)\T * v'.
  Proof.
    intros.
    pose proof (R2_spec2 v θ). simpl in H0. specialize (H0 H).
    unfold v',vx',vy',l,α. rewrite <- R2_neg_eq_trans. auto.
  Qed.

  (** 预乘和后乘旋转矩阵的关系，即: v ~ v' -> R(θ) * v ~ v' * R(θ) *)
  Lemma R2_spec4 : forall (v1 : vec 2) (θ : R),
      let v1' : rvec 2 := v1\T in  (* v1和v1'是列向量和行向量形式的同一个向量 *)
      let v2 : vec 2 := (R2 θ) * v1 in       (* 用列向量形式计算 *)
      let v2' : rvec 2 := v1' * ((R2 θ)\T) in (* 用行向量形式计算 *)
      let v2'' : vec 2 := v2'\T in           (* v2' 的列向量形式 *)
      v2 = v2''. (* 结果应该相同 *)
  Proof. lma. Qed.

  (** R的乘法是交换的: R(θ1) * R(θ2) = R(θ2) * R(θ1) *)
  Lemma R2_mul_comm : forall (θ1 θ2 : R), (R2 θ1) * (R2 θ2) = (R2 θ2) * (R2 θ1).
  Proof. lma. Qed.

  (** R的乘法等价于对参数的加法: R(θ1) * R(θ2) = R(θ1 + θ2) *)
  Lemma R2_mul_eq_sum : forall (θ1 θ2 : R), (R2 θ1) * (R2 θ2) = R2 (θ1 + θ2).
  Proof. lma; autounfold with T; autorewrite with R; ring. Qed.

End RotationMatrix2D.


(** ** Rotation: Friendly name for user, avoid low-level matrix operation *)
Section Rotation.

  (** 为了避免旋转矩阵使用错误，命名一些操作 *)
  
  (** 2D中旋转一个列向量 *)
  Definition Rot2C (θ : R) (v : vec 2) : vec 2 := (R2 θ) * v.

  (** 2D中旋转一个行向量 *)
  Definition Rot2R (θ : R) (v : rvec 2) : rvec 2 := v * ((R2 θ)\T).

  (** 旋转列向量，等效于旋转行向量 *)
  Lemma Rot2C_eq_Rot2R : forall θ (v : vec 2), Rot2C θ v = (Rot2R θ (v\T))\T.
  Proof. lma. Qed.

  (** 旋转行向量，等效于旋转列向量 *)
  Lemma Rot2R_eq_Rot2C : forall θ (v : rvec 2), Rot2R θ v = (Rot2C θ (v\T))\T.
  Proof. lma. Qed.

  (** 旋转两次，等价于一次旋转两个角度之和: Rot(θ2, Rot(θ1,v)) = Rot(θ1+θ2, v) *)
  Lemma Rot2C_twice : forall (θ1 θ2 : R) (v : vec 2),
      Rot2C θ2 (Rot2C θ1 v) = Rot2C (θ1+θ2) v.
  Proof.
    intros. unfold Rot2C. rewrite <- mmul_assoc. rewrite R2_mul_eq_sum.
    rewrite Rplus_comm. easy.
  Qed.
  
  Lemma Rot2R_twice : forall (θ1 θ2 : R) (v : rvec 2),
      Rot2R θ2 (Rot2R θ1 v) = Rot2R (θ1+θ2) v.
  Proof.
    intros. unfold Rot2R. rewrite mmul_assoc.
    rewrite <- mtrans_mmul. rewrite R2_mul_eq_sum. rewrite Rplus_comm. easy.
  Qed.
  
End Rotation.
