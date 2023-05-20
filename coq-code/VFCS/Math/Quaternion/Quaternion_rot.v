(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Quaternion_rot (rotation theory)
  author    : ZhengPu Shi
  date      : 2022.06

  remark    :
  1. quat:{w,x,y,z} <==> vec4[w;x;y;z]
                    <==> vec3[x;y;z]

  reference :
  1. (QQ) Introduction to Multicopter Design and Control, Springer, Quan Quan, page 96
  2. (Dunn) 3D Math Primer for Graphics and Game Development, Second Edition
     Fletcher Dunn, Ian Parberry.
  3. (Krasjet) Quaternion and 3D rotation（四元数与三维旋转）
 *)

Require Export Quaternion_base.

Open Scope R.
Open Scope mat_scope.
Open Scope cvec_scope.
Open Scope quat_scope.


(* ######################################################################### *)
(** * Rotate 3D vector by unit quaternion *)

(** vector v (be wrapped to quaterion) is rotated by a quaternion q.
      Note that: q must be a rotation quaternion *)
Definition qrot (q : quat) (v : quat) : quat := q * v * q⁻¹.

(** vector form of qrot *)
Definition qrotv (q : quat) (v : cvec 3) : cvec 3 := (qrot q (qpure v)).Im.

(** 使用四元数连接两个旋转: First by q1, then by q2 *)
Lemma qrot_twice : forall (q1 q2 : quat) (v : quat),
    q1 <> qzero -> q2 <> qzero -> qrot q2 (qrot q1 v) = qrot (q2 * q1) v.
Proof.
  intros. unfold qrot. rewrite qinv_qmul; auto. rewrite !qmul_assoc. auto.
Qed.

(** 备注：四元数乘法可以连接多个旋转，就像矩阵乘法一样。
    但实际上还有一些区别。矩阵乘法时，可以使用行矢量左乘矩阵，也可使用列矢量右乘
    矩阵（转置形式）。而四元数没有这种灵活性，多个连接总是从右到左或说“从里到外”
    读取。对于 Dunn 的这个观点，我们可以进一步实验，看看四元数是否也能通过某种
    “转置”操作实现更换方向。当然，这个实验可能只是理论上的需要，实际并无此需求。
    由于四元数乘法有对应的矩阵形式，我么可以直接在矩阵上操作 *)

(** 证明四元数乘法能够旋转三维矢量 *)

(** 方法1：计算其生成的结果与轴角表示的结果相同，这是大多数文献所采用的方法。*)
Module qrot_spec_method1.
  
  Local Open Scope fun_scope.
  
  Lemma qrot_spec : forall (θ : R) (n : cvec 3) (H : cvunit n) (v : cvec 3),
      let q := aa2quat (θ, n) in
      (qrotv q v) == rotAxisAngle θ n v.
  Proof.
    intros.
    pose proof (cv3unit_eq1 n H).
    cvec2fun. lma.
    (* 以下三部分一模一样，但为了看到过程，所以没有全部使用分号策略“;”。*)
    - cbv in H0; ring_simplify in H0. unfold cvdot; cbv; ring_simplify.
      remember (θ * / (R1 + R1))%R as α; replace θ with (α + α)%R by lra.
      remember (n.11) as n1; remember (n.21) as n2; remember (n.31) as n3.
      remember (v.11) as v1; remember (v.21) as v2; remember (v.31) as v3.
      rewrite cos_plus, sin_plus. unfold Rminus; field_simplify.
      + rewrite H0; field_simplify. rewrite cos2'. field; try lra.
        rewrite cos2'; intro H1; field_simplify in H1; lra.
      + intro H1; ring_simplify in H1.
        rewrite cos2',H0 in H1; field_simplify in H1; lra.
    - cbv in H0; ring_simplify in H0. unfold cvdot; cbv; ring_simplify.
      remember (θ * / (R1 + R1))%R as α; replace θ with (α + α)%R by lra.
      remember (n.11) as n1; remember (n.21) as n2; remember (n.31) as n3.
      remember (v.11) as v1; remember (v.21) as v2; remember (v.31) as v3.
      rewrite cos_plus, sin_plus. unfold Rminus; field_simplify.
      + rewrite H0; field_simplify. rewrite cos2'. field; try lra.
        rewrite cos2'; intro H1; field_simplify in H1; lra.
      + intro H1; ring_simplify in H1.
        rewrite cos2',H0 in H1; field_simplify in H1; lra.
    - cbv in H0; ring_simplify in H0. unfold cvdot; cbv; ring_simplify.
      remember (θ * / (R1 + R1))%R as α; replace θ with (α + α)%R by lra.
      remember (n.11) as n1; remember (n.21) as n2; remember (n.31) as n3.
      remember (v.11) as v1; remember (v.21) as v2; remember (v.31) as v3.
      rewrite cos_plus, sin_plus. unfold Rminus; field_simplify.
      + rewrite H0; field_simplify. rewrite cos2'. field; try lra.
        rewrite cos2'; intro H1; field_simplify in H1; lra.
      + intro H1; ring_simplify in H1.
        rewrite cos2',H0 in H1; field_simplify in H1; lra.
  Qed.

End qrot_spec_method1.

(** 方法2：QQ书上的推导过程 *)
Module qrot_spec_method2.

  (* 1. 任给单位四元数q，总能写成
     q = [cos(θ/2), v * sin(θ/2)]
     其中，v是带单位向量，表示旋转轴，θ是旋转的角度，q表示绕v旋转θ。

     我们声称，以下公式能够将向量 v1 按照q的作用旋转到 v1'
     [0,v1'] = q⊗[0,v1]⊗ q^{-1}
     其中，q是单位四元数。

     下面，证明这个结论。
     1. 第一行可以验证是成立的（即从纯四元数得到了纯四元数）。
        这里其实分了两步，左乘，右乘。每一步都使得w不为0，但两次抵消了。
     2. 经过变换，v1' 和 v1 的长度不变。
     3. 非零实数s乘以q以后，仍然是相同的作用。
     4. 表示旋转的论证
     (1). 两个3D单位向量 v0 v1 (v0 ≠ ± v1，即，
        θ/2 为 v0 到 v1 之间的夹角，<v0,v1> = cos(θ/2),
        同时，确定了一个新的向量 
        v = (v0 × v1) / |v0 × v1| 
        = (v0 × v1) / (|v0| * |v1| * sin(θ/2))
        = (v0 × v1) / sin(θ/2)
        所以，v0 × v1 = v * sin(θ/2)
        所以，q = [<v0,v1>, v0 × v1] = [0,v1] ⊗ [0,v0]*
     (2) 定义 [0,v2] = q⊗[0,v0]⊗q^{-1}
        可证明 [<v1,v2>, v1 × v2] = [0,v2] ⊗ [0,v1]* = q
        于是，现在可知 <v1,v2> = <v0,v1> 且 v1 × v2 = v0 × v1
        这表明：
        v2位于v0和v1所在的平面，且v1与v2夹角是θ/2
        所以对v0作用单位向量q，可看作是把v0绕v旋转θ后得到v2。
     (3) 定义 [0,v3] = q⊗[0,v1]⊗q^{-1}
        可证明 [<v2,v3>, v1 × v2] = [0,v3] ⊗ [0,v2]* = q
        于是，现在可知 <v2,v3> = <v1,v2> 且 v2 × v3 = v1 × v2
        这表明：
        v3位于v1和v2所在的平面，且v2与v3夹角是θ/2
        所以对v1作用单位向量q，可看作是把v1绕v旋转θ后得到v3。
     (4) 还能很容易验证 q ⊗ [0,v] = [0,v] ⊗ q，进一步可验证
        q ⊗ [0,v] ⊗ q* = [0,v] ⊗ q ⊗ q* = [0,v]
        这表明，v是旋转轴（经过作用后没有变化）。
     (5) 任意向量 vt 可分解为 vt = s0*v0 + s1*v1 + s2*v,
        由双线性性质，我们可以分别对v0,v1,v2作用。
        因此，q对向量vt的作用是绕v进行θ角的一次旋转。

     一般化定理5.1，可知每个3D旋转对应一个单位四元数。
     进一步，若q1,q2两次相继旋转可得到进一步的公式。
   *)
  
  (** qrot作用于某个四元数后不改变它的w分量。公式5.26 *)
  Lemma qrot_keep_w : forall (q v : quat), qunit q -> (qrot q v).W = v.W.
  Proof.
    intros. pose proof (qunit_imply_eq1 q H). destruct q,v. cbv in *.
    field_simplify in H0. field_simplify; try lra. rewrite H0. field. lra.
  Qed.

  (** qrot作用于某个纯四元数后所得四元数的w分量为0，即仍然是纯四元数 *)
  Lemma qrot_qpure_w0 : forall (q : quat) (v : cvec 3),
      qunit q -> (qrot q (qpure v)).W = 0.
  Proof. intros. rewrite qrot_keep_w; auto. Qed.

  (** 单位四元数的另一种表示形式：由旋转轴(单位向量)和旋转角构成 5.25 *)
  
  (* 若旋转轴 v 是单位向量，则依转轴和转角生成的四元数是单位四元数 *)

  (** 通过四元数进行向量旋转会保持向量范数不变 *)
  Lemma qrot_keep_cvlen : forall (q v : quat),
      qunit q -> (|| v.Im || = || (qrot q v).Im ||)%CV.
  Proof.
    (* 1. 推理式的证明。先证明q的范数不变，然后 v的范数+w的平方和等于q的范数，
         所以v的范数不变 *)
    
    (* 2. 计算式的证明 *)
    intros. pose proof (qunit_imply_eq1 q H).
    destruct q as [a b c d], v as [e f g h]. simpl in *.
    lqa. field_simplify; try lra. field_simplify in H0.
    rewrite Rpow4_Rsqr_Rsqr'. rewrite H0. field. lra.
  Qed.

  (** qrot作用于单位向量，得到的仍然是单位向量 *)
  Lemma qrot_qpure_cvunit : forall (q : quat) (v : cvec 3),
      qunit q -> cvunit v -> cvunit (qrotv q v).
  Proof.
    intros. apply cvunit_spec. unfold qrotv. rewrite <- qrot_keep_cvlen; auto.
    rewrite qim_qpure; auto. apply cvunit_spec; auto.
  Qed.
  
  (** qrot作用于单位向量，得到了另一个单位四元数 *)
  Lemma qrot_qpure_qunit : forall (q : quat) (v : cvec 3),
      qunit q -> cvunit v -> qunit (qrot q (qpure v)).
  Proof.
    intros. apply qim_cvunit_imply_qunit; auto.
    apply qrot_qpure_w0; auto. apply qrot_qpure_cvunit; auto.
  Qed.

  (* 任意非零实数s与q相乘，结论仍然成立 *)
  Lemma qrot_keep_len_ext :  forall (q v : quat) (s : R),
      let q' : quat := qrot (s c* q) v in
      s <> 0 -> qunit q -> (|| v.Im || = || q'.Im ||)%CV.
  Proof.
    intros. unfold q' in *.
    assert (qrot (s c* q) v = qrot q v).
    { unfold qrot. rewrite qinv_qcmul; auto.
      rewrite !qmul_qcmul_l, !qmul_qcmul_r. rewrite qcmul_assoc.
      replace (s * (1 / s))%R with 1; try field; auto.
      rewrite qcmul_1_l; auto. apply qunit_neq0; auto. }
    rewrite H1.
    pose proof (qrot_keep_cvlen q v) as H2. simpl in H2. auto.
  Qed.

  (* 公式5.25中的四元数作用：绕v轴旋转θ角度。
       换言之，公式5.25是如何构造的？它为什么能表示旋转 *)

  (* 计算两个向量的夹角 *)
  (* Check cvangle. *)
  (* Check cv2angle. *)

  (* 计算两个向量所决定的转轴（垂直于所在平面的法向量) *)
  (* Check cv3cross. *)
  
  (* 谓词：两向量不共线（不平行的） *)
  (* Definition v3_non_colinear (v0 v1 : cvec 3) : Prop := *)
  (*   v0 <> v1 /\ v0 <> (-v1)%M. *)

  (* 两个不共线的单位向量确定了一个旋转。*)

  (* 由两个单位向量构造四元数 : (<u,v>, u × v)
       几何意义，该四元数的w分量是u,v夹角的余弦，向量分量是由u,v确定的垂直轴 *)
  Definition uv2q (u v : cvec 3) : quat := quat_of_s_v (<u,v>) (u × v).
  
  (* 由两个单位向量的乘法构造四元数 : (0,v) ⊗ (0,u)∗ 
       代数意义，两个四元数的乘积代表了一个四元数 *)
  Definition uv2q' (u v : cvec 3) : quat := (qpure v) * ((qpure u)∗).

  Open Scope fun_scope.

  (** 两种方式定义出的四元数相等，(0,v) ⊗ (0,u)∗ = (<u,v>,u × v) *)
  Lemma uv2q_eq_uv2q' : forall u v : cvec 3, uv2q u v = uv2q' u v.
  Proof. intros. lqa. Qed.

  (** 该四元数是单位四元数 cvunit u -> cvunit v -> qunit (uv2q u v) *)
  Lemma uv2q_qunit : forall u v : cvec 3,
      cvunit u -> cvunit v -> qunit (uv2q u v).
  Proof.
    intros. rewrite uv2q_eq_uv2q'. unfold uv2q'.
    apply qunit_qmul.
    apply qpure_qunit; auto.
    rewrite qconj_qunit. apply qpure_qunit; auto.
  Qed.

  (** 任给两个单位向量v0,v1，并由它们的夹角和垂直轴确定出一个四元数q，若将v1由q
        旋转后得到v2，则(v1,v2)所确定的四元数也等于q q *)
  Lemma uv2q_eq : forall (v0 v1 : cvec 3) (H0 : cvunit v0) (H1 : cvunit v1),
      let q : quat := uv2q v0 v1 in
      let v2 : cvec 3 := qrotv q v0 in
      uv2q v1 v2 = q.
  Proof.
    intros.
    rewrite uv2q_eq_uv2q'. unfold uv2q'. unfold v2. unfold qrotv.
    rewrite qpure_qim. unfold qrot. unfold q at 2.
    rewrite uv2q_eq_uv2q'. unfold uv2q'.
    rewrite qinv_qmul. rewrite !qinv_eq_qconj, !qconj_qconj.
    rewrite <- qmul_assoc. rewrite (qmul_assoc q _ _). rewrite qsqr_qpure; auto.
    rewrite qmul_assoc. rewrite qconj_qpure. rewrite qsqr_qpure.
    rewrite qmul_assoc. rewrite qsqr_qscalar. lqa.
    (* small things *)
    rewrite cvopp_cvunit; auto.
    all: try apply qpure_qunit; auto.
    rewrite cvopp_cvunit; rewrite qim_qpure; auto.
    apply qpure_neq0_iff. apply cvunit_neq0; auto.
    rewrite qconj_qpure. apply qpure_neq0_iff, cvunit_neq0, cvopp_cvunit; auto.
    rewrite qrot_qpure_w0; auto. unfold q. apply uv2q_qunit; auto.
  Qed.

  (** qrot对向量加法是线性的 *)
  Lemma qrot_linear_cvadd : forall (q : quat) (v1 v2 : cvec 3),
      (qrotv q (v1 + v2) == qrotv q v1 + qrotv q v2)%CV.
  Proof. lma. Qed.

  (** qrot对向量数乘是线性的 *)
  Lemma qrot_linear_cvcmul : forall (q : quat) (v : cvec 3) (k : R),
      (qrotv q (k c* v) == k c* (qrotv q v))%CV.
  Proof. lma. Qed.

  (* (** u × v = sin (cvangle u v) c* cvnormalize (u × v) *) *)
  (* Lemma cv3cross_eq_cmul : forall u v : cvec 3, *)
  (*     u × v == (sin (cvangle u v) c* cvnormalize (u × v))%CV. *)
  (* Proof. *)
  (*   intros. *)

  Lemma cv_eq_iff_len_parallel : forall {n} (v1 v2 : cvec n),
      ((||v1|| = ||v2||)%CV /\ v1 ∥ v2) <-> v1 == v2.
  Admitted.

  Lemma cv_eq_iff_len_angle0 : forall {n} (v1 v2 : cvec n),
      ((||v1|| = ||v2||)%CV /\ cvangle v1 v2 = 0) <-> v1 == v2.
  Admitted.
  
  (** 论证旋转，需要构造一些中间变量，所以逻辑有点绕 *)
  Section rotation_derivation.
    (* 任给旋转角θ(在[0,2π]), 旋转轴v，并按照轴角方式构造一个四元数 *)
    Variable θ : R.
    Variable v : cvec 3.
    Hypotheses Hbound_θ : 0 <= θ < 2 * PI.
    Hypotheses Hunit_v : cvunit v.
    Let q : quat := aa2quat (θ, v).
    (* (* 由于经常要用到 θ/2，所以定义给出记号 α *) *)
    (* Let α : R := θ / 2. *)
    (* 在以v为法线的平面上给出夹角为θ/2的两个3D单位向量v0,v1 *)
    Variable v0 v1 : cvec 3.
    Hypotheses Hunit_v0 : cvunit v0.
    Hypotheses Hunit_v1 : cvunit v1.
    Hypotheses Hnorm_v01_v : cvnormalize (v0 × v1) == v.
    Hypotheses Hangle_v01_θ : cvangle v0 v1 = θ/2.

    (** cos (θ / 2) = <v0,v1> *)
    Fact cos_θ2_cvdot01 : cos (θ / 2) = <v0,v1>.
    Proof.
      unfold cvangle in Hangle_v01_θ.
      rewrite <- Hangle_v01_θ. rewrite cos_acos.
      rewrite !cvnormalize_cvunit_fixpoint; auto.
      apply cvdot_vnormalize_bound; apply cvunit_neq0; auto.
    Qed.

    (** 0 <= sin (θ/2) *)
    Fact sin_θ2_ge0 : 0 <= sin (θ/2).
    Proof. rewrite <- Hangle_v01_θ. apply sin_cvangle_ge0. Qed.

    (** v1 ∥ v2 -> (a c* v1) ∥ v2 *)
    Lemma cvcmul_cvparallel_l : forall {n} (v1 v2 : cvec n) (a : R),
        v1 ∥ v2 -> a <> 0 -> (a c* v1)%CV ∥ v2.
    Proof.
      intros. unfold cvparallel in *. destruct H as [k [H1 H2]].
      exists (k/a). split.
      - unfold Rdiv.
        apply Rmult_integral_contrapositive_currified; auto.
        apply Rinv_neq_0_compat; auto.
      - rewrite cvcmul_assoc.
        replace (k / a * a)%A with k; auto. cbv. field; auto.
    Qed.

    (** v1 ∥ v2 -> v1 ∥ (a c* v2) *)
    Lemma cvcmul_cvparallel_r : forall {n} (v1 v2 : cvec n) (a : R),
        v1 ∥ v2 -> a <> 0 -> v1 ∥ (a c* v2)%CV.
    Proof.
      intros. apply cvparallel_sym. apply cvcmul_cvparallel_l; auto.
      apply cvparallel_sym; auto.
    Qed.

    (** 0 / a = 0 *)
    Lemma Rdiv_0_eq0 : forall a : R, a <> 0 -> 0 / a = 0.
    Proof. intros. field; auto. Qed.

    Hint Rewrite Rdiv_0_eq0 : R.

    (** || cvec0 || = 0 *)
    Lemma cvlen_cvec0: forall {n : nat}, (|| @cvec0 n ||)%CV = 0.
    Proof. intros. apply cvlen_eq0_iff_eq0. lma. Qed.

    (** θ = 0 <-> v0 = v1 *)
    Fact θ0_v0_eq_v1 : θ = 0 <-> v0 == v1.
    Proof.
      split; intros.
      - apply cv_eq_iff_len_angle0; ra. rewrite !cvlen_cvunit; ra.
      - apply cv_eq_iff_len_angle0 in H; ra.
    Qed.

    (** sin (θ/2) = 0 -> θ = 0 *)
    Fact sin_θ2_eq0_θ0 : sin (θ/2) = 0 <-> θ = 0.
    Proof.
      split; intros H.
      - apply sin_eq_O_2PI_0 in H; ra.
      - apply sin_eq_O_2PI_1; ra.
    Qed.
                               
    (** sin (θ/2) ≠ 0 -> θ ≠ 0 *)
    Fact sin_θ2_neq0_θ_neq0 : sin (θ/2) <> 0 <-> θ <> 0.
    Proof. split; intros H; intro; apply sin_θ2_eq0_θ0 in H0; auto. Qed.
                               
    (** θ = 0 <-> ||v0×v1|| = 0 *)
    Fact θ0_v01_cross_len0 : θ = 0 <-> (||v0 × v1|| = 0)%CV.
    Proof.
      split; intros.
      - rewrite cvlen_cv3cross. rewrite 2!cvlen_cvunit; auto.
        rewrite Hangle_v01_θ. replace (θ / 2) with 0; ra. autorewrite with R; auto.
      - rewrite cvlen_cv3cross in H. rewrite 2!cvlen_cvunit in H; auto.
        rewrite Hangle_v01_θ in H. assert (sin (θ/2) = 0); ra.
        apply sin_eq_O_2PI_0 in H0; ra.
    Qed.

    (** a <> 0 -> (a c* v1) ∠ v2 = v1 ∠ v2 *)
    Lemma cvcmul_keep_cvangle_l : forall {n} (v1 v2 : cvec n) (a : R),
        a <> 0 -> (a c* v1)%CV ∠ v2 = v1 ∠ v2.
    Proof.
    Admitted.

    (** a <> 0 -> v1 ∠ (a c* v2) = v1 ∠ v2 *)
    Lemma cvcmul_keep_cvangle_r : forall {n} (v1 v2 : cvec n) (a : R),
        a <> 0 -> v1 ∠ (a c* v2)%CV = v1 ∠ v2.
    Proof.
    Admitted.

    Check cvnormalize_direction.

    Lemma cvnormalize_keep_angle_l : forall {n} (v1 v2 : cvec n),
        cvnormalize v1 ∠ v2 = v1 ∠ v2.
    Admitted.
    Lemma cvnormalize_keep_angle_r : forall {n} (v1 v2 : cvec n),
        v1 ∠ cvnormalize v2 = v1 ∠ v2.
    Admitted.

    Lemma cvangle_same_eq0 : forall {n} (v : cvec n), v ∠ v = 0.
    Admitted.

    
    (** θ = 0 <-> v0 × v1 = cvec0 *)
    Fact θ0_iff_cross_eq0 : θ = 0 <-> v0 × v1 == cvec0.
    Proof.
      split; intros.
      - apply θ0_v01_cross_len0 in H. apply cvlen_eq0_iff_eq0 in H; auto.
      - apply cvlen_eq0_iff_eq0 in H. apply θ0_v01_cross_len0; auto.
    Qed.
        
    (** sin (θ/2) * v = v0 × v1 *)
    Fact sin_θ2_cmul_eq_cross : (sin (θ / 2) c* v)%CV == v0 × v1.
    Proof.
      bdestruct (θ =? 0).
      - rewrite H. autorewrite with R; auto. rewrite cvcmul_0_l.
        apply θ0_iff_cross_eq0 in H. symmetry; auto.
      - apply cv_eq_iff_len_angle0.
        rewrite cvlen_cv3cross.
        rewrite cvlen_cmul. rewrite !cvlen_cvunit; auto.
        rewrite Hangle_v01_θ. rewrite Rabs_pos_eq. split; try ring.
        rewrite cvcmul_keep_cvangle_l. rewrite <- Hnorm_v01_v.
        rewrite cvnormalize_keep_angle_l. apply cvangle_same_eq0.
        apply sin_θ2_neq0_θ_neq0; auto. apply sin_θ2_ge0.
    Qed.

    ?

    (** q = (<v0,v1>, v0 × v1) *)
    Lemma q_eq_uv2q : q = uv2q v0 v1.
    Proof.
      unfold q. unfold aa2quat. unfold uv2q. f_equiv.
      - apply cos_θ2_cvdot01.
      - apply cv_eq_by_len_parallel.
        rewrite cvlen_cv3cross.
        rewrite cvlen_cmul. rewrite !cvlen_cvunit; auto.
        rewrite Hangle_v01_θ. rewrite Rabs_pos_eq. ring. apply sin_θ2_ge0.
        ?
        ring.
        ; try apply sin_θ2_ge0. 
        rewrite 
        Search cvlen.

        f_equiv.
      assert (cos (θ / 2) = <v0,v1>).
      { unfold cvangle in Hangle_v0_v1_θ.
        rewrite <- Hangle_v0_v1_θ. rewrite cos_acos.
        rewrite !cvnormalize_cvunit_fixpoint; auto.
        apply cvdot_vnormalize_bound; apply cvunit_neq0; auto. }
      assert ((sin (θ / 2) c* v)%CV == (v0 × v1)).
      { Search cvparallel.
      admit.
      rewrite H. rewrite H0. auto.
    Qed.
                               
                               f_equiv.
      - 
      -
        Search cv3cross.

        sin (cvangle v0 v1) c* cvnormalize (v0 × v1) = v0 × v1.
        Search (-1 <= _ <= 1).
        Search cvnormalize.
        
        un
          
          
          
          
          (* (* v0到v1的角度 *) *)
          (* Let θ : R := 2 * cos (cvangle v0 v1). *)
          (* (* v0,v1平面的法向量 *) *)
          (* Let v : cvec 3 := cvnormalize (v0 × v1). *)
          
          (* 构造出四元数 q，它的w分量是<v0,v1>, 向量分量是v0 × v1，具有一定的几何意义 *)
          Let q : quat := uv2q v0 v1.
        (* 用 q 来旋转 v0 得到 v2 *)
        Let v2 : cvec 3 := qrotv q v0.
        (* 用 q 来旋转 v1 得到 v3 *)
        Let v3 : cvec 3 := qrotv q v1.

        (** q 是单位向量 *)
        Lemma q_qunit : qunit q.
        Proof. unfold q. apply uv2q_qunit; auto. Qed.

        (** qrot 的输出是单位向量 *)
        Lemma qrot_cvunit : forall (v : cvec 3), cvunit v -> qunit (qrot q (qpure v)).
        Proof. intros. apply qrot_qpure_qunit; auto. apply q_qunit. Qed.

        (** *** 1. 证明 (v1,v2) 与 (v0,v1) 的几何关系 *)
        
        (** v2 是单位向量，即长度不变 *)
        Lemma v2_cvunit : cvunit v2.
        Proof. unfold v2. apply qrot_qpure_cvunit; auto. apply q_qunit. Qed.

        (** 由 v1,v2 构造的四元数等于 q *)
        Lemma v12_eq_q : uv2q v1 v2 = q.
        Proof. apply uv2q_eq; auto. Qed.

        (** <v1,v2> = <v0,v1>，保持点积 *)
        Lemma v12_v01_keep_cvdot : <v1,v2> = <v0,v1>.
        Proof.
          intros. pose proof (v12_eq_q). unfold q in H. unfold uv2q in *. 
          apply quat_of_s_v_inj in H. destruct H; auto.
        Qed.

        (** (v1,v2)和(v0,v1)的这两个夹角相同 *)
        Lemma v12_v01_same_angle : cvangle v1 v2 = cvangle v0 v1.
        Proof.
          unfold cvangle. f_equal. rewrite !cvnormalize_cvunit_fixpoint; auto.
          apply v12_v01_keep_cvdot. apply v2_cvunit.
        Qed.
        
        (** (v0,v2) 的夹角是 2θ，待证明... *)

        (** v1 × v2 = v0 × v1, 表明(v1,v2)和(v0,v1)所确定的垂直轴相同 *)
        Lemma v12_v01_keep_cvcross : v1 × v2 == v0 × v1.
        Proof.
          intros. pose proof (v12_eq_q). unfold q in H. unfold uv2q in *. 
          apply quat_of_s_v_inj in H. destruct H; auto.
        Qed.

        (** v0,v1,v2 共面 *)
        Lemma v012_coplanar : cv3coplanar v0 v1 v2.
        Proof.
          apply cv3cross_same_cv3coplanar. symmetry. apply v12_v01_keep_cvcross.
        Qed.
        
        (** *** 2. 证明 (v2,v3) 与 (v1,v2) 的几何关系 *)
        
        (** v3 是单位向量，即长度不变 *)
        Lemma v3_cvunit : cvunit v3.
        Proof. unfold v3. apply qrot_qpure_cvunit; auto. apply q_qunit. Qed.

        (** 由 v2,v3 构造的四元数等于 q *)
        Lemma v23_eq_q : uv2q v2 v3 = q.
        Proof.
          pose proof (uv2q_eq v1 v2 H1 v2_cvunit) as H; simpl in H.
          unfold v3. rewrite v12_eq_q in H. auto.
        Qed.

        (** <v2,v3> = <v1,v2>，保持点积 *)
        Lemma v23_v12_keep_cvdot : <v2,v3> = <v1,v2>.
        Proof.
          intros. pose proof (v23_eq_q). rewrite <- v12_eq_q in H.
          unfold uv2q in *. apply quat_of_s_v_inj in H. destruct H; auto.
        Qed.

        (** (v2,v3)和(v1,v2)的这两个夹角相同 *)
        Lemma v23_v12_same_angle : cvangle v2 v3 = cvangle v1 v2.
        Proof.
          unfold cvangle. f_equal. rewrite !cvnormalize_cvunit_fixpoint; auto.
          apply v23_v12_keep_cvdot. apply v3_cvunit. apply v2_cvunit.
        Qed.

        (** (v1,v3) 的夹角是 2θ，待证明... *)
        
        (** v2 × v3 = v1 × v2, 表明(v2,v3)和(v1,v2)所确定的垂直轴相同 *)
        Lemma v23_v12_keep_cvcross : v2 × v3 == v1 × v2.
        Proof.
          intros. pose proof (v23_eq_q). rewrite <- v12_eq_q in H.
          unfold uv2q in *. apply quat_of_s_v_inj in H. destruct H; auto.
        Qed.

        (** v1,v2,v3 共面 *)
        Lemma v123_coplanar : cv3coplanar v1 v2 v3.
        Proof.
          apply cv3cross_same_cv3coplanar. symmetry. apply v23_v12_keep_cvcross.
        Qed.

        (** *** 3. 证明 q 与 v 的几何关系 *)

        (** q ⊗ [0,v] = [0,v] ⊗ q *)
        Lemma qv_eq_vq : q * qpure v = qpure v * q.
        Proof.
          unfold v.
        Admitted.
        
        (** 使用 q 对 v 旋转，不改变 q。即, v 是旋转轴 *)
        Lemma v_unchanged : qrot q (qpure v) = qpure v.
        Proof.
          unfold qrot. rewrite qv_eq_vq. rewrite qmul_assoc.
          rewrite qmul_qinv_r. apply qmul_1_r. apply qunit_neq0. apply q_qunit.
        Qed.
        
        (** *** 4. 证明 q 与任意向量 vt 的几何关系 *)
        Section main_theorem_analysis.
          
          (* 由于v0,v1,v2是线性无关的一组基，所以任意向量vt都可以由它们线性表出。
           这里跳过了这部分理论的论证。
           假设用(v0,v1,v)和给定的一组系数(s0,s1,s2)表出了一个向量 *)
          Variable s0 s1 s2 : R.
          Let vt : cvec 3 := (s0 c* v0 + s1 c* v1 + s2 c* v)%CV.
          (* 假设 vt 被 qrot 作用后成为了 vt' *)
          Let vt' : cvec 3 := qrotv q vt.
          (* 定义 θ 的一半为 alpha *)
          Let α : R := θ / 2.

          (** 我们证明如下结论：
            (1) (vt,vt')的夹角是2θ
            (2) (vt,vt')的法向量是v
            (3) vt和vt'的长度相等
            这三个条件同时满足，则说明了 qrot 将 vt 绕 v 轴旋转了 2θ 度，到达 vt'。
            令 α = 2θ ，则说明qrot将 vt 绕 v 轴旋转了 α 度后到达 vt'。
            所以，单位四元数旋转公式
                [0 v'] = qrot (q, v) = q ⊗ [0 v] ⊗ q∗
            表达式了我们想要的旋转。
           *)
          
          (** (vt,vt')的夹角是α *)
          Lemma qrot_any_imply_angle : cvangle vt vt' = α.
          Proof.
          Admitted.
          
          (** (vt,vt')的法向量是v *)
          Lemma qrot_any_imply_n : vt × vt' == v.
          Proof.
          Admitted.
          
          (** vt和vt'的长度相等 *)
          Lemma qrot_any_imply_len : (||vt'|| = ||vt||)%CV.
          Proof.
          Admitted.
          
        End main_theorem_analysis.

  End rotation_spec.
  
  (** 四元数乘法能表示旋转 *)
  Theorem qrot_valid : forall (v0 v1 : cvec 3) (s0 s1 s2 : R) (α : R) (v : cvec 3),
      let q : quat := aa2quat (α/2, v) in
      let vt : cvec 3 := (s0 c* v0 + s1 c* v1 + s2 c* v)%CV in
      let vt' : cvec 3 := qrotv q vt in
      cvunit v0 -> cvunit v1 ->
      cvangle vt vt' = α /\ vt × vt' == v /\ (||vt'|| = ||vt||)%CV.
  Proof.
    intros. split.
    - pose proof (qrot_any_imply_angle v0 v1 H H0 s0 s1 s2).
      unfold vt. ?
                   rewrite H1.
      Check vt.
      
      rewrite qrot_any_imply_angle.
  Admitted.

End spec2.

(** 方法3：Dunn 中提到的 *)
Section spec3.
(* 我们想知道，最初是如何发现这个旋转操作的。
       在 8.7.3 将根据几何关系推导从四元数到矩阵形式的转换 *)

End spec3.

End qrot.


(** ** Dot product of quaternion *)
Section qdot.

  Definition qdot (q1 q2 : quat) : quat :=
    mk_quat (q1.W * q1.W) (q1.X * q2.X) (q1.Y * q2.Y) (q1.Z * q2.Z).
  
End qdot.


(** ** Logrithm of quaternion *)
Section qlog.

  (* Definition qlog (q : quat) : quat := *)
  (*   let a := quat_to_aa q in *)
  (*   let θ : R := aa_angle a in *)
  (*   let n : cvec 3 := aa_axis a in *)
  (*   let α : R := θ / 2 in *)
  (*   quat_of_s_v 0 (α c* n)%CV. *)
  Parameter qlog : quat -> quat.

End qlog.


(** ** Exponential of quaternion *)
Section qexp.

  (* Definition qexp (q : quat) : quat := *)
  (*   let a := quat_to_aa q in *)
  (*   quat_of_aa a. *)
  Parameter qexp : quat -> quat.

  (* Lemma qexp_qlog : forall a : axisangle, *)
  (*     qexp  *)
  Axiom qexp_qlog : forall q : quat, qexp (qlog q) = q.

End qexp.

(** ** Exponentiation of quaternion *)
Section qpower.

  (* 四元数被取幂，含义是：当 t 从 0 变换到 1 时，q^t 从 qone 变化到 q *)
  (* 例如，若 q 表示绕 x 顺时针转 30度，则 q^2 表示绕 x 顺时针转 60度，q^{-1/3} 表示
     绕 x 逆时针转 10度。在此语境下，qinv 与 q^{-1} 是一致的。*)

  (* 另外，四元数使用最短弧表示角位移，无法表示多圈旋转。实际上四元数只捕获最终结果。
     某些情况，我们关心旋转的总量，而不仅是最终结果（例如角速度）。
     此时，四元数不是正确的工具，可使用指数映射，或轴角格式。*)
  
  Definition qpower' (q : quat) (t : R) : quat := qexp (t c* qlog q).

  (* 理解 q^t 的插值（Interpolate）为什么会从qone到q。
     对数运算实际上将四元数转换为指数映射格式（except因子2）。
     当用 t c* q 时，效果是角度乘以 t，
     当用 exp q 时，“撤销”对数运算所做的事，从指数矢量重新计算新的 w 和 v。 *)

  (* 虽然 qpow 的公式是正式的数学定义，并在理论上很优雅，但直接转为代码则很复杂。
     以下是如何在C语言中计算 q^t 的值，并没有按公式那样使用单个指数映射，而是
     分别计算了轴和角。

     // 要插值的四元数
     float w, x, y, z;
     // 指数
     float exponent;
     // 检查四元数，防止除零
     if (fabs(w) < 0.9999f) {
        // 提取半角 alpha = theta / 2
        float alpha = acos (w);
        // 计算新的 alpha 值
        float newAlpha = alpha * exponent;
        // 计算新的 w 值
        w = cos (newAlpha);
        // 计算新的xyz值
        float mult = sin(newAlpha) / sin(alpha);
        x *= mult;
        y *= mult;
        z *= mult;
     }

     注意，上述代码中，检查四元数单位元（即 [1 0 0 0] ）是必要的，因为 w = ±1 的值导致
     alpha 为 0 或 π，sin(alpha) 得到0，将导致 mult 的除数为0。
     由于四元素单位元的任何幂次还是它，所以忽略即可。
     另外，计算 alpha 时，使用的是 acos 函数，它返回一个正角度，这没有问题。*)

  Definition qpower (q : quat) (exponent : R) : quat :=
    if (Rabs (q.X) <? 0.9999)
    then
      (let alpha : R := acos (q.W) in
       let newAlpha : R := (alpha * exponent)%R in
       let mult : R := (sin newAlpha) / (sin alpha) in
       mk_quat (cos newAlpha) (q.X * mult) (q.Y * mult) (q.Z * mult))
    else q.
  
End qpower.


(** ** Spherical Linear Interpolation 球面线性插值 *)
Section qslerp.
  (* 标准线性插值（Lerp, Linear Interpolation）公式：
     lerp(q0,q1,t) = q0 + t * (q1 - q0)
     三个步骤：
     1. 计算差值 Δq = f(q0,q1)
     2. 计算差值的一部分 q' = g(Δq,t)
     3. 根据原始值和插值的这部分来调整 h(q0, q')
   *)
  
  (* 四元数的存在还有一个理由，球面线性插值。它允许在两个朝向之间平滑插值。
     Slerp避免了困扰欧拉角插值的所有问题。
     函数 slerp(q0,q1,t) 将根据t从0到1的变化返回从 q0 到 q1 插值的朝向。
     可以使用与线性插值相同的思路来推导 Slerp：
     1. 计算 q0 到 q1 的角位移：Δq = q1 * q0⁻¹
     2. 使用四元数指数，计算这个插值的一部分：(Δq)^t
     3. 使用四元素乘法来调整初始值：(Δq)^t * q0
     所以，理论上的四元数 Slerp 公式：slerp(q0,q1,t) = (q1 * q0⁻¹)^t * q0 *)

  (* 在实践中，使用数学上等效，但计算上更有效的公式（不使用指数，而是另一个直接的公式）。
     为推导这个替代公式，首先将四元数解释为存在于四维欧几里得空间中。
     我们感兴趣的所有四元数都是单位四元数，所以它们位于四维超球面(Hypersphere)上。
     基本思想是绕连接两个四元数的弧进行插值。这两个弧沿着四维超球面，所以
     称为球面线性插值。*)

  (* 实际的四元数Slerp公式：
     slerp(q0,q1,t) = [sin(1-t)ω / sin ω] q0 + [sin tω / sin ω] q1
     剩下的问题是，计算 ω (两个四元数之间的“角度”）。可将四元数点积视为返回的 cos ω。
     
     还有两个问题要考虑：
     1. 四元数 q 和 -q 表示相同的方向，但在 slerp 时产生不同的结果。
        该问题在2D和3D不会发生，而在4维超球面中。。。解决方案是选择 q0 和 q1 的符号，
        使得点积非负。结果是始终选择从 q0 到 q1 的最短旋转弧。
     2. 当 q0 和 q1 很接近时，ω很小，所以 sin ω 很小，可能导致除零问题。
        此时，若 sin ω很小，则使用简单的线性插值。
   *)

  (** 将作者给出的C语言程序转换为Coq程序。*)

  (* 计算四元数之间的“角度的余弦”，并处理符号问题 *)
  Definition qslerp_cosOmega (q0 q1 : quat) : quat * quat * R :=
    (* 使用点积计算两个四元数之间的“角度的余弦” *)
    let cosOmega : R := (q0.W * q1.W + q0.X * q1.X + q0.Y * q1.Y + q0.Z * q1.Z)%R in
    (* 若点积为负，则将其中一个输入的四元数变负，以取得最短四维“弧” *)
    if (cosOmega <? 0)
    then (q0, -q1, (-cosOmega)%R)
    else (q0, q1, cosOmega).

  (* 计算插值参数 k0,k1 *)
  Definition qslerp_parameter (q0 q1 : quat) (cosOmega : R) (t : R) : R * R :=
    (* 检查是否很接近，若是则使用线性插值，避免除零 *)
    if (cosOmega >? 0.9999)
    then (
        let k0 : R := (1 - t)%R in
        let k1 : R := t in
        (k0, k1))
    else (
        (* 计算角度的正弦 *)
        let sinOmega : R := sqrt (1 - cosOmega * cosOmega) in
        (* 根据正弦和余弦计算角度 *)
        let omega : R := atan2 sinOmega cosOmega in
        (* 计算分母的倒数 *)
        let oneOverSinOmega : R := 1 / sinOmega in
        let k0 : R := (sin ((1 - t) * omega) * oneOverSinOmega)%R in
        let k1 : R := (sin (t * omega) * oneOverSinOmega)%R in
        (k0, k1)).
  
  Definition qslerp (q0 q1 : quat) (t : R) : quat :=
    (* 计算角度的余弦 *)
    let '(q0,q1,cosOmega) := qslerp_cosOmega q0 q1 in
    (* 计算插值参数 *)
    let '(k0, k1) := qslerp_parameter q0 q1 cosOmega t in
    (* 插值 *)
    let w := (q0.W * k0 + q1.W * k1)%R in
    let x := (q0.X * k0 + q1.X * k1)%R in
    let y := (q0.Y * k0 + q1.Y * k1)%R in
    let z := (q0.Z * k0 + q1.Z * k1)%R in
    mk_quat w x y z.

End qslerp.


(** ** 四元数与旋转矩阵 *)


(* Extract Constant Rabst => "__". *)
(* Extract Constant Rrepr => "__". *)
(* Extraction "quat.ml" mk_mat_3_1. (* Why so many warning? *) *)
(* Recursive Extraction mk_quat quat_of_wxyz quat_of_t4 qmul qconj qinv qlen rot_by_quat. *)
(* Extraction "quat.ml" mk_quat quat_of_wxyz quat_of_t4 qmul qconj qinv. qlen rot_by_quat. *)
