(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Quaternion
  author    : ZhengPu Shi
  date      : 2022.06

  remark    :
  1. Introduction to Multicopter Design and Control, Springer, Quan Quan, page 96
  2. quat:{w,x,y,z} <==> vec4[w;x;y;z]
                    <==> vec3[x;y;z]
 *)

Require Export VectorR.

Open Scope R.
Open Scope mat_scope.
Open Scope cvec_scope.

(** Scope for quaternion *)
Declare Scope quat_scope.
Delimit Scope quat_scope with q.
Open Scope quat_scope.


(* ######################################################################### *)
(** * Axis-Angle method *)

(** Axis-Angle representation. (aa: means Axis-Angle) *)
Record axisangle :=
  mk_axisangle {
      aa_angle : R;
      aa_axis : cvec 3; (* should be a unit vector *)
    }.


(* ######################################################################### *)
(** * Definition of Quaternion *)

Section def.

  (** A quaternion q = w + x i + y j + z k, can be considered as a linear 
    combination with the basis of {1, i, j, k} *)
  Record quat : Type := mk_quat { W : R; X : R; Y : R; Z : R }.

  Bind Scope quat_scope with quat.
End def.

Notation "q .W" := (W q) (at level 30, format "q .W") : quat_scope.
Notation "q .X" := (X q) (at level 30, format "q .X") : quat_scope.
Notation "q .Y" := (Y q) (at level 30, format "q .Y") : quat_scope.
Notation "q .Z" := (Z q) (at level 30, format "q .Z") : quat_scope.

(** Construction. *)
Section construction.
  
  (** Get the component of a given quaternion number q *)
  Definition Re (q : quat) : R := q.W.
  Definition Im1 (q : quat) : R := q.X.
  Definition Im2 (q : quat) : R := q.Y.
  Definition Im3 (q : quat) : R := q.Z.
  
  Definition Im (q : quat) : cvec 3 := l2cv [q.X; q.Y; q.Z].
  Notation "q .Im" := (Im q) (at level 30, format "q .Im") : quat_scope.
  
  Lemma quat_eq_iff : forall (q1 q2 : quat),
      q1 = q2 <-> (q1.W = q2.W /\ q1.X = q2.X /\ q1.Y = q2.Y /\ q1.Z = q2.Z).
  Proof.
    intros. split; intros; subst; auto.
    do 3 destruct H as [? H]. destruct q1,q2; simpl in *. f_equal; auto.
  Qed.

  Lemma quat_neq_iff : forall (q1 q2 : quat),
      q1 <> q2 <-> (q1.W <> q2.W \/ q1.X <> q2.X \/ q1.Y <> q2.Y \/ q1.Z <> q2.Z).
  Proof.
    intros. split; intros.
    - rewrite quat_eq_iff in H. lra.
    - intro. subst. lra.
  Qed.

  (** Construct a quaternion by 4 scalar number *)
  Definition quat_of_ssss (w x y z : R) : quat := mk_quat w x y z.

  Lemma quat_of_ssss_ok : forall w x y z,
      let q := quat_of_ssss w x y z in
      q.W = w /\ q.X = x  /\ q.Y = y /\ q.Z = z.
  Proof. intros. split; auto. Qed.

  (** Construct a quaternion by a scalar number and a 3-dim vector *)
  Definition quat_of_s_v (w : R) (v : cvec 3) := mk_quat w (v.0) (v.1) (v.2).

  Lemma quat_of_s_v_ok : forall w v,
      let q := quat_of_s_v w v in
      q.W = w /\ q.X = v.0  /\ q.Y = v.1 /\ q.Z = v.2.
  Proof. intros. split; auto. Qed.

  (** Construct a quaternion by a scalar number *)
  Definition quat_of_s (w : R) : quat := mk_quat w 0 0 0.
  
  Lemma quat_of_s_ok : forall w,
      let q := quat_of_s w in
      q.W = w /\ q.X = R0 /\ q.Y = R0 /\ q.Z = R0.
  Proof. intros. cbv. auto. Qed.

  (** Construct a quaternion by a 3-dim vector *)
  Definition quat_of_v3 (v : cvec 3) : quat := quat_of_s_v 0 v.
  
  Lemma quat_of_v3_ok : forall v,
      let q := quat_of_v3 v in
      q.W = R0 /\ q.X = v.0 /\ q.Y = v.1 /\ q.Z = v.2.
  Proof. intros. apply quat_of_s_v_ok. Qed.
  
  (** Construct a quaternion by a vec4[w;x;y;z] *)
  Definition cv2q (v : cvec 4) : quat := mk_quat (v.0) (v.1) (v.2) (v.3).
  
  Lemma cv2q_ok : forall v,
      let q := cv2q v in
      q.W = v.0 /\ q.X = v.1 /\ q.Y = v.2 /\ q.Z = v.3.
  Proof. intros. cbv. auto. Qed.
  
  (** Quaternion to vec4[w;x;y;z] *)
  Definition q2cv (q : quat) : cvec 4 := l2cv [q.W; q.X; q.Y; q.Z].
  
  Lemma q2cv_ok : forall q,
      let v := q2cv q in
      v.0 = q.W /\ v.1 = q.X /\ v.2 = q.Y /\ v.3 = q.Z.
  Proof. intros. cbv. auto. Qed.

  (** Construction a quaternion from axis-angle. *)
  Definition quat_of_aa (a : axisangle) : quat :=
    let n := aa_axis a in
    let θ := aa_angle a in
    let s2 := sin (θ/2) in
    let c2 := cos (θ/2) in
    quat_of_s_v c2 (l2cv [s2 * n.0; s2 * n.1; s2 * n.2]%R).

End construction.

Notation "q .Im" := (Im q) (at level 30, format "q .Im") : quat_scope.


(* ######################################################################### *)
(** * Customized tactic / tactical for proof *)

(** Linear Quaternion Algebra, q1 = q2. *)
Ltac lqa (* tac *) :=
  cbv; f_equal; ra.


(* ######################################################################### *)
(** * Quaternion operations *)

(** ** Quaternion addition 四元数加法 *)
Section qadd.
  
  Definition qadd (q1 q2 : quat) : quat :=
    mk_quat (q1.W + q2.W) (q1.X + q2.X) (q1.Y + q2.Y) (q1.Z + q2.Z).
  Notation "p + q" := (qadd p q) : quat_scope.

End qadd.
Notation "p + q" := (qadd p q) : quat_scope.


(** ** Quaternion negation 四元数取负 *)
Section qopp.
  
  Definition qopp (q : quat) : quat := mk_quat (- q.W) (- q.X) (- q.Y) (- q.Z).
  Notation "- q" := (qopp q) : quat_scope.

End qopp.
Notation "- q" := (qopp q) : quat_scope.


(** ** Quaternion subtraction 四元数减法 *)
Section qsub.
  
  Definition qsub (q1 q2 : quat) : quat := qadd q1 (qopp q2).
  Notation "p - q" := (qsub p q) : quat_scope.
  
End qsub.
Notation "p - q" := (qsub p q) : quat_scope.


(** ** Quaternion multiplication *)
Section qmul.

  (* Also called "Hamilton product" *)
  Definition qmul (q1 q2 : quat) : quat :=
    mk_quat
      (q1.W * q2.W - q1.X * q2.X - q1.Y * q2.Y - q1.Z * q2.Z)
      (q1.W * q2.X + q1.X * q2.W + q1.Y * q2.Z - q1.Z * q2.Y) 
      (q1.W * q2.Y - q1.X * q2.Z + q1.Y * q2.W + q1.Z * q2.X) 
      (q1.W * q2.Z + q1.X * q2.Y - q1.Y * q2.X + q1.Z * q2.W).
  
  Notation "p * q" := (qmul p q) : quat_scope.

  (** Multiplication of two quaternions by vector form，(p96)
                |pw|   |qw|   |   pw qw - <pv,qv>      |
        p * q = |pv| + |qv| = |pv × qv + pw qv + qw pv | *)
  Definition qmulVEC (p q : quat) : quat :=
    quat_of_s_v
      (p.W * q.W - <p.Im, q.Im>)
      (p.Im × q.Im + p.W c* q.Im + q.W c* p.Im)%M.

  Lemma qmulVEC_eq_qmul (p q : quat) : qmulVEC p q = p * q.
  Proof. destruct p, q. lqa. Qed.

  (** Quaternion multiplication with PLUS form. page96, p+ *)
  Definition qPLUS (q : quat) : mat 4 4 :=
    let m1 : mat 4 4 := (q.W c* mat1)%M in
    let m2a : mat 1 4 := mconsc (mk_mat_1_1 0) (-(q.Im\T))%M in
    let m2b : mat 3 4 := mconsc (q.Im) (cv3skew (q.Im)) in
    let m2 : mat 4 4 := mconsr m2a m2b in
    (m1 + m2)%M.

  Definition qmulPLUS (p q : quat) : quat :=
    cv2q ((qPLUS p) * (q2cv q))%M.

  Lemma qmulPLUS_correct (p q : quat) : p * q = qmulPLUS p q.
  Proof. destruct p, q. lqa. Qed.

  (** Quaternion multiplication with MINUS form. page96, p- *)
  Definition qMINUS (q : quat) : mat 4 4 :=
    let m1 : mat 4 4 := (q.W c* mat1)%M in
    let m2a : mat 1 4 := mconsc (mk_mat_1_1 0) (-(q.Im\T))%M in
    let m2b : mat 3 4 := mconsc (q.Im) (-(cv3skew (q.Im)))%M in
    let m2 : mat 4 4 := mconsr m2a m2b in
    (m1 + m2)%M.

  Definition qmulMINUS (p q : quat) :=
    cv2q ((qMINUS q) * (q2cv p))%M.

  Lemma qmulMINUS_correct (p q : quat) : p * q = qmulMINUS p q.
  Proof. destruct p, q. lqa. Qed.

  (** (q * r) * m = q * (r * m) *)
  Lemma qmul_assoc (q r m : quat) : (q * r) * m = q * (r * m).
  Proof. destruct q,r,m. lqa. Qed.

  (** The multiplication is non-commutative. That is: p * q <> q * p. *)
  Lemma qmul_not_comm : exists (p q : quat), p * q <> q * p.
  Proof.
    exists (quat_of_ssss 0 1 2 1).
    exists (quat_of_ssss 0 2 1 2).
    cbv. intros. inversion H. lra.
  Qed.
  
  (** q * (r + m) = q * r + q * m *)
  Lemma qmul_qadd_distr_l (q r m : quat) : q * (r + m) = q * r + q * m.
  Proof. destruct q,r,m. lqa. Qed.

  (** (r + m) * q = r * q + m * q *)
  Lemma qmul_qadd_distr_r (r m q : quat) : (r + m) * q = r * q + m * q.
  Proof. destruct r,m,q. lqa. Qed.

  (** multplication of two pure quaternions: (0,u) * (0,v) = (-<u,v>, u × v)  *)
  Lemma qmul_vec3 (u v : cvec 3) :
    (quat_of_v3 u) * (quat_of_v3 v) = quat_of_s_v (- <u,v>) (u × v).
  Proof. lqa. Qed.

  (** Left scalar multiplication *)
  Definition qcmul (s : R) (q : quat) : quat := (quat_of_s s) * q.
  Notation "a c* q" := (qcmul a q) : quat_scope.

  (** 1 c* q = q *)
  Lemma qcmul_1_l : forall q : quat, 1 c* q = q.
  Proof. intros. destruct q. lqa. Qed.

  (** Right scalar multiplication *)
  Definition qmulc (q : quat) (s : R) : quat := q * (quat_of_s s).
  Notation "q *c a" := (qmulc q a) : quat_scope.

  (* s * q = q * s *)
  Lemma qcmul_eq_qmulc (s : R) (q : quat) : s c* q = q *c s.
  Proof. destruct q. lqa. Qed.

End qmul.

Notation "p * q" := (qmul p q) : quat_scope.
Notation "a c* q" := (qcmul a q) : quat_scope.
Notation "q *c a" := (qmulc q a) : quat_scope.


(** ** Zero quaternion 零四元数 *)
Section qzero.

  Definition qzero : quat := mk_quat 0 0 0 0.

End qzero.


(** ** Identity quaternion 恒等四元数 *)
Section qone.

  (** 恒定四元数：角位移为0的四元数（因为角位移就是朝向的变换，所以这里就是恒等元）

    几何上有两个恒等四元数：[0̂ 1] 和 [0̂ -1]
    当 θ 是 2π 的偶数倍时，cos (θ/2) = 1, sin(θ/2) = 0, n̂是任意值
    当 θ 是 2π 的奇数倍时，cos (θ/2) = -1, sin(θ/2) = 0, n̂是任意值
    直观上，若旋转角度是绕任何轴转完整的整数圈，则在三维中方向上不会有任何实际的改变。

    代数上只有一个恒等四元数 [0̂ 1]。因为要求任意 q 乘以单位元后不变。
   *)
  Definition qone : quat := mk_quat 1 0 0 0.

  (** 1 * q = q *)
  Lemma qmul_1_l : forall q : quat, qone * q = q.
  Proof. intros. destruct q. lqa. Qed.

  (** q * 1 = q *)
  Lemma qmul_1_r : forall q : quat, q * qone = q.
  Proof. intros. destruct q. lqa. Qed.

  (** ToDo: 这里最好再证明一下 qone 和 - qone 这二者的唯一性，即，所有恒等四元数都是它 *)
  
End qone.


(** ** Square of magnitude (Length) of a quaternion *)
Section qlen2.

  (** Get square of magnitude (length) of a quaternion *)
  Definition qlen2 (q : quat) : R :=
    q.W * q.W + q.X * q.X + q.Y * q.Y + q.Z * q.Z.
  (* || q2cv q ||. *)

  (** 0 <= qlen2 q *)
  Lemma qlen2_ge0 : forall (q : quat), (0 <= qlen2 q)%R.
  Proof. intros. destruct q. unfold qlen2. simpl. ra. Qed.

  (** q = qzero <-> qlen2 q = 0 *)
  Lemma qlen2_eq0_iff : forall q : quat, qlen2 q = 0 <-> q = qzero.
  Proof.
    intros. destruct q. rewrite quat_eq_iff. cbv.
    autorewrite with R. rewrite Rplus4_sqr_eq0. auto.
  Qed.

  (** q <> qzero <-> qlen2 q <> 0 *)
  Lemma qlen2_neq0_iff : forall q : quat, qlen2 q <> 0 <-> q <> qzero.
  Proof. intros. unfold not. rewrite qlen2_eq0_iff. easy. Qed.

End qlen2.

(** ** Magnitude (Length) of a quaternion *)
Section qlen.

  (** Get magnitude (length) of a quaternion *)
  Definition qlen (q : quat) : R := sqrt (qlen2 q).

  Notation "|| q ||" := (qlen q) : quat_scope.

  (** (||q||)² = qlen2 q *)
  Lemma sqr_qlen : forall q : quat, (||q||)² = qlen2 q.
  Proof. intros. unfold qlen. autorewrite with R sqrt; auto. apply qlen2_ge0. Qed.

  (** 0 <= ||q|| *)
  Lemma qlen_ge0 : forall q : quat, 0 <= ||q||.
  Proof. intros. unfold qlen. ra. Qed.

  (** || q || = 0 <-> q = qzero *)
  Lemma qlen_eq0_iff : forall q : quat, || q || = 0 <-> q = qzero.
  Proof.
    intros. unfold qlen.
    rewrite sqrt_eq0_iff. rewrite <- qlen2_eq0_iff. pose proof (qlen2_ge0 q). ra.
  Qed.

  (** || q || <> 0 <-> q <> qzero *)
  Lemma qlen_neq0_iff : forall q : quat, || q || <> 0 <-> q <> qzero.
  Proof.
    intros. unfold qlen.
    rewrite sqrt_neq0_iff. rewrite <- qlen2_eq0_iff. pose proof (qlen2_ge0 q). ra.
  Qed.

  (** || q1 || = || q2 || <-> qlen2 q1 = qlen2 q2 *)
  Lemma qlen_eq_iff_qlen2_eq : forall q1 q2 : quat,
      || q1 || = || q2 || <-> qlen2 q1 = qlen2 q2.
  Proof.
    intros. rewrite <- !sqr_qlen. split; intros; ra.
    apply Rsqr_inj; auto. all: apply qlen_ge0.
  Qed.

  (** || q1 * q2 || = ||q1|| * ||q2|| *)
  (* 该引理表明，两个单位四元数相乘后还是一个单位四元数 *)
  Lemma qlen_qmul : forall (q1 q2 : quat),
      || q1 * q2 || = (||q1|| * ||q2||)%R.
  Proof.
    intros. apply Rsqr_inj. apply qlen_ge0. apply Rmult_le_pos; apply qlen_ge0.
    autorewrite with R. rewrite !sqr_qlen. destruct q1,q2; cbv; ring.
  Qed.

End qlen.

Notation "|| q ||" := (qlen q) : quat_scope.


(** ** Unit quaternion *)
Section qunit.

  (** A unit quaternion has a magnitude equal to 1 *)
  Definition qunit (q : quat) : Prop := ||q|| = 1.

  (** Any quaternion constructed from axis-angle is unit quaternion *)
  Lemma qunit_rotation : forall (θ : R) (n : cvec 3),
      let q := quat_of_aa (mk_axisangle θ n) in
      cvunit n -> qunit q.
  Proof.
    intros. unfold qunit, qlen, cvlen.
    apply sqrt_eq1_imply_eq1_rev.
    pose proof (cv3unit_eq1 n H).
    cvec2fun. cbv. ring_simplify in H0. ring_simplify. rewrite H0. ring_simplify.
    autorewrite with R. auto.
  Qed.

  (** qunit p -> qunit q -> || p * q || = 1 *)
  Lemma qlen_qmul_qunit (p q : quat) : qunit p -> qunit q -> || p * q || = 1.
  Proof. destruct p,q. intros. rewrite qlen_qmul. rewrite H,H0. ring. Qed.

  (** qunit q -> qlen2 q = 1 *)
  Lemma qunit_imply_qlen2_eq1 : forall q : quat, qunit q -> qlen2 q = 1.
  Proof. intros. unfold qunit, qlen, qlen2 in *. ra. Qed.
  
End qunit.


(** ** Quaternion normalization *)


(** ** Quaternion conjugate *)
Section qconj.
  
  (** Conjugate of a quaternion *)
  Definition qconj (q : quat) : quat := quat_of_s_v (q.W) (- q.Im)%CV.

  Notation "q ∗" := (qconj q) (at level 30) : quat_scope.
  
  (** q ∗ ∗ = q *)
  Lemma qconj_qconj (q : quat) : q ∗ ∗ = q.
  Proof. destruct q. lqa. Qed.

  (** (p * q)∗ = q∗ * p∗ *)
  Lemma qconj_qmul (p q : quat) : (p * q)∗ = q∗ * p∗.
  Proof. destruct p,q. lqa. Qed.

  (** (p + q)∗ = p∗ + q∗ *)
  Lemma qconj_qadd (p q : quat) : (p + q)∗ = p∗ + q∗.
  Proof. destruct p,q. lqa. Qed.

  (** q * q∗ = q∗ * q *)
  Lemma qmul_qconj_comm (q : quat) : q * q∗ = q∗ * q.
  Proof. destruct q. lqa. Qed.

  (** Im (q * q∗) = 0 *)
  Lemma qmul_qconj_Im0 (q : quat) : Im (q * q∗) == cvec0.
  Proof. lma. Qed.

  (** || q∗ || = || q || *)
  Lemma qlen_qconj (q : quat) : || q∗ || = || q ||.
  Proof.
    intros. apply Rsqr_inj; try apply qlen_ge0.
    rewrite !sqr_qlen. destruct q; cbv; ring.
  Qed.

  (** || q∗ * q || = qlen2 q *)
  Lemma qlen_qmul_qconj_l : forall (q : quat), || q∗ * q || = qlen2 q.
  Proof. intros. rewrite qlen_qmul. rewrite qlen_qconj. apply sqr_qlen. Qed.
  
  (** || q * q∗ || = qlen2 q *)
  Lemma qlen_qmul_qconj_r : forall (q : quat), || q * q∗ || = qlen2 q.
  Proof. intros. rewrite qlen_qmul. rewrite qlen_qconj. apply sqr_qlen. Qed.

End qconj.

Notation "q ∗" := (qconj q) (at level 30) : quat_scope.


(** ** Quaternion inverse *)
Section  qinv.

  (** inversion of quaternion *)
  
  Definition qinv (q : quat) : quat := (/ (qlen2 q)) c* (q ∗).

  Notation "q ⁻¹" := (qinv q) : quat_scope.

  (** q ⁻¹ * q = 1 *)
  Lemma qmul_qinv_l : forall q : quat, q <> qzero -> q ⁻¹ * q = qone.
  Proof.
    intros. destruct q. lqa. field. 
    apply quat_neq_iff in H. apply Rplus4_sqr_neq0. ra.
  Qed.
  
  (** q * q ⁻¹ = 1 *)
  Lemma qmul_qinv_r : forall q : quat, q <> qzero -> q * q ⁻¹ = qone.
  Proof.
    intros. destruct q. lqa. field. 
    apply quat_neq_iff in H. apply Rplus4_sqr_neq0. ra.
  Qed.
  
  (** qunit q -> q ⁻¹ = q ∗ *)
  Lemma qinv_eq_qconj : forall q : quat, qunit q -> q ⁻¹ = q ∗.
  Proof.
    intros. unfold qinv. apply qunit_imply_qlen2_eq1 in H. rewrite H.
    autorewrite with R. rewrite qcmul_1_l. auto.
  Qed.
  
  (* 推论：表示旋转的四元数都是单位四元数，此时共轭和逆相等。*)
  Lemma quat_of_aa_imply_qinv_eq_qconj : forall θ n,
      let q := quat_of_aa (mk_axisangle θ n) in
      cvunit n -> q ⁻¹ = q ∗.
  Proof. intros. apply (qunit_rotation θ n) in H. apply qinv_eq_qconj. auto. Qed.

  (** p * q = r -> p = r * q⁻¹ *)
  Lemma qmul_imply_solve_l : forall p q r : quat, q <> qzero -> p * q = r -> p = r * q⁻¹.
  Proof.
    intros. rewrite <- H0. rewrite qmul_assoc, qmul_qinv_r, qmul_1_r; auto.
  Qed.

  (** p * q = r -> q = p⁻¹ * r *)
  Lemma qmul_imply_solve_r : forall p q r : quat, p <> qzero -> p * q = r -> q = p⁻¹ * r.
  Proof.
    intros. rewrite <- H0. rewrite <- qmul_assoc, qmul_qinv_l, qmul_1_l; auto.
  Qed.

End qinv.

Notation "q ⁻¹" := (qinv q) : quat_scope.

(*

(** 3. quaterion can represent rotation *)

(** vector v is rotated by a quaternion q *)
Definition rot_by_quat (q : quat) (v : quat) : quat := q * v * (qinv q).

(** 四元数p经过单位四元数q作用后得到四元数p'，其标量部分保持不变。公式5.26 *)
Lemma rot_by_unit_quat_keep_s : forall (q p : quat) (H1 : qunit q),
    W p = W (rot_by_quat q p).
Proof.
  intros. destruct p,q. lqa. cbv in *. intros. rewrite H in H1.
  replace R0 with 0 in H1; auto. rewrite sqrt_0 in H1. lra.
Qed.

(** 利用四元数进行向量旋转的公式 5.24 *)
Definition vec_rot_by_quat (q : quat) (v : cvec 3) : quat :=
  q * (quat_of_v3 v) * (qinv q).

(** 四元数旋转向量后的四元数第一个分量为0 *)
Lemma vec_rot_by_quat_w_is_0 : forall q v, 
    q <> mk_quat 0 0 0 0 ->   (* 非零四元数范数非零，才存在逆 *)
    Re (vec_rot_by_quat q v) = R0.
Proof.
  intros. unfold vec_rot_by_quat. destruct q.
  lqa.
  (* xxx <> 0 *)
  apply quat_neq0_iff_qlen2_neq0 in H. auto.
Qed.

(** 四元数旋转向量后的四元数取出虚部作为向量 *)
Definition vec_rot_by_quat_IM (q : quat) (v : cvec 3) : cvec 3 :=
  t2cv_3 (Im (vec_rot_by_quat q v)).

(** 单位四元数的另一种表示形式：由旋转轴(单位向量)和旋转角构成 5.25 *)
Definition qrot_by_axis_angle (v : cvec 3) (θ : R) : quat :=
  quat_of_s_v (cos (θ/2)) (v *c (sin (θ/2)))%M.

(* 若旋转轴 v 是单位向量，则依转轴和转角生成的四元数是单位四元数 *)
Lemma qrot_by_axis_angle_keep_unitary : forall v θ,
    cvlen v = 1 -> qunit (qrot_by_axis_angle v θ).
Proof.
  intros. destruct v as [v]. lqa. cbv in H.
  apply sqrt_eq1_imply_eq1 in H.
  apply sqrt_eq1_imply_eq1_rev.
  ring_simplify in H.
  ring_simplify.
  remember (cos (θ * / (R1 + R1))) as r1.
  remember (sin (θ * / (R1 + R1))) as r2.
  rewrite ?Rplus_assoc.
  assert (v 0%nat 0%nat ^ 2 * r2 ^ 2 + 
  (r2 ^ 2 * v 1%nat 0%nat ^ 2 + r2 ^ 2 * v 2%nat 0%nat ^ 2)
          = r2 ^ 2)%R; ra.
  rewrite H0. rewrite Heqr1, Heqr2. autorewrite with R. auto.
Qed.


(** 四元数能表示三维旋转的定理 Th5.1 *)

(* (1) 通过四元数进行向量旋转会保持向量范数不变 *)
Lemma vec_rot_by_quat_keep_norm : forall (pv : cvec 3) (q : quat) (H : qunit q),
    let p' := vec_rot_by_quat q pv in
    let pv' := v3_of_quat p' in
    cvlen pv = cvlen pv'.
Proof.
  intros. destruct q as [x y z w]. destruct pv as [pv].
  cbv. apply Rsqr_inj; ra; rewrite !sqrt_sqrt; ra. field.
  apply qunit_imply_eq_R1 in H. lra.
Qed.

(* (2) 任意非零实数s与q相乘，结论仍然成立 *)
Lemma vec_rot_by_quat_keep_norm_ext : forall (pv : cvec 3) (s : R) (q : quat) 
                                        (H : qunit q) (H1 : s <> 0),
    let q' := s c* q in
    let p' := vec_rot_by_quat q' pv in
    let pv' := v3_of_quat p' in
    cvlen pv = cvlen pv'.
Proof.
  intros. destruct q as [x y z w]. destruct pv as [pv].
  cbv. apply Rsqr_inj; ra; rewrite !sqrt_sqrt; ra. field.
  apply qunit_imply_eq_R1 in H. nra.
Qed.

(* (3) 公式5.25中的四元数作用：绕v轴旋转θ角度。
 换言之，公式5.25是如何构造的？它为什么能表示旋转 *)

(* 计算两个向量的夹角 *)
Definition rot_angle_by_twovec (v0 v1 : cvec 3) : R := 
  acos (scalar_of_mat (v0\T * v1)%M).

(* 计算两个向量所决定的转轴（垂直与所在平面的法向量) *)
Definition rot_axis_by_twovec (v0 v1 : cvec 3) : cvec 3 :=
  let s : R := (cvlen v0 * cvlen v1)%R in
  (s c* (cv3cross v0 v1))%M.

(* 谓词：两向量不共线（不平行的） *)
Definition v3_non_colinear (v0 v1 : cvec 3) : Prop :=
  v0 <> v1 /\ v0 <> (-v1)%M.

(* Let ex1 : (R*R*R) := Eval cbv in 
   v2t_3 (rot_axis_by_twovec (t2v_3 (1,0.4,0)) (t2v_3 (0,0.5,0))). *)
Let ex1 : (R*R*R) := Eval cbv in
(* cv2t_3 (rot_axis_by_twovec (t2cv_3 (0.23,0.43,0)) (t2cv_3 (1.25,3.1,4.7))). *)


      (* 两个不共线的单位向量确定了一个旋转。*)

      (* 两个不共线的?? *)

      (* 按旋转轴和旋转角表示的四元数，等于，用旋转轴垂直平面上两个单位向量的运算来构造的
四元数 *)
      Definition qrot_by_two_vec_ops (v0 v1 : cvec 3) : quat :=
      quat_of_s_v (scalar_of_mat (v0\T * v1)%M) (cv3cross v0 v1).


(* (* 若单位向量v0和v1的夹角是 θ/2，且不共线，则由它们生成的垂直方向的向量v有确定形式 *)
Lemma gen_vec_by_v0_v1_eq : forall (v0 v1 : cvec 3) (θ : R) (H1 : v3norm v0 = 1)
  (H2 : v3norm v1 = 1) (H3 : v3_non_colinear v0 v1),
  v3cross v0 v1 =  *)


(** * 4. 四元数与旋转矩阵 *)

Variable q0 q1 q2 q3 : R.
Definition q_e_b := quat_of_ssss q0 q1 q2 q3.

(* Check qPLUS q_e_b. *)
(* Cbv m2l (qPLUS q_e_b). *)

Definition qPLUS_direct (q : quat) :=
  let (q0,q1,q2,q3) := q in
  @l2m 4 4 [
      [q0;-q1;-q2;-q3];
      [q1;q0;-q3;q2];
      [q2;q3;q0;-q1];
      [q3;-q2;q1;q0]]%R.

Lemma qPLUS_direct_ok : forall q, (qPLUS q == qPLUS_direct q)%M.
Proof. destruct q as [q0 q1 a2 q3]. lma. Qed.

Definition quat_inv_MINUS_direct (q : quat) :=
  let (q0,q1,q2,q3) := q in
  @l2m 4 4 [
      [q0;q1;q2;q3];
      [-q1;q0;-q3;q2];
      [-q2;q3;q0;-q1];
      [-q3;-q2;q1;q0]]%R.

Lemma quat_inv_MINUS_direct_ok : forall q, ((qMINUS q)\T == quat_inv_MINUS_direct q)%M.
Proof. destruct q as [q0 q1 a2 q3]. lma. Qed.

(** 以下三个公式是我推导中自己发现的 *)

(** qPLUS(q) * qMINUS(q^-1) = qMINUS(q^-1) * qPLUS(q) *)
Lemma qPLUS_mul_qinv_qMINUS_comm : forall q,
    let m1 := qPLUS q in
    let m2 := qMINUS (qinv q) in
    (m1 * m2 == m2 * m1)%M.
Proof. destruct q as [q0 q1 a2 q3]. lma. Qed.

(** qPLUS(q^-1) = qPLUS(q)\T *)
Lemma qPLUS_qinv_eq_trans_qPLUS : forall q,
    let m1 := qPLUS (qinv q) in
    let m2 := (qPLUS q)\T in
    (m1 * m2 == m2 * m1)%M.
Proof. destruct q as [q0 q1 a2 q3]. lma. Qed.

(** qMINUS(q^-1) = qMINUS(q)\T *)
Lemma qMINUS_qinv_eq_trans_qMINUS : forall q,
    let m1 := qMINUS (qinv q) in
    let m2 := (qPLUS q)\T in
    (m1 * m2 == m2 * m1)%M.
Proof.
  destruct q as [q0 q1 a2 q3].
  (* Compute (qinv (quat_of_ssss q0 q1 q2 q3)). *)
  (* Compute (m2l (qPLUS(quat_of_ssss q0 q1 q2 q3))). *)
  (* Compute (m2l (qMINUS(quat_of_ssss q0 q1 q2 q3))). *)
  lma.
Qed.
 *)

(*


Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import MyExtrOCamlR.
 (* Extract Constant Rabst => "__". *)
 (* Extract Constant Rrepr => "__". *)
 (* Extraction "quat.ml" mk_mat_3_1. (* Why so many warning? *) *)
 (* Recursive Extraction mk_quat quat_of_ssss quat_of_t4 qmul qconj qinv qlen rot_by_quat. *)
 (* Extraction "quat.ml" mk_quat quat_of_ssss quat_of_t4 qmul qconj qinv. qlen rot_by_quat. *)

 *)

