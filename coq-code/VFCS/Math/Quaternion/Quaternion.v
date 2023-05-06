(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Quaternion
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

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import MyExtrOCamlR.

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

  (** Convert axis-angle to quaternion *)
  Definition quat_of_aa (a : axisangle) : quat :=
    let n := aa_axis a in
    let θ := aa_angle a in
    let s2 := sin (θ/2) in
    let c2 := cos (θ/2) in
    quat_of_s_v c2 (l2cv [s2 * n.0; s2 * n.1; s2 * n.2]%R).

  (** Convert quaternion to axis-angle *)
  Definition quat_to_aa (q : quat) : axisangle :=
    let c2 : R := q.W in
    let θ : R := (2 * acos c2)%R in
    let s2 : R := sin (θ / 2) in
    let n : cvec 3 := l2cv [q.X / s2; q.Y / s2; q.Z / s2] in
    mk_axisangle θ n.

End construction.

Notation "q .Im" := (Im q) (at level 30, format "q .Im") : quat_scope.


(* ######################################################################### *)
(** * Customized tactic / tactical for proof *)

(** Linear Quaternion Algebra, q1 = q2. *)
Ltac lqa (* tac *) :=
  cbv; f_equal; ra.


(* ######################################################################### *)
(** * Quaternion operations *)

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

End qlen.

Notation "|| q ||" := (qlen q) : quat_scope.


(** ** Unit quaternion *)
Section qunit.

  (** A unit quaternion has a magnitude equal to 1 *)
  Definition qunit (q : quat) : Prop := ||q|| = 1.

  (** qunit q -> qlen2 q = 1 *)
  Lemma qunit_eq1 : forall q : quat, qunit q -> qlen2 q = 1.
  Proof. intros. unfold qunit, qlen, qlen2 in *. ra. Qed.
  
  (** qunit q -> q.W ^ 2 = 1 - q.X ^ 2 - q.Y ^ 2 - q.Z ^ 2 *)
  Lemma qunit_eq2 : forall q : quat,
      qunit q -> q.W ^ 2 = (1 - q.X ^ 2 - q.Y ^ 2 - q.Z ^ 2)%R.
  Proof. intros. pose proof (qunit_eq1 q H). rewrite <- H0. cbv. ring. Qed.
  
End qunit.


(** ** Quaternion normalization *)


(** ** Rotation quaternion *)
Section qrotation.
  
  (** Rotation quaternion is constructed from a unit vector of axis and an angle. *)
  Definition qrotation (θ : R) (n : cvec 3) (H : cvunit n) : quat :=
    quat_of_aa (mk_axisangle θ n).

  (** Any quaternion constructed from axis-angle is unit quaternion *)
  Lemma qrotation_imply_qunit : forall (θ : R) (n : cvec 3),
      let q := quat_of_aa (mk_axisangle θ n) in
      cvunit n -> qunit q.
  Proof.
    intros. unfold qunit, qlen. apply sqrt_eq1_imply_eq1_rev.
    pose proof (cv3unit_eq1 n H).
    cvec2fun. cbv. ring_simplify in H0. ring_simplify. rewrite H0. ring_simplify.
    autorewrite with R. auto.
  Qed.

End qrotation.


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
                |pw|   |qw|   |   pw qw - <pv,qv>     |
        p * q = |pv| + |qv| = |pw qv + qw pv + pv × qv| *)
  Definition qmulVEC (p q : quat) : quat :=
    quat_of_s_v
      (p.W * q.W - <p.Im, q.Im>)
      (p.W c* q.Im + q.W c* p.Im + p.Im × q.Im)%M.

  Lemma qmulVEC_eq_qmul (p q : quat) : qmulVEC p q = p * q.
  Proof. destruct p, q. lqa. Qed.

  (** Quaternion multiplication with PLUS form. page96, p+ *)
  Definition qPLUS (q : quat) : smat 4 :=
    let (q0,q1,q2,q3) := q in
    l2m [[q0; -q1; -q2; -q3];
         [q1; q0; -q3; q2];
         [q2; q3; q0; -q1];
         [q3; -q2; q1; q0]]%R.

  Lemma qPLUS_spec : forall q : quat,
      let m1 : smat 4 := (q.W c* mat1)%M in
      let m2a : mat 1 4 := mconsc (mk_mat_1_1 0) (-(q.Im\T))%M in
      let m2b : mat 3 4 := mconsc (q.Im) (cv3skew (q.Im)) in
      let m2 : smat 4 := mconsr m2a m2b in
      qPLUS q == (m1 + m2)%M.
  Proof. destruct q. lma. Qed.

   (** p * q = p⁺ * q *)
  Definition qmulPLUS (p q : quat) : quat := cv2q ((qPLUS p) * (q2cv q))%M.

  Lemma qmulPLUS_spec (p q : quat) : p * q = qmulPLUS p q.
  Proof. destruct p, q. lqa. Qed.

  (** Quaternion multiplication with MINUS form. page96, p- *)
  Definition qMINUS (q : quat) : smat 4 :=
    let m1 : smat 4 := (q.W c* mat1)%M in
    let m2a : mat 1 4 := mconsc (mk_mat_1_1 0) (-(q.Im\T))%M in
    let m2b : mat 3 4 := mconsc (q.Im) (-(cv3skew (q.Im)))%M in
    let m2 : smat 4 := mconsr m2a m2b in
    (m1 + m2)%M.

   (** p * q = q⁻ * p *)
  Definition qmulMINUS (p q : quat) : quat := cv2q ((qMINUS q) * (q2cv p))%M.

  Lemma qmulMINUS_correct (p q : quat) : p * q = qmulMINUS p q.
  Proof. destruct p, q. lqa. Qed.

  (** qlen2 (q1 * q2) = (qlen2 q1) * (qlen2 q2) *)
  Lemma qlen2_qmul : forall (q1 q2 : quat), qlen2 (q1 * q2) = ((qlen2 q1) * (qlen2 q2))%R.
  Proof. intros. destruct q1,q2. cbv. ring. Qed.

  (** || q1 * q2 || = ||q1|| * ||q2|| *)
  Lemma qlen_qmul : forall (q1 q2 : quat), || q1 * q2 || = (||q1|| * ||q2||)%R.
  Proof.
    intros. apply Rsqr_inj. apply qlen_ge0. apply Rmult_le_pos; apply qlen_ge0.
    autorewrite with R. rewrite !sqr_qlen. destruct q1,q2; cbv; ring.
  Qed.

  (** qunit p -> qunit q -> || p * q || = 1 *)
  (* 两个单位四元数相乘后还是一个单位四元数 *)
  Lemma qlen_qmul_qunit (p q : quat) : qunit p -> qunit q -> || p * q || = 1.
  Proof. destruct p,q. intros. rewrite qlen_qmul. rewrite H,H0. ring. Qed.

  (** (q * r) * m = q * (r * m) *)
  Lemma qmul_assoc (q r m : quat) : (q * r) * m = q * (r * m).
  Proof. destruct q,r,m. lqa. Qed.

  (** The multiplication is non-commutative. That is: p * q <> q * p. *)
  Lemma qmul_comm_fail : exists (p q : quat), p * q <> q * p.
  Proof.
    exists (quat_of_ssss 0 1 2 1).
    exists (quat_of_ssss 0 2 1 2).
    cbv. intros. inversion H. lra.
  Qed.

  (** 1 * q = q *)
  Lemma qmul_1_l : forall q : quat, qone * q = q.
  Proof. intros. destruct q. lqa. Qed.

  (** q * 1 = q *)
  Lemma qmul_1_r : forall q : quat, q * qone = q.
  Proof. intros. destruct q. lqa. Qed.

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
  Definition qcmul (a : R) (q : quat) : quat := (quat_of_s a) * q.
  Notation "a c* q" := (qcmul a q) : quat_scope.

  (** 1 c* q = q *)
  Lemma qcmul_1_l : forall q : quat, 1 c* q = q.
  Proof. intros. destruct q. lqa. Qed.

  (** (a c* p) * q = a c* (p * q) *)
  Lemma qmul_qcmul_l : forall (a : R) (p q : quat), (a c* p) * q = a c* (p * q).
  Proof. intros. destruct p,q. lqa. Qed.
  
  (** p * (a c* q) = a c* (p * q) *)
  Lemma qmul_qcmul_r : forall (a : R) (p q : quat), p * (a c* q) = a c* (p * q).
  Proof. intros. destruct p,q. lqa. Qed.

  (** a c* (b c* q) = (a * b) c* q *)
  Lemma qcmul_assoc : forall (a b : R) (q : quat), a c* (b c* q) = (a * b) c* q.
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
    intros. unfold qinv. apply qunit_eq1 in H. rewrite H.
    autorewrite with R. rewrite qcmul_1_l. auto.
  Qed.
  
  (** Any rotation quaternion, inverse equal to conjugate. *)
  Lemma qrotation_imply_qinv_eq_qconj : forall θ n H,
      let q := qrotation θ n H in
      q ⁻¹ = q ∗.
  Proof. intros. apply qinv_eq_qconj. apply qrotation_imply_qunit. auto. Qed.

  (** (p * q)⁻¹ = q⁻¹ * p⁻¹ *)
  Lemma qinv_qmul : forall p q : quat, p <> qzero -> q <> qzero -> (p * q)⁻¹ = q⁻¹ * p⁻¹.
  Proof.
    intros. unfold qinv. rewrite qconj_qmul.
    rewrite qmul_qcmul_l. rewrite qmul_qcmul_r. rewrite qcmul_assoc. f_equal.
    rewrite qlen2_qmul. field. split; apply qlen2_neq0_iff; auto.
  Qed.

  (** 以下几个公式是我发现的 *)

  (** Let q1 = q⁺, q2 = (q⁻¹)⁻, then q1 * q2 = q2 * q1 *)
  Lemma qmul_qPLUS_qMINUS_qinv_comm : forall q,
      let m1 := qPLUS q in
      let m2 := qMINUS (q⁻¹) in
      (m1 * m2 == m2 * m1)%M.
  Proof. destruct q. lma. Qed.

  (** Let q1 = (q⁻¹)⁺, q2 = (q⁺)\T, then q1 * q2 = q2 * q1 *)
  Lemma qmul_qPLUS_qinv_trans_qPLUS_comm : forall q,
      let m1 := qPLUS (q⁻¹) in
      let m2 := (qPLUS q)\T in
      (m1 * m2 == m2 * m1)%M.
  Proof. destruct q. lma. Qed.

  (** Let q1 = (q⁻¹)⁻, q2 = (q⁺)\T, then q1 * q2 = q2 * q1 *)
  Lemma qmul_qMINUS_qinv_trans_qPLUS_comm : forall q,
      let m1 := qMINUS (q⁻¹) in
      let m2 := (qPLUS q)\T in
      (m1 * m2 == m2 * m1)%M.
  Proof. destruct q. lma. Qed.

  (** Let q1 = (q⁻¹)⁺, q2 = (q⁻¹)⁻, then q1 * q2 = q2 * q1 *)
  Lemma qmul_qPLUS_qinv_qMINUS_qinv_comm : forall q,
      let m1 := qPLUS (q⁻¹) in
      let m2 := qMINUS (q⁻¹) in
      (m1 * m2 == m2 * m1)%M.
  Proof. destruct q. lma. Qed.

End qinv.

Notation "q ⁻¹" := (qinv q) : quat_scope.


(** ** Divide of quaternion *)
Section qdiv.

  (** 利用除法，可以计算两个给定旋转 a 和 b 之间的某种角位移 d。在 Slerp 时会使用它。*)

  (** If d * a = b, then d ≜ b * a⁻¹ 表示从a到b旋转的角位移 *)
  Definition qdiv (a b : quat) : quat := b * a⁻¹.

  Lemma qdiv_spec : forall a b : quat, a <> qzero -> (qdiv a b) * a = b.
  Proof. intros. unfold qdiv. rewrite qmul_assoc,qmul_qinv_l,qmul_1_r; auto. Qed.

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

End qdiv.


(** ** Rotate 3D vector by quaterion multiplication *)
Section qrot.

  (** vector v (be wrapped to quaterion) is rotated by a quaternion q.
      Note that: q must be a rotation quaternion *)
  Definition qrot (q : quat) (v : quat) : quat := q * v * q⁻¹.

  (** 使用四元数连接多个旋转: First by q1, then by q2 *)
  Lemma qrot2 : forall (q1 q2 : quat) (v : quat),
      q1 <> qzero -> q2 <> qzero -> qrot q2 (qrot q1 v) = qrot (q2 * q1) v.
  Proof.
    intros. unfold qrot. rewrite qinv_qmul; auto. rewrite !qmul_assoc. auto.
  Qed.

  (** 备注：四元数乘法可以连接多个旋转，就像矩阵乘法一样。
      但实际上还有一些区别。矩阵乘法时，可以使用行矢量左乘矩阵，也可使用列矢量右乘
      矩阵（转置形式）。而四元数没有这种灵活性，多个连接总是从右到左或说“从里到外”
      读取。对于 Dunn 的这个观点，我们可以进一步实验，看看四元数是否也能通过某种
      “转置”操作实现更换方向。当然，这个实验可能只是理论上的需要，实际并无此需求。*)

  
  (** 证明四元数乘法能够旋转三维矢量 *)
  (** 方法1：计算其生成的结果与轴角表示的结果相同，这是大多数文献所采用的方法。*)
  Section spec1.
    
    Local Open Scope fun_scope.
    Lemma qrot_spec : forall (θ : R) (n : cvec 3) (H : cvunit n) (v : cvec 3),
        let q := qrotation θ n H in
        (qrot q (quat_of_v3 v)).Im == rotAxisAngle θ n v.
    Proof.
      intros.
      (* pose proof (cv3unit_eq1 n H). *)
      (* cvec2fun. *)
      (* lma. *)
      (* cbv. *)
      (* ring_simplify. *)
      (* remember (cos (θ * / (R1 + R1))) as c. *)
      (* remember (sin (θ * / (R1 + R1))) as s. *)
      (* ring_simplify in H0. rewrite H0. field_simplify. *)
      (* ring_simplify. *)
      (* rewrite (Rmult_assoc _ _ (n.00)). *)
      (* rewrite H0. *)
      (* field_simplify. *)
    Abort.

  End spec1.

  (** 方法2：QQ书上的推导过程 *)
  Section spec2.

    (** 四元数p经过单位四元数q作用后得到四元数p'，其标量部分保持不变。公式5.26 *)
    Lemma qrot_keep_s : forall (q v : quat), qunit q -> (qrot q v).W = v.W.
    Proof.
      intros. pose proof (qunit_eq2 q H). destruct q,v. cbv in *.
      field_simplify in H0. field_simplify; try lra. rewrite H0. field. lra.
    Qed.

    (** 利用四元数进行向量旋转的公式 5.24 *)
    (* Definition qrot_vec (q : quat) (v : cvec 3) : quat := q * (quat_of_v3 v) * q⁻¹. *)

    (** 四元数旋转向量后的四元数第一个分量为0 *)
    (* Lemma vec_rot_by_quat_w_is_0 : forall q v, (qrot_vec q v).W = R0. *)
    (* Proof. intros. destruct q. lqa. Qed. *)

    (** 四元数旋转向量后的四元数取出虚部作为向量 *)
    Definition qrot_vec (q : quat) (v : cvec 3) : cvec 3 :=
      (q * (quat_of_v3 v) * q⁻¹).Im.

    (** 单位四元数的另一种表示形式：由旋转轴(单位向量)和旋转角构成 5.25 *)
    (* Check quat_of_aa. *)
    (* Check qrotation. *)

    (* 若旋转轴 v 是单位向量，则依转轴和转角生成的四元数是单位四元数 *)
    (* Check qrotation_imply_qunit. *)

    (** 四元数能表示三维旋转的定理 Th5.1 *)

    (* (1) 通过四元数进行向量旋转会保持向量范数不变 *)
    (* Lemma vec_rot_by_quat_keep_norm : forall (pv : cvec 3) (q : quat) (H : qunit q), *)
    (*     let p' := vec_rot_by_quat q pv in *)
    (*     let pv' := v3_of_quat p' in *)
    (*     cvlen pv = cvlen pv'. *)
    (* Proof. *)
    (*   intros. destruct q as [x y z w]. destruct pv as [pv]. *)
    (*   cbv. apply Rsqr_inj; ra; rewrite !sqrt_sqrt; ra. field. *)
    (*   apply qunit_imply_eq_R1 in H. lra. *)
    (* Qed. *)
    Lemma qrot_keep_len : forall (q v : quat),
        let v3 : cvec 3 := v.Im in
        let v3' : cvec 3 := (qrot q v).Im in
        qunit q -> (|| v3 || = || v3' ||)%CV.
    Admitted.

    (* (2) 任意非零实数s与q相乘，结论仍然成立 *)
    (* Lemma vec_rot_by_quat_keep_norm_ext : forall (pv : cvec 3) (s : R) (q : quat)  *)
    (*                                         (H : qunit q) (H1 : s <> 0), *)
    (*     let q' := s c* q in *)
    (*     let p' := vec_rot_by_quat q' pv in *)
    (*     let pv' := v3_of_quat p' in *)
    (*     cvlen pv = cvlen pv'. *)
    (* Proof. *)
    (*   intros. destruct q as [x y z w]. destruct pv as [pv]. *)
    (*   cbv. apply Rsqr_inj; ra; rewrite !sqrt_sqrt; ra. field. *)
    (*   apply qunit_imply_eq_R1 in H. nra. *)
    (* Qed. *)
    Lemma qrot_keep_len_ext :  forall (q v : quat) (s : R),
        let q := s c* q in
        let v3 : cvec 3 := v.Im in
        let v3' : cvec 3 := (qrot q v).Im in
        s <> 0 -> qunit q -> (|| v3 || = || v3' ||)%CV.
    Admitted.

    (* (3) 公式5.25中的四元数作用：绕v轴旋转θ角度。
       换言之，公式5.25是如何构造的？它为什么能表示旋转 *)

    (* 计算两个向量的夹角 *)
    Definition rot_angle_by_twovec (v0 v1 : cvec 3) : R := 
      acos (<v0, v1>).

    (* 计算两个向量所决定的转轴（垂直于所在平面的法向量) *)
    Definition rot_axis_by_twovec (v0 v1 : cvec 3) : cvec 3 :=
      let s : R := (cvlen v0 * cvlen v1)%R in
      (s c* (v0 × v1))%M.

    (* 谓词：两向量不共线（不平行的） *)
    Definition v3_non_colinear (v0 v1 : cvec 3) : Prop :=
      v0 <> v1 /\ v0 <> (-v1)%M.

    (* Let ex1 : (R*R*R) := Eval cbv in 
       v2t_3 (rot_axis_by_twovec (t2v_3 (1,0.4,0)) (t2v_3 (0,0.5,0))). *)
    (* Let ex1 : (R*R*R) := Eval cbv in *)
    (*       cv2t_3 (rot_axis_by_twovec (t2cv_3 (0.23,0.43,0)) (t2cv_3 (1.25,3.1,4.7))). *)


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
(* Recursive Extraction mk_quat quat_of_ssss quat_of_t4 qmul qconj qinv qlen rot_by_quat. *)
(* Extraction "quat.ml" mk_quat quat_of_ssss quat_of_t4 qmul qconj qinv. qlen rot_by_quat. *)
