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
Require Export VectorR2.
Require Export VectorR3.

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
Definition AxisAngle := (R * cvec 3)%type.


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
  Definition quat_of_wxyz (w x y z : R) : quat := mk_quat w x y z.

  Lemma quat_of_wxyz_ok : forall w x y z,
      let q := quat_of_wxyz w x y z in
      q.W = w /\ q.X = x  /\ q.Y = y /\ q.Z = z.
  Proof. intros. split; auto. Qed.

  (** Construct a quaternion by a scalar number and a 3-dim vector *)
  Definition quat_of_s_v (w : R) (v : cvec 3) := mk_quat w (v.1) (v.2) (v.3).

  Lemma quat_of_s_v_ok : forall w v,
      let q := quat_of_s_v w v in
      q.W = w /\ q.X = v.1  /\ q.Y = v.2 /\ q.Z = v.3.
  Proof. intros. split; auto. Qed.

  Lemma quat_of_s_v_inj : forall w1 w2 v1 v2,
      quat_of_s_v w1 v1 = quat_of_s_v w2 v2 -> w1 = w2 /\ v1 == v2.
  Proof.
    intros. unfold quat_of_s_v in H. inversion H. split; auto.
    apply cv3eq_iff; auto.
  Qed.

  (** Construct a quaternion by a scalar number *)
  Definition qscalar (w : R) : quat := mk_quat w 0 0 0.
  
  Lemma qscalar_ok : forall w,
      let q := qscalar w in
      q.W = w /\ q.X = R0 /\ q.Y = R0 /\ q.Z = R0.
  Proof. intros. cbv. auto. Qed.

  (** Construct a quaternion by a 3-dim vector *)
  Definition qpure (v : cvec 3) : quat := quat_of_s_v 0 v.
  
  Lemma qpure_ok : forall v,
      let q := qpure v in
      q.W = R0 /\ q.X = v.1 /\ q.Y = v.2 /\ q.Z = v.3.
  Proof. intros. apply quat_of_s_v_ok. Qed.

  Lemma quat_of_s_v_eq_qpure : forall v,
      quat_of_s_v 0 v = qpure v.
  Proof. intros. unfold qpure. auto. Qed.

  (** (qpure v).Im = v *)
  Lemma qim_qpure : forall (v : cvec 3), (qpure v).Im == v.
  Proof. lma. Qed.
  
  (** q.W = 0 -> qpure (q.Im) = q *)
  Lemma qpure_qim : forall (q : quat), q.W = 0 -> qpure (q.Im) = q.
  Proof. intros. destruct q. cbv. simpl in *. f_equal. auto. Qed.
  
  (** Construct a quaternion by a vec4[w;x;y;z] *)
  Definition cv2q (v : cvec 4) : quat := mk_quat (v.1) (v.2) (v.3) (v.4).
  
  Lemma cv2q_ok : forall v,
      let q := cv2q v in
      q.W = v.1 /\ q.X = v.2 /\ q.Y = v.3 /\ q.Z = v.4.
  Proof. intros. cbv. auto. Qed.
  
  (** Quaternion to vec4[w;x;y;z] *)
  Definition q2cv (q : quat) : cvec 4 := l2cv [q.W; q.X; q.Y; q.Z].
  
  Lemma q2cv_ok : forall q,
      let v := q2cv q in
      v.1 = q.W /\ v.2 = q.X /\ v.3 = q.Y /\ v.4 = q.Z.
  Proof. intros. cbv. auto. Qed.

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

  (** v != cvec0 -> qpure v <> qzero. *)
  Lemma qpure_neq0_iff : forall (v : cvec 3), v != cvec0 -> qpure v <> qzero.
  Proof.
    intros. apply cv3neq_iff in H. cvec2fun.
    cbv. cbv in H. intro. inversion H0. ra.
  Qed.

End qzero.


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

  (** cvunit v -> qunit [0,v] *)
  Lemma qpure_qunit : forall v : cvec 3, cvunit v -> qunit (qpure v).
  Proof.
    intros. cvec2fun. cbv. cbv in H.
    autorewrite with  R in H. autorewrite with R. rewrite H. ra.
  Qed.

  (** qunit q <-> qlen2 q = 1 *)
  Lemma qunit_iff_qlen2_eq1 : forall q : quat, qunit q <-> qlen2 q = 1.
  Proof. intros. unfold qunit, qlen, qlen2 in *. split; intros; ra. rewrite H; ra. Qed.
  
  (** qunit q -> q.W ^ 2 = 1 - q.X ^ 2 - q.Y ^ 2 - q.Z ^ 2 *)
  Lemma qunit_imply_eq1 : forall q : quat,
      qunit q -> q.W ^ 2 = (1 - q.X ^ 2 - q.Y ^ 2 - q.Z ^ 2)%R.
  Proof. intros. apply qunit_iff_qlen2_eq1 in H. rewrite <- H. cbv. ring. Qed.

  (** qunit q -> q <> qzero *)
  Lemma qunit_neq0 : forall q : quat, qunit q -> q <> qzero.
  Proof. intros. apply qlen_neq0_iff. intro. unfold qunit in H. lra. Qed.

  (** q.W = 0 -> cvunit (q.Im) -> qunit q *)
  Lemma qim_cvunit_imply_qunit : forall q : quat, q.W = 0 -> cvunit (q.Im) -> qunit q.
  Proof. intros. apply qunit_iff_qlen2_eq1. destruct q. simpl in *. cbv in *. ra. Qed.
  
End qunit.


(** ** Quaternion normalization *)


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
        p * q = |pv| + |qv| = |pw qv + qw pv + pv × qv|
      This formula is also known Graβmann Product. *)
  Lemma qmul_spec (p q : quat) :
    p * q =
      quat_of_s_v
        (p.W * q.W - <p.Im, q.Im>)
        (p.W c* q.Im + q.W c* p.Im + p.Im × q.Im)%M.
  Proof. destruct p, q. lqa. Qed.
  
  (** qlen2 (q1 * q2) = (qlen2 q1) * (qlen2 q2) *)
  Lemma qlen2_qmul : forall (q1 q2 : quat),
      qlen2 (q1 * q2) = ((qlen2 q1) * (qlen2 q2))%R.
  Proof. intros. destruct q1,q2. cbv. ring. Qed.

  (** || q1 * q2 || = ||q1|| * ||q2|| *)
  Lemma qlen_qmul : forall (q1 q2 : quat), || q1 * q2 || = (||q1|| * ||q2||)%R.
  Proof.
    intros. apply Rsqr_inj. apply qlen_ge0. apply Rmult_le_pos; apply qlen_ge0.
    autorewrite with R. rewrite !sqr_qlen. destruct q1,q2; cbv; ring.
  Qed.

  (** qunit p -> qunit q -> qunit (p * q) *)
  Lemma qunit_qmul (p q : quat) : qunit p -> qunit q -> qunit (p * q).
  Proof.
    intros. destruct p,q. unfold qunit. rewrite qlen_qmul. rewrite H,H0. ring.
  Qed.

  (** (q * r) * m = q * (r * m) *)
  Lemma qmul_assoc (q r m : quat) : (q * r) * m = q * (r * m).
  Proof. destruct q,r,m. lqa. Qed.

  (** The multiplication is non-commutative. That is: p * q <> q * p. *)
  Lemma qmul_comm_fail : exists (p q : quat), p * q <> q * p.
  Proof.
    exists (quat_of_wxyz 0 1 2 1).
    exists (quat_of_wxyz 0 2 1 2).
    cbv. intros. inversion H. lra.
  Qed.

  (** q * (r + m) = q * r + q * m *)
  Lemma qmul_qadd_distr_l (q r m : quat) : q * (r + m) = q * r + q * m.
  Proof. destruct q,r,m. lqa. Qed.

  (** (r + m) * q = r * q + m * q *)
  Lemma qmul_qadd_distr_r (r m q : quat) : (r + m) * q = r * q + m * q.
  Proof. destruct r,m,q. lqa. Qed.

  (** multplication of two pure quaternions: (0,u) * (0,v) = (-<u,v>, u × v)  *)
  Lemma qmul_qpure_eq (u v : cvec 3) :
    (qpure u) * (qpure v) = quat_of_s_v (- <u,v>) (u × v).
  Proof. lqa. Qed.

  (** (s1,0) * (s2,0) = (s1*s2,0) *)
  Lemma qsqr_qscalar : forall s1 s2 : R,
      (qscalar s1) * (qscalar s2) = qscalar (s1 * s2).
  Proof. intros. lqa. Qed.

  (** (0,u) * (0,u) = (-1,0) *)
  Lemma qsqr_qpure : forall v : cvec 3,
      cvunit v -> (qpure v) * (qpure v) = qscalar (-1).
  Proof. intros. pose proof (cv3unit_eq1 v H). cvec2fun. lqa. Qed.


  (** Left scalar multiplication *)
  (* 此定义也正确，但是太繁琐 *)
  (* Definition qcmul (a : R) (q : quat) : quat := (qscalar a) * q. *)
  Definition qcmul (a : R) (q : quat) : quat :=
    quat_of_wxyz (a * q.W) (a * q.X) (a * q.Y) (a * q.Z).
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

  (* Variable q0 q1 q2 q3 a : R. *)
  (* Let q : quat := quat_of_wxyz q0 q1 q2 q3. *)
  (* Compute qlen2 (a c* q). *)
  (* Compute (a² * qlen2 (q))%R. *)
  (* Goal qlen2 (a c* q) = (a² * qlen2 (q))%R. *)
  (*   cbv. field. *)
  
  (** qlen2 (a c* q) = a² * (qlen2 q) *)
  Lemma qlen2_qcmul : forall (a : R) (q : quat), qlen2 (a c* q) = (a² * (qlen2 q))%R.
  Proof. intros. destruct q. cbv. ring. Qed.

  (** Right scalar multiplication *)
  (* 此定义也正确，但是太繁琐 *)
  (* Definition qmulc (q : quat) (s : R) : quat := q * (qscalar s). *)
  Definition qmulc (q : quat) (s : R) : quat := qcmul s q.
  Notation "q *c a" := (qmulc q a) : quat_scope.

  (* s * q = q * s *)
  Lemma qcmul_eq_qmulc (s : R) (q : quat) : s c* q = q *c s.
  Proof. destruct q. lqa. Qed.


  (** *** The matrix form of quaternion multiplication *)

  (** Quaternion matrix function, also be found in QQ,p96,p+ *)
  Definition qmatL (q : quat) : smat 4 :=
    let (w,x,y,z) := q in
    l2m [[w; -x; -y; -z];
         [x; w; -z; y];
         [y; z; w; -x];
         [z; -y; x; w]]%R.

  (** Verify the construction *)
  Lemma qmatL_construct_spec : forall q : quat,
      let m1 : smat 4 := (q.W c* mat1)%M in
      let m2a : mat 1 4 := mconsc (mk_mat_1_1 0) (-(q.Im\T))%M in
      let m2b : mat 3 4 := mconsc (q.Im) (cv3skew (q.Im)) in
      let m2 : smat 4 := mconsr m2a m2b in
      qmatL q == (m1 + m2)%M.
  Proof. destruct q. lma. Qed.

  (** p * q = L(p) * q *)
  Lemma qmatL_mul_spec : forall (p q : quat), p * q = cv2q ((qmatL p) * (q2cv q))%M.
  Proof. intros. destruct p,q. lqa. Qed.

  (** Right matrix form of a quaternion, also be found in QQ,p96,p- *)
  Definition qmatR (q : quat) : smat 4 :=
    let (w,x,y,z) := q in
    l2m [[w; -x; -y; -z];
         [x; w; z; -y];
         [y; -z; w; x];
         [z; y; -x; w]]%R.

  (** Verify the construction *)
  Lemma qmatR_construct_spec : forall q : quat,
      let m1 : smat 4 := (q.W c* mat1)%M in
      let m2a : mat 1 4 := mconsc (mk_mat_1_1 0) (-(q.Im\T))%M in
      let m2b : mat 3 4 := mconsc (q.Im) (-(cv3skew (q.Im)))%M in
      let m2 : smat 4 := mconsr m2a m2b in
      qmatR q == (m1 + m2)%M.
  Proof. destruct q. lma. Qed.

  (** p * q = R(q) * p *)
  Lemma qmatR_mul_spec : forall (p q : quat), p * q = cv2q ((qmatR q) * (q2cv p))%M.
  Proof. intros. destruct p,q. lqa. Qed.
  
End qmul.

Notation "p * q" := (qmul p q) : quat_scope.
Notation "a c* q" := (qcmul a q) : quat_scope.
Notation "q *c a" := (qmulc q a) : quat_scope.


(** ** Identity quaternion 恒等四元数 *)
Section qone.

  (** 恒定四元数：角位移为0的四元数（因为角位移就是朝向的变换，所以这里就是恒等元）

    几何上有两个恒等四元数：[0̂ 1] 和 [0̂ -1]
    当 θ 是 2π 的偶数倍时，cos (θ/2) = 1, sin(θ/2) = 0, n̂是任意值
    当 θ 是 2π 的奇数倍时，cos (θ/2) = -1, sin(θ/2) = 0, n̂是任意值
    直观上，若旋转角度是绕任何轴转完整的整数圈，则在三维中方向上不会有任何实际的改变。

    代数上只有一个恒等四元数 [0̂ 1]。因为要求任意 q 乘以单位元后不变。
   *)

  (** (1,0,0,0) *)
  Definition qone : quat := quat_of_wxyz 1 0 0 0.
  (** (-1,0,0,0) *)
  Definition qone_neg : quat := quat_of_wxyz (-1) 0 0 0.

  (** ToDo: 是否可证只有 qone 是唯一的恒等四元数？*)
  
  (** 1 * q = q *)
  Lemma qmul_1_l : forall q : quat, qone * q = q.
  Proof. intros. destruct q. lqa. Qed.

  (** q * 1 = q *)
  Lemma qmul_1_r : forall q : quat, q * qone = q.
  Proof. intros. destruct q. lqa. Qed.
  
End qone.


(** ** Quaternion conjugate *)
Section qconj.

  (** 当只使用单位四元数时，共轭和逆相等。
      q和q∗ 代表相反的角位移。
      可直观的验证这种想法：q∗使得v变成了-v，所以旋转轴反向，颠倒了正方向，所以是相反的。
   *)
  
  (** Conjugate of a quaternion *)
  Definition qconj (q : quat) : quat := quat_of_s_v (q.W) (- q.Im)%CV.

  Notation "q ∗" := (qconj q) (at level 30) : quat_scope.
  
  (** q ∗ ∗ = q *)
  Lemma qconj_qconj (q : quat) : q ∗ ∗ = q.
  Proof. destruct q. lqa. Qed.

  (** (qpure v)∗ = qpure (-v) *)
  Lemma qconj_qpure : forall (v : cvec 3), qconj (qpure v) = qpure (-v)%CV.
  Proof. lqa. Qed.

  (** (p * q)∗ = q∗ * p∗ *)
  Lemma qconj_qmul (p q : quat) : (p * q)∗ = q∗ * p∗.
  Proof. destruct p,q. lqa. Qed.

  (** (a c* q)∗ = a c* (q∗) *)
  Lemma qconj_qcmul : forall (a : R) (q : quat), (a c* q)∗ = a c* (q∗).
  Proof. intros. lqa. Qed.

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

  (** qunit q <-> qunit (q∗) *)
  Lemma qconj_qunit : forall (q : quat), qunit (q∗) <-> qunit q.
  Proof. intros. unfold qunit. rewrite qlen_qconj. easy. Qed.

  (** L(q∗) = L(q)\T *)
  Lemma qmatL_qconj : forall q : quat, qmatL (q∗) == (qmatL q)\T.
  Proof. intros. destruct q. lma. Qed.

  (** R(q∗) = R(q)\T *)
  Lemma qmatR_qconj : forall q : quat, qmatR (q∗) == (qmatR q)\T.
  Proof. intros. destruct q. lma. Qed.

  (** L(q) R(q∗) *)
  Definition qmat (q : quat) : smat 4 :=
    let (w,x,y,z) := q in
    l2m [[1; 0; 0; 0];
         [0; 1 - 2*y² - 2*z²; 2*x*y - 2*w*z; 2*w*y + 2*x*z];
         [0; 2*x*y + 2*w*z; 1 - 2*x² - 2*z²; 2*y*z - 2*w*x];
         [0; 2*x*z - 2*w*y; 2*w*x + 2*y*z; 1 - 2*x² - 2*y²]]%R.

  (** qunit q -> q v q* = L(q) R(q* ) v *)
  Lemma qmat_spec : forall (q v : quat),
      qunit q -> q * v * q∗ = cv2q ((qmat q) * (q2cv v))%M.
  Proof.
    intros. destruct q,v.
    apply qunit_imply_eq1 in H; simpl in H; ring_simplify in H.
    lqa; ring_simplify; rewrite H; ring.
  Qed.

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
    intros. unfold qinv. apply qunit_iff_qlen2_eq1 in H. rewrite H.
    autorewrite with R. rewrite qcmul_1_l. auto.
  Qed.

  (** (p * q)⁻¹ = q⁻¹ * p⁻¹ *)
  Lemma qinv_qmul : forall p q : quat, p <> qzero -> q <> qzero -> (p * q)⁻¹ = q⁻¹ * p⁻¹.
  Proof.
    intros. unfold qinv. rewrite qconj_qmul.
    rewrite qmul_qcmul_l. rewrite qmul_qcmul_r. rewrite qcmul_assoc. f_equal.
    rewrite qlen2_qmul. field. split; apply qlen2_neq0_iff; auto.
  Qed.

  (** (a c* q)⁻¹ = (1/a) c* q⁻¹ *)
  Lemma qinv_qcmul : forall (q : quat) (a : R),
      a <> 0 -> q <> qzero -> (a c* q)⁻¹ = (1/a) c* q⁻¹.
  Proof.
    intros.
    unfold qinv. rewrite qlen2_qcmul.
    rewrite qconj_qcmul. rewrite !qcmul_assoc. f_equal.
    unfold Rsqr. field. apply qlen2_neq0_iff in H0. auto.
  Qed.

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

  (** 以下几个公式是我发现的，或许本质上很简单 *)

  (** L(q) * R(q⁻¹) = R(q⁻¹) * L(q) *)
  Lemma qmul_qL_qR_qinv_comm : forall q,
      let m1 := qmatL q in
      let m2 := qmatR (q⁻¹) in
      (m1 * m2 == m2 * m1)%M.
  Proof. destruct q. lma. Qed.

  (** L(q⁻¹) * L(q)\T = L(q)\T * L(q⁻¹) *)
  Lemma qmul_qL_qinv_qtrans_qL_comm : forall q,
      let m1 := qmatL (q⁻¹) in
      let m2 := (qmatL q)\T in
      (m1 * m2 == m2 * m1)%M.
  Proof. destruct q. lma. Qed.

  (** R(q⁻¹) * L(q)\T = L(q)\T * R(q⁻¹) *)
  Lemma qmul_qR_qinv_qtrans_qL_comm : forall q,
      let m1 := qmatR (q⁻¹) in
      let m2 := (qmatL q)\T in
      (m1 * m2 == m2 * m1)%M.
  Proof. destruct q. lma. Qed.

  (** L(q⁻¹) * R(q⁻¹) = R(q⁻¹) * L(q⁻¹) *)
  Lemma qmul_qL_qinv_qR_qinv_comm : forall q,
      let m1 := qmatL (q⁻¹) in
      let m2 := qmatR (q⁻¹) in
      (m1 * m2 == m2 * m1)%M.
  Proof. destruct q. lma. Qed.

End qinv.

Notation "q ⁻¹" := (qinv q) : quat_scope.


(** ** Divide of quaternion *)
Section qdiv.

  (** 利用除法，可以计算两个给定旋转 a 和 b 之间的某种角位移 d。在 Slerp 时会使用它。*)

  (** If r * p = q, then r ≜ q * p⁻¹ 表示从p到q旋转的角位移 *)
  Definition qdiv (q p : quat) : quat := p * q⁻¹.

  Lemma qdiv_spec : forall a b : quat, a <> qzero -> (qdiv a b) * a = b.
  Proof. intros. unfold qdiv. rewrite qmul_assoc,qmul_qinv_l,qmul_1_r; auto. Qed.

End qdiv.


(** ** Unit quaternion <-> Axis-Angle *)
Section quat_aa.
  
  (** Unit quaternion and the Axis-Angle representation are bijection. That is,
      every unit quaternion has a corresponded unique axis-angle value,
      every axis-angle value has a corresponded unique unit quaternion. *)
  
  (** Convert axis-angle value to unit quaternion *)
  Definition aa2quat (aa : AxisAngle) : quat :=
    let (θ,n) := aa in
    quat_of_s_v (cos (θ/2)) (sin (θ/2) c* n)%CV.

  (** Any quaternion constructed from axis-angle is unit quaternion *)
  Lemma aa2quat_unit : forall aa : AxisAngle,
      let (θ,n) := aa in
      cvunit n -> qunit (aa2quat aa).
  Proof.
    intros. destruct aa. intros.
    pose proof (cv3unit_eq1 c H). cvec2fun. cbv.
    apply sqrt_eq1_imply_eq1_rev. ring_simplify.
    cbv in H0. ring_simplify in H0. rewrite H0, cos2'. field.
  Qed.
  
  (** Convert unit quaternion to axis-angle value *)
  Definition quat2aa (q : quat) : AxisAngle :=
    let θ : R := (2 * acos (q.W))%R in
    let n : cvec 3 := ((1 / sqrt (1-q.W²)) c* q.Im)%CV in
    (θ, n).

  (** 若q是(1,0,0,0)，则θ为2kπ；否则 θ≠2kπ 且 n 是单位向量。
      换言之，若 q ≠ (1,0,0,0)，则n一定是单位向量 *)
  Lemma quat2aa_unit : forall (q : quat) (H : qunit q) (H1 : q <> qone),
      let (θ,n) := quat2aa q in cvunit n.
  Proof.
    intros.
    pose proof qunit_imply_eq1 q H.
    destruct q. simpl in *.
    apply quat_neq_iff in H1. simpl in *.
    cbv; ring_simplify. cbv in H0;  field_simplify in H0.
    autorewrite with R. autorewrite with R in H0.
    replace ((/ sqrt (1 + - W0²))²) with (/ (1 - W0²)). rewrite H0. field.
    - rewrite <- H0.
  Abort.
  
  Lemma aa2quat_quat2aa_id : forall q : quat, aa2quat (quat2aa q) = q.
  Proof.
    intros. destruct q. lqa.
  Abort.

  Lemma quat2aa_aa2quat_id : forall aa : AxisAngle, quat2aa (aa2quat aa) = aa.
  Proof.
    intros. destruct aa. lqa.
  Abort.

End quat_aa.


(** ** Rotate 3D vector by unit quaternion *)
Section qrot.
  
  (** vector v (be wrapped to quaterion) is rotated by a quaternion q.
      Note that: q must be a rotation quaternion *)
  Definition qrot (q : quat) (v : quat) : quat := q * v * q⁻¹.

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
  Section spec1.
    Local Open Scope fun_scope.
    Lemma qrot_spec : forall (θ : R) (n : cvec 3) (H : cvunit n) (v : cvec 3),
        let q := aa2quat (θ, n) in
        (qrot q (qpure v)).Im == rotAxisAngle θ n v.
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

  End spec1.

  (** 方法2：QQ书上的推导过程 *)
  Section spec2.

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
       (1). 两个3D单位向量 v0 v1 (v0 ≠ ± v1，即，不共线)，
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
        qunit q -> cvunit v -> cvunit ((qrot q (qpure v)).Im).
    Proof.
      intros. apply cvunit_spec. rewrite <- qrot_keep_cvlen; auto.
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
        let v2 : cvec 3 := (qrot q (qpure v0)).Im in
        uv2q v1 v2 = q.
    Proof.
      intros.
      rewrite uv2q_eq_uv2q'. unfold uv2q'. unfold v2.
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

    (** 论证旋转，逻辑有点绕口 *)
    Section rotation_spec.
      (* 任给两个3D单位向量 *)
      Variable v0 v1 : cvec 3.
      Hypotheses H0 : cvunit v0.
      Hypotheses H1 : cvunit v1.
      (* v0到v1的角度 *)
      Definition θ : R := 2 * cos (cvangle v0 v1).
      (* v0,v1平面的法向量 *)
      Definition v : cvec 3 := cvnormalize (v0 × v1).
      (* 构造出四元数 q，它的w分量是<v0,v1>, 向量分量是v0 × v1，具有一定的几何意义 *)
      Definition q : quat := uv2q v0 v1.
      (* 用 q 来旋转 v0 得到 v2 *)
      Definition v2 : cvec 3 := (qrot q (qpure v0)).Im.
      (* 用 q 来旋转 v1 得到 v3 *)
      Definition v3 : cvec 3 := (qrot q (qpure v1)).Im.

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
      Theorem qrot_relation : forall (vt : cvec 3) (s0 s1 s2 : R),
          (vt == s0 c* v0 + s1 c* v1 + s2 c* v)%CV ->
          let vt' : cvec 3 := (qrot q (qpure vt)).Im in
          cvangle vt vt' = θ (* 夹角是 θ *)
          /\ vt × vt' = v (* 法向量是 q *)
          /\ (||vt'|| = ||vt||)%CV (* 长度不变 *)
      .
      Proof.
        intros. split.
        2:{ split.
            (* 2:{ apply qrot_qpure_qunit. _keep_cvlen. *)
      Abort.

    End rotation_spec.

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
