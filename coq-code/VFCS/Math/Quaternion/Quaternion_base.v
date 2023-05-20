(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Quaternion_base (basic part)
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

  #[export] Instance quat_of_s_v_mor : Proper (eq ==> meq ==> eq) quat_of_s_v.
  Proof.
    simp_proper. intros. hnf in *.
    unfold quat_of_s_v; f_equal; auto; apply H0; auto.
  Qed.

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


(* Extract Constant Rabst => "__". *)
(* Extract Constant Rrepr => "__". *)
(* Extraction "quat.ml" mk_mat_3_1. (* Why so many warning? *) *)
(* Recursive Extraction mk_quat quat_of_wxyz quat_of_t4 qmul qconj qinv qlen rot_by_quat. *)
(* Extraction "quat.ml" mk_quat quat_of_wxyz quat_of_t4 qmul qconj qinv. qlen rot_by_quat. *)
