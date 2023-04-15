(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Quaternion
  author    : ZhengPu Shi
  date      : 2022.06

  remark    :
  1. Introduction to Multicopter Design and Control, Springer, Quan Quan
     page 96
*)

Require Import VectorR.

Open Scope R.
Open Scope mat_scope.
Open Scope cvec_scope.


(* ######################################################################### *)
(** * Definition of Quaternion *)

Section quat_def.

  (** A quaternion q = w + x i + y j + z k, can be considered as a linear 
    combination with the basis of {1, i, j, k} *)
  Record quat : Type := mk_quat {
    W : R;
    X : R;
    Y : R;
    Z : R
  }.

  (** Get the component of a given quaternion number q *)
  Definition Re (q : quat) : R := W q.
  Definition Im (q : quat) : T3 := (X q, Y q, Z q).
  Definition Im1 (q : quat) : R := X q.
  Definition Im2 (q : quat) : R := Y q.
  Definition Im3 (q : quat) : R := Z q.
  Definition v3_of_quat (q : quat) : cvec 3 :=
    mk_mat_3_1 (X q) (Y q) (Z q).
  
  (** Two quaternions are equal iff all of its components equal *)
  Lemma quat_eq_iff : forall (w0 x0 y0 z0 w1 x1 y1 z1 : R),
    mk_quat w0 x0 y0 z0 = mk_quat w1 x1 y1 z1 <->
    (w0 = w1 /\ x0 = x1 /\ y0 = y1 /\ z0 = z1).
  Proof.
    intros. split; intros.
    - inversion H. subst; auto.
    - do 3 destruct H as [? H]. subst; auto.
  Qed.
  
  (** Two quaternions are not equal iff at least one of its components not equal *)
  Lemma quat_neq_iff : forall (w0 x0 y0 z0 w1 x1 y1 z1 : R),
    mk_quat w0 x0 y0 z0 <> mk_quat w1 x1 y1 z1 <->
    (w0 <> w1 \/ x0 <> x1 \/ y0 <> y1 \/ z0 <> z1).
  Proof.
    intros. split; intros.
    - unfold not in H. rewrite quat_eq_iff in H.
      (* automatic proof *)
      (* lra. *)
      (* manual proof *)
      remember (w0=w1) as a.
      remember (x0=x1) as b.
      remember (y0=y1) as c.
      remember (z0=z1) as d.
      assert (~a \/ ~(b/\c/\d)).
      apply Decidable.not_and in H; auto.
      rewrite Heqa. compute. destruct (Req_EM_T w0 w1); auto.
      destruct H0. left; auto. right.
      apply Decidable.not_and in H0.
      destruct H0. left; auto. right; auto.
      apply Decidable.not_and in H0; auto.
      rewrite Heqc. compute. destruct (Req_EM_T y0 y1); auto.
      rewrite Heqb. compute. destruct (Req_EM_T x0 x1); auto.
    - intro. inversion H0. subst. lra.
  Qed.

  (** Construct a quaternion by 4 scalar number *)
  Definition quat_of_ssss (w x y z : R) : quat :=
    mk_quat w x y z.

  Lemma quat_of_ssss_ok : forall w x y z,
    let q := quat_of_ssss w x y z in
      W q = w /\ X q = x  /\ Y q = y /\ Z q = z.
  Proof. intros. split; auto. Qed.

  (** Construct a quaternion by a scalar number and a 3-dim vector *)
  Definition quat_of_s_v (w : R) (v : cvec 3) :=
    let '(x,y,z) := cv2t_3 v in
      mk_quat w x y z.

  Lemma quat_of_s_v_ok : forall w v,
    let q := quat_of_s_v w v in
      W q = w /\ X q = v!0  /\ Y q = v!1 /\ Z q = v!2.
  Proof. intros. split; auto. Qed.

  (** Construct a quaternion by a scalar number *)
  Definition quat_of_s (w : R) : quat := mk_quat w 0 0 0.
  
  Lemma quat_of_s_ok : forall w,
    let q := quat_of_s w in
      W q = w /\ X q = R0 /\ Y q = R0 /\ Z q = R0.
  Proof. intros. compute. auto. Qed.

  (** Construct a quaternion by a 3-dim vector *)
  Definition quat_of_v3 (v : cvec 3) : quat := quat_of_s_v 0 v.
  
  Lemma quat_of_v3_ok : forall v,
    let q := quat_of_v3 v in
      W q = R0 /\ X q = v!0 /\ Y q = v!1 /\ Z q = v!2.
  Proof. apply quat_of_s_v_ok. Qed.
  
  (** Construct a quaternion by a vec4 *)
  Definition quat_of_v4 (v : cvec 4) : quat :=
    let '(w,x,y,z) := cv2t_4 v in
      mk_quat w x y z.
  
  Lemma quat_of_v4_ok : forall v,
    let q := quat_of_v4 v in
      W q = v!0 /\ X q = v!1 /\ Y q = v!2 /\ Z q = v!3.
  Proof. intros. compute. auto. Qed.
  
  (** Construct a quaternion by tuple4 *)
  Definition quat_of_t4 (t : T4) : quat :=
    let '(w,x,y,z) := t in
      mk_quat w x y z.
      
  Lemma quat_of_t4_ok : forall t,
    let q := quat_of_t4 t in
    let '(a,b,c,d) := t in
      W q = a /\ X q = b /\ Y q = c /\ Z q = d.
  Proof. intros. destruct t as [[[a b] c] d]. compute. auto. Qed.
  
  (** Quaternion to vec4 *)
  Definition v4_of_quat (q : quat) : cvec 4 :=
    let '(w,x,y,z) := (W q, X q, Y q, Z q) in
      mk_mat_4_1 w x y z.
  
  Lemma v4_of_quat_ok : forall q,
    let v := v4_of_quat q in
      v!0 = W q /\ v!1 = X q /\ v!2 = Y q /\ v!3 = Z q.
  Proof. intros. compute. auto. Qed.
  
  (** Quaternion to tuple4 *)
  Definition t4_of_quat (q : quat) : T4 :=
    (W q, X q, Y q, Z q).
  
  Lemma t4_of_quat_ok : forall q,
    let t := t4_of_quat q in
      t = (W q, X q, Y q, Z q).
  Proof. auto. Qed.
  
End quat_def.


(* ######################################################################### *)
(** * Customized tactical for proof *)

(** Auto f_equal apply to some structure, eg: list, pair, record *)
Ltac f_equal_auto :=
  repeat match goal with
  (* (a,b) = (c,d) *)
  | |- (_,_) = (_,_) => f_equal
  (* [_;_] = [_;_] *)
  | |- cons _ _ = cons _ _ => f_equal
  (* (p : quat) = (q : quat) *)
  | |- _ = _ => try (apply quat_eq_iff; 
    (* a /\ b /\ c /\ d *)
    try repeat split)
  end.

Example f_equal_auto_test1 : forall A (a b c d : A), 
  a = c -> b = d -> (a,b) = (c,d).
Proof. intros. f_equal_auto; auto. Qed.

Example f_equal_auto_test2 : forall A (ha hb : A) (tla tlb : list A), 
  ha = hb -> tla = tlb -> ha :: tla = hb :: tlb.
Proof. intros. f_equal_auto; auto. Qed.

Example f_equal_auto_test3 : forall (w0 x0 y0 z0 w1 x1 y1 z1 : R)
  (H : w0 = w1) (H0 : x0 = x1) (H1 : y0 = y1) (H2 : z0 = z1),
  mk_quat w0 x0 y0 z0 = mk_quat w1 x1 y1 z1.
Proof. intros. f_equal_auto; auto. Qed.

(** Linear Quaternion Algebra, q1 = q2. *)
Ltac lqa (* tac *) :=
(*   tac; *)
  (* simplify sqrt and pow2 *)
  simpl_sqrt_pow2;
  compute;
  f_equal_auto;
  try field.


(* ######################################################################### *)
(** * Quaternion operations *)

(** (1) Addition, Subtraction *)
Definition qadd (q1 q2 : quat) : quat := mk_quat 
  (Re q1 + Re q2) 
  (Im1 q1 + Im1 q2) 
  (Im2 q1 + Im2 q2) 
  (Im3 q1 + Im3 q2).

Definition qsub (q1 q2 : quat) : quat := mk_quat
  (Re q1 - Re q2) 
  (Im1 q1 - Im1 q2) 
  (Im2 q1 - Im2 q2) 
  (Im3 q1 - Im3 q2).

(** (2) Multiplication *)


(** Multiplication of two quaternions *)
Definition qmul' (p q : quat) : quat :=
  let p0 := Re p in
  let p1 := Im1 p in
  let p2 := Im2 p in
  let p3 := Im3 p in
  let q0 := Re q in
  let q1 := Im1 q in
  let q2 := Im2 q in
  let q3 := Im3 q in
    mk_quat
      (p0 * q0 - p1 * q1 - p2 * q2 - p3 * q3) 
      (p0 * q1 + p1 * q0 + p2 * q3 - p3 * q2) 
      (p0 * q2 - p1 * q3 + p2 * q0 + p3 * q1) 
      (p0 * q3 + p1 * q2 - p2 * q1 + p3 * q0).


Definition qmul (q1 q2 : quat) : quat :=
  let w1 := Re q1 in
  let x1 := Im1 q1 in
  let y1 := Im2 q1 in
  let z1 := Im3 q1 in
  let w2 := Re q2 in
  let x2 := Im1 q2 in
  let y2 := Im2 q2 in
  let z2 := Im3 q2 in
    mk_quat
      (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) 
      (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) 
      (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) 
      (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2).

(** Left scalar multiplication *)
Definition qcmul (s : R) (q : quat) : quat :=
  let w := (s * Re q)%R in
  let v := s c* v3_of_quat q in
  quat_of_s_v w v.

(* s * q = [s q0; s qv]^T *)
Lemma qcmul_eq : forall (s : R) (q : quat),
    let pq1 := qmul (quat_of_s s) q in
    let pq2 := qcmul s q in
    pq1 = pq2.
Proof. destruct q. lqa. Qed.

(** Right scalar multiplication *)
Definition qmulc (q : quat) (s : R) : quat :=
  let w := (Re q * s)%R in
  let v := (v3_of_quat q) *c s in
  quat_of_s_v w v.

(* q * s = [s q0; s qv]^T *)
Lemma qmulc_eq : forall (q : quat) (s : R),
    let pq1 := qmul q (quat_of_s s) in
    let pq2 := qmulc q s in
    pq1 = pq2.
Proof. intros. destruct q. lqa. Qed.

(** Scope for quaternion *)
Declare Scope quat_scope.
Delimit Scope quat_scope with q.
Open Scope quat_scope.

Bind Scope quat_scope with quat.

(** Useful notations *)
Notation "p + q" := (qadd p q) 
  (at level 50, left associativity) : quat_scope.
Notation "p - q" := (qsub p q) 
  (at level 50, left associativity) : quat_scope.
Notation "a c* q" := (qcmul a q) 
  (at level 40, left associativity) : quat_scope.
Notation "q *c a" := (qmulc q a)
  (at level 40, left associativity) : quat_scope.
Notation "p * q" := (qmul p q) 
  (at level 40, left associativity) : quat_scope.

(** Multiplication of two quaternions by vector form，(p96)
        |p0|   |q0|   |p0 q0 - qv^T pv         |
p ⊗ q = |pv| + |qv| = |pv x qv + p0 qv + q0 pv |
 *)
Definition qmulVEC (p q : quat) : quat :=
  let p0 : R := Re p in
  let q0 : R := Re q in
  let pv : cvec 3 := t2cv_3 (Im p) in
  let qv : cvec 3 := t2cv_3 (Im q) in
  let w : R := (p0 * q0 - scalar_of_mat ((qv \T) * pv)%M)%R in
  let v : cvec 3 := (cv3cross pv qv + p0 c* qv + q0 c* pv)%M in
    quat_of_s_v w v.

Lemma qmulVEC_correct (p q : quat) : p * q = qmulVEC p q.
Proof. destruct p, q. lqa. Qed.

(** Quaternion multiplication with PLUS form. page96, p+ *)
Definition qPLUS (q : quat) : mat 4 4 :=
  let p0 : R := Re q in
  let pv : cvec 3 := t2cv_3 (Im q) in
  let m1 : mat 4 4 := (p0 c* mat1)%M in
  let m2a : mat 1 4 := mconsc (mk_mat_1_1 0) (-(pv\T))%M in
  let m2b : mat 3 4 := mconsc pv (cv3_skew_sym_mat pv) in
  let m2 : mat 4 4 := mconsr m2a m2b in
    madd m1 m2.

Definition qmulPLUS (p q : quat) : quat :=
  let PLUS : mat 4 4 := qPLUS p in
    quat_of_v4 (PLUS * (v4_of_quat q))%M.

Lemma qmulPLUS_correct (p q : quat) : p * q = qmulPLUS p q.
Proof. destruct p, q. lqa. Qed.

(** Quaternion multiplication with MINUS form. page96, p- *)
Definition qMINUS (q : quat) : mat 4 4 :=
  let q0 : R := Re q in
  let qv : cvec 3 := t2cv_3 (Im q) in
  let m1 : mat 4 4 := (q0 c* mat1)%M in
  let m2a : mat 1 4 := mconsc (mk_mat_1_1 0) (-(qv\T))%M in
  let m2b : mat 3 4 := mconsc qv (-(cv3_skew_sym_mat qv))%M in
  let m2 : mat 4 4 := mconsr m2a m2b in
    madd m1 m2.

Definition qmulMINUS (p q : quat) :=
  let MINUS : mat 4 4 := qMINUS q in
    quat_of_v4 (MINUS * (v4_of_quat p))%M.
    
Lemma qmulMINUS_correct (p q : quat) : p * q = qmulMINUS p q.
Proof. destruct p, q. lqa. Qed.


(* ######################################################################### *)
(** * Properties of quaternion multiplication *)

(** <1> It is non-commutative. *)

(* p * q <> q * p. *)
Lemma qmul_not_comm : exists (p q : quat), p * q <> q * p.
Proof.
  exists (quat_of_t4 (0,1,2,1)%R).
  exists (quat_of_t4 (0,2,1,2)%R).
  compute. intros. inversion H. lra.
Qed.

(** <2> distributive and associative *)

(* q * (r + m) = q * r + q * m *)
Lemma qmul_qadd_dist_l (q r m : quat) : q * (r + m) = q * r + q * m.
Proof. destruct q,r,m. lqa. Qed.

(* (r + m) * q = r * q + m * q *)
Lemma qmul_qadd_dist_r (r m q : quat) : (r + m) * q = r * q + m * q.
Proof. destruct r,m,q. lqa. Qed.

(* (q * r) * m = q * (r * m) *)
Lemma qmul_assoc (q r m : quat) : (q * r) * m = q * (r * m).
Proof. destruct q,r,m. lqa. Qed.

(** <3> constant multiplication law *)

(* s * q = q * s *)
Lemma qcmul_eq_qmulc (s : R) (q : quat) : s c* q = q *c s.
Proof. destruct q. lqa. Qed.

(** <4> multplication by image part of two quaternions *)

(* [0;u]^T * [0;v]^T = [(-u^T)*v; u×v]^T *)
Lemma qmul_by_im (u v : cvec 3) :
  let qu : quat := quat_of_v3 u in
  let qv : quat := quat_of_v3 v in
  let q : quat := quat_of_s_v
                    (- (scalar_of_mat (u\T * v)%M))
                    (cv3cross u v) in
  qu * qv = q.
Proof. lqa. Qed.

(** (3) Conjugate of quaternion *)
Definition qconj (q : quat) : quat :=
  let w : R := Re q in
  let v : cvec 3 := - (t2cv_3 (Im q)) in
    quat_of_s_v w v.

Notation "q ∗" := (qconj q) (at level 30) : quat_scope.

(** Properties of conjugate *)

(* q ∗ ∗ = q *)
Lemma qconj_conj (q : quat) : q ∗ ∗ = q.
Proof. destruct q. lqa. Qed.

(* (p * q)∗ = q∗ * p∗ *)
Lemma qconj_qmul_dist (p q : quat) : (p * q)∗ = q∗ * p∗.
Proof. destruct p,q. lqa. Qed.

(* (p + q)∗ = q∗ + p∗ *)
Lemma qconj_qadd_dist (p q : quat) : (p + q)∗ = q∗ + p∗.
Proof. destruct p,q. lqa. Qed.

(* q * q∗ = q∗ * q *)
Lemma qmul_qconj_comm (q : quat) : q * q∗ = q∗ * q.
Proof. destruct q. lqa. Qed.

(* Im (q * q∗) = (0,0,0) *)
Lemma qmul_qconj_Re_eq_0 (q : quat) : Im (q * q∗) = (0,0,0)%R.
Proof. destruct q. lqa. Qed.

(** (4) Norm *)

(** ** norm *)

(** The square of norm of a quaternion *)
Definition qnorm2 (q : quat) : R :=
  let '(w0,x0,y0,z0) := t4_of_quat q in
    (w0 * w0) + (x0 * x0) + (y0 * y0) + (z0 * z0).

(* 0 <= qnorm2 q *)
Lemma zero_le_qnorm2 : forall (q : quat), (0 <= qnorm2 q)%R.
Proof.
  intros. destruct (t4_of_quat q) as [[[w0 x0] y0] z0].
  unfold qnorm2. simpl. ra.
Qed.

Global Hint Resolve zero_le_qnorm2 : fcs.

(** The norm of a quaternion *)

(** Note, there are two methods for square root:
  1. sqrt，it will generate a proof goal of "the value inside the root sign is >=0",
     although this is easy to finish.
  2. Rsqrt，it will generate a proof goal of "Rsqrt_exists".
  We will use the former way.
*)
Definition qnorm (q : quat) : R := sqrt (qnorm2 q).

(** This is the definition using Rsqrt. (This is deprecated) *)
Definition qnorm_old (q : quat) : R.
Proof.
  destruct q as [w x y z].
  set (w * w + x * x + y * y + z * z)%R as r.
  refine (Rsqrt (mknonnegreal r _)).
  unfold r. ra.
Defined.

Notation "‖ q ‖" := (qnorm q) (at level 50) : quat_scope.

(* ‖ q ‖ * ‖ q ‖ = qnorm2 q *)
Lemma qnorm_mul_qnorm_eq_qnorm2 : forall (q : quat),
  (‖ q ‖ * ‖ q ‖)%R = qnorm2 q.
Proof. intros. destruct q. compute. apply sqrt_sqrt.
  (* Tips: a good example for tactic ra *)
  ra.
Qed.

(* ‖ q ‖² = qnorm2 q *)
Lemma qnorm_sqr_eq_qnorm2 : forall (q : quat),
  (‖ q ‖²)%R = qnorm2 q.
Proof. intros. unfold Rsqr. apply qnorm_mul_qnorm_eq_qnorm2. Qed.

(* 0 <= ‖ q ‖ *)
Lemma zero_le_qnorm : forall (q : quat), (0 <= qnorm q)%R.
Proof. intros. destruct q. unfold qnorm. apply sqrt_pos. Qed.


(** Properties of norm or square of norm *)

(* (let (a, _) := Rsqrt_exists ?b _ in a) = _ *)
Ltac case_rsqrt_exists :=
  match goal with
  | |- (let (a, _) := Rsqrt_exists ?b _ in a) = _ => 
    destruct (Rsqrt_exists b) as [r Hr];
    (* 0 <= r /\ _ *)
    destruct Hr as [Hr1 Hr2]
  end.

(* ‖ q ‖²  = ‖ q * q∗ ‖ *)
Lemma qnorm2_eqation1 : forall (q : quat),
  qnorm2 q = ‖ q * q∗ ‖.
Proof. destruct q. lqa. apply Rsqr_inj; ra. lqa. ra. Qed.

(** ‖ q ‖² = q0^2 + qv^T * qv *)
Lemma qnorm2_eqation2 : forall (q : quat),
  let q0 := Re q in
  let qv := t2cv_3 (Im q) in
    qnorm2 q = (q0 * q0 + (scalar_of_mat (qv\T * qv)%M))%R.
Proof. destruct q. lqa. Qed.

(** Norm of the multiplication of two quaternions, equal to the multiplication of 
    the norms of these two quaternions. *)
Lemma qnorm_qmul_distr : forall (p q : quat), ‖ p * q ‖ = (‖ p ‖ * ‖ q ‖)%R.
Proof. intros. destruct p,q. lqa. apply Rsqr_inj; ra. lqa; ra. Qed.

(** The norm of conjugate equal to the norm *)
Lemma qnorm_qconj (q : quat) : ‖ q∗ ‖ = ‖ q ‖.
Proof.
  apply Rsqr_inj.
  - apply zero_le_qnorm.
  - apply zero_le_qnorm.
  - repeat rewrite qnorm_sqr_eq_qnorm2. lqa.
Qed.

(** The norm is not equal to 0, iff the square norm is not equal to 0 *)
Lemma qnorm_neq0_iff_qnorm2_neq0 : forall q, ‖ q ‖ <> R0 <-> qnorm2 q <> R0.
Proof.
  intros. rewrite <- qnorm_sqr_eq_qnorm2. remember (‖ q ‖). split; intros.
  - rewrite Rsqr_pow2. apply pow_nonzero. auto.
  - apply Rsqr_gt_0_0. apply Rlt_0_sqr. intro. rewrite H0 in H. compute in H.
    ra.
Qed.

(** A quaternion is not 0, iff its square norm is not 0 *)
Lemma quat_neq0_iff_qnorm2_neq0 : forall q, (q <> mk_quat 0 0 0 0) <-> (qnorm2 q <> R0).
Proof.
  intros. destruct q. rewrite quat_neq_iff. split; intros.
  - apply Rplus_sqr_neq0_iff4 in H. auto.
  - apply Rplus_sqr_neq0_iff4. auto.
Qed.

(** (5) Inversion *)

(* Definition of inversion of quaternion *)
Definition qinv (q : quat) : quat := (/ (qnorm2 q)) c* q∗.

(* Properties *)

(** Tips: a good example shows that Coq could find the hypthesis, 
    but the mathematical derivation maybe lost this promise. *)
Lemma qmul_qinv_unitary : forall (q : quat), ‖ q ‖ <> R0 -> q * (qinv q) = quat_of_s 1.
Proof. intros. destruct q. rewrite qnorm_neq0_iff_qnorm2_neq0 in H. lqa; auto. Qed.

Lemma qmul_qinv_unitary_rev : forall (q : quat), ‖ q ‖ <> R0 -> (qinv q) * q = quat_of_s 1.
Proof. intros. destruct q. rewrite qnorm_neq0_iff_qnorm2_neq0 in H. lqa; auto. Qed.

(** (6) Unit quaternion *)

(** q is a unit quaternion, with the help of qnorm *)
Definition qunit (q : quat) : Prop := ‖ q ‖ = R1.

(** q is a unit quaternion, with the help of qnorm2 *)
Definition qunit2 (q : quat) : Prop := qnorm2 q = R1.

(** qunit q <-> qunit2 q *)
Lemma qunit_iff_qunit2 : forall q, qunit q <-> qunit2 q.
Proof.
  intros q. unfold qunit,qunit2. rewrite <- qnorm_mul_qnorm_eq_qnorm2.
  split; intros.
  - rewrite H. ring.
  - unfold qnorm in *. rewrite sqrt_def in H.
    + rewrite H. ra.
    + apply zero_le_qnorm2.
Qed.

Lemma qunit_qmul_unit (p q : quat) : qunit p -> qunit q -> ‖ p * q ‖ = R1.
Proof.
  destruct p,q. intros. rewrite qnorm_qmul_distr. rewrite H,H0. ring.
Qed.

(** qunit q -> w0 * w0 + x0 * x0 + y0 * y0 + z0 * z0 = R1 *)
Lemma qunit_imply_eq_R1 : forall w0 x0 y0 z0,
  let q := mk_quat w0 x0 y0 z0 in
    qunit q ->
    (w0 * w0 + x0 * x0 + y0 * y0 + z0 * z0)%R = R1.
Proof. intros. apply qunit_iff_qunit2 in H. compute in H. auto. Qed.

(** qunit q -> qinv q = q∗ *)
Lemma qunit_imply_qinv_eq_qconj : forall q, qunit q -> qinv q = q∗.
Proof.
  intros. apply qunit_iff_qunit2 in H. destruct q. unfold qunit2 in *.
  compute in *. rewrite H. lqa.
Qed.

(** Division of quaternion *)

(** Division defined by left multiplication. r * p = m => r = m* inv p *) 
Definition qdivl (p m : quat) : quat := m * (qinv p).

(** Division defined by right multiplication. p * r = m => r = inv p * m *) 
Definition qdivr (p m : quat) : quat := (qinv p) * m.

(** (qdivl p m) * p = m *)
Lemma qdivl_correct : forall p m, p <> mk_quat 0 0 0 0 -> (qdivl p m) * p = m.
Proof.
  intros. destruct p,m.
  apply quat_neq_iff in H. lqa; apply Rplus_sqr_neq0_iff4; auto.
Qed.

(** p * (qdivr p m) = m *)
Lemma qdivr_correct : forall p m, p <> mk_quat 0 0 0 0 -> p * (qdivr p m) = m.
Proof.
  intros. destruct p,m.
  apply quat_neq_iff in H. lqa; apply Rplus_sqr_neq0_iff4; auto.
Qed.


(** Destruct v3 to theee element *)
Ltac v3_to_three_ele  v :=
  destruct v as [vdl vlen vwid];
  destruct vdl as [|l1]; [simpl in *; lia | idtac];
  destruct vdl as [|l2]; [simpl in *; lia | idtac];
  destruct vdl as [|l3]; [simpl in *; lia | idtac];
  (* width *)
  destruct vwid as [w1 vwid];
  destruct vwid as [w2 vwid];
  destruct vwid as [w3 vwid];
  (* list -> x *)
  destruct l1; [simpl in *; lia |];
  destruct l2; [simpl in *; lia |];
  destruct l3; [simpl in *; lia |].


(** 3. quaterion can represent rotation *)

(** vector v is rotated by a quaternion q *)
Definition rot_by_quat (q : quat) (v : quat) : quat := q * v * (qinv q).

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import MyExtrOCamlR.
(* Extract Constant Rabst => "__". *)
(* Extract Constant Rrepr => "__". *)
(* Search quat. *)
(* Recursive Extraction mk_quat quat_of_ssss quat_of_t4 qmul qconj qinv qnorm rot_by_quat. *)
(* Extraction "quat.ml" mk_quat quat_of_ssss quat_of_t4  qmul qconj qinv qnorm rot_by_quat. *)

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
  apply quat_neq0_iff_qnorm2_neq0 in H. auto.
Qed.

(** 四元数旋转向量后的四元数取出虚部作为向量 *)
Definition vec_rot_by_quat_IM (q : quat) (v : cvec 3) : cvec 3 :=
  t2cv_3 (Im (vec_rot_by_quat q v)).

(** 单位四元数的另一种表示形式：由三维旋转轴和旋转角构成 5.25 *)
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
  assert (v 0%nat 0%nat ^ 2 * r2 ^ 2 + (r2 ^ 2 * v 1%nat 0%nat ^ 2 + r2 ^ 2 * v 2%nat 0%nat ^ 2)
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
  intros. destruct q as [w x y z]. destruct pv as [pv].
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
  intros. destruct q as [w x y z]. destruct pv as [pv].
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
      cv2t_3 (rot_axis_by_twovec (t2cv_3 (0.23,0.43,0)) (t2cv_3 (1.25,3.1,4.7))).

Extraction "quat.ml"
  mk_quat quat_of_ssss quat_of_t4
  qmul qconj qinv qnorm rot_by_quat
  ex1.

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
(* Compute m2l (qPLUS q_e_b). *)

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
