(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Quaternion
  author      : ZhengPu Shi
  date        : 2021.12
  
  remark      :
  1. Introduction to Multicopter Design and Control, Springer, Quan Quan
     page 96
*)

From CoqMatrix Require Import VectorR.

Open Scope R.
Open Scope mat_scope.
Open Scope vec_scope.


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
  Definition quat_of_s_v (w : R) (v : vec 3) :=
    let '(x,y,z) := v2t_3 v in
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
  Definition quat_of_v3 (v : vec 3) : quat := quat_of_s_v 0 v.
  
  Lemma quat_of_v3_ok : forall v,
    let q := quat_of_v3 v in
      W q = R0 /\ X q = v!0 /\ Y q = v!1 /\ Z q = v!2.
  Proof. apply quat_of_s_v_ok. Qed.
  
  (** Construct a quaternion by a vec4 *)
  Definition quat_of_v4 (v : vec 4) : quat :=
    let '(w,x,y,z) := v2t_4 v in
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
  Definition v4_of_quat (q : quat) : vec 4 :=
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

(** Left scalar multiplication *)
Definition qcmul (c : R) (q : quat) : quat := 
  let w1 := (c * Re  q)%R in
  let x1 := (c * Im1 q)%R in
  let y1 := (c * Im2 q)%R in
  let z1 := (c * Im3 q)%R in
    mk_quat w1 x1 y1 z1.

(** Right scalar multiplication *)
Definition qmulc (q : quat) (c : R) : quat :=
  let w1 := (Re  q * c)%R in
  let x1 := (Im1 q * c)%R in
  let y1 := (Im2 q * c)%R in
  let z1 := (Im3 q * c)%R in
    mk_quat w1 x1 y1 z1.

(** Multiplication of two quaternions *)
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
  let pv : vec 3 := t2v_3 (Im p) in
  let qv : vec 3 := t2v_3 (Im q) in
  let w : R := (p0 * q0 - scalar_of_mat ((qv \T) * pv)%mat)%R in
  let v : vec 3 := (vcross3 pv qv + p0 c* qv + q0 c* pv)%mat in
    quat_of_s_v w v.

Lemma qmulVEC_correct (p q : quat) : 
  p * q = qmulVEC p q.
Proof.
  destruct p, q. lqa.
Qed.

(** Quaternion multiplication with PLUS form. page96, p+ *)
Definition quat_PLUS (q : quat) : mat 4 4 :=
  let p0 : R := Re q in
  let pv : vec 3 := t2v_3 (Im q) in
  let m1 : mat 4 4 := (p0 c* (mat1 4))%mat in
  let m2a : vec 4 := mconsr (mk_mat_1_1 0) (-pv) in
  let m2b : mat 3 4 := mconsc pv (skew_sym_mat_of_v3 pv) in
  let m2 : mat 4 4 := mconsr m2a m2b in
    madd m1 m2.

Definition qmulPLUS (p q : quat) : quat :=
  let PLUS : mat 4 4 := quat_PLUS p in
    quat_of_v4 (PLUS * (v4_of_quat q))%mat.

Lemma qmulPLUS_correct (p q : quat) : 
  p * q = qmulPLUS p q.
Proof.
  destruct p, q. lqa.
Qed.

(** Quaternion multiplication with MINUS form. page96, p- *)
Definition quat_MINUS (q : quat) : mat 4 4 :=
  let q0 : R := Re q in
  let qv : vec 3 := t2v_3 (Im q) in
  let m1 : mat 4 4 := (q0 c* (mat1 4))%mat in
  let m2a : vec 4 := mconsr (mk_mat_1_1 0) (-qv) in
  let m2b : mat 3 4 := mconsc qv (-(skew_sym_mat_of_v3 qv))%mat in
  let m2 : mat 4 4 := mconsr m2a m2b in
    madd m1 m2.

Definition qmulMINUS (p q : quat) :=
  let MINUS : mat 4 4 := quat_MINUS q in
    quat_of_v4 (MINUS * (v4_of_quat p))%mat.
    
Lemma qmulMINUS_correct (p q : quat) : 
  p * q = qmulMINUS p q.
Proof.
  destruct p, q. lqa.
Qed.


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
Lemma qmul_qadd_dist_l (q r m : quat) :
  q * (r + m) = q * r + q * m.
Proof.
  destruct q,r,m. lqa.
Qed.

(* (r + m) * q = r * q + m * q *)
Lemma qmul_qadd_dist_r (r m q : quat) :
  (r + m) * q = r * q + m * q.
Proof.
  destruct r,m,q. lqa.
Qed.

(* (q * r) * m = q * (r * m) *)
Lemma qmul_assoc (q r m : quat) :
  (q * r) * m = q * (r * m).
Proof.
  destruct q,r,m. lqa.
Qed.

(** <3> constant multiplication law *)

(* s * q = q * s *)
Lemma qcmul_eq_qmulc (s : R) (q : quat) : 
  s c* q = q *c s.
Proof.
  destruct q. lqa.
Qed.

(* s * q = [s q0; s qv]^T *)
Lemma qcmul_eq (s : R) (q : quat) :
  let q0 := Re q in
  let qv := t2v_3 (Im q) in 
  s c* q = quat_of_s_v (s * q0) (s c* qv)%vec.
Proof.
  destruct q. lqa.
Qed.

(* q * s = [s q0; s qv]^T *)
Lemma qmulc_eq (s : R) (q : quat) :
  let q0 := Re q in
  let qv := t2v_3 (Im q) in 
  q *c s = quat_of_s_v (s * q0) (s c* qv)%vec.
Proof.
  destruct q. lqa.
Qed.

(** <4> multplication by image part of two quaternions *)

(* [0;u]^T * [0;v]^T = [(-u^T)*v; u×v]^T *)
Lemma qmul_by_im (u v : vec 3) :
  let qu : quat := quat_of_v3 u in
  let qv : quat := quat_of_v3 v in
  let q : quat := quat_of_s_v
                    (- (scalar_of_mat (u\T * v)%mat))
                    (vcross3 u v) in
  qu * qv = q.
Proof.
  lqa.
Qed.

(** (3) Conjugate of quaternion *)
Definition qconj (q : quat) : quat :=
  let w : R := Re q in
  let v : vec 3 := - (t2v_3 (Im q)) in
    quat_of_s_v w v.

Notation "q ∗" := (qconj q) (at level 30) : quat_scope.

(** Properties of conjugate *)

(* q ∗ ∗ = q *)
Lemma qconj_conj (q : quat) : q ∗ ∗ = q.
Proof.
  destruct q. lqa.
Qed.

(* (p * q)∗ = q∗ * p∗ *)
Lemma qconj_qmul_dist (p q : quat) : (p * q)∗ = q∗ * p∗.
Proof.
  destruct p,q. lqa.
Qed.

(* (p + q)∗ = q∗ + p∗ *)
Lemma qconj_qadd_dist (p q : quat) : (p + q)∗ = q∗ + p∗.
Proof.
  destruct p,q. lqa.
Qed.

(* q * q∗ = q∗ * q *)
Lemma qmul_qconj_comm (q : quat) : q * q∗ = q∗ * q.
Proof.
  destruct q. lqa.
Qed.

(* Im (q * q∗) = (0,0,0) *)
Lemma qmul_qconj_Re_eq_0 (q : quat) : Im (q * q∗) = (0,0,0)%R.
Proof.
  destruct q. lqa.
Qed.

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
Proof.
  intros. destruct q. compute. apply sqrt_sqrt.
  (* Tips: a good example for tactic ra *)
  ra.
Qed.

(* ‖ q ‖² = qnorm2 q *)
Lemma qnorm_sqr_eq_qnorm2 : forall (q : quat),
  (‖ q ‖²)%R = qnorm2 q.
Proof.
  intros. unfold Rsqr. apply qnorm_mul_qnorm_eq_qnorm2.
Qed.

(* 0 <= ‖ q ‖ *)
Lemma zero_le_qnorm : forall (q : quat), (0 <= qnorm q)%R.
Proof.
  intros. destruct q. unfold qnorm. apply sqrt_pos.
Qed.


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
Proof.
  destruct q. lqa. apply Rsqr_inj; ra.
  lqa. ra.
Qed.

(** ‖ q ‖² = q0^2 + qv^T * qv *)
Lemma qnorm2_eqation2 : forall (q : quat),
  let q0 := Re q in
  let qv := t2v_3 (Im q) in
    qnorm2 q = (q0 * q0 + (scalar_of_mat (qv\T * qv)%mat))%R.
Proof.
  destruct q. lqa.
Qed.

(** Norm of the multiplication of two quaternions, equal to the multiplication of 
    the norms of these two quaternions. *)
Lemma qnorm_qmul_distr : forall (p q : quat),
  ‖ p * q ‖ = (‖ p ‖ * ‖ q ‖)%R.
Proof.
  intros. destruct p,q. lqa.
  apply Rsqr_inj; ra. lqa; ra.
Qed.

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
Lemma quat_neq0_iff_qnorm2_neq0 : forall q,
  (q <> mk_quat 0 0 0 0) <-> (qnorm2 q <> R0).
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
Lemma qmul_qinv_unitary : forall (q : quat), ‖ q ‖ <> R0 ->
  q * (qinv q) = quat_of_s 1.
Proof.
  intros. destruct q. rewrite qnorm_neq0_iff_qnorm2_neq0 in H. lqa; auto.
Qed.

Lemma qmul_qinv_unitary_rev : forall (q : quat), ‖ q ‖ <> R0 ->
  (qinv q) * q = quat_of_s 1.
Proof.
  intros. destruct q. rewrite qnorm_neq0_iff_qnorm2_neq0 in H. lqa; auto.
Qed.

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

Lemma qunit_qmul_unit (p q : quat) :
  qunit p -> 
  qunit q -> 
  ‖ p * q ‖ = R1.
Proof.
  destruct p,q. intros. rewrite qnorm_qmul_distr. rewrite H,H0. ring.
Qed.

(** qunit q -> w0 * w0 + x0 * x0 + y0 * y0 + z0 * z0 = R1 *)
Lemma qunit_imply_eq_R1 : forall w0 x0 y0 z0,
  let q := mk_quat w0 x0 y0 z0 in
    qunit q ->
    (w0 * w0 + x0 * x0 + y0 * y0 + z0 * z0)%R = R1.
Proof.
  intros. apply qunit_iff_qunit2 in H. compute in H. auto.
Qed.

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
From CoqMatrix Require Import ExtrOcamlR.
(* Extract Constant Rabst => "__". *)
(* Extract Constant Rrepr => "__". *)
(* Search quat. *)
Recursive Extraction mk_quat quat_of_ssss quat_of_t4 qmul qconj qinv qnorm rot_by_quat.
Extraction "quat.ml" mk_quat quat_of_ssss quat_of_t4  qmul qconj qinv qnorm rot_by_quat.

?
(** 四元数p经过单位四元数q作用后得到四元数p'，其标量部分保持不变。公式5.26 *)
(* Lemma rot_by_unit_quat_keep_s : forall (q p : quat) (H1 : qunit q),
  W p = W (rot_by_quat q p).
Proof.
  intros. unfold rot_by_quat. 
  rewrite qunit_imply_qinv_eq_qconj; auto.
  destruct q,p. simpl. ring_simplify.
  apply qunit_imply_eq_R1 in H1.
  match goal with
  | |- W1 = ?A => assert (A = W1 * (W0^2 + X0^2 + Y0^2 + Z0^2))%R
  end; try ring.
  rewrite <- ?Rsqr_pow2. unfold Rsqr.
  rewrite H1. apply qunit_iff_qunit2 in H1. compute in H1.
  repeat rewrite <- Rsqr_pow2. unfold Rsqr. rewrite H1. ring.
Qed. *)

(** 利用四元数进行向量旋转的公式 5.24 *)
Definition vec_rot_by_quat (q : quat) (v : vec 3) : quat :=
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
Definition vec_rot_by_quat_IM (q : quat) (v : vec 3) : vec 3 :=
  t2v_3 (Im (vec_rot_by_quat q v)).

(** 单位四元数的另一种表示形式：由三维旋转轴和旋转角构成 5.25 *)
Definition qrot_by_axis_angle (v : vec 3) (θ : R) : quat :=
  quat_of_s_v (cos (θ/2)) (v *c (sin (θ/2)))%mat.

(* 若旋转轴 v 是单位向量，则依转轴和转角生成的四元数是单位四元数 *)
Lemma qrot_by_axis_angle_keep_unitary : forall v θ,
  vlen v = 1 -> qunit (qrot_by_axis_angle v θ).
Proof.
  intros.
  v3_to_three_ele v. unfold v3norm in H. simpl in *.
  inversion vlen. inversion w1. inversion w2. inversion w3.
  apply length_zero_iff_nil in H1,H2,H3,H4. subst; simpl in *.
  unfold vnorm in *. simpl in *.
  Opaque cos sin sqrt. lqa. remember (θ * / (R1 + R1))%R.
  match goal with 
  | |- sqrt ?A == R1 => assert (A = 1)
  end.
  - repeat rewrite Rplus_assoc.
    replace (a * sin r * (a * sin r) + (a0 * sin r * (a0 * sin r) + 
      a1 * sin r * (a1 * sin r)))%R with (sin r * sin r)%R.
    trigo_simp. ring_simplify. remember (sin r ^ 2).
    apply sqrt_eqR1_imply_R1 in H. rewrite Rplus_0_l in H.
    replace (r0 * a ^ 2 + r0 * a0 ^ 2 + r0 * a1 ^ 2)%R with
      (r0 * (a * a + a0 * a0 + a1 * a1))%R.
    + rewrite H. ring.
    + field.
  - rewrite H0. apply sqrtR1_R1.
Qed.


(** 四元数能表示三维旋转的定理 Th5.1 *)

(* (1) 通过四元数进行向量旋转会保持向量范数不变 *)
Lemma vec_rot_by_quat_keep_norm : forall (pv : vec 3) (q : quat) (H : qunit q),
  let pv' := vec_rot_by_quat q pv in
  v3norm pv = v3norm pv'.
Proof.
  intros. unfold v3norm. unfold pv'. ?
  unfold vec_rot_by_quat. ?  
  
  intros. v3_to_three_ele pv. simpl in *.
  inversion vlen. inversion w1. inversion w2. inversion w3.
  apply length_zero_iff_nil in H1,H2,H3,H4. subst; simpl in *.
  unfold pv'. unfold v3norm. unfold vnorm. f_equal.
  unfold vec_rot_by_quat.
  rewrite qunit_imply_qinv_eq_qconj; auto. simpl.
  unfold qunit in H.
  destruct q. simpl in *. lqa. repeat trigo_simp.
  
  assert (w0 * w0 + x0 * x0 + y0 * y0 + z0 * z0 = R1)%R.
  { unfold qnorm in H. apply sqrt_eqR1_imply_R1 in H.
    unfold qnorm2 in H. simpl in *. auto. }
  match goal with
  | |- ?A = ?B => replace B with
    ((t² + t0² + t1²) * (w0 * w0 + x0 * x0 + y0 * y0 + z0 * z0))%R
  end.
  rewrite H0; ring. ring_simplify.
  
  
  
   lqa. ring. ring_simplify. compute. ring_simplify. simpl.
  ring_simplify. compute. simpl.
  unfold qnorm in H. apply sqrt_eqR1_imply_R1 in H.
  unfold qnorm2 in H. simpl in H. rewrite H. ring.
  ring_simplify.
  
  
  compute. ring_simplify.
  apply Rminus_diag_uniq.
  ring_simplify. compute. trigo_simp.
  assert (forall r1 r2, r1 - r2 = R0 -> r1 = r2)%R.
  { intros. Search (_ - _ = 0)%R. ring. }
  apply H0.
  Search (_ = _ -> _).
  simpl. trigo_simp. ring_simplify.
  
  
  Search (_ * /R1).
  Search (/R1).
   
  repeat trigo_simp. 
  Search (R1).
  
  autorewrite with R.
  rewrite Rmul
   unfold qunit in H.
  Search qunit. ?
  unfold qnorm2. simpl.
  
  Search qunit. apply meq_iff. lqa.
  remember (/ (w0 * w0 + x0 * x0 + y0 * y0 + z0 * z0)).
  rewrite ?Rmult_0_l,?Rmult_0_r,?Rplus_0_l,?Rplus_0_r.
  ring_simplify.
  
   ring_simplify. compute. simpl in *. lqa; ring. compute. simpl in *. f_equal. simpl in *. compute. simpl in *.
  simpl in *.
  compute in pv'.
  subst.
  
  
  destruct q. lqa. f_equal. field.
  unfold qunit in H. fold qnorm2.
  assert (‖ {| w := w0; x := x0; y := y0; z := z0 |} ‖ <> 0). lra.
  apply qnorm_neq0_iff_qnorm2_neq0 in H0. auto.
Qed.

(* (2) 任意非零实数s与q相乘，结论仍然成立 *)
Lemma vec_rot_by_quat_keep_norm_ext : forall (pv : vec 3) (s : R) (q : quat) 
  (H : qunit q) (H1 : s <> 0),
  let q' := s c* q in
  let pv' := vec_rot_by_quat q' pv in
  v3norm pv = v3norm pv'.
Proof.
  intros. v3_to_three_ele pv. destruct q. lqa. f_equal. field.
  unfold qunit in H. fold qnorm2.
  assert (‖ {| w := w0; x := x0; y := y0; z := z0 |} ‖ <> 0). lra.
  apply qnorm_neq0_iff_qnorm2_neq0 in H0. auto.
  replace (s * w0 * (s * w0) + s * x0 * (s * x0) + s * y0 * (s * y0) 
    + s * z0 * (s * z0))%R 
    with ((s * s) * (qnorm2 {| w := w0; x := x0; y := y0; z := z0 |}))%R.
  repeat apply Rmult_integral_contrapositive_currified; auto. lqa.
Qed.

(* (3) 公式5.25中的四元数作用：绕v轴旋转θ角度。
 换言之，公式5.25是如何构造的？它为什么能不表示旋转 *)

(* 根据两个单位来计算夹角、转轴。*)
Definition rot_angle_by_twovec (v0 v1 : vec 3) : R := 
  acos (scalar_of_mat (v0 ⊤ × v1)).

Definition rot_axis_by_twovec (v0 v1 : vec 3) : vec 3 :=
  let s : R := (v3norm v0 * v3norm v1)%R in
    (s c* (v3cross v0 v1))%mat.

(* 谓词：两向量不共线（不平行的） *)
Definition v3_non_colinear (v0 v1 : vec 3) : Prop :=
  v0 <> v1 /\ v0 <> (-v1)%mat.
  
(* 两个不共线的单位向量确定了一个旋转。*)

(* 两个不共线的

(* 按旋转轴和旋转角表示的四元数，等于，用旋转轴垂直平面上两个单位向量的运算来构造的
四元数 *)
Definition qrot_by_two_vec_ops (v0 v1 : vec 3) : quat :=
  quat_of_s_v (scalar_of_mat (v0 ⊤ × v1)) (v3cross v0 v1).


(* (* 若单位向量v0和v1的夹角是 θ/2，且不共线，则由它们生成的垂直方向的向量v有确定形式 *)
Lemma gen_vec_by_v0_v1_eq : forall (v0 v1 : vec 3) (θ : R) (H1 : v3norm v0 = 1)
  (H2 : v3norm v1 = 1) (H3 : v3_non_colinear v0 v1),
  v3cross v0 v1 =  *)
  
