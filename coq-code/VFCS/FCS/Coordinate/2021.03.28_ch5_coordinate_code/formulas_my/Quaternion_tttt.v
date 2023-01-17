(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       quatuaternion_tttt.v
  by:         ZhengPu Shi
  purpose:    Quaternion implmentation based on tuple4.
  
  reference: 
  1. Formalizing basic quaternionic analysis, Andrea Gabrielli etc.
  
*)

(*
Require Import Nat.   (* Nat.eqb : nat -> nat -> bool *)
Require Import Bool.  (* Bool.eqb : bool -> bool -> bool *)
Require Import ZArith.
Require Import Reals.
*)
From FlyCtrl Require Import Basic.
From FlyCtrl Require Import Array.
From FlyCtrl Require Import Quaternion_aijk.


(* --------------------------------------------------------------- *)
(* Definitions and operations of quaternion *)

Module Module_quat (E : EType).
  Module quat_aijk := Module_Quaternion_aijk E.
  Export quat_aijk.

  Module ArrayE := Module_Array E.
  Import ArrayE.
  
  (* Quaternion implemented usig four real numbers in a particular order *)
  Record quat : Set := mk_quat {
    w : T;
    x : T;
    y : T;
    z : T
  }.

  (* I4 *)
  (* Definition I4 := M_4_4_unit_T. *)
  
  Definition quat_from_tuple4 (t : T * T * T * T) : quat :=
    let '(w,x,y,z) := t in
      mk_quat w x y z.
  Definition quat_to_tuple4 (q : quat) : T * T * T * T :=
    (w q, x q, y q, z q).

  (* Construct a quaternion by a scalar number and a 3-dim vector *)
  Definition quat_from_s_v (w : T) (v : array 3) :=
    let '(x,y,z) := a3_to_tuples v in
      mk_quat w x y z.
  
  (* Construct a quaternion by a scalar number *)
  Definition quat_from_s (w : T) : quat := quat_from_s_v w [0,0,0].

  (* Construct a quaternion by a 3-dim vector *)
  Definition quat_from_v (v : array 3) : quat := quat_from_s_v 0 v.

  (* get the component of a given quaternion *)
  Definition Re (q : quat) : T := w q.
  Definition Im (q : quat) : T * T * T := (x q, y q, z q).
  Definition Im1 (q : quat) : T := x q.
  Definition Im2 (q : quat) : T := y q.
  Definition Im3 (q : quat) : T := z q.
  
  (* conversion between qexp and quat *)
  Definition quat_from_qexp (e : qexp) : quat :=
    let '(w,x,y,z) := qexp_to_tuple4 e in
      mk_quat w x y z.
  Definition quat_to_qexp (q : quat) : qexp :=
      qexp_from_tuple4 (quat_to_tuple4 q).

  (*
  Check qexp_from_tuple4_equality.
  *)
  
  (* --------------------------------------------------------------- *)
  (* Basic operation rules *)

  (* (1) Addition, Subtraction *)
  Definition quat_add (q1 q2 : quat) : quat := mk_quat 
    (Re q1 + Re q2) 
    (Im1 q1 + Im1 q2) 
    (Im2 q1 + Im2 q2) 
    (Im3 q1 + Im3 q2).

  Definition quat_sub (q1 q2 : quat) : quat := mk_quat
    (Re q1 - Re q2) 
    (Im1 q1 - Im1 q2) 
    (Im2 q1 - Im2 q2) 
    (Im3 q1 - Im3 q2).
  
  (* (2) Multiplication *)
  Definition quat_cmul (c : T) (q : quat) : quat := 
    let w : T := c * (Re q) in
    let v : T * T * T := Im q in
    let v3 : array 3 := a_cmul c (a3_from_tuples v) in
      quat_from_s_v w v3.

  Definition quat_mulc (q : quat) (c : T) : quat :=
    let w : T := (Re q) * c in
    let v : T * T * T := Im q in
    let v3 : array 3 := a_mulc (a3_from_tuples v) c in
      quat_from_s_v w v3.

  Definition quat_mul (q1 q2 : quat) : quat :=
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
  
  Declare Scope quat_scope.
  Bind Scope quat_scope with quat.
  Delimit Scope quat_scope with quattype.
  Open Scope quat_scope.
  
  Notation "a + b" := (quat_add a b) 
    (at level 50, left associativity) : quat_scope.
  Notation "a - b" := (quat_sub a b) 
    (at level 50, left associativity) : quat_scope.
  Notation "a * b" := (quat_mul a b) 
    (at level 40, left associativity) : quat_scope.
  
  (* Some useful tactic, compute then split to components, then ring. *)
  Ltac comp_ring :=
    compute; 
    ring.
  Ltac comp_quat_ring :=
    compute; 
    f_equal; 
    ring.
  Ltac comp_tuple_ring :=
    compute; 
    simpl_equal_of_tuples; 
    ring.
  
  Lemma quat_mul_imp_qexp_mul (q1 q2 : quat) : quat_mul q1 q2 
    = quat_from_qexp ((quat_to_qexp q1) * (quat_to_qexp q2)).
  Proof.
    destruct q1,q2; comp_quat_ring.
  Qed.
  
  Section Something_I_want_prove_but_neednot_to_do.
  
    Lemma qexp_mul_imp_quat_mul (q1 q2 : qexp) : quat_from_qexp (q1 * q2) 
      = quat_mul (quat_from_qexp q1) (quat_from_qexp q2).
    Proof.
      unfold quat_from_qexp.
      generalize dependent q2.
      induction q1.
      Admitted.
      
  End Something_I_want_prove_but_neednot_to_do.


  Definition quat_mul_formu1 (q1 q2 : quat) : quat :=
    let w1 : T := Re q1 in
    let w2 : T := Re q2 in
    let v1 : array 3 := a3_from_tuples (Im q1) in
    let v2 : array 3 := a3_from_tuples (Im q2) in
    let v1m : matrix 3 1 := cv_to_m v1 in
    let v2m : matrix 3 1 := cv_to_m v2 in
    let w : T := (w1 * w2 - m_1x1_to_scalar (m_mul (v2m ') v1m))%element in
    let xyz : T * T * T := m_3x1_to_tuples (m_add (cv3_cross v1 v2)
      (m_add (m_cmul w1 v2m) (m_cmul w2 v1m))) in
    let '(x,y,z) := xyz in 
      mk_quat w x y z.
  
  Lemma quat_mul_formu1_correct (q1 q2 : quat) : 
    q1 * q2 = quat_mul_formu1 q1 q2.
  Proof.
    destruct q1,q2; comp_quat_ring.
  Qed.
  
  (* p+ *)
  Definition quat_PLUS (q : quat) : matrix 4 4 :=
    let w : T := Re q in
    let v : array 3 := a3_from_tuples (Im q) in
    let m1 : matrix 4 4 := m_cmul w I4 in
    let m2a : matrix 1 4 := 
      m_cons_byCol (m_make 1 1 Zero) (m_neg (rv_to_m v)) in
    let m2b : matrix 3 4 := 
      m_cons_byCol (cv_to_m v) (cv3_skew_symmetric_matrix v) in
    let m2 : matrix 4 4 := m_cons_byRow m2a m2b in
      m_add m1 m2.
  
  Definition quat_mul_formu_PLUS (q1 q2 : quat) : quat :=
    let PLUS : matrix 4 4 := quat_PLUS q1 in
    let m1 : matrix 4 1 := cv_to_m (a4_from_tuples (quat_to_tuple4 q2)) in
    let m2 : matrix 4 1 := m_mul PLUS m1 in
    let '(w,x,y,z) := a4_to_tuples (m_rx1_to_a m2) in
      mk_quat w x y z.
  
  Lemma quat_mul_formu_PLUS_correct (q1 q2 : quat) : 
    q1 * q2 = quat_mul_formu_PLUS q1 q2.
  Proof.
    destruct q1,q2; comp_quat_ring.
  Qed.
  
  (* p- *)
  Definition quat_MINUS (q : quat) : matrix 4 4 :=
    let w : T := Re q in
    let v : array 3 := a3_from_tuples (Im q) in
    let m1 : matrix 4 4 := m_cmul w I4 in
    let m2a : matrix 1 4 := 
      m_cons_byCol (m_make 1 1 Zero) (m_neg (rv_to_m v)) in
    let m2b : matrix 3 4 := 
      m_cons_byCol (cv_to_m v) (m_neg (cv3_skew_symmetric_matrix v)) in
    let m2 : matrix 4 4 := m_cons_byRow m2a m2b in
      m_add m1 m2.
  
  Definition quat_mul_formu_MINUS (q1 q2 : quat) :=
    let MINUS : matrix 4 4 := quat_MINUS q2 in
    let m1 : matrix 4 1 := cv_to_m (a4_from_tuples (quat_to_tuple4 q1)) in
    let m2 : matrix 4 1 := m_mul MINUS m1 in
    let '(w,x,y,z) := a4_to_tuples (m_rx1_to_a m2) in
      mk_quat w x y z.

  Lemma quat_mul_formu_MINUS_correct (q1 q2 : quat) : 
    q1 * q2 = quat_mul_formu_MINUS q1 q2.
  Proof.
    destruct q1,q2; comp_quat_ring.
  Qed.

    
  (* <1> It is non-commutative *)
  (*
  q1 * q2 <> q2 * q1.
  *)

  (* <2> distributive and associative *)

  Lemma quat_mul_dist_plus_l (q1 q2 q3 : quat) : 
    quat_mul q1 (quat_add q2 q3) = quat_add (quat_mul q1 q2) (quat_mul q1 q3).
  Proof.
    destruct q1,q2,q3; comp_quat_ring.
  Qed.

  Lemma quat_mul_assoc (q1 q2 q3 : quat) :
    quat_mul (quat_mul q1 q2 ) q3 = quat_mul q1 (quat_mul q2 q3).
  Proof.
    destruct q1,q2,q3; comp_quat_ring.
  Qed.

  (* <3> constant multiplication law *)
  Lemma quat_cmul_mulc_eq (c : T) (q : quat) : 
    quat_cmul c q = quat_mulc q c.
  Proof.
    destruct q; comp_quat_ring.
  Qed.
  
  (* <4> multplication by two array3 *)
  Lemma quat_mul_two_v3 (u v : array 3) :
    let qu : quat := quat_from_v u in
    let qv : quat := quat_from_v v in
    let q : quat :=  quat_from_s_v
      (m_1x1_to_scalar (m_neg (m_mul (m_trans (cv_to_m u)) (cv_to_m v)))) 
      (m_rx1_to_a (cv3_cross u v)) in
      qu * qv = q.
  Proof.
    destruct u as [u0 [u1 [u2 u3]]].
    destruct v as [v0 [v1 [v2 v3]]].
    destruct u3,v3.
    comp_quat_ring.
  Qed.
  
  (* (3) Conjugate of quat *)
  Definition quat_conjugate (q : quat) : quat :=
    let w : T := Re q in
    let v : array 3 := a_neg (a3_from_tuples (Im q)) in
      quat_from_s_v w v.
  
  Notation "q #" := (quat_conjugate q) (at level 30).
  
  (* Properties of conjugate *)
  
  Lemma quat_conjugate_twice (q : quat) : q # # = q.
  Proof.
    destruct q; comp_quat_ring.
  Qed.
  
  Lemma quat_conjugate_dist_mul (q1 q2 : quat) : (q1 * q2) # = q2 # * q1 #.
  Proof.
    destruct q1,q2; comp_quat_ring.
  Qed.
  
  Lemma quat_conjugate_dist_add (q1 q2 : quat) : (q1 + q2) # = q1 # + q2 #.
  Proof.
    destruct q1,q2; comp_quat_ring.
  Qed.
  
  Lemma quat_conjugate_mul_comm (q : quat) : q * (q #) = (q #) * q.
  Proof.
    destruct q; comp_quat_ring.
  Qed.
  
  Lemma quat_conjugate_mul_v_is_0 (q : quat) : Im (q * (q #)) = (0,0,0).
  Proof.
    destruct q; comp_tuple_ring.
  Qed.
  
  (* (4) Norm *)
  Definition quat_norm (q : quat) : T :=
    let '(w,x,y,z) := quat_to_tuple4 q in
      (w * w) + (x * x) + (y * y) + (z * z).
  
  (*
  Notation "|| q ||" := (quat_norm q) (at level 20).

  Parameter q : quat.
  Locate "||".
  Check || q ||.
  *)
  
  Definition quat_norm_formu1 (q : quat) : T :=
    let qstar : quat := quat_conjugate q in
      Re (qstar * q).
  
  Definition quat_norm_formu2 (q : quat) : T :=
    let qstar : quat := quat_conjugate q in
      Re (q * qstar).
  
  Definition quat_norm_formu3 (q : quat) : T :=
    let q0 : T := Re q in
    let qv : array 3 := a3_from_tuples (Im q) in
      (q0 * q0) + (m_1x1_to_scalar (m_mul (cv_to_m qv ') (cv_to_m qv))).
  
  
  Lemma quat_norm_formu1_ok (q : quat) : quat_norm q = quat_norm_formu1 q.
  Proof.
    destruct q; comp_ring.
  Qed.
  
  Lemma quat_norm_formu2_ok (q : quat) : quat_norm q = quat_norm_formu2 q.
  Proof.
    destruct q; comp_ring.
  Qed.
  
  Lemma quat_norm_formu3_ok (q : quat) : quat_norm q = quat_norm_formu3 q.
  Proof.
    destruct q; comp_ring.
  Qed.
  
  Lemma quat_norm_eq_conjugate_norm (q : quat) : quat_norm q = quat_norm (q #).
  Proof.
    destruct q; comp_ring.
  Qed.
  
  Lemma quat_norm_dist_mul (q1 q2 : quat) : 
    quat_norm (q1 * q2) = ((quat_norm q1) * (quat_norm q2))%element.
  Proof.
    destruct q1,q2; comp_ring.
  Qed.
  
  (* Unit quaternion *)
  Definition quat_unit_mul_unified (q1 q2 : quat) :
    quat_norm q1 = 1 -> 
    quat_norm q2 = 1 -> 
    quat_norm (q1 * q2) = 1.
  Proof.
    intros. rewrite quat_norm_dist_mul. rewrite H,H0. ring.
  Qed.
  
  (* (5) Inverse, only suitable for Real Number *)
  
  
End Module_quat.

(* --------------------------------------------------------------- *)
(* Concrete Module *)

(* based on Integer *)
Module Module_Quaternion_tttt_Z.
  Module quatZ := Module_quat ETypeZ.

  Export quatZ.
End Module_Quaternion_tttt_Z.

(* based on RealNumber *)
Module Module_Quaternion_tttt_R.
  Module quatR := Module_quat ETypeR.
  
  Export quatR.
  
  (* Inverse, only defined with Real number *)
  Definition quat_inverse (q : quat) : quat :=
    quat_cmul (1 / (quat_norm q)) (q #).
  
  Definition quat_inverse_mul_comm (q : quat) :
    quat_norm q <> 0 ->
    q * (quat_inverse q) = (quat_inverse q) * q.
  Proof.
    destruct q. compute. intros. f_equal; ring_simplify; auto.
  Qed.
  
  Definition quat_inverse_mul_unified (q : quat) :
    quat_norm q <> 0 ->
    q * (quat_inverse q) = quat_from_s 1.
  Proof.
    destruct q. compute. intros. f_equal; ring_simplify; auto.
    field. auto.
  Qed.
  
  Definition quat_inverse_mul_rev_unified (q : quat) :
    quat_norm q <> 0 ->
    (quat_inverse q) * q = quat_from_s 1.
  Proof.
    intros.
    rewrite <- quat_inverse_mul_comm; auto.
    rewrite quat_inverse_mul_unified; auto.
  Qed.
  
  Definition quat_unit_inverse_eq_conjugate (q : quat) :
    quat_norm q = 1 ->
    quat_inverse q = quat_conjugate q.
  Proof.
    intros.
    destruct q. compute in *. rewrite H. f_equal; field.
  Qed.
  
  (* Divide *)
  Lemma quat_divide_l (q1 q2 q3 : quat) :
    quat_norm q2 <> 0 ->
    q1 * q2 = q3 -> 
    q1 = q3 * (quat_inverse q2).
  Proof.
    intros H1 H2. rewrite <- H2.
    rewrite quat_mul_assoc.
    rewrite quat_inverse_mul_unified; auto.
    destruct q1. unfold T in *. comp_quat_ring.
  Qed.
  
  Lemma quat_divide_r (q1 q2 q3 : quat) :
    quat_norm q1 <> 0 ->
    q1 * q2 = q3 -> 
    q2 = (quat_inverse q1) * q3.
  Proof.
    intros H1 H2. rewrite <- H2.
    rewrite <- quat_mul_assoc.
    rewrite quat_inverse_mul_rev_unified; auto.
    destruct q2. unfold T in *. comp_quat_ring.
  Qed.
  
  
End Module_Quaternion_tttt_R.

(* --------------------------------------------------------------- *)
(* Usage demo *)

(* based on Integer *)

(* based on Integer *)
Module DemoUsage_QuatZ.
  Import Module_Quaternion_tttt_Z.
  Open Scope Z.

  (*
  Check mk_quat 1 2 3 4.
  Fail Compute quat_inverse (mk_quat 1 2 3 4).
  *)
End DemoUsage_QuatZ.

(* based on RealNumber *)
Module DemoUsage_QuatR.
  Export Module_Quaternion_tttt_R.
  Open Scope R.
  
  (*
  Check mk_quat 1 2 3 4.
  Compute quat_inverse (mk_quat 1 2 3 4).
  *)
  
End DemoUsage_QuatR.
