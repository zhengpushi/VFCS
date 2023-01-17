(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       Quaternion_aijk.v
  by:         ZhengPu Shi
  date:       2021.01.05
  
  reference: 
  1. Formalizing basic quaternionic analysis, Andrea Gabrielli etc.
  
  purpose:
  1. Normalize a Quaternion number with the format of {a + bi + cj + dk}
  2. prove Quaternion multiplication formula.
  
  remark:
  1. How to reuse code?
    Module Type is a better way.
  2. What difference between Notation and Definition?
    Notation look like a macro in C, Coq make no diferent with original type.
    Definition look like a const in C, need to unfold manually.
  3. What's "Set Implicit Arguments" meaning?
    this will make all parameters automatically implicit
  
*)

From FlyCtrl Require Export Basic.

(* --------------------------------------------------------------- *)
(* Definitions and operations of Quaternion *)

Module Module_Quaternion_aijk (E : EType).
  Export E.
  
  (* ======================================== *)
  (* THE REAL PART OF Quaternion *)

  (* Type definition of the real part, it is an arithmetic expression *)
  Inductive realpart : Set :=
    | RPNum (n : T)
    | RPNeg (a : realpart) (* negation *)
    | RPAdd (a1 a2 : realpart)
    | RPMul (a1 a2 : realpart).

  (* Subtraction operation of two real parts *)
  Definition RPSub (a1 a2 : realpart) := RPAdd a1 (RPNeg a2).

  (* Useful coercion, but maybe fail outside the module *)
  Coercion RPNum : T >-> realpart.

  Declare Scope realpart_scope.
  Bind Scope realpart_scope with realpart.
  Delimit Scope realpart_scope with rptype.
  Open Scope realpart_scope.
  
  Notation " - b" := (RPNeg b) 
    (at level 35, right associativity) : realpart_scope.
  Notation "a * b" := (RPMul a b) 
    (at level 40, left associativity) : realpart_scope.
  Notation "a + b" := (RPAdd a b) 
    (at level 50, left associativity) : realpart_scope.
  Notation "a - b" := (RPSub a b) 
    (at level 50, left associativity) : realpart_scope.


  (* Evaluation of the real part *)
  Fixpoint rpeval (a : realpart) : T :=
    match a with
    | RPNum n => n
    | RPNeg a => neg (rpeval a)
    | RPAdd a1 a2 => add (rpeval a1) (rpeval a2)
    | RPMul a1 a2 => mul (rpeval a1) (rpeval a2)
    end.


  (* ======================================== *)
  (* THE IMAGINARY PART OF Quaternion *)

  (* Type definition of the imaginary part, this is a group *)
  Inductive imagepart : Set :=
    | IPOne
    | IPNOne
    | IPI
    | IPJ
    | IPK
    | IPNI
    | IPNJ
    | IPNK.

  (* Abstract multiplication operation for imaginary parts *)
  Parameter IPMul : imagepart -> imagepart -> imagepart.

  Declare Scope imagepart_scope.
  Bind Scope imagepart_scope with imagepart.
  Delimit Scope imagepart_scope with iptype.
  Open Scope imagepart_scope.

  (* Notations for convenient *)
  Notation ip1 := IPOne.
  Notation ipn1 := IPNOne.
  Notation i := IPI.
  Notation j := IPJ.
  Notation k := IPK.
  Notation ni := IPNI.
  Notation nj := IPNJ.
  Notation nk := IPNK.
  Notation "a * b" := (IPMul a b) 
    (at level 40, left associativity) : imagepart_scope.

  (* Multiplication operation of the imaginary part *)

  Definition IPMul_1_a (a : imagepart) : imagepart := a.
  Definition IPMul_n1_a (a : imagepart) : imagepart := match a with
    | ip1 => ipn1 | ipn1 => ip1 
    | i => ni | j => nj | k => nk 
    | ni => i | nj => j | nk => k
    end.
  Definition IPMul_i_a (a : imagepart) : imagepart := match a with
    | ip1 => i | ipn1 => ni
    | i => ipn1 | j => k | k => nj
    | ni => ip1 | nj => nk | nk => j
    end.
  Definition IPMul_j_a (a : imagepart) : imagepart := match a with
    | ip1 => j | ipn1 => nj 
    | i => nk | j => ipn1 | k => i 
    | ni => k | nj => ip1 | nk => ni
    end.
  Definition IPMul_k_a (a : imagepart) : imagepart := match a with
    | ip1 => k | ipn1 => nk 
    | i => j | j => ni | k => ipn1 
    | ni => nj | nj => i | nk => ip1
    end.
  Definition IPMul_ni_a (a : imagepart) : imagepart := match a with
    | ip1 => ni | ipn1 => i
    | i => ip1 | j => nk | k => j
    | ni => ipn1 | nj => k | nk => nj
    end.
  Definition IPMul_nj_a (a : imagepart) : imagepart := match a with
    | ip1 => nj | ipn1 => j 
    | i => k | j => ip1 | k => ni 
    | ni => nk | nj => ipn1 | nk => i
    end.
  Definition IPMul_nk_a (a : imagepart) : imagepart := match a with
    | ip1 => nk | ipn1 => k 
    | i => nj | j => i | k => ip1 
    | ni => j | nj => ni | nk => ipn1
    end.

  Definition IPMul_a_b (a b : imagepart) : imagepart := match a with
    | ip1 => IPMul_1_a b 
    | ipn1 => IPMul_n1_a b 
    | i => IPMul_i_a b 
    | j => IPMul_j_a b 
    | k => IPMul_k_a b 
    | ni => IPMul_ni_a b 
    | nj => IPMul_nj_a b 
    | nk => IPMul_nk_a b
    end.

  (* Negation operation of the imaginary part *)
  Definition IPNeg_a (a : imagepart) := match a with
    | ip1 => ipn1 | ipn1 => ip1 
    | i => ni | j => nj | k => nk 
    | ni => i | nj => j | nk => k
    end.


  (* ======================================== *)
  (* THE Quaternion *)

  (* Type definition of quaternion expression *)
  Inductive qexp : Set :=
    | QR (r : realpart)
    | QI (i : imagepart)
    | QNeg (a1 : qexp)
    | QAdd (a1 a2 : qexp)
    | QMul (a1 a2 : qexp). 

  (* Subtraction operation of two quaternion expressions *)
  Definition QSub (a1 a2 : qexp) := QAdd a1 (QNeg a2).


  (* Useful coercion, but maybe fail outside the module *)
  Coercion QR : realpart >-> qexp.
  Coercion QI : imagepart >-> qexp.

  Declare Scope qexp_scope.
  Bind Scope qexp_scope with qexp.
  Delimit Scope qexp_scope with qtype.
  Open Scope qexp_scope.

  (* Notations for convenient *)
  Notation " - b" := (QNeg b) 
    (at level 35, right associativity) : qexp_scope.
  Notation "a * b" := (QMul a b) 
    (at level 40, left associativity) : qexp_scope.
  Notation "a + b" := (QAdd a b) 
    (at level 50, left associativity) : qexp_scope.
  Notation "a - b" := (QSub a b) 
    (at level 50, left associativity) : qexp_scope.

  (* calculate tree depth of qexp *)
  Fixpoint qexp_depth (q : qexp) : nat :=
    match q with
      | q1 * q2 => 1 + (qexp_depth q1) + (qexp_depth q2)
      | q1 + q2 => 1 + (qexp_depth q1) + (qexp_depth q2)
      | - q2 => 1 + (qexp_depth q2)
      | _ => 0
    end.


  (* unfold all bracket step1, distributive of multiplication to addition.
    example:
    a * (b1 + b2) = a * b1 + a * b2
    (a1 + a2) * b = a1 * b + a2 * b
  *)
  Fixpoint qexp_opt_bracket_step1 (n : nat) (q : qexp) : qexp :=
    match n, q with
    | S m, a * (b1 + b2) =>
      (qexp_opt_bracket_step1 m (a * (qexp_opt_bracket_step1 m b1))) +
      (qexp_opt_bracket_step1 m (a * (qexp_opt_bracket_step1 m b2)))
    | S m, (a1 + a2) * b =>
      (qexp_opt_bracket_step1 m ((qexp_opt_bracket_step1 m a1) * b)) +
      (qexp_opt_bracket_step1 m ((qexp_opt_bracket_step1 m a2) * b))
    | S m, -(a + b) => qexp_opt_bracket_step1 m (
      (qexp_opt_bracket_step1 m (-a)) + (qexp_opt_bracket_step1 m (-b)))
    | S m, -(a * b) => qexp_opt_bracket_step1 m (
      (qexp_opt_bracket_step1 m (-a)) * b)
    | S m, a + b => qexp_opt_bracket_step1 m (
      (qexp_opt_bracket_step1 m a) +
      (qexp_opt_bracket_step1 m b))
    | S m, a * b => qexp_opt_bracket_step1 m (
      (qexp_opt_bracket_step1 m a) *
      (qexp_opt_bracket_step1 m b))
    | _, _ => q
    end.
    
  Definition qexp_opt_bracket1 (q : qexp) := 
    qexp_opt_bracket_step1 (qexp_depth q) q.


  (* unfold all bracket step2, associativity of multiplication or addition.
    example:
    a1 * (a2 * a3) = a1 * a2 * a3
    a1 + (a2 + a3) = a1 + a2 + a3
  *)
  Fixpoint qexp_opt_bracket_step2 (n : nat) (q : qexp) : qexp :=
    match n, q with
    | S m, a + (b + c) => qexp_opt_bracket_step2 m (a + b + c)
    | S m, a * (b * c) => qexp_opt_bracket_step2 m (a * b * c)
    | S m, a + b => qexp_opt_bracket_step2 m 
      (qexp_opt_bracket_step2 m a) + (qexp_opt_bracket_step2 m b)
    | S m, a * b => qexp_opt_bracket_step2 m 
      (qexp_opt_bracket_step2 m a) * (qexp_opt_bracket_step2 m b)
    | _, _ => q
    end.
    
  Definition qexp_opt_bracket2 (q : qexp) := 
    qexp_opt_bracket_step2 (qexp_depth q) q.


  (* unfold all bracket at once *)
  Definition qexp_opt_bracket (q : qexp) := 
    qexp_opt_bracket2 (qexp_opt_bracket1 q).


  (* replace all QNeg QI to QI,
   Notice that no brackets in parameters. 
  *)
  Fixpoint qexp_elim_negi (q : qexp) : qexp :=
    match q with
    | - (QI i1) => QI (IPNeg_a i1)
    | a * b => (qexp_elim_negi a) * (qexp_elim_negi b)
    | a + b => (qexp_elim_negi a) + (qexp_elim_negi b)
    | _ => q
    end.


  (* replace all QNeg QR to QR,
   Notice that no brackets in parameters. 
  *)
  Fixpoint qexp_elim_negr (q : qexp) : qexp :=
    match q with
    | - (QR r1) => QR (rpeval (- (rpeval r1)))
    | a * b => (qexp_elim_negr a) * (qexp_elim_negr b)
    | a + b => (qexp_elim_negr a) + (qexp_elim_negr b)
    | _ => q
    end.


  (* split the Real part and the Image part of a quaternion expressions with 
   continuous multiplication format, 
   Notice that no brackets in parameters.
   examples:
   i * r = r * i
   q1 * i1 * i2 = (split q1) * (i1.i2)
   q1 * i = (split q1) * i
   q1 * r = unfold_bracket (r * (split q1))
  *)
  Fixpoint qexp_split_ri_mul (q : qexp) : qexp :=
    match q with
    | QI i1 * QR r1 => QR r1 * QI i1
    | q1 * QI i1 * QI i2 => 
      qexp_opt_bracket ((qexp_split_ri_mul q1) * (i1 * i2))
    | q1 * QI i1 => (qexp_split_ri_mul q1) * QI i1
    | q1 * QR r1 => qexp_opt_bracket (QR r1 * (qexp_split_ri_mul q1))
    | q1 + q2 =>  (
      (qexp_split_ri_mul q1) +
      (qexp_split_ri_mul q2))
    | _ => q
    end.


  (* Simplify the quaterion expressions with continuous multiplication format,
   Notice that no brackets in parameters,
   and no subtraction in it,
   and every item of addition has been splited to real_part * image_part.
   examples:
   2 * 3 * i * j
   2 * (-3) * i
   q1 + q2 + ...
  *)
  Fixpoint qexp_simp_mul_aux (n : nat) (q : qexp) : qexp :=
    match n, q with
    | S m, q1 * QI i1 * QI i2 => qexp_simp_mul_aux m 
      (q1 * (QI (IPMul_a_b i1 i2)))
    | S m, QR r1 * QR r2 => QR (rpeval ((rpeval r1) * (rpeval r2)))
    | S m, q1 * QI i1 => qexp_simp_mul_aux m 
      ((qexp_simp_mul_aux m q1) * QI i1)
    | S m, q1 + q2 => (qexp_simp_mul_aux m q1) + (qexp_simp_mul_aux m q2)
    | _, _ => q
    end.

  Definition qexp_simp_mul (q : qexp) : qexp :=
    qexp_simp_mul_aux (qexp_depth q) q.

  (* convert a well-formed quaternion expression to tuple4.
  given format must be an addition of such elements:
    rp = realpart
    ip = imagepart
    q0 = rp | ip | rp * ip
    q = q0 | q + q0
   *)
  Fixpoint qexp_wf_to_tuple4 (q : qexp) : T * T * T * T :=
    match q with 
    | QR r1 => (rpeval r1, 0, 0, 0)  
    | QI i1 => 
      let t1 : T := 1 in
      let t1' : T := NOne in
      let t4 := match i1 with
        | ip1 => (t1, 0, 0, 0)
        | i => (0, t1, 0, 0)
        | j => (0, 0, t1, 0)
        | k => (0, 0, 0, t1)
        | ipn1 => (t1', 0, 0, 0)
        | ni => (0, t1', 0, 0)
        | nj => (0, 0, t1', 0)
        | nk => (0, 0, 0, t1')
        end in t4
    | QR r1 * QI i1 =>
      let t1 : T := rpeval r1 in
      let t1' : T := rpeval (r1 * NOne) in
      let t4 := match i1 with
        | ip1 => (t1, 0, 0, 0)
        | i => (0, t1, 0, 0)
        | j => (0, 0, t1, 0)
        | k => (0, 0, 0, t1)
        | ipn1 => (t1', 0, 0, 0)
        | ni => (0, t1', 0, 0)
        | nj => (0, 0, t1', 0)
        | nk => (0, 0, 0, t1')
        end in t4
    | a + b => 
      let '(a1,a2,a3,a4) := (qexp_wf_to_tuple4 a) in
      let '(b1,b2,b3,b4) := (qexp_wf_to_tuple4 b) in
      (a1 + b1, a2 + b2, a3 + b3, a4 + b4)%element
    | _ => (0, 0, 0, 0)
    end.


  (* convert a tuple4 to quaternion expression *)
  Definition qexp_from_tuple4 (t : T * T * T * T) : qexp :=
    let '(a,b,c,d) := t in
      a + b * i + c * j + d * k.


  (* rearrange the addition sequence of a quaterion expression.
  given format must be an addition of such elements:
    a = t : aexp
    q = a | i | j | k | a * i | a * j | a * k
    element = q | q + q
   example :
    a + c * j + d * k + b * i   = a + b * i + c * j + d * k
    a + b * i                   = a + b * i + 0 * j + 0 * k
    c * k + a                   = a + 0 * i + 0 * j + c * k
    a                           = a + 0 * i + 0 * j + 0 * k
   *)
  Definition qexp_rearrange (q : qexp) : qexp :=
    let q := qexp_from_tuple4 (qexp_wf_to_tuple4 q) in
      q.

  (* Return tuple4 from an qexp *)
  Definition qexp_to_tuple4 (a : qexp) : T * T * T * T :=
    qexp_wf_to_tuple4 (qexp_simp_mul (qexp_split_ri_mul (qexp_elim_negr 
      (qexp_elim_negi (qexp_opt_bracket a))))).

  (* Return tuple4 from an qexp with form A x B *)
  Definition qexp_AxB_to_tuple4 (a b : qexp) : T * T * T * T := 
    qexp_to_tuple4 (a * b).

  (* Return normalization of for A x B *)
  Definition qexp_norm_for_AxB (a b : qexp) : qexp :=
    qexp_from_tuple4 (qexp_AxB_to_tuple4 a b).

  (** Equality of Conversion functions *)
  
  (* qexp_from_tuple4 *)
  Lemma qexp_from_tuple4_equality (q1 q2 : T * T * T * T) : 
    q1 = q2 <-> qexp_from_tuple4 q1 = qexp_from_tuple4 q2.
  Proof.
    split.
    - intros H. f_equal. assumption.
    - intros H.
      repeat destruct q1 as [q1]; repeat destruct q2 as [q2].
      inversion H. subst. trivial.
  Qed.
  
  (* qexp_to_tuple4 *)
  Lemma qexp_to_tuple4_equality (q1 q2 : qexp) :
    q1 = q2 <-> qexp_to_tuple4 q1 = qexp_to_tuple4 q2.
  Proof.
    split.
    - intros H. f_equal. assumption.
    - intros H.
      destruct q1,q2.
      Abort.
    
  (** Equality of two quaternions, iff corresponding elements are equal. *)

  (* T *)
  Lemma qexp_equalityT (a0 a1 a2 a3 b0 b1 b2 b3 : T) :
    (a0 + a1 * i + a2 * j + a3 * k) = (b0 + b1 * i + b2 * j + b3 * k) <->
    (a0 = b0) /\ (a1 = b1) /\ (a2 = b2) /\ (a3 = b3).
  Proof.
    split.
    - intros. inversion H. auto.
    - intros. repeat (destruct H as [H1 H]; subst). auto.
  Qed.

  (* realpart *)
  Lemma qexp_equalityRP (a0 a1 a2 a3 b0 b1 b2 b3 : realpart) :
    (a0 + a1 * i + a2 * j + a3 * k) = (b0 + b1 * i + b2 * j + b3 * k) <->
    (a0 = b0) /\ (a1 = b1) /\ (a2 = b2) /\ (a3 = b3).
  Proof.
    split.
    - intros. inversion H. auto.
    - intros. repeat (destruct H as [H1 H]; subst). auto.
  Qed.

  (* qexp *)
  Lemma qexp_equalityQEXP (a0 a1 a2 a3 b0 b1 b2 b3 : qexp) :
    (a0 + a1 * i + a2 * j + a3 * k) = (b0 + b1 * i + b2 * j + b3 * k) <->
    (a0 = b0) /\ (a1 = b1) /\ (a2 = b2) /\ (a3 = b3).
  Proof.
    split.
    - intros. inversion H. auto.
    - intros. repeat (destruct H as [H1 H]; subst). auto.
  Qed.
  
  
  (** Simplification Tactic *)

  Axiom qexp_add_elim : forall (a0 a1 : realpart), 
    QR a0 + QR a1 = QR (a0 + a1).
  Axiom qexp_sub_elim : forall (a0 a1 : realpart), 
    QR a0 - QR a1 = QR (a0 - a1).
  Axiom qexp_mul_elim : forall (a0 a1 : realpart), 
    QR a0 * QR a1 = QR (a0 * a1).
    
  Axiom aexp_neg_elim : forall (a0 : T), 
    (RPNeg a0 = RPNum (neg a0))%rptype.
  Axiom aexp_add_elim : forall (a0 a1 : T), 
    (RPNum a0 + RPNum a1 = RPNum (add a0 a1))%rptype.
  Axiom aexp_sub_elim : forall (a0 a1 : T), 
    (RPNum a0 - RPNum a1 = RPNum (sub a0 a1))%rptype.
  Axiom aexp_mul_elim : forall (a0 a1 : T), 
    (RPNum a0 * RPNum a1 = RPNum (mul a0 a1))%rptype.


  Ltac simpl_equal_of_qexp :=
    repeat rewrite ?qexp_add_elim,?qexp_sub_elim,?qexp_mul_elim;
    unfold RPSub;
    repeat rewrite ?aexp_neg_elim,?aexp_add_elim,?aexp_sub_elim,
      ?aexp_mul_elim.
  
  Ltac simpl_qexp_bracket :=
    unfold qexp_opt_bracket, qexp_opt_bracket1; simpl qexp_depth;
    unfold qexp_opt_bracket_step1, qexp_opt_bracket2; simpl qexp_depth;
    unfold qexp_opt_bracket_step2.

  Ltac simpl_qexp_AxB :=
    unfold qexp_norm_for_AxB, qexp_AxB_to_tuple4, qexp_to_tuple4;
    (* brackets *)
    simpl_qexp_bracket;
    unfold qexp_elim_negi,qexp_elim_negr,qexp_split_ri_mul;
    simpl_qexp_bracket;
    (* expand multiplication *)
    unfold qexp_simp_mul; simpl qexp_depth;
    unfold qexp_simp_mul_aux,IPMul_a_b,IPMul_i_a,IPMul_j_a,IPMul_k_a;
    simpl rpeval;
    (* combine addition *)
    unfold qexp_wf_to_tuple4, qexp_from_tuple4; simpl rpeval; unfold NOne.
    
  Ltac simpl_qexp_AxB_eq_C :=
    simpl_qexp_AxB;
    (* split to component *)
    rewrite qexp_equalityQEXP; repeat split;
    repeat rewrite ?qexp_mul_elim,?qexp_add_elim,?qexp_sub_elim;
    repeat rewrite ?aexp_mul_elim,?aexp_neg_elim,?aexp_add_elim;
    unfold RPSub.
  
  (* ======================================== *)
  (* Formula of Quaternion Multiplication *)
  
  (* http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/
    arithmetic/other.htm
    (a + i b + j c + k d)*(e + i f + j g + k h) = 
         a*e - b*f - c*g - d*h
    + i (b*e + a*f + c*h - d*g)
    + j (a*g - b*h + c*e + d*f)
    + k (a*h + b*g - c*f + d*e)
  *)
  
  Lemma qexp_AxB_formula1 (a0 a1 a2 a3 b0 b1 b2 b3 : T) :
    qexp_AxB_to_tuple4
      (a0 + a1 * i + a2 * j + a3 * k) 
      (b0 + b1 * i + b2 * j + b3 * k) 
    = (
      (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3),
      (a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2),
      (a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1),
      (a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0))%element.
  Proof.
    simpl_qexp_AxB.
    simpl_equal_of_tuples; ring.
  Qed.
 
  Lemma qexp_AxB_formula1_old (a0 a1 a2 a3 b0 b1 b2 b3 : T) :
    qexp_norm_for_AxB 
      (a0 + a1 * i + a2 * j + a3 * k) 
      (b0 + b1 * i + b2 * j + b3 * k) 
    = 
      (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3) +
      (a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2) * i + 
      (a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1) * j +
      (a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0) * k.
  Proof.
    simpl_qexp_AxB_eq_C;
    repeat rewrite ?add_0_l,?add_0_r,?mul_neg_r,?mul_1_r,
        ?aexp_neg_elim, ?aexp_add_elim; f_equal; f_equal.
    (* the code below, should be insteaded by RING, but need more work. *)
    - f_equal. f_equal. f_equal.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
    - (*  a + b + c + d => b + a + d + c
        = (a + b) + (c + d)
        = (b + a) + (d + c)
        = b + a + d + c
      *)
      rewrite <- add_assoc.
      rewrite (add_comm (b0*a1) _).
      rewrite (add_comm _ (b3*a2)).
      rewrite add_assoc.
      f_equal. f_equal. f_equal.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
    - (*  a + b + c + d => c + d + a + b
        = (a + b) + (c + d) 
        = (c + d) + (a + b)
        = c + d + a + b
      *)
      rewrite <- add_assoc.
      rewrite add_comm.
      rewrite <-(add_assoc _ (a2*b0)).
      f_equal; f_equal.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
    - (*  a + b + c + d => d + c + b + a
        = (a + b) + (c + d)
        = (c + d) + (a + b)
        = (d + c) + (b + a)
        = d + c + b + a
      *)
      rewrite <- (add_assoc _ _ (b3*a0)).
      rewrite <-(add_assoc _ _ (a3*b0)).
      rewrite add_comm.
      rewrite (add_comm (b2*a1)).
      rewrite (add_comm _ (a3*b0)).
      f_equal; f_equal.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      rewrite mul_comm; auto.
      Qed.
  
  
End Module_Quaternion_aijk.


(* --------------------------------------------------------------- *)
(* Concrete module of Quaternion *)

(* based on Integer *)
Module Module_Quaternion_aijk_Z.
  Module Quaternion_aijk_Z := Module_Quaternion_aijk ETypeZ.

  Export Quaternion_aijk_Z.

  (* Extra code for Coercion from Z to aexp *)
  Definition RPNum_Z (t : Z) : realpart := RPNum t.
  Coercion RPNum_Z : Z >-> realpart.

  (* Open needed scopes at a special sequence, consider the notations *)
  Open Scope Z.
  Open Scope realpart_scope.
  Open Scope imagepart_scope.
  Open Scope qexp_scope.

End Module_Quaternion_aijk_Z.


(* based on real number *)
Module Module_Quaternion_aijk_R.
  Module Quaternion_aijk_R := Module_Quaternion_aijk ETypeR.

  Export Quaternion_aijk_R.

  (* Extra code for Coercion from R to aexp *)
  Definition RPNum_R (t : R) : realpart := RPNum t.
  Coercion RPNum_R : R >-> realpart.

  (* Open needed scopes at a special sequence, consider the notations *)
  Open Scope R.
  Open Scope realpart_scope.
  Open Scope imagepart_scope.
  Open Scope qexp_scope.

End Module_Quaternion_aijk_R.


(* --------------------------------------------------------------- *)
(* Usage demo *)

(* based on Integer *)
Module DemoUsage_Quaternion_aijk_Z.
  Import Module_Quaternion_aijk_Z.

  (* same number could have multi different types *)
  Check 3 : Z.
  Check 3 : realpart.
  Check 3 : qexp.

  (* same expression could have multi different types *)
  Check (3 + 2).
  Check (3 + 2)%Z : Z.
  Check (3 + 2)%rptype : realpart.
  Check (3 + 2)%qtype : qexp.
End DemoUsage_Quaternion_aijk_Z.

(* based on RealNumber *)
Module DemoUsage_Quaternion_aijk_R.
  Import Module_Quaternion_aijk_R.

  (* same number could have multi different types *)
  Check 3 : R.
  Check 3 : realpart.
  Check 3 : qexp.

  (* same expression could have multi different types *)
  Check (3 + 2).
  Check (3 + 2)%R : R.
  Check (3 + 2)%rptype : realpart.
  Check (3 + 2)%qtype : qexp.
End DemoUsage_Quaternion_aijk_R.
