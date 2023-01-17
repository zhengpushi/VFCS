(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       Real_proof.v
  by:         ZhengPu Shi
  purpose:    common code for proof about Real Numbers.
  
*)

Require Import Reals.
Open Scope R.





(* --------------------------------------------------------------- *)
(* Give some lost definitions about Real Numbers *)

(* arcsin *)
Parameter asin : R -> R.

(* sign of a real number *)
Definition Rsign (r : R) : R := if Rcase_abs r then -1 else 1.


(* --------------------------------------------------------------- *)
(* some losing lemmas we need, and expand auto-tatic-library *)

(*
some predefined notations:
  x ^ z , pow : R -> nat -> R , rewrite <- Rsqr_pow2, to x²
  x²    , Rsqr: R -> R        , unfold Rsqr, to x * x
  x * y , Rmult x y
  ----------------------
  Rsqr = fun r : R => r * r.
  Rsqr_pow2: forall x : R, x² = x ^ 2
*)
(* x ^ 2 = Rsqr x *)
Lemma pow2_sqr : forall x : R, pow x 2 = Rsqr x.
intros. rewrite Rsqr_pow2. reflexivity. Qed.
Global Hint Resolve pow2_sqr : coordinate.

(* x * x = (x² := Rsqr x) *)
Lemma xx_sqr : forall x : R, x * x = Rsqr x.
intros. unfold Rsqr. reflexivity. Qed.
Hint Rewrite xx_sqr : coordinate.

(* r2 * / r1 * r1 = r2 *)
Lemma Rinv_r_simpl_l_rev : forall r1 r2 : R, r1 <> 0 -> r2 * / r1 * r1 = r2.
  intros. rewrite Rmult_assoc. rewrite (Rmult_comm _ r1).
  rewrite <- Rmult_assoc. rewrite Rinv_r_simpl_l; auto. Qed.
Hint Rewrite Rinv_r_simpl_l_rev : coordinate.

(* cos^2 + sin^2 = 1 *)
Lemma cos2_sin2 : forall x:R, Rsqr (cos x) + Rsqr (sin x) = 1.
intros; rewrite Rplus_comm; rewrite sin2_cos2; reflexivity. Qed.
Hint Rewrite sin2_cos2 : coordinate.
Hint Rewrite cos2_sin2 : coordinate.

(* cos^2 = 1 - sin^2 *)
Lemma cos2_sin2' : forall x:R, Rsqr (cos x) = 1 - Rsqr (sin x).
intros. apply (Rplus_eq_reg_l (sin x)²). rewrite sin2_cos2. ring. Qed.
Hint Rewrite cos2_sin2' : coordinate.

Lemma cos2_sin2'' : forall x:R, (cos x) * (cos x) = 1 - ((sin x) * (sin x)).
intros. repeat rewrite xx_sqr. rewrite cos2_sin2'. trivial. Qed.
Hint Rewrite cos2_sin2'' : coordinate.

(* cos * sin = sin * cos *)
Lemma cos_sin' : forall x:R, (cos x) * (sin x) = (sin x) * (cos x).
intros. rewrite Rmult_comm. reflexivity. Qed.
Hint Rewrite cos_sin' : coordinate.

(* (a * sin)^2 + (a * cos)^2 = a^2 *)
Lemma asin2_acos2 : forall a x:R, Rsqr (a * sin x) + Rsqr (a * cos x) = Rsqr a.
intros. repeat rewrite <- xx_sqr. ring_simplify. 
rewrite <- Rmult_plus_distr_l. repeat rewrite <- Rsqr_pow2.
rewrite sin2_cos2. ring. Qed.
Hint Rewrite asin2_acos2 : coordinate.
(* (a * cos)^2 + (a * sin)^2 = a^2 *)
Lemma acos2_asin2 : forall a x:R, Rsqr (a * cos x) + Rsqr (a * sin x) = Rsqr a.
Proof. intros; rewrite Rplus_comm. rewrite asin2_acos2. ring. Qed.
Hint Rewrite acos2_asin2 : coordinate.

(* (sin * a)^2 + (cos * a)^2 = a^2 *)
Lemma sina2_cosa2 : forall a x:R, Rsqr (sin x * a) + Rsqr (cos x * a) = Rsqr a.
intros. repeat rewrite <- xx_sqr. ring_simplify.
rewrite Rmult_comm. rewrite <- Rmult_plus_distr_l. repeat rewrite <- Rsqr_pow2.
rewrite sin2_cos2. ring. Qed.
Hint Rewrite sina2_cosa2 : coordinate.
(* (cos * a)^2 + (sin * a)^2 = a^2 *)
Lemma cosa2_sina2 : forall a x:R, Rsqr (cos x * a) + Rsqr (sin x * a) = Rsqr a.
Proof. intros; rewrite Rplus_comm. rewrite sina2_cosa2. ring. Qed.
Hint Rewrite cosa2_sina2 : coordinate.

(* cos (- (PI / 2)) = 0 *)
(*Lemma cos_neg_pi_2 : cos (- PI / 2) = 0.
Proof. rewrite cos_neg. *)

(* --------------------------------------------------------------- *)
(* continue expand auto-tatic-library *)

(* simplify of mult/plus with 0/1 *)
Hint Rewrite 
  Rplus_0_l   (* 0 + x = x *)
  Rplus_0_r   (* x + 0 = x *)
  Rmult_0_l   (* 0 * x = 0 *)
  Rmult_0_r   (* x * 0 = 0 *)
  Rmult_1_l   (* 1 * x = x *)
  Rmult_1_r   (* x * 1 = x *)
: coordinate.

Global Hint Unfold 
  tan         (* tan x = sin x / cos x *)
  Rdiv        (* x / y = x * 1/y *)
  Rminus      (* x - y = x + -y *)
: coordinate.

Hint Rewrite <- Rsqr_pow2   (* x² = x ^ 2 *)
  : coordinate.

Hint Rewrite <- Rmult_plus_distr_l   (* r1 * (r2 + r3) = r1 * r2 + r1 * r3 *)
: coordinate.

Hint Rewrite 
  sin_PI2         (* sin (PI / 2) = 1 *)
  cos_PI2         (* cos (PI / 2) = 0 *)
  sin_plus        (* sin (x + y) = sin x * cos y + cos x * sin y *)
  sin_minus       (* sin (x - y) = sin x * cos y - cos x * sin y *)
  cos_plus        (* cos (x + y) = cos x * cos y - sin x * sin y *)
  cos_minus       (* cos (x - y) = cos x * cos y + sin x * sin y *)
  cos_neg         (* cos (- x) = cos x *)
  sin_neg         (* sin (- x) = - sin x *)
: coordinate.

Hint Rewrite
  Rmult_opp_opp               (* - r1 * - r2 = r1 * r2 *)
  Ropp_involutive             (* - - r = r *)
  Ropp_mult_distr_l_reverse   (* - r1 * r2 = - (r1 * r2) *)
  Ropp_mult_distr_r_reverse   (* r1 * - r2 = - (r1 * r2) *)
  Rinv_r_simpl_r              (* r1 * / r1 * r2 = r2 *)
  Rinv_r_simpl_m              (* r1 * r2 * / r1 = r2 *)
  Rinv_r_simpl_l              (* r2 * r1 * / r1 = r2 *)
  Rinv_r_simpl_l_rev          (* r2 * / r1 * r1 = r1 *)
: coordinate.


(* --------------------------------------------------------------- *)
(* customized tactic *)

(*
(* GENERAL EQUATION *)
Ltac simpl_equation :=
  intros;                       (* import Hypothesis *)
  autounfold with coordinate;   (* unfold definitions *)
  auto with coordinate;         (* solve trivial *)
  unfold Rdiv;                  (* unfold the divide operator *)
  autorewrite with coordinate;  (* try to rewrite and simple *)
  try apply Rmult_le_pos;       (* use this rule in addition *)
  try field;                    (* solve an equation *)
  auto with coordinate.         (* solve trivial again *)
*)

(*

  intros;                       (* import Hypothesis *)
  autorewrite with coordinate;  (* try to rewrite and simple *)
  try field.                    (* solve an equation *)
  
  autounfold with coordinate.   (* unfold definitions *)
  auto with coordinate;         (* solve trivial *)
  unfold Rdiv;                  (* unfold the divide operator *)
*)

(* tactic for simplification of triangle functions *)
Ltac trigo_simp :=
  autorewrite with coordinate;
  rewrite ?Rmult_opp_opp;   (* -x * -x = x * x *)
  rewrite ?xx_sqr;          (* x * x = Rsqr x *)
  rewrite ?sin2_cos2,       (* sin^2 + cos^2 = 1 *)
          ?cos2_sin2,       (* cos^2 + sin^2 = 1 *)
          ?cos_sin',        (* cos * sin = sin * cos *)
          ?sin_minus,       (* sin (x-y) = sin x * cos y - cos x * sin y *)
          ?Ropp_mult_distr_l,     (* -x * y = - (x * y) *)
          ?Ropp_mult_distr_r_reverse,     (* x * -y = - (x * y) *)
          ?Rplus_opp_l,     (* x + -x = 0 *)
          ?Rplus_opp_r;     (* -x + x = 0 *)
  try ring.

(* tactic for simplification contains R0 or R1 *)
Ltac real_simp :=
  repeat 
  rewrite ?Ropp_0,        (* -0 = 0 *)
          ?Rmult_0_l,     (* 0 * r = 0 *)
          ?Rmult_0_r,     (* r * 0 = 0 *)
          ?Rplus_0_l,     (* 0 + r = r *)
          ?Rplus_0_r,     (* r + 0 = r *)
          ?Rmult_1_l,     (* 1 * r = r *)
          ?Rmult_1_r;     (* r * 1 = r *)
  try ring.

