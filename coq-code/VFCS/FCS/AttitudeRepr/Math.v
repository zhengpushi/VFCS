(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Mathematics for position and orientation representation
  author    : ZhengPu Shi
  date      : 2024.01

  reference :
  remark    :
  1. mainly use MatrixR and VectorR3
  2. rvec, cvec, and vec are different and can be converted.
     especially, rvec and cvec are automaticaly converted to vec by coercion.

 *)

Require Export MatrixR.
Require Export VectorR.
(* Require Import Quaternion. *)

Open Scope mat_scope.
Open Scope vec_scope.


(* ======================================================================= *)
(** ** Automation for proof *)

(* Convert equality of two vectors to point-wise element equalities *)
Ltac veq :=
  apply v2l_inj; cbv; list_eq.

(* Convert equality of two matrices to point-wise element equalities *)
Ltac meq :=
  apply m2l_inj; cbv; list_eq.

(* Try to prove equality of two R values. *)
Ltac Req :=
  ra.

(* Try to prove equality of two R values, using `R` db, especially for triangle *)
Ltac Req_more :=
  autorewrite with R; ra.

(* Convert `a ^ (n + 2)` to `(a ^ 2) * (a ^ n)` *)
Ltac simp_pow :=
  match goal with
  | |- context[?a ^ 4] => replace (a ^ 4) with ((a ^ 2) ^ 2); [|ring]
  | |- context[?a ^ 3] => replace (a ^ 3) with ((a ^ 2) * a)%R; [|ring]
  end.


(* ======================================================================= *)
(** ** Mixed operations contain matrix and vector *)


(* ======================================================================= *)
(** ** Row vector and column vector *)

(* Definition cv2v {n} (v : cvec n) : vec n := cv2v v. *)
(* Definition v2cv {n} (v : vec n) : cvec n := v2cv v. *)

(** cv2v (v1 + v2) = cv2v v1 + cv2v v2 *)
Lemma cv2v_madd : forall {n} (v1 v2 : cvec n), cv2v (v1 + v2)%M = cv2v v1 + cv2v v2.
Proof. intros. apply cv2v_madd. Qed.

(** cv2v (a .* v) = a .* (cv2v v) *)
Lemma cv2v_mcmul : forall {n} (a : A) (v : cvec n), cv2v (a \.* v)%M = (a \.* (cv2v v))%V.
Proof. intros. apply cv2v_mcmul. Qed.


(* Section rvec_cvec. *)

(*   (** Convert row/column vector to vector *) *)
(*   Definition rv2v {n} (v : rvec n) : vec n := rv2v v. *)
(*   Definition cv2v {n} (v : cvec n) : vec n := cv2v v. *)

(*   (* (** Convert vector to row/column vector *) *) *)
(*   Definition v2rv {n} (v : vec n) : rvec n := v2rv v. *)
(*   Definition v2cv {n} (v : vec n) : cvec n := v2cv v. *)
  
(* End rvec_cvec. *)



(* ======================================================================= *)
(** linear combination *)
Section lcomb.

  (* x1*v1 + x2*v2 + ... + xr*vr *)
  (* Definition lcomb {r c} (x : vec r) (v : mat r c) : vec r. *)
  (*   Check v : @Vector.vec (@Vector.vec A c) r. *)
  (*   Set Printing All. *)
  (*   Check Vector.vmap (vdot x) (v : @Vector.vec (@Vector.vec A c) r). *)
  (*   Check Vector.vmap2 vcmul x v. *)
  (*   Check Vector.vsum. *)

End lcomb.


(* ======================================================================= *)
(** ** Convert a angle between degree and radian *)
Section angle.

  Inductive AngleKind := Radian | Degree.

  Definition deg2rad (d : R) : R := d * PI / 180.
  Definition rad2deg (r : R) : R := r * 180 / PI.

  Record angle := {
      angle_radian : R;
      angle_degree : R
    }.
  
  Definition mk_angle_deg (d : R) : angle :=
    Build_angle (deg2rad d) d.

  Definition mk_angle_rad (r : R) : angle :=
    Build_angle r (rad2deg r).

  Notation "r 'rad" := (mk_angle_rad r) (at level 30).
  Notation "d 'deg" := (mk_angle_deg d) (at level 30).

  Goal 180 'deg = PI 'rad.
  Proof. cbv. f_equal; field. ra. Qed.

End angle.

Notation "r 'rad" := (mk_angle_rad r) (at level 30).
Notation "d 'deg" := (mk_angle_deg d) (at level 30).

