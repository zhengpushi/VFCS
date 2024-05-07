(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Mathematics for position and orientation representation
  author    : ZhengPu Shi
  date      : 2024.01

  reference :
  remark    :
  1. mainly use MatrixR.
  2. rvec, cvec and vec are different, but can be converted each other.
     especially, rvec and cvec are automaticaly converted to vec by coercion.

 *)

From FinMatrix Require Export MatrixR.
(* Require Import Quaternion. *)

Open Scope nat_scope.
Open Scope R_scope.
Open Scope vec_scope.
Open Scope mat_scope.


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

