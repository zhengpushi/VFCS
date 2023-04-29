(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on Qc.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Import VectorModule.


(* ======================================================================= *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryQc := RingVectorTheory RingElementTypeQc.

Open Scope Q_scope.
Open Scope Qc_scope.
Open Scope mat_scope.
Open Scope rvec_scope.
Open Scope cvec_scope.


(* ======================================================================= *)
(** * Vector theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let l1 := Q2Qc_list [1%Q;2;3].
  Let v1 := @l2rv 2 l1.
  Let v2 := @l2cv 2 l1.
  (* Compute rv2l v1. *)
  (* Compute cv2l v2. *)

  Variable a0 a1 a2 : A.
  Let v3 := t2rv_3 (a0,a1,a2).
  (* Compute rv2l (rvmap v3 Qcopp). *)
  (* Eval cbn in rv2l (rvmap v3 Qcopp). *)

  Let v4 := t2cv_3 (a0,a1,a2).
  (* Compute cv2l (cvmap v4 Qopp). *)
  (* Eval cbn in cv2l (cvmap v4 Qcopp). *)
End test.
