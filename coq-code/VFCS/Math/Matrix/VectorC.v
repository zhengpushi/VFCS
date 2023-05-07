(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on Complex.
  author    : ZhengPu Shi
  date      : 2023.04
 *)

Require Export VectorModule.
Require Export MatrixC.


(* ======================================================================= *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryC := RingVectorTheory RingElementTypeC.

Open Scope C_scope.
Open Scope mat_scope.
Open Scope rvec_scope.
Open Scope cvec_scope.


(* ======================================================================= *)
(** * Vector theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let l1 := [1 +i 2; 3 +i 4; 5 +i 6].
  Let v1 := @l2rv 2 l1.
  Let v2 := @l2cv 2 l1.
  (* Compute rv2l v1. *)
  (* Compute cv2l v2. *)

  Variable a1 a2 a3 : A.
  Variable f : A -> A.
  Let v3 := t2rv_3 (a1,a2,a3).
  Let v4 := t2cv_3 (a1,a2,a3).
  (* Compute rv2l (rvmap v3 f). *)
  (* Compute cv2l (cvmap v4 f). *)
  
End test.
