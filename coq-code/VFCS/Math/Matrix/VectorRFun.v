(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on function of R to R.
  author    : ZhengPu Shi
  date      : 2023.04

 *)

Require Import VectorModule.


(* ======================================================================= *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryRFun := RingVectorTheory RingElementTypeRFun.

Open Scope Rfun_scope.
Open Scope mat_scope.
Open Scope rvec_scope.
Open Scope cvec_scope.


(* ======================================================================= *)
(** * Vector theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.

  Variable a1 a2 a3 : T.
  Variable f : T -> T.
  Let v3 := t2rv_3 (a1,a2,a3).
  Let v4 := t2cv_3 (a1,a2,a3).
  (* Compute rv2l (rvmap v3 f). *)
  (* Compute cv2l (cvmap v4 f). *)

End test.
