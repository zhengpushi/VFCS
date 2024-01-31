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
Open Scope vec_scope.


(* ======================================================================= *)
(** * Vector theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.

  Variable a1 a2 a3 : A.
  Variable f : A -> A.
  Let v := mkvec3 a1 a2 a3.
  (* Compute v2l (vmap v f). *)

End test.
