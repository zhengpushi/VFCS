(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on nat.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Import VectorModule.


(* ======================================================================= *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryNat := BasicVectorTheory ElementTypeNat.


(* ======================================================================= *)
(** * Vector theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let l1 := [1;2;3].
  Let v1 := @l2rv 2 l1.
  Let v2 := @l2cv 2 l1.
  (* Compute rv2l v1. *)
  (* Compute cv2l v2. *)

  (* Compute v1$0. *)
  (* Compute v1.1. *)
  (* Compute (v1!0)%RV. *)
  
  (* Compute v2$1. *)
  (* Compute v2.1. *)
  (* Compute v2!1. *)

  Variable a1 a2 a3 : A.
  Let v3 := t2rv_3 (a1,a2,a3).
  (* Compute rv2l (rvmap v3 S). *)

  Let v4 := t2cv_3 (a1,a2,a3).
  (* Compute cv2l (cvmap v4 S). *)
  
End test.
