(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on nat.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export NatExt VectorModule.
(* Require Export RowColVectorModule. *)

(* ######################################################################### *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryNat := MonoidVectorTheory MonoidElementTypeNat.


(* ######################################################################### *)
(** * Vector theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let V1 := @l2v 3 [1;2;3].
  Let V2 := @f2v 3 (fun i => 5 + i)%nat.
  
  (* Compute v2l V1. *)
  (* Compute v2l V2. *)
  (* Compute V1$fin0. *)
  (* Compute v2l (vmap V1 S). *)
  (* Compute v2l (vmap2 V1 V2 Nat.add). *)
  (* Compute @Vector.v2l _ _ (@Vector.vmap2 _ _ _ pair _ V1 V2). *)
  (* Compute vsum V1 Nat.add 0.  *)
  (* Compute v2l (V1 + V2). *)
End test.
