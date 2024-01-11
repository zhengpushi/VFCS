(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on Z.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export ZExt VectorModule.
(* Require Export RowColVectorModule. *)

(* ######################################################################### *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryZ := RingVectorTheory RingElementTypeZ.

Open Scope Z_scope.
Open Scope vec_scope.


(* ######################################################################### *)
(** * Vector theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let V1 := @l2v 3 [1;2;-3].
  Let V2 := @f2v 3 (fun i => -1 + nat2Z i)%Z.
  
  (* Compute v2l V1. *)
  (* Compute v2l V2. *)
  (* Compute V1$fin0. *)
  (* Compute v2l (vmap V1 (Z.add 1)). *)
  (* Compute v2l (vmap2 V1 V2 Z.add). *)
  (* Compute @Vector.v2l _ _ (@Vector.vmap2 _ _ _ pair _ V1 V2). *)
  (* Compute vsum V1 Z.add 0. *)
  (* Compute v2l (V1 + V2). *)

  (* Compute v2l (V1 - V2). *)
  (* Compute v2l (3 c* V1). *)
  (* Compute <V1,V2>. *)
End test.
