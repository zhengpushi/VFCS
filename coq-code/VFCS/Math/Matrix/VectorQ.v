(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on Q.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export QExt VectorModule.
(* Require Export RowColVectorModule. *)

(* ######################################################################### *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryQ := BasicVectorTheory ElementTypeQ.

Open Scope Q_scope.
Open Scope vec_scope.


(* ######################################################################### *)
(** * Vector theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let V1 := @l2v 3 [1.5;3/2;6/4].
  Let V2 := @f2v 3 (fun i => -1 + nat2Q i)%Q.
  
  (* Compute v2l V1. *)
  (* Compute v2l V2. *)
  (* Compute V1$fin0. *)
  (* Compute v2l (vmap V1 Qopp). *)
  (* Compute v2l (vmap2 V1 V2 Qplus). *)
  (* Compute @Vector.v2l _ _ (@Vector.vmap2 _ _ _ pair _ V1 V2). *)
  (* Compute vsum V1 Qplus 0. *)
End test.
