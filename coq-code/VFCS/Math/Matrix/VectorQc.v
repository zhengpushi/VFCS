(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on Qc.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export QcExt VectorModule.
(* Require Export RowColVectorModule. *)

(* ######################################################################### *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryQc := RingVectorTheory RingElementTypeQc.

Open Scope Q_scope.
Open Scope Qc_scope.
Open Scope vec_scope.


(* ######################################################################### *)
(** * Vector theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let V1 := @l2v 3 (Q2Qc_list [1.5;3#2;(-6/4)%Q]).
  Let V2 := @f2v 3 (fun i => (Q2Qc 1.5) + nat2Qc i)%Qc.
  
  (* Compute v2l V1. *)
  (* Compute v2l V2. *)
  (* Compute V1$fin0. *)
  (* Compute v2l (vmap V1 Qcopp). *)
  (* Compute v2l (vmap2 V1 V2 Qcplus). *)
  (* Compute @Vector.v2l _ _ (@Vector.vmap2 _ _ _ pair _ V1 V2). *)
  (* Compute vsum V1 Qcplus 0. *)
  (* Compute v2l (V1 + V2). *)

  (* Compute v2l (V1 - V2). *)
  (* Compute v2l ((Q2Qc 3) c* V1). *)
  (* Compute <V1,V2>. *)
End test.
