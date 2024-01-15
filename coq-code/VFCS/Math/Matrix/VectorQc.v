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
  Let u := @l2v 3 (Q2Qc_list [1.5;3#2;(-6/4)%Q]).
  Let v := @f2v 3 (fun i => (Q2Qc 1.5) + nat2Qc i)%Qc.
  
  (* Compute vl u. *)
  (* Compute vl v. *)
  (* Compute u$fin0. *)
  (* Compute vl (vmap u Qcopp). *)
  (* Compute vl (vmap2 u v Qcplus). *)
  (* Compute @Vector.vl _ _ (@Vector.vmap2 _ _ _ pair _ u v). *)
  (* Compute vsum u Qcplus 0. *)
  (* Compute vl (u + v). *)

  (* Compute vl (u - v). *)
  (* Compute vl ((Q2Qc 3) c* u). *)
  (* Compute <u,v>. *)
End test.
