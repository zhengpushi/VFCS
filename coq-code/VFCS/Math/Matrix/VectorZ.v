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
  Let u := @l2v 3 [1;2;-3].
  Let v := @f2v 3 (fun i => -1 + nat2Z i)%Z.
  
  (* Compute vl u. *)
  (* Compute vl v. *)
  (* Compute u$fin0. *)
  (* Compute vl (vmap u (Z.add 1)). *)
  (* Compute vl (vmap2 u v Z.add). *)
  (* Compute @Vector.vl _ _ (@Vector.vmap2 _ _ _ pair _ u v). *)
  (* Compute vsum u Z.add 0. *)
  (* Compute vl (u + v). *)

  (* Compute vl (u - v). *)
  (* Compute vl (3 c* u). *)
  (* Compute <u,v>. *)
End test.
