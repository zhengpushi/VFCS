(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on Complex.
  author    : ZhengPu Shi
  date      : 2023.04
 *)

Require Export Complex VectorModule.
(* Require Export RowColVectorModule. *)

(* ######################################################################### *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryC := RingVectorTheory RingElementTypeC.

Open Scope R_scope.
Open Scope C_scope.
Open Scope vec_scope.


(* ######################################################################### *)
(** * Vector theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let u := @l2v 3 [1+i2; 2+i(-2); (3,-3)].
  Let v := @f2v 3 (fun i => (nat2R i, (-(nat2R i))%R)).
  
  (* Compute v2l u. *)
  (* Compute v2l v. *)
  (* Compute u$fin0. *)
  (* Compute v2l (vmap u Copp). *)
  (* Compute v2l (vmap2 u v Cadd). *)
  (* Compute @Vector.v2l _ _ (@Vector.vmap2 _ _ _ pair _ u v). *)
  (* Compute vsum u Cadd C0. *)
  (* Compute v2l (u + v). *)

  (* Compute v2l (u - v). *)
  (* Compute v2l ((1+i1) c* u). *)
  (* Compute <u,v>. *)
End test.
