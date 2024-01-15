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
  Let u := @l2v 3 [1;2;3].
  Let v := @f2v 3 (fun i => 5 + i)%nat.
  
  (* Compute vl u. *)
  (* Compute vl v. *)
  (* Compute u$fin0. *)
  (* Compute vl (vmap u S). *)
  (* Compute vl (vmap2 u v Nat.add). *)
  (* Compute @Vector.vl _ _ (@Vector.vmap2 _ _ _ pair _ u v). *)
  (* Compute vsum u Nat.add 0.  *)
  (* Compute vl (u + v). *)
End test.
