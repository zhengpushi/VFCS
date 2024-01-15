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
  Let u := @l2v 3 [1.5;3/2;6/4].
  Let v := @f2v 3 (fun i => -1 + nat2Q i)%Q.
  
  (* Compute vl u. *)
  (* Compute vl v. *)
  (* Compute u$fin0. *)
  (* Compute vl (vmap u Qopp). *)
  (* Compute vl (vmap2 u v Qplus). *)
  (* Compute @Vector.vl _ _ (@Vector.vmap2 _ _ _ pair _ u v). *)
  (* Compute vsum u Qplus 0. *)
End test.
