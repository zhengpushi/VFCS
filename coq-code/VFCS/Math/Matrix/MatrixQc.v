(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Qc.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export QcExt.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryQc := FieldMatrixTheory FieldElementTypeQc.

Open Scope Q_scope.
Open Scope Qc_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let M1 := @l2m 3 3 (Q2Qc_dlist [[1;-3;-2];[-2;1;-4];[-1;4;-1]]%Q).
  (* Compute m2l M1. *)
  (* Compute m2l (mmap Qcopp M1). *)
  (* Compute m2l (M1 * M1). *)
  (* Compute m2l ((Q2Qc 5) \.* M1). *)

  Variable a11 a12 a21 a22 : A.
  Variable f : A -> A.
  Let M2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l M2.             (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f M2).    (* = [[f a11; f a12]; [f a21; f a22]] *) *)

  (** matrix inversion by gauss elimnation *)
  Opaque Aadd Amul Aopp.
  (* Compute m2l (minv (@l2m 1 1 [[1]])). *)
  (* Compute m2l (minv (@l2m 2 2 [[1;0];[0;1]])). *)
  (* Compute m2l (minv (@l2m 3 3 (Q2Qc_dlist [[1;2;3];[4;5;6];[7;9;8]]%Q))). *)
  
End test.
