(*
  Copyright 2024 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Metric Space
  author    : ZhengPu Shi
  date      : 2024.01
  
  remark    :
 *)

Require Export Hierarchy.
Require Import RExt.

Open Scope nat_scope.
Open Scope A_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Adiv Alt.


(* ######################################################################### *)
(** * Metric space *)

(** Adist:A×A→R(>=0) is a metric over A, if it satisfy three axioms.
    Then, (A, Adist) is called a metric space, and Adist(a,b) is called the 
    distance between point a and b in (A,dist)     *)
Class MetricSpace {A} (Adist : A -> A -> R) := {
    ms_gt0 : forall a b : A, (R0 <= Adist a b)%R;
    ms_eq0_iff_eq : forall a b : A, Adist a b = R0 <-> a = b;
    ms_sym : forall a b : A, Adist a b = Adist b a;
    ms_tri_ineg : forall a b c : A, (Adist a c <= Adist a b + Adist b c)%R
  }.

(** ** Instances *)

(** ** Extra Theories *)
Section Theory.
End Theory.
