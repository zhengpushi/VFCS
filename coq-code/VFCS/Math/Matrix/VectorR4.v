(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 4-dimensional vector on R.
  author    : ZhengPu Shi
  date      : 2023.01

  reference :
  remark    :
 *)

Require Import VectorR.


(* ======================================================================= *)
(** * 4D vector theory *)

(** Equality and Inequality *)
Section cv4eq_cv4neq.

  (** Convert equality of vector to equality of its components *)
  Lemma cv4eq_iff : forall (v1 v2 : cvec 4),
      v1 == v2 <-> (v1.1 = v2.1 /\ v1.2 = v2.2 /\ v1.3 = v2.3 /\ v1.4 = v2.4).
  Proof. intros. split; intros. repeat (split; try apply H; auto). lma. Qed.

  (** Convert inequality of vector to inequality of its components *)
  Lemma cv4neq_iff : forall (v1 v2 : cvec 4),
      v1 != v2 <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2 \/ v1.3 <> v2.3 \/ v1.4 <> v2.4).
  Proof. intros. unfold not. rewrite cv4eq_iff. lra. Qed.

End cv4eq_cv4neq.

(** Standard unit vector in space of 4-dimensions *)
Section basis_vector.
  Definition cv4i : cvec 4 := mk_cvec4 1 0 0 0.
  Definition cv4j : cvec 4 := mk_cvec4 0 1 0 0.
  Definition cv4k : cvec 4 := mk_cvec4 0 0 1 0.
  Definition cv4l : cvec 4 := mk_cvec4 0 0 0 1.

  Definition rv4i : rvec 4 := mk_rvec4 1 0 0 0.
  Definition rv4j : rvec 4 := mk_rvec4 0 1 0 0.
  Definition rv4k : rvec 4 := mk_rvec4 0 0 1 0.
  Definition rv4l : rvec 4 := mk_rvec4 0 0 0 1.
End basis_vector.
