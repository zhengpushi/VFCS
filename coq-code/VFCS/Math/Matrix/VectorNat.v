(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on nat.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export Vector.
Require Export NatExt.


(* ======================================================================= *)
(** ** Vector theory come from common implementations *)

Open Scope nat_scope.
Open Scope mat_scope.
Open Scope vec_scope.

(** general notations *)
Notation listA := (list nat).

(** *** vector type and basic operation *)
Definition vec (n : nat) : Type := @vec nat n.

Notation "v ! i" := (vnth 0 v i) : vec_scope.

Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
    (v1 == v2) <-> (forall i, i < n -> v1!i = v2!i)%nat.
Proof. apply veq_iff_vnth. Qed.
  
(** *** convert between list and vector *)
Definition l2v n (l : listA) : vec n := l2v 0 n l.
Definition v2l {n} (v : vec n) : listA := v2l v.

Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
Proof. intros. apply v2l_length. Qed.

Lemma v2l_l2v_id : forall {n} (l : listA), length l = n -> v2l (l2v n l) = l.
Proof. intros. apply v2l_l2v_id; auto. Qed.

Lemma l2v_v2l_id : forall {n} (v : vec n), l2v n (v2l v) == v.
Proof. intros. apply l2v_v2l_id; auto. Qed.

(** *** Convert between tuples and vector *)
Definition t2v_2 (t : T2) : vec 2 := t2v_2 0 t.
Definition t2v_3 (t : T3) : vec 3 := t2v_3 0 t.
Definition t2v_4 (t : T4) : vec 4 := t2v_4 0 t.

Definition v2t_2 (v : vec 2) : T2 := v2t_2 v.
Definition v2t_3 (v : vec 3) : T3 := v2t_3 v.
Definition v2t_4 (v : vec 4) : T4 := v2t_4 v.

(* Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v. *)
(* Lemma v2t_t2v_id_2 : forall (t : T2), v2t_2 (t2v_2 t) = t. *)

(** *** make concrete vector *)
Definition mk_vec2 a0 a1 : vec 2 := mk_vec2 0 a0 a1.
Definition mk_vec3 a0 a1 a2 : vec 3 := mk_vec3 0 a0 a1 a2.
Definition mk_vec4 a0 a1 a2 a3 : vec 4 := mk_vec4 0 a0 a1 a2 a3.

(** *** vector mapping *)
Definition vmap {n} f (v : vec n) : vec n := vmap v f.
Definition vmap2 {n} f (v1 v2 : vec n) : vec n := vmap2 v1 v2 f.

(** *** vector folding *)
(* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)


(* ======================================================================= *)
(** ** Vector theory applied to this type *)


(* ======================================================================= *)
(** ** Usage demo *)
Section test.
  Let l1 := [1;2;3].
  Let v1 := l2v 2 l1.
  (* Compute v2l v1. *)
  (* Compute v2l (@l2v 3 l1). *)

  Variable a1 a2 a3 : nat.
  Let v2 := t2v_3 (a1,a2,a3).
  (* Compute v2l v2. *)
  (* Compute v2l (vmap S v2). *)
  
End test.
