(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on Qc.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export Vector.
Require Export MatrixQc.


(* ======================================================================= *)
(** ** Vector theory come from common implementations *)

Open Scope Q_scope.
Open Scope Qc_scope.
Open Scope mat_scope.
Open Scope vec_scope.

(** general notations *)
Notation A := Qc.
Notation A0 := 0.
Notation A1 := 1.
Notation Aadd := Qcplus.
Notation Aopp := Qcopp.
Notation Amul := Qcmult.

(** *** vector type and basic operation *)
Definition vec (n : nat) : Type := @vec A n.

Notation "v ! i" := (vnth A0 v i) : vec_scope.

Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
    (v1 == v2) <-> (forall i, i < n -> v1!i = v2!i)%nat.
Proof. apply veq_iff_vnth. Qed.
  
(** *** convert between list and vector *)
Definition l2v n (l : list A) : vec n := l2v A0 n l.
Definition v2l {n} (v : vec n) : list A := v2l v.

Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
Proof. intros. apply v2l_length. Qed.

Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> v2l (l2v n l) = l.
Proof. intros. apply v2l_l2v_id; auto. Qed.

Lemma l2v_v2l_id : forall {n} (v : vec n), l2v n (v2l v) == v.
Proof. intros. apply l2v_v2l_id; auto. Qed.

(** *** Convert between tuples and vector *)
Definition t2v_2 (t : T2) : vec 2 := t2v_2 A0 t.
Definition t2v_3 (t : T3) : vec 3 := t2v_3 A0 t.
Definition t2v_4 (t : T4) : vec 4 := t2v_4 A0 t.

Definition v2t_2 (v : vec 2) : T2 := v2t_2 v.
Definition v2t_3 (v : vec 3) : T3 := v2t_3 v.
Definition v2t_4 (v : vec 4) : T4 := v2t_4 v.

(* Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v. *)
(* Lemma v2t_t2v_id_2 : forall (t : T2), v2t_2 (t2v_2 t) = t. *)

(** *** make concrete vector *)
Definition mk_vec2 a0 a1 : vec 2 := mk_vec2 A0 a0 a1.
Definition mk_vec3 a0 a1 a2 : vec 3 := mk_vec3 A0 a0 a1 a2.
Definition mk_vec4 a0 a1 a2 a3 : vec 4 := mk_vec4 A0 a0 a1 a2 a3.

(** *** vector mapping *)
Definition vmap {n} f (v : vec n) : vec n := vmap v f.
Definition vmap2 {n} f (v1 v2 : vec n) : vec n := vmap2 v1 v2 f.

(** *** vector folding *)
(* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)

(** *** zero vector *)
Definition vec0 {n} : vec n := vec0 (A0:=A0).

(** *** vector addition *)
Definition vadd {n} (v1 v2 : vec n) : vec n := vadd v1 v2 (Aadd:=Aadd).
Infix "+" := vadd : vec_scope.

Lemma vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
Proof. intros. apply vadd_comm. Qed.

Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
Proof. intros. apply vadd_assoc. Qed.

Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v == v.
Proof. intros. apply vadd_0_l. Qed.

Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
Proof. intros. apply vadd_0_r. Qed.

(** *** vector opposition *)
Definition vopp {n} (v : vec n) : vec n := vopp v (Aopp:=Aopp).
Notation "- v" := (vopp v) : vec_scope.

Lemma vadd_opp_l : forall {n} (v : vec n), (- v) + v == vec0.
Proof. intros. apply vadd_opp_l. Qed.

Lemma vadd_opp_r : forall {n} (v : vec n), v + (- v) == vec0.
Proof. intros. apply vadd_opp_r. Qed.

(** *** vector subtraction *)
Definition vsub {n} (v1 v2 : vec n) : vec n := vsub v1 v2 (Aadd:=Aadd)(Aopp:=Aopp).
Infix "-" := vsub : vec_scope.

(** *** vector scalar multiplication *)
Definition vcmul {n} a (v : vec n) : vec n := vcmul a v (Amul:=Amul).
Infix "c*" := vcmul : vec_scope.

Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b) c* v.
Proof. intros. apply vcmul_assoc. Qed.

Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
Proof. intros. apply vcmul_perm. Qed.

Lemma vcmul_add_distr_l : forall {n} a b (v : vec n), (a + b) c* v == (a c* v) + (b c* v).
Proof. intros. apply vcmul_add_distr_l. Qed.

Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n),
    a c* (v1 + v2) == (a c* v1) + (a c* v2).
Proof. intros. apply vcmul_add_distr_r. Qed.

Lemma vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0.
Proof. intros. apply vcmul_0_l. Qed.

Lemma vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.
Proof. intros. apply vcmul_1_l. Qed.

(** *** vector dot product *)
Definition vdot {n} (v1 v2 : vec n) := vdot v1 v2 (Aadd:=Aadd)(A0:=A0)(Amul:=Amul).


(* ======================================================================= *)
(** ** Vector theory applied to this type *)


(* ======================================================================= *)
(** ** Usage demo *)
Section test.

  Let l1 := Q2Qc_list [1%Q;2;3].
  Let v1 := l2v 2 l1.
  (* Compute v2l v1. *)
  (* Compute v2l (@l2v 3 l1). *)

  Variable a1 a2 a3 : Qc.
  Let v2 := t2v_3 (a1,a2,a3).
  (* Compute v2l v2. *)
  (* Eval cbn in v2l (vmap Qcopp v2). *)
  
End test.
