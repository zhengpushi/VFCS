(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on Z.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export Vector.
Require Export MatrixZ.

Open Scope Z_scope.
Open Scope mat_scope.


Module Export RowVectorZ.
  Open Scope rvec_scope.

  (* ======================================================================= *)
  (** ** Vector theory come from common implementations *)
  
  (** *** vector type and basic operation *)
  Definition rvec (n : nat) : Type := @rvec A n.

  Definition rvnth {n : nat} (v : rvec n) (i : nat) : A := rvnth A0 v i.
  Notation "v ! i" := (rvnth v i) : rvec_scope.

  Lemma veq_iff_rvnth : forall {n : nat} (v1 v2 : rvec n),
      (v1 == v2) <-> (forall i, i < n -> (v1!i == v2!i)%A)%nat.
  Proof. intros. apply veq_iff_rvnth. Qed.

  
  (** *** convert between list and vector *)
  Definition l2rv n (l : list A) : rvec n := l2rv A0 n l.
  Definition rv2l {n} (v : rvec n) : list A := rv2l v.

  Lemma rv2l_length : forall {n} (v : rvec n), length (rv2l v) = n.
  Proof. intros. apply rv2l_length. Qed.

  Lemma rv2l_l2rv_id : forall {n} (l : list A), length l = n -> (rv2l (l2rv n l) == l)%list.
  Proof. intros. apply rv2l_l2rv_id; auto. Qed.

  Lemma l2rv_rv2l_id : forall {n} (v : rvec n), l2rv n (rv2l v) == v.
  Proof. intros. apply l2rv_rv2l_id; auto. Qed.


  (** *** Convert between tuples and vector *)
  Definition t2rv_2 (t : T2) : rvec 2 := t2rv_2 A0 t.
  Definition t2rv_3 (t : T3) : rvec 3 := t2rv_3 A0 t.
  Definition t2rv_4 (t : T4) : rvec 4 := t2rv_4 A0 t.

  Definition rv2t_2 (v : rvec 2) : T2 := rv2t_2 v.
  Definition rv2t_3 (v : rvec 3) : T3 := rv2t_3 v.
  Definition rv2t_4 (v : rvec 4) : T4 := rv2t_4 v.

  (* Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v. *)
  (* Lemma v2t_t2v_id_2 : forall (t : T2), v2t_2 (t2v_2 t) = t. *)


  (** *** make concrete vector *)
  Definition mk_rvec2 a0 a1 : rvec 2 := mk_rvec2 A0 a0 a1.
  Definition mk_rvec3 a0 a1 a2 : rvec 3 := mk_rvec3 A0 a0 a1 a2.
  Definition mk_rvec4 a0 a1 a2 a3 : rvec 4 := mk_rvec4 A0 a0 a1 a2 a3.


  (** *** vector mapping *)
  Definition rvmap {n} f (v : rvec n) : rvec n := rvmap v f.
  Definition rvmap2 {n} f (v1 v2 : rvec n) : rvec n := rvmap2 v1 v2 f.

  
  (** *** vector folding *)
  (* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)


  (** *** zero vector *)
  Definition rvec0 {n} : rvec n := rvec0 (A0:=A0).


  (** *** vector addition, opposition and subtraction *)
  Definition rvadd {n} (v1 v2 : rvec n) : rvec n := rvadd v1 v2 (Aadd:=Aadd).
  Infix "+" := rvadd : rvec_scope.

  Lemma rvadd_comm : forall {n} (v1 v2 : rvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply rvadd_comm. Qed.

  Lemma rvadd_assoc : forall {n} (v1 v2 v3 : rvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply rvadd_assoc. Qed.

  Lemma rvadd_0_l : forall {n} (v : rvec n), rvec0 + v == v.
  Proof. intros. apply rvadd_0_l. Qed.

  Lemma rvadd_0_r : forall {n} (v : rvec n), v + rvec0 == v.
  Proof. intros. apply rvadd_0_r. Qed.

  Definition rvopp {n} (v : rvec n) : rvec n := rvopp v (Aopp:=Aopp).
  Notation "- v" := (rvopp v) : rvec_scope.

  Lemma rvadd_opp_l : forall {n} (v : rvec n), (- v) + v == rvec0.
  Proof. intros. apply rvadd_opp_l. Qed.

  Lemma rvadd_opp_r : forall {n} (v : rvec n), v + (- v) == rvec0.
  Proof. intros. apply rvadd_opp_r. Qed.

  Definition rvsub {n} (v1 v2 : rvec n) : rvec n := rvsub v1 v2 (Aadd:=Aadd) (Aopp:=Aopp).
  Infix "-" := rvsub : rvec_scope.


  (** *** vector scalar multiplication *)
  Definition rvcmul {n} a (v : rvec n) : rvec n := rvcmul a v (Amul:=Amul).
  Infix "c*" := rvcmul : rvec_scope.

  Lemma rvcmul_assoc : forall {n} a b (v : rvec n), a c* (b c* v) == (a * b) c* v.
  Proof. intros. apply rvcmul_assoc. Qed.

  Lemma rvcmul_perm : forall {n} a b (v : rvec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply rvcmul_perm. Qed.

  Lemma rvcmul_add_distr_l : forall {n} a b (v : rvec n),
      (a + b) c* v == (a c* v) + (b c* v).
  Proof. intros. apply rvcmul_add_distr_l. Qed.

  Lemma rvcmul_add_distr_r : forall {n} a (v1 v2 : rvec n),
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply rvcmul_add_distr_r. Qed.

  Lemma rvcmul_0_l : forall {n} (v : rvec n), A0 c* v == rvec0.
  Proof. intros. apply rvcmul_0_l. Qed.

  Lemma rvcmul_1_l : forall {n} (v : rvec n), A1 c* v == v.
  Proof. intros. apply rvcmul_1_l. Qed.


  (** *** vector dot product *)
  Definition rvdot {n} (v1 v2 : rvec n) :=
    rvdot v1 v2 (Aadd:=Aadd)(A0:=A0)(Amul:=Amul).

  
  (* ======================================================================= *)
  (** ** Vector theory applied to this type *)


  (* ======================================================================= *)
  (** ** Usage demo *)
  Section test.

    Let l1 := [1;2;3].
    Let v1 := l2rv 2 l1.
    (* Compute rv2l (@l2rv 3 l1). *)

    Variable a1 a2 a3 : Z.
    Let v2 := t2rv_3 (a1,a2,a3).
    (* Eval cbn in rv2l (rvmap Z.opp v2). *)
  End test.

End RowVectorZ.


Module Export ColVectorZ.
  Open Scope cvec_scope.

  (* ======================================================================= *)
  (** ** Vector theory come from common implementations *)

  (** *** vector type and basic operation *)
  Definition cvec (n : nat) : Type := @cvec A n.

  Definition cvnth {n : nat} (v : cvec n) (i : nat) : A := cvnth A0 v i.
  Notation "v ! i" := (cvnth v i) : cvec_scope.

  Lemma veq_iff_cvnth : forall {n : nat} (v1 v2 : cvec n),
      (v1 == v2) <-> (forall i, i < n -> (v1!i = v2!i)%A)%nat.
  Proof. intros. apply veq_iff_cvnth. Qed.


  (** *** convert between list and vector *)
  Definition l2cv n (l : list A) : cvec n := l2cv A0 n l.
  Definition cv2l {n} (v : cvec n) : list A := cv2l v.

  Lemma cv2l_length : forall {n} (v : cvec n), length (cv2l v) = n.
  Proof. intros. apply cv2l_length. Qed.

  Lemma cv2l_l2cv_id : forall {n} (l : list A), length l = n -> (cv2l (l2cv n l) == l)%list.
  Proof. intros. apply cv2l_l2cv_id; auto. Qed.

  Lemma l2cv_cv2l_id : forall {n} (v : cvec n), l2cv n (cv2l v) == v.
  Proof. intros. apply l2cv_cv2l_id; auto. Qed.


  (** *** Convert between tuples and vector *)
  Definition t2cv_2 (t : T2) : cvec 2 := t2cv_2 A0 t.
  Definition t2cv_3 (t : T3) : cvec 3 := t2cv_3 A0 t.
  Definition t2cv_4 (t : T4) : cvec 4 := t2cv_4 A0 t.

  Definition cv2t_2 (v : cvec 2) : T2 := cv2t_2 v.
  Definition cv2t_3 (v : cvec 3) : T3 := cv2t_3 v.
  Definition cv2t_4 (v : cvec 4) : T4 := cv2t_4 v.

  (* Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v. *)
  (* Lemma v2t_t2v_id_2 : forall (t : T2), v2t_2 (t2v_2 t) = t. *)


  (** *** make concrete vector *)
  Definition mk_cvec2 a0 a1 : cvec 2 := mk_cvec2 A0 a0 a1.
  Definition mk_cvec3 a0 a1 a2 : cvec 3 := mk_cvec3 A0 a0 a1 a2.
  Definition mk_cvec4 a0 a1 a2 a3 : cvec 4 := mk_cvec4 A0 a0 a1 a2 a3.


  (** *** vector mapping *)
  Definition cvmap {n} f (v : cvec n) : cvec n := cvmap v f.
  Definition cvmap2 {n} f (v1 v2 : cvec n) : cvec n := cvmap2 v1 v2 f.


  (** *** vector folding *)
  (* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)


  (** *** zero vector *)
  Definition cvec0 {n} : cvec n := cvec0 (A0:=A0).


  (** *** vector addition, opposition and subtraction *)
  Definition cvadd {n} (v1 v2 : cvec n) : cvec n := cvadd v1 v2 (Aadd:=Aadd).
  Infix "+" := cvadd : cvec_scope.

  Lemma cvadd_comm : forall {n} (v1 v2 : cvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply cvadd_comm. Qed.

  Lemma cvadd_assoc : forall {n} (v1 v2 v3 : cvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply cvadd_assoc. Qed.

  Lemma cvadd_0_l : forall {n} (v : cvec n), cvec0 + v == v.
  Proof. intros. apply cvadd_0_l. Qed.

  Lemma cvadd_0_r : forall {n} (v : cvec n), v + cvec0 == v.
  Proof. intros. apply cvadd_0_r. Qed.

  Definition cvopp {n} (v : cvec n) : cvec n := cvopp v (Aopp:=Aopp).
  Notation "- v" := (cvopp v) : cvec_scope.

  Lemma cvadd_opp_l : forall {n} (v : cvec n), (- v) + v == cvec0.
  Proof. intros. apply cvadd_opp_l. Qed.

  Lemma cvadd_opp_r : forall {n} (v : cvec n), v + (- v) == cvec0.
  Proof. intros. apply cvadd_opp_r. Qed.

  Definition cvsub {n} (v1 v2 : cvec n) : cvec n := cvsub v1 v2 (Aadd:=Aadd) (Aopp:=Aopp).
  Infix "-" := cvsub : cvec_scope.


  (** *** vector scalar multiplication *)
  Definition cvcmul {n} a (v : cvec n) : cvec n := cvcmul a v (Amul:=Amul).
  Infix "c*" := cvcmul : cvec_scope.

  Lemma cvcmul_assoc : forall {n} a b (v : cvec n), a c* (b c* v) == (a * b) c* v.
  Proof. intros. apply cvcmul_assoc. Qed.

  Lemma cvcmul_perm : forall {n} a b (v : cvec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply cvcmul_perm. Qed.

  Lemma cvcmul_add_distr_l : forall {n} a (v1 v2 : cvec n),
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply cvcmul_add_distr_l. Qed.

  Lemma cvcmul_add_distr_r : forall {n} a b (v : cvec n),
      (a + b) c* v == (a c* v) + (b c* v).
  Proof. intros. apply cvcmul_add_distr_r. Qed.

  Lemma cvcmul_0_l : forall {n} (v : cvec n), A0 c* v == cvec0.
  Proof. intros. apply cvcmul_0_l. Qed.

  Lemma cvcmul_1_l : forall {n} (v : cvec n), A1 c* v == v.
  Proof. intros. apply cvcmul_1_l. Qed.


  (** *** vector dot product *)
  Definition cvdot {n} (v1 v2 : cvec n) :=
    cvdot v1 v2 (Aadd:=Aadd)(A0:=A0)(Amul:=Amul).


  (* ======================================================================= *)
  (** ** Vector theory applied to this type *)


  (* ======================================================================= *)
  (** ** Usage demo *)
  Section test.

    Let l1 := [1;2;3].
    Let v1 := l2cv 2 l1.
    (* Compute cv2l (@l2cv 3 l1). *)

    Variable a1 a2 a3 : Z.
    Let v2 := t2cv_3 (a1,a2,a3).
    (* Eval cbn in cv2l (cvmap Z.opp v2). *)

  End test.

End ColVectorZ.
