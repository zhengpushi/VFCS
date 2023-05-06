(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Module
  author    : ZhengPu Shi
  date      : 2023.04
  
  remark    :
  1. use functor to generate many similiar modules
  2. The vector theory is orgainized at several levels
  (1) BasicVectoryTheory
      vector theory on element with equivalence relaton.
  (2) DecidableVectoryTheory
      vector theory on element with decidable relation
  (3) RingVectoryTheory
      vector theory on element with ring structure.
  (4) FieldVectoryTheory
      vector theory on element with field structure.
  (5) DecidableFieldTheory
      vector theory on element with decidable field structure.
 *)

Require Export Vector.
Require Export ElementType.

(** Note: use lower-level Matrix instead of BasicMatrixTheory/RingMatrixtheory.
    To avoiding type confusion *)


(* ######################################################################### *)
(** * Basic Vector Theory *)
Module BasicVectorTheory (E : ElementType).

  (* ==================================== *)
  (** ** Matrix theroy *)
  (* Module Export BasicMatrixTheory_inst := BasicMatrixTheory E. *)

  (* ==================================== *)
  (** ** Vector element type *)
  Export E.
  
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "!=" := (fun l1 l2 => ~(l1 == l2)%list) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "!=" := (fun d1 d2 => ~(d1 == d2)%dlist) : dlist_scope.

  Notation "m ! i ! j " := (mnth Azero m i j) : mat_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.
  

  (** ######################################################################### *)
  (** * (Row Vector part) *)
  Open Scope rvec_scope.
  

  (* ==================================== *)
  (** ** Vector type *)

  (** A vector rvec(n) is a colum vector, equal to a matrix mat(n,1) *)
  Definition rvec (n : nat) := @rvec A n.

  (** Convert between function and vector *)
  Definition f2rv {n} (f : nat -> A) : rvec n := f2rv f.
  Definition rv2f {n} (v : rvec n) : nat -> A := rv2f v.

  (** Convert vec to function *)
  Ltac rvec2fun :=
    repeat match goal with
      | v : rvec ?n |- _ => destruct v as [v]; simpl in *
      end.

  (* ==================================== *)
  (** ** Get element of vector *)

  (** Get element of vector from raw data, unsafe *)
  Notation "v $ i " := (v $ 0 $ i) : rvec_scope.
  Notation "v .0" := (v $ 0) : rvec_scope.
  Notation "v .1" := (v $ 1) : rvec_scope.
  Notation "v .2" := (v $ 2) : rvec_scope.
  Notation "v .3" := (v $ 3) : rvec_scope.
  (* Notation "v .x" := (v $ 0) : rvec_scope. *)
  (* Notation "v .y" := (v $ 1) : rvec_scope. *)
  (* Notation "v .z" := (v $ 2) : rvec_scope. *)
  (* Notation "v .w" := (v $ 3) : rvec_scope. *)
  
  
  (** Get element of vector, the index will be restricted to in the bound, safe *)
  Definition rvnth {n} (v : rvec n) i : A := v ! 0 ! i.
  Notation "v ! i " := (rvnth v i) : rvec_scope.

  (** If the index is in bound, its behavior is equal to get element from raw data *)
  Lemma rvnth_spec : forall {n : nat} (v : rvec n) i, i < n -> (v ! i == v $ i)%A.
  Proof. intros. apply rvnth_spec; auto. Qed.

  (** veq, iff vnth *)
  Lemma veq_iff_rvnth : forall {n : nat} (v1 v2 : rvec n),
      v1 == v2 <-> (forall i, i < n -> (v1 ! i == v2 ! i)%A).
  Proof. intros. apply veq_iff_rvnth. Qed.

  
  (* ==================================== *)
  (** ** Get row-vector of a matrix *)
  Definition mrow {r c : nat} (m : mat r c) (ri : nat) : rvec c := mrow m ri.

  
  (* ==================================== *)
  (** ** List like operations for vector *)
  
  (** a :: v  *)
  Definition rvcons {n} (a : A) (v : rvec n) : rvec (S n) := rvcons a v.

  Lemma rvcons_spec : forall n a (v : rvec n) i,
      let v' := rvcons a v in
      (v' $ 0 == a)%A /\ (i < n -> (v $ i == v' $ (S i))%A).
  Proof. intros. apply rvcons_spec. Qed.

  (** Get a vector from a given vector by remove i-th element *)
  Definition rvremove {n : nat} (v : rvec (S n)) (i : nat) : rvec n := rvremove v i.

  
  (* ==================================== *)
  (** ** Convert between list and vector *)
  Definition rv2l {n} (v : rvec n) : list A := rv2l v.
  Definition l2rv {n} (l : list A) : rvec n := l2rv Azero n l.

  (** list of vector to dlist *)
  Definition rvl2dl {n} (l : list (rvec n)) : dlist A := rvl2dl l.

  Lemma rv2l_length : forall {n} (v : rvec n), length (rv2l v) = n.
  Proof. intros. apply rv2l_length. Qed.

  Lemma rv2l_l2rv_id : forall {n} (l : list A),
      length l = n -> (rv2l (@l2rv n l) == l)%list.
  Proof. intros. apply rv2l_l2rv_id; auto. Qed.

  Lemma l2rv_rv2l_id : forall {n} (v : rvec n), @l2rv n (rv2l v) == v.
  Proof. intros. apply l2rv_rv2l_id. Qed.

  
  (* ==================================== *)
  (** ** Make concrete vector *)
  Definition mk_rvec2 (a0 a1 : A) : rvec 2 := mk_rvec2 Azero a0 a1.
  Definition mk_rvec3 (a0 a1 a2 : A) : rvec 3 :=  mk_rvec3 Azero a0 a1 a2.
  Definition mk_rvec4 (a0 a1 a2 a3 : A) : rvec 4 := mk_rvec4 Azero a0 a1 a2 a3.

  
  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Definition t2rv_2 (t : @T2 A) : rvec 2 := t2rv_2 Azero t.
  Definition t2rv_3 (t : @T3 A) : rvec 3 := t2rv_3 Azero t.
  Definition t2rv_4 (t : @T4 A) : rvec 4 := t2rv_4 Azero t.

  Definition rv2t_2 (v : rvec 2) : @T2 A := rv2t_2 v.
  Definition rv2t_3 (v : rvec 3) : @T3 A := rv2t_3 v.
  Definition rv2t_4 (v : rvec 4) : @T4 A := rv2t_4 v.

  (* Lemma rv2t_t2rv_id_2 : forall (t : A * A), rv2t_2 (t2rv_2 t) == t. *)
  (* Proof. intros. destruct t. simpl. unfold v2t_2. f_equal. Qed. *)

  Lemma t2rv_rv2t_id_2 : forall (v : rvec 2), t2rv_2 (rv2t_2 v) == v.
  Proof. intros. apply t2rv_rv2t_id_2. Qed.

  
  (* ==================================== *)
  (** ** vector mapping *)
  Definition rvmap {n} (v : rvec n) (f : A -> A) : rvec n := rvmap v f.
  Definition rvmap2 {n} (v1 v2 : rvec n) (f : A -> A -> A) : rvec n := rvmap2 v1 v2 f.

  
  (* ==================================== *)
  (** ** vector folding *)
  (* Definition rvfold {B : Type} {n} (v : @rvec A n) (f : A -> B) (b0 : B) : B. *)

  
  (* ==================================== *)
  (** ** Zero vector *)

  (** Make a zero vector *)
  Definition rvec0 {n} : rvec n := @rvec0 _ Azero _.

  (** A vector is a zero vector. *)
  Definition rvzero {n} (v : rvec n) : Prop := @rvzero _ Aeq Azero _ v.

  (** A vector is a non-zero vector. *)
  Definition rvnonzero {n} (v : rvec n) : Prop := ~(rvzero v).

  (** vec0 is equal to mat0 with column 1 *)
  Lemma rvec0_eq_mat0 : forall n, (@rvec0 n) == mat0 Azero.
  Proof. intros. apply rvec0_eq_mat0. Qed.


  (** ######################################################################### *)
  (** * (Column Vector part) *)
  Open Scope cvec_scope.

  (* ==================================== *)
  (** ** Vector type *)

  (** A vector cvec(n) is a colum vector, equal to a matrix mat(n,1) *)
  Definition cvec (n : nat) := @cvec A n.

  (** Convert between function and vector *)
  Definition f2cv {n} (f : nat -> A) : cvec n := f2cv f.
  Definition cv2f {n} (v : cvec n) : nat -> A := cv2f v.

  (** Convert vec to function *)
  Ltac cvec2fun :=
    repeat match goal with
      | v : cvec ?n |- _ => destruct v as [v]; simpl in *
      end.
  

  (* ==================================== *)
  (** ** Get element of vector *)

  (** Get element of vector from raw data, unsafe *)
  Notation "v $ i " := (v $ i $ 0) : cvec_scope.
  Notation "v .0" := (v $ 0) : cvec_scope.
  Notation "v .1" := (v $ 1) : cvec_scope.
  Notation "v .2" := (v $ 2) : cvec_scope.
  Notation "v .3" := (v $ 3) : cvec_scope.
  (* Notation "v .x" := (v $ 0) : cvec_scope. *)
  (* Notation "v .y" := (v $ 1) : cvec_scope. *)
  (* Notation "v .z" := (v $ 2) : cvec_scope. *)
  (* Notation "v .w" := (v $ 3) : cvec_scope. *)
  
  (** Get element of vector, the index will be restricted to in the bound, safe *)
  Definition cvnth {n} (v : cvec n) i : A := v ! i ! 0.
  Notation "v ! i " := (cvnth v i) : cvec_scope.
  
  (** If the index is in bound, its behavior is equal to get element from raw data *)
  Lemma cvnth_spec : forall {n : nat} (v : cvec n) i, i < n -> (v ! i == v $ i)%A.
  Proof. intros. apply cvnth_spec; auto. Qed.

  (** veq, iff vnth *)
  Lemma veq_iff_cvnth : forall {n : nat} (v1 v2 : cvec n),
      v1 == v2 <-> (forall i, i < n -> (v1 ! i == v2 ! i)%A).
  Proof. intros. apply veq_iff_cvnth. Qed.

  (** veq, iff {top n-1 elements equal, and the n-th elements equal} *)

  
  (* ==================================== *)
  (** ** Get column-vector of a matrix *)
  Definition mcol {r c : nat} (m : mat r c) (ci : nat) : cvec r := mcol m ci.

  
  (* ==================================== *)
  (** ** List like operations for vector *)
  
  (** a :: v  *)
  Definition cvcons {n} (a : A) (v : cvec n) : cvec (S n) := cvcons a v.

  Lemma cvcons_spec : forall n a (v : cvec n) i,
      let v' := cvcons a v in
      (v' $ 0 == a)%A /\ (i < n -> (v $ i == v' $ (S i))%A).
  Proof. intros. apply cvcons_spec. Qed.

  (** Get a vector from a given vector by remove i-th element *)
  Definition cvremove {n : nat} (v : cvec (S n)) (i : nat) : cvec n := cvremove v i.

  (** (v.0) :: (v.remove(0)) = v *)
  Lemma cvcons_remove : forall {n} (v : cvec (S n)), cvcons (v$0) (cvremove v 0) == v.
  Proof. intros. apply cvcons_remove. Qed.

  
  (* ==================================== *)
  (** ** Convert between list and vector *)
  Definition cv2l {n} (v : cvec n) : list A := cv2l v.
  Definition l2cv {n} (l : list A) : cvec n := l2cv Azero n l.

  (** list of vector to dlist *)
  Definition cvl2dl {n} (l : list (cvec n)) : dlist A := cvl2dl l.

  Lemma cv2l_length : forall {n} (v : cvec n), length (cv2l v) = n.
  Proof. intros. apply cv2l_length. Qed.

  Lemma cv2l_l2cv_id : forall {n} (l : list A),
      length l = n -> (cv2l (@l2cv n l) == l)%list.
  Proof. intros. apply cv2l_l2cv_id; auto. Qed.

  Lemma l2cv_cv2l_id : forall {n} (v : cvec n), @l2cv n (cv2l v) == v.
  Proof. intros. apply l2cv_cv2l_id. Qed.

  
  (* ==================================== *)
  (** ** Make concrete vector *)
  Definition mk_cvec2 (a0 a1 : A) : cvec 2 := mk_cvec2 Azero a0 a1.
  Definition mk_cvec3 (a0 a1 a2 : A) : cvec 3 := mk_cvec3 Azero a0 a1 a2.
  Definition mk_cvec4 (a0 a1 a2 a3 : A) : cvec 4 := mk_cvec4 Azero a0 a1 a2 a3.

  
  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Definition t2cv_2 (t : @T2 A) : cvec 2 := t2cv_2 Azero t.
  Definition t2cv_3 (t : @T3 A) : cvec 3 := t2cv_3 Azero t.
  Definition t2cv_4 (t : @T4 A) : cvec 4 := t2cv_4 Azero t.

  Definition cv2t_2 (v : cvec 2) : @T2 A := cv2t_2 v.
  Definition cv2t_3 (v : cvec 3) : @T3 A := cv2t_3 v.
  Definition cv2t_4 (v : cvec 4) : @T4 A := cv2t_4 v.

  (* Lemma cv2t_t2cv_id_2 : forall (t : A * A), cv2t_2 (t2cv_2 t) == t. *)
  (* Proof. intros. destruct t. simpl. unfold v2t_2. f_equal. Qed. *)

  Lemma t2cv_cv2t_id_2 : forall (v : cvec 2), t2cv_2 (cv2t_2 v) == v.
  Proof. intros. apply t2cv_cv2t_id_2. Qed.

  
  (* ==================================== *)
  (** ** vector mapping *)
  Definition cvmap {n} (v : cvec n) (f : A -> A) : cvec n := cvmap v f.
  Definition cvmap2 {n} (v1 v2 : cvec n) (f : A -> A -> A) : cvec n := cvmap2 v1 v2 f.


  (* ==================================== *)
  (** ** vector folding *)
  Definition cvfold {n} {B:Type} (v : cvec n) (f : B -> A -> B) (b0 : B) : B :=
    cvfold v f b0.


  (* ==================================== *)
  (** ** Zero vector *)

  (** Make a zero vector *)
  Definition cvec0 {n} : cvec n := @cvec0 _ Azero n.

  (** A vector is a zero vector. *)
  Definition cvzero {n} (v : cvec n) : Prop := @cvzero _ Aeq Azero _ v.

  (** A vector is a non-zero vector. *)
  Definition cvnonzero {n} (v : cvec n) : Prop := ~(cvzero v).

  (** vec0 is equal to mat0 with column 1 *)
  Lemma cvec0_eq_mat0 : forall n, (@cvec0 n) == mat0 Azero.
  Proof. intros. apply cvec0_eq_mat0. Qed.

  (** Any zero vector is vec0 *)
  Lemma cvzero_imply_vec0 : forall {n} (v : cvec n), cvzero v -> v == cvec0.
  Proof. intros. apply cvzero_imply_vec0; auto. Qed.

  
  (** ######################################################################### *)
  (** * (Convertion between cvec and rvec *)

  Definition cv2rv {n} (v : cvec n) : rvec n := @cv2rv _ Azero _ v.

  Lemma cv2rv_spec : forall {n} (v : cvec n), cv2rv v == v\T.
  Proof. intros. apply cv2rv_spec. Qed.

  Definition rv2cv {n} (v : rvec n) : cvec n := @rv2cv _ Azero _ v.

  Lemma rv2cv_spec : forall {n} (v : rvec n), rv2cv v == v\T.
  Proof. intros. apply rv2cv_spec. Qed.
  
End BasicVectorTheory.


(* ######################################################################### *)
(** * Ring vector theory *)
Module RingVectorTheory (E : RingElementType).

  (* Include (RingMatrixTheory E). *)
  
  Include (BasicVectorTheory E).

  Infix "*" := (mmul (Aadd:=Aadd)(Azero:=Azero)(Amul:=Amul)) : mat_scope.
  Infix "c*" := (mcmul (Amul:=Amul)) : mat_scope.
  
  
  (** ######################################################################### *)
  (** * (Row Vector part) *)

  Open Scope rvec_scope.
  
  (* ==================================== *)
  (** ** Vector addition *)

  Definition rvadd {n} (v1 v2 : rvec n) : rvec n := @rvadd _ Aadd _ v1 v2.
  Infix "+" := rvadd : rvec_scope.

  (** v1 + v2 = v2 + v1 *)
  Lemma rvadd_comm : forall {n} (v1 v2 : rvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply rvadd_comm. Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma rvadd_assoc : forall {n} (v1 v2 v3 : rvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply rvadd_assoc. Qed.

  (** vec0 + v = v *)
  Lemma rvadd_0_l : forall {n} (v : rvec n), rvec0 + v == v.
  Proof. intros. apply rvadd_0_l. Qed.

  (** v + vec0 = v *)
  Lemma rvadd_0_r : forall {n} (v : rvec n), v + rvec0 == v.
  Proof. intros. apply rvadd_0_r. Qed.


  (* ==================================== *)
  (** ** Vector opposition *)

  Definition rvopp {n} (v : rvec n) : rvec n := @rvopp _ Aopp _ v.
  Notation "- v" := (rvopp v) : rvec_scope.

  (** (- v) + v = vec0 *)
  Lemma rvadd_vopp_l : forall {n} (v : rvec n), (- v) + v == rvec0.
  Proof. intros. apply rvadd_vopp_l. Qed.

  (** v + (- v) = vec0 *)
  Lemma rvadd_vopp_r : forall {n} (v : rvec n), v + (- v) == rvec0.
  Proof. intros. apply rvadd_vopp_r. Qed.


  (* ==================================== *)
  (** ** Vector subtraction *)

  Definition rvsub {n} (v1 v2 : rvec n) : rvec n := @rvsub _ Aadd Aopp _ v1 v2.
  Infix "-" := rvsub : rvec_scope.


  (* ==================================== *)
  (** ** Vector scalar multiplication *)

  Definition rvcmul {n} a (v : rvec n) : rvec n := @rvcmul _ Amul _ a v.
  Infix "c*" := rvcmul : rvec_scope.

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma rvcmul_assoc : forall {n} a b (v : rvec n), a c* (b c* v) == (a * b)%A c* v.
  Proof. intros. apply rvcmul_assoc. Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma rvcmul_perm : forall {n} a b (v : rvec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply rvcmul_perm. Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma rvcmul_add_distr : forall {n} a b (v : rvec n),
      (a + b)%A c* v == (a c* v) + (b c* v).
  Proof. intros. apply rvcmul_add_distr. Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma rvcmul_vadd_distr : forall {n} a (v1 v2 : rvec n), 
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply rvcmul_vadd_distr. Qed.

  (** 1 c* v = v *)
  Lemma rvcmul_1_l : forall {n} (v : rvec n), Aone c* v == v.
  Proof. intros. apply rvcmul_1_l. Qed.

  (** 0 c* v = rvec0 *)
  Lemma rvcmul_0_l : forall {n} (v : rvec n), Azero c* v == rvec0.
  Proof. intros. apply rvcmul_0_l. Qed.

  Definition rvmulc {n} (v : rvec n) a : rvec n := mmulc (Amul:=Amul) v a.
  Infix "*c" := rvmulc : rvec_scope.

  (** v *c a = a c* v *)
  Lemma rvmulc_eq_vcmul : forall {n} a (v : rvec n), (v *c a) == (a c* v).
  Proof. intros. apply rvmulc_eq_vcmul. Qed.

  (** (v *c a) *c b = v *c (a * b) *)
  Lemma rvmulc_assoc : forall {n} (v : rvec n) (a b : A), (v *c a) *c b == v *c (a * b)%A.
  Proof. intros. apply rvmulc_assoc. Qed.

  (** (v *c a) *c b = (v *c b) c* a *)
  Lemma rvmulc_perm : forall {n} (v : rvec n) (a b : A), (v *c a) *c b == (v *c b) *c a.
  Proof. intros. apply rvmulc_perm. Qed.


  (* ==================================== *)
  (** ** Vector dot product *)

  (** dot production of two vectors. *)
  Definition rvdot {n : nat} (v1 v2 : rvec n) : A := @rvdot _ Aadd Azero Amul _ v1 v2.
  Notation "< a , b >" := (rvdot a b) : rvec_scope.

  (** <v1,v2> = <v2,v1> *)
  Lemma rvdot_comm : forall {n} (v1 v2 : rvec n), (<v1,v2> == <v2,v1>)%A.
  Proof. intros. apply rvdot_comm. Qed.

  (** <v1 + v2,v3> = <v1,v3> + <v2,v3> *)
  Lemma rvdot_vadd_distr_l : forall {n} (v1 v2 v3 : rvec n),
      (<(v1 + v2)%RV,v3> == <v1,v3> + <v2,v3>)%A.
  Proof. intros. apply rvdot_add_distr_l. Qed.

  (** <v1, v2 + v3> = <v1,v2> + <v1,v3> *)
  Lemma rvdot_vadd_distr_r : forall {n} (v1 v2 v3 : rvec n),
      (<v1,(v2 + v3)%RV> == <v1,v2> + <v1,v3>)%A.
  Proof. intros. apply rvdot_add_distr_r. Qed.

  (** <a c* v1, v2> = a * <v1,v2> *)
  Lemma rvdot_vcmul_l : forall {n} (v1 v2 : rvec n) (a : A),
      (<a c* v1,v2> == a * <v1,v2>)%A.
  Proof. intros. apply rvdot_cmul_l. Qed.

  (** <v1, a c* v2> == a * <v1,v2> *)
  Lemma rvdot_vcmul_r : forall {n} (v1 v2 : rvec n) (a : A),
      (<v1, a c* v2> == a * <v1,v2>)%A.
  Proof. intros. apply rvdot_cmul_r. Qed.

  (** <0,v> = 0 *)
  Lemma rvdot_0_l : forall {n} (v : rvec n), (<rvec0,v> == Azero)%A.
  Proof. intros. apply rvdot_0_l. Qed.

  (** <v,0> = 0 *)
  Lemma rvdot_0_r : forall {n} (v : rvec n), (<v,rvec0> == Azero)%A.
  Proof. intros. apply rvdot_0_r. Qed.

  
  (** ######################################################################### *)
  (** * (Column Vector part) *)
  
  Open Scope cvec_scope.

  (* ==================================== *)
  (** ** Vector addition *)

  Definition cvadd {n} (v1 v2 : cvec n) : cvec n := @cvadd _ Aadd _ v1 v2.
  Infix "+" := cvadd : cvec_scope.
  
  (** v1 + v2 = v2 + v1 *)
  Lemma cvadd_comm : forall {n} (v1 v2 : cvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply cvadd_comm. Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma cvadd_assoc : forall {n} (v1 v2 v3 : cvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply cvadd_assoc. Qed.

  (** (v1 + v2) + v3 = (v1 + v3) + v2 *)
  Lemma cvadd_perm : forall {n} (v1 v2 v3 : cvec n), (v1 + v2) + v3 == (v1 + v3) + v2.
  Proof. intros. apply cvadd_perm. Qed.

  (** vec0 + v = v *)
  Lemma cvadd_0_l : forall {n} (v : cvec n), cvec0 + v == v.
  Proof. intros. apply cvadd_0_l. Qed.

  (** v + vec0 = v *)
  Lemma cvadd_0_r : forall {n} (v : cvec n), v + cvec0 == v.
  Proof. intros. apply cvadd_0_r. Qed.


  (* ==================================== *)
  (** ** Vector opposition *)

  Definition cvopp {n} (v : cvec n) : cvec n := @cvopp _ Aopp _ v.
  Notation "- v" := (cvopp v) : cvec_scope.

  (** (- v) + v = vec0 *)
  Lemma cvadd_vopp_l : forall {n} (v : cvec n), (- v) + v == cvec0.
  Proof. intros. apply cvadd_vopp_l. Qed.

  (** v + (- v) = vec0 *)
  Lemma cvadd_vopp_r : forall {n} (v : cvec n), v + (- v) == cvec0.
  Proof. intros. apply cvadd_vopp_r. Qed.

  (** - (v1 + v2) = (- v1) + (- v2) *)
  Lemma cvopp_vadd : forall {n} (v1 v2 : cvec n), - (v1 + v2) == (- v1) + (- v2).
  Proof. intros. apply cvopp_vadd. Qed.

  (** - (- v) = v *)
  Lemma cvopp_vopp : forall {n} (v : cvec n), - (- v) == v.
  Proof. intros. apply cvopp_vopp. Qed.

  
  (* ==================================== *)
  (** ** Vector subtraction *)

  Definition cvsub {n} (v1 v2 : cvec n) : cvec n := v1 + (- v2).
  Infix "-" := cvsub : cvec_scope.

  (** Rewrite vsub: v1 - v2 = v1 + (-v2) *)
  Lemma cvsub_rw : forall {n} (v1 v2 : cvec n), v1 - v2 == v1 + (-v2).
  Proof. intros. apply cvsub_rw. Qed.

  (** v1 - v2 = -(v2 - v1) *)
  Lemma cvsub_comm : forall {n} (v1 v2 : cvec n), v1 - v2 == - (v2 - v1).
  Proof. intros. apply cvsub_comm. Qed.

  (** (v1 - v2) - v3 = v1 - (v2 + v3) *)
  Lemma cvsub_assoc : forall {n} (v1 v2 v3 : cvec n), (v1 - v2) - v3 == v1 - (v2 + v3).
  Proof. intros. apply cvsub_assoc. Qed.

  (** (v1 + v2) - v3 = v1 + (v2 - v3) *)
  Lemma cvsub_assoc1 : forall {n} (v1 v2 v3 : cvec n), (v1 + v2) - v3 == v1 + (v2 - v3).
  Proof. intros. apply cvsub_assoc1. Qed.

  (** (v1 - v2) - v3 = v1 - (v3 - v2) *)
  Lemma cvsub_assoc2 : forall {n} (v1 v2 v3 : cvec n), (v1 - v2) - v3 == (v1 - v3) - v2.
  Proof. intros. apply cvsub_assoc2. Qed.

  (** vec0 - v = - v *)
  Lemma cvsub_0_l : forall {n} (v : cvec n), cvec0 - v == - v.
  Proof. intros. apply cvsub_0_l. Qed.

  (** v - vec0 = v *)
  Lemma cvsub_0_r : forall {n} (v : cvec n), v - cvec0 == v.
  Proof. intros. apply cvsub_0_r. Qed.

  (** v - v = vec0 *)
  Lemma cvsub_self : forall {n} (v : cvec n), v - v == cvec0.
  Proof. intros. apply cvsub_self. Qed.


  (* ==================================== *)
  (** ** Vector scalar multiplication *)

  (** Left scalar multiplication *)
  Definition cvcmul {n} a (v : cvec n) : cvec n := @cvcmul _ Amul _ a v.
  Infix "c*" := cvcmul : cvec_scope.

  (** (a * v)[i] = a * [i] *)
  Lemma cvcmul_nth : forall {n} (v : cvec n) (a : A) i,
      i < n -> (a c* v)$i = (a * (v$i))%A.
  Proof. intros. apply cvcmul_nth; auto. Qed.

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma cvcmul_assoc : forall {n} a b (v : cvec n), a c* (b c* v) == (a * b)%A c* v.
  Proof. intros. apply cvcmul_assoc. Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma cvcmul_perm : forall {n} a b (v : cvec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply cvcmul_perm. Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma cvcmul_add_distr : forall {n} a b (v : cvec n),
      (a + b)%A c* v == (a c* v) + (b c* v).
  Proof. intros. apply cvcmul_add_distr. Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma cvcmul_vadd_distr : forall {n} a (v1 v2 : cvec n), 
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply cvcmul_vadd_distr. Qed.

  (** 1 c* v = v *)
  Lemma cvcmul_1_l : forall {n} (v : cvec n), Aone c* v == v.
  Proof. intros. apply cvcmul_1_l. Qed.

  (** 0 c* v = cvec0 *)
  Lemma cvcmul_0_l : forall {n} (v : cvec n), Azero c* v == cvec0.
  Proof. intros. apply cvcmul_0_l. Qed.

  (** a c* 0 = cvec0 *)
  Lemma cvcmul_0_r : forall {n} a, a c* cvec0 == (@Vector.cvec0 _ Azero n).
  Proof. intros. apply cvcmul_0_r. Qed.

  (** - (a c* v) = (-a) c* v *)
  Lemma cvopp_vcmul : forall {n} a (v : cvec n), - (a c* v) == (-a)%A c* v.
  Proof. intros. apply cvopp_cmul. Qed.

  (** a c* (v1 - v2) = (a c* v1) - (a c* v2) *)
  Lemma cvcmul_vsub : forall {n} a (v1 v2 : cvec n),
      a c* (v1 - v2) == (a c* v1) - (a c* v2).
  Proof. intros. apply cvcmul_sub. Qed.

  (** a c* (m * v) = (a c* m) * v *)
  Lemma cvcmul_mmul_assoc_l : forall {r c} (a : A) (m : mat r c) (v : cvec c), 
      a c* (m * v) == (a c* m)%M * v.
  Proof. intros. apply cvcmul_mmul_assoc_l. Qed.

  (** a c* (m * v) = m c* (a c* v) *)
  Lemma cvcmul_mmul_assoc_r : forall {r c} (a : A) (m : mat r c) (v : cvec c), 
      a c* (m * v) == m * (a c* v).
  Proof. intros. apply cvcmul_mmul_assoc_r. Qed.

  (** Right scalar multiplication *)
  Definition cvmulc {n} (v : cvec n) a : cvec n := @cvmulc _ Amul _ v a.
  Infix "*c" := cvmulc : cvec_scope.

  (** v *c a = a c* v *)
  Lemma cvmulc_eq_vcmul : forall {n} a (v : cvec n), (v *c a) == (a c* v).
  Proof. intros. apply cvmulc_eq_vcmul. Qed.

  (** (v *c a) *c b = v *c (a * b) *)
  Lemma cvmulc_assoc : forall {n} (v : cvec n) (a b : A), (v *c a) *c b == v *c (a * b)%A.
  Proof. intros. apply cvmulc_assoc. Qed.

  (** (v *c a) *c b = (v *c b) c* a *)
  Lemma cvmulc_perm : forall {n} (v : cvec n) (a b : A), (v *c a) *c b == (v *c b) *c a.
  Proof. intros. apply cvmulc_perm. Qed.

  
  (* ==================================== *)
  (** ** Vector dot product *)

  (** dot production of two vectors. *)
  Definition cvdot {n : nat} (v1 v2 : cvec n) : A := @cvdot _ Aadd Azero Amul _ v1 v2.
  Notation "< a , b >" := (cvdot a b) : cvec_scope.

  (** <row(m1,i)\T, col(m2,j)> = [m1 * m2].ij *)
  Lemma cvdot_row_col_eq_mnth : forall {r c s} (m1 : mat r c) (m2 : mat c s) i j,
      i < r -> j < s -> (<(mrow m1 i)\T, mcol m2 j> == (m1 * m2)%M $ i $ j)%A.
  Proof. intros. apply cvdot_row_col_eq_mnth; auto. Qed.

  (** <v1,v2> = v1\T * v2 *)
  Lemma cvdot_eq_mul_trans : forall {n} (v1 v2 : cvec n),
      (<v1,v2> == scalar_of_mat (v1\T * v2)%M)%A.
  Proof. intros. apply cvdot_eq_mul_trans. Qed.

  (** <v1,v2> = <v2,v1> *)
  Lemma cvdot_comm : forall {n} (v1 v2 : cvec n), (<v1,v2> == <v2,v1>)%A.
  Proof. intros. apply cvdot_comm. Qed.

  (** <v1 + v2, v3> = <v1,v3> + <v2,v3> *)
  Lemma cvdot_vadd_distr_l : forall {n} (v1 v2 v3 : cvec n),
      (<(v1 + v2)%CV,v3> == <v1,v3> + <v2,v3>)%A.
  Proof. intros. apply cvdot_add_distr_l. Qed.

  (** <v1, v2 + v3> = <v1,v2> + <v1,v3> *)
  Lemma cvdot_vadd_distr_r : forall {n} (v1 v2 v3 : cvec n),
      (<v1, (v2 + v3)%CV> == <v1,v2> + <v1,v3>)%A.
  Proof. intros. apply cvdot_add_distr_r. Qed.

  (** <a c* v1, v2> = a * <v1,v2> *)
  Lemma cvdot_vcmul_l : forall {n} (v1 v2 : cvec n) (a : A),
      (<a c* v1, v2> == a * <v1,v2>)%A.
  Proof. intros. apply cvdot_vcmul_l. Qed.

  (** <v1, a c* v2> == a * <v1,v2> *)
  Lemma cvdot_vcmul_r : forall {n} (v1 v2 : cvec n) (a : A),
      (<v1, a c* v2> == a * <v1,v2>)%A.
  Proof. intros. apply cvdot_vcmul_r. Qed.

  (** <0,v> = 0 *)
  Lemma cvdot_0_l : forall {n} (v : cvec n), (<cvec0,v> == Azero)%A.
  Proof. intros. apply cvdot_0_l. Qed.

  (** <v,0> = 0 *)
  Lemma cvdot_0_r : forall {n} (v : cvec n), (<v,cvec0> == Azero)%A.
  Proof. intros. apply cvdot_0_r. Qed.
  
  (** < - v1, v2> = - <v1,v2> *)
  Lemma cvdot_vopp_l : forall {n} (v1 v2 : cvec n), (< (-v1)%CV, v2> == - <v1,v2>)%A.
  Proof. intros. apply cvdot_vopp_l. Qed.
  
  (** < v1, - v2> = - <v1,v2> *)
  Lemma cvdot_vopp_r : forall {n} (v1 v2 : cvec n), (< v1, (-v2)%CV> == - <v1,v2>)%A.
  Proof. intros. apply cvdot_vopp_r. Qed.


  (* ==================================== *)
  (** ** Comparison of matrix left or right multiply to a vector *)
  
  (* (** M * v = v * M\T *) *)
  (* Lemma mmv_eq_vmmt : forall {r c : nat} (M : mat r c) (v : cvec c), *)
  (*     (* Treat the column vector v as a row vector *) *)
  (*     let v' : rvec c := v\T in *)
  (*     (* matrix left multiply a vector *) *)
  (*     let u1 : cvec r := M * v in *)
  (*     (* matrix right multiply a vector (the matrix need to be transposed) *) *)
  (*     let u2 : rvec r := v' * M\T in *)
  (*     (* Treat the row vector u2 as a column vector *) *)
  (*     let u2' : cvec r := u2\T in *)
  (*     (* The result must be same *) *)
  (*     u1 == u2'. *)
  (* Proof. intros. apply mmv_eq_vmmt. Qed. *)

  (* (** v * M = M\T * v *) *)
  (* Lemma mvm_eq_mtmv : forall {r c : nat} (v : rvec r) (M : mat r c), *)
  (*     (* Treat the row vector v as a column vector *) *)
  (*     let v' : cvec r := v\T in *)
  (*     (* matrix right multiply a vector *) *)
  (*     let u1 : rvec c := v * M in *)
  (*     (* matrix left multiply a vector (the matrix need to be transposed) *) *)
  (*     let u2 : cvec c := M\T * v' in *)
  (*     (* Treat the column vector u2 as a row vector *) *)
  (*     let u2' : rvec c := u2\T in *)
  (*     (* The result must be same *) *)
  (*     u1 == u2'. *)
  (* Proof. intros. apply mvm_eq_mtmv. Qed. *)

(** Thus, we proved that, row vector and column vector are different but have 
      a tight connection. *)

End RingVectorTheory.


(* ######################################################################### *)
(** * Field vector theory *)
Module FieldVectorTheory (E : FieldElementType).
  
  (* Include (FieldMatrixTheory E). *)
  
  Include (RingVectorTheory E).
  
  
  (** ######################################################################### *)
  (** * (Row Vector part) *)

  Open Scope rvec_scope.
  
  
  (** ######################################################################### *)
  (** * (Column Vector part) *)

  Open Scope cvec_scope.

  (* ==================================== *)
  (** ** xxx *)

End FieldVectorTheory.
