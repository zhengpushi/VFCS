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
  (2) RingVectoryTheory
      vector theory on element with ring structure.
  (3) FieldVectoryTheory
      vector theory on element with field structure.
 *)

Require Export Vector.
Require Export Matrix.
Require Export ElementType.


(* ######################################################################### *)
(** * Basic Vector Theory *)
Module BasicVectorTheory (E : ElementType).
  Export E.
  
  Open Scope nat_scope.
  Open Scope A_scope.

  (* ======================================================================= *)
  (** ** Vector *)
  Open Scope vec_scope.

  Definition vec (n : nat) := @vec A n.

  (** Convert between function and vector *)
  Definition f2v {n} (f : nat -> A) : vec n := f2v f.
  Definition v2f {n} (V : vec n) : nat -> A := v2f Azero V.

  (** veq, iff vnth *)
  Lemma veq_iff_vnth : forall {n} (V1 V2 : vec n), V1 = V2 <-> (forall i, V1$i = V2$i).
  Proof. intros. apply veq_iff_vnth. Qed.

  (** a :: v  *)
  Definition vconsH {n} (a : A) (V : vec n) : vec (S n) := @vconsH _ Azero _ a V.
  (** v ++ [a]  *)
  Definition vconsT {n} (V : vec n) (a : A) : vec (S n) := @vconsT _ Azero _ V a.

  (** Convert between list and vector *)
  Definition v2l {n} (V : vec n) : list A := v2l V.
  Definition l2v {n} (l : list A) : vec n := l2v Azero _ l.
  
  Lemma v2l_length : forall {n} (V : vec n), length (v2l V) = n.
  Proof. intros. apply v2l_length. Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> (v2l (@l2v n l) = l).
  Proof. intros. apply v2l_l2v_id; auto. Qed.

  Lemma l2v_v2l_id : forall {n} (V : vec n), @l2v n (v2l V) = V.
  Proof. intros. apply l2v_v2l_id. Qed.

  (** Make concrete vector *)
  Definition mkvec1 (a1 : A) : vec 1 := @mkvec1 _ Azero a1.
  Definition mkvec2 (a1 a2 : A) : vec 2 := @mkvec2 _ Azero a1 a2.
  Definition mkvec3 (a1 a2 a3 : A) : vec 3 := @mkvec3 _ Azero a1 a2 a3.
  Definition mkvec4 (a1 a2 a3 a4 : A) : vec 4 := @mkvec4 _ Azero a1 a2 a3 a4.

  (** Vector mapping *)
  Definition vmap {n} (V : vec n) (f : A -> A) : vec n := vmap f V.
  Definition vmap2 {n} (V1 V2 : vec n) (f : A -> A -> A) : vec n := vmap2 f V1 V2.
  
  (** Sum of a vector (also named folding) *)
  Definition vsum {n} (V : vec n) (f : A -> A -> A) (b : A) : A := @vsum _ f b _ V.

  (** Make a zero vector *)
  Definition vzero {n} : vec n := vzero Azero.
  

  (* ======================================================================= *)
  (** ** Row Vector *)
  Open Scope rvec_scope.
  
  (** Row vector is a matrix which has one row *)
  Definition rvec (n : nat) := mat A 1 n.

  (** Convert between function and vector *)
  Definition f2rv {n} (f : nat -> A) : rvec n := f2m (fun i j => f j).
  Definition rv2f {n} (V : rvec n) : nat -> A := fun j => (m2f Azero V) 0 j.

  (** Get element of row vector *)
  Notation "V $ i " := (V fin0 i) : rvec_scope.
  Notation "V .1" := (V $ nat2finS 0) : rvec_scope.
  Notation "V .2" := (V $ nat2finS 1) : rvec_scope.
  Notation "V .3" := (V $ nat2finS 2) : rvec_scope.
  Notation "V .4" := (V $ nat2finS 3) : rvec_scope.
  Notation "V .x" := (V.1) : rvec_scope.
  Notation "V .y" := (V.2) : rvec_scope.
  Notation "V .z" := (V.3) : rvec_scope.
  (* Notation "v .w" := (V.4) : rvec_scope. *)

  (** veq, iff vnth *)
  Lemma veq_iff_rvnth : forall {n : nat} (V1 V2 : rvec n), V1 = V2 <-> (forall j, V1$j = V2$j).
  Proof.
    intros. unfold rvec in *. rewrite meq_iff_mnth. split; intros; auto.
    assert (i = fin0). { destruct i; apply fin_eq_iff; lia. } subst. auto.
  Qed.
  
  (** Convert between list and vector *)
  Definition rv2l {n} (V : rvec n) : list A := hd [] (m2l V).
  Definition l2rv {n} (l : list A) : rvec n := l2m Azero [l].

  Lemma rv2l_length : forall {n} (V : rvec n), length (rv2l V) = n.
  Proof.
    intros. unfold rvec,rv2l in *.
    pose proof (m2l_width_form2 Azero V). rewrite hd_eq_nth_0. auto.
  Qed.

  Lemma rv2l_l2rv_id : forall {n} (l : list A), length l = n -> (rv2l (@l2rv n l) = l).
  Proof.
    intros. unfold rvec,rv2l,l2rv. rewrite m2l_l2m_id; simpl; auto.
    constructor; auto.
  Qed.

  Lemma l2rv_rv2l_id : forall {n} (V : rvec n), @l2rv n (rv2l V) = V.
  Proof.
    intros. unfold l2rv,rv2l,rvec in *. apply meq_iff_mnth; intros.
    unfold l2m.
    assert (i = fin0). { destruct i; apply fin_eq_iff; lia. } subst. simpl.
    rewrite l2v_v2l_id. rewrite vnth_l2v. simpl. f_equal.
  Qed.

  (** Make concrete vector *)
  Definition mkrvec1 (a1 : A) : rvec 1 := @mkmat_1_1 _ Azero a1.
  Definition mkrvec2 (a1 a2 : A) : rvec 2 := @mkmat_1_2 _ Azero a1 a2.
  Definition mkrvec3 (a1 a2 a3 : A) : rvec 3 := @mkmat_1_3 _ Azero a1 a2 a3.
  Definition mkrvec4 (a1 a2 a3 a4 : A) : rvec 4 := @mkmat_1_4 _ Azero a1 a2 a3 a4.
  
  (** Vector mapping *)
  Definition rvmap {n} (V : rvec n) (f:A -> A) : rvec n := mmap f V.
  Definition rvmap2 {n} (V1 V2 : rvec n) (f:A -> A -> A) : rvec n := mmap2 f V1 V2.
  
  (** Sum of a vector (also named folding) *)
  Definition rvsum {n} (V : rvec n) (f:A -> A -> A) (b : A) : A :=
    @Vector.vsum _ f b _ (fun j => V$j).
  
  (** Make a zero vector *)
  Definition rvec0 {n} : rvec n := f2m (fun i j => Azero).

  (** rvec0 is equal to mat0 *)
  Lemma rvec0_eq_mat0 : forall n, (@rvec0 n) = @mat0 _ Azero _ _.
  Proof. intros. auto. Qed.


  (** ** Column Vector *)
  Open Scope cvec_scope.

  (** Colum vector is a matrix which has one column *)
  Definition cvec (n : nat) := mat A n 1.

  (** Convert between function and vector *)
  Definition f2cv {n} (f : nat -> A) : cvec n := f2m (fun i j=> f i).
  Definition cv2f {n} (V : cvec n) : nat -> A := fun i => (m2f Azero V) i 0.

  (** Get element of column vector *)
  Notation "V $ i " := (V i fin0) : cvec_scope.
  Notation "V .1" := (V $ nat2finS 0) : cvec_scope.
  Notation "V .2" := (V $ nat2finS 1) : cvec_scope.
  Notation "V .3" := (V $ nat2finS 2) : cvec_scope.
  Notation "V .4" := (V $ nat2finS 3) : cvec_scope.
  Notation "V .x" := (V.1) : cvec_scope.
  Notation "V .y" := (V.2) : cvec_scope.
  Notation "V .z" := (V.3) : cvec_scope.
  (* Notation "V .w" := (V.4) : cvec_scope. *)

  (** veq, iff vnth *)
  Lemma veq_iff_cvnth : forall {n : nat} (V1 V2 : cvec n), V1 = V2 <-> (forall i, V1$i = V2$i).
  Proof.
    intros. unfold cvec in *. rewrite meq_iff_mnth. split; intros; auto.
    assert (j = fin0). { destruct j; apply fin_eq_iff; lia. } subst. auto.
  Qed.

  (** Convert between list and vector *)
  Definition cv2l {n} (V : cvec n) : list A := map (hd Azero) (m2l V).
  Definition l2cv {n} (l : list A) : cvec n := l2m Azero (map (fun a => [a]) l).

  Lemma cv2l_length : forall {n} (V : cvec n), length (cv2l V) = n.
  Proof.
    intros. unfold cvec,cv2l in *.
  Abort.
  
  Lemma cv2l_l2cv_id : forall {n} (l : list A), length l = n -> cv2l (@l2cv n l) = l.
  Proof.
  Abort.

  Lemma l2cv_cv2l_id : forall {n} (V : cvec n), @l2cv n (cv2l V) = V.
  Proof.
  Abort.

  (** Make concrete vector *)
  Definition mkcvec1 (a1 : A) : cvec 1 := @mkmat_1_1 _ Azero a1.
  Definition mkcvec2 (a1 a2 : A) : cvec 2 := @mkmat_2_1 _ Azero a1 a2.
  Definition mkcvec3 (a1 a2 a3 : A) : cvec 3 := @mkmat_3_1 _ Azero a1 a2 a3.
  Definition mkcvec4 (a1 a2 a3 a4 : A) : cvec 4 := @mkmat_4_1 _ Azero a1 a2 a3 a4.

  (** Vector mapping *)
  Definition cvmap {n} (V : cvec n) (f:A -> A) : cvec n := mmap f V.
  Definition cvmap2 {n} (V1 V2 : cvec n) (f:A -> A -> A) : cvec n := mmap2 f V1 V2.

  (** Sum of a vector (also named folding) *)
  Definition cvsum {n} (V : cvec n) (f:A -> A -> A) (b : A) : A :=
    @Vector.vsum _ f b _ (fun i => V$i).

  (** Make a zero vector *)
  Definition cvec0 {n} : cvec n := f2m (fun i j => Azero).
  
  (** cvec0 is equal to mat0 *)
  Lemma cvec0_eq_mat0 : forall n, (@cvec0 n) = @mat0 _ Azero _ _.
  Proof. intros. auto. Qed.

  
  (* ======================================================================= *)
  (** ** Convertion between vec/rvec/cvec *)

  Definition v2rv {n} (V : vec n) : rvec n := fun i j => V j.
  Definition v2cv {n} (V : vec n) : cvec n := fun i j => V i.
  
  Definition rv2v {n} (V : rvec n) : vec n := fun j => V fin0 j.
  Definition rv2cv {n} (V : rvec n) : cvec n := fun i j => V fin0 i.
  
  Definition cv2v {n} (V : cvec n) : vec n := fun i => V i fin0.
  Definition cv2rv {n} (V : cvec n) : rvec n := fun i j => V j fin0.

  Lemma rv2cv_spec : forall {n} (V : rvec n), rv2cv V = V\T.
  Proof.
    intros. cbv. apply meq_iff_mnth; intros. f_equal.
    destruct j. apply fin_eq_iff. lia.
  Qed.
    
  Lemma cv2rv_spec : forall {n} (V : cvec n), cv2rv V = V\T.
  Proof.
    intros. cbv. apply meq_iff_mnth; intros. f_equal.
    destruct i. apply fin_eq_iff. lia.
  Qed.
  
End BasicVectorTheory.

?

(* ######################################################################### *)
(** * Ring vector theory *)
Module RingVectorTheory (E : RingElementType).

  (* Include (RingMatrixTheory E). *)
  
  Include (BasicVectorTheory E).

  Infix "*" := (mmul (Tadd:=Tadd)(Azero:=Azero)(Tmul:=Tmul)) : mat_scope.
  Infix "c*" := (mcmul (Tmul:=Tmul)) : mat_scope.
  
  
  (** ######################################################################### *)
  (** * (Row Vector part) *)

  Open Scope rvec_scope.
  
  (* ==================================== *)
  (** ** Vector addition *)

  Definition rvadd {n} (v1 v2 : rvec n) : rvec n := @rvadd _ Tadd _ v1 v2.
  Infix "+" := rvadd : rvec_scope.

  (** v1 + v2 = v2 + v1 *)
  Lemma rvadd_comm : forall {n} (v1 v2 : rvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply rvadd_comm. Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma rvadd_assoc : forall {n} (v1 v2 v3 : rvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply rvadd_assoc. Qed.

  (** vec0 + v = v *)
  Lemma rvadd_0_l : forall {n} (V : rvec n), rvec0 + v == V.
  Proof. intros. apply rvadd_0_l. Qed.

  (** v + vec0 = v *)
  Lemma rvadd_0_r : forall {n} (V : rvec n), v + rvec0 == V.
  Proof. intros. apply rvadd_0_r. Qed.


  (* ==================================== *)
  (** ** Vector opposition *)

  Definition rvopp {n} (V : rvec n) : rvec n := @rvopp _ Topp _ V.
  Notation "- v" := (rvopp V) : rvec_scope.

  (** (- V) + v = vec0 *)
  Lemma rvadd_vopp_l : forall {n} (V : rvec n), (- V) + v == rvec0.
  Proof. intros. apply rvadd_vopp_l. Qed.

  (** v + (- V) = vec0 *)
  Lemma rvadd_vopp_r : forall {n} (V : rvec n), v + (- V) == rvec0.
  Proof. intros. apply rvadd_vopp_r. Qed.


  (* ==================================== *)
  (** ** Vector subtraction *)

  Definition rvsub {n} (v1 v2 : rvec n) : rvec n := @rvsub _ Tadd Topp _ v1 v2.
  Infix "-" := rvsub : rvec_scope.


  (* ==================================== *)
  (** ** Vector scalar multiplication *)

  Definition rvcmul {n} a (V : rvec n) : rvec n := @rvcmul _ Tmul _ a V.
  Infix "c*" := rvcmul : rvec_scope.

  (** a c* (b c* V) = (a * b) c* v *)
  Lemma rvcmul_assoc : forall {n} a b (V : rvec n), a c* (b c* V) == (a * b)%T c* V.
  Proof. intros. apply rvcmul_assoc. Qed.

  (** a c* (b c* V) = b c* (a c* V) *)
  Lemma rvcmul_perm : forall {n} a b (V : rvec n), a c* (b c* V) == b c* (a c* V).
  Proof. intros. apply rvcmul_perm. Qed.

  (** (a + b) c* v = (a c* V) + (b c* V) *)
  Lemma rvcmul_add_distr : forall {n} a b (V : rvec n),
      (a + b)%T c* v == (a c* V) + (b c* V).
  Proof. intros. apply rvcmul_add_distr. Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma rvcmul_vadd_distr : forall {n} a (v1 v2 : rvec n), 
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply rvcmul_vadd_distr. Qed.

  (** 1 c* v = v *)
  Lemma rvcmul_1_l : forall {n} (V : rvec n), T1 c* v == V.
  Proof. intros. apply rvcmul_1_l. Qed.

  (** 0 c* v = rvec0 *)
  Lemma rvcmul_0_l : forall {n} (V : rvec n), Azero c* v == rvec0.
  Proof. intros. apply rvcmul_0_l. Qed.

  Definition rvmulc {n} (V : rvec n) a : rvec n := mmulc (Tmul:=Tmul) v a.
  Infix "*c" := rvmulc : rvec_scope.

  (** v *c a = a c* v *)
  Lemma rvmulc_eq_vcmul : forall {n} a (V : rvec n), (v *c a) == (a c* V).
  Proof. intros. apply rvmulc_eq_vcmul. Qed.

  (** (v *c a) *c b = v *c (a * b) *)
  Lemma rvmulc_assoc : forall {n} (V : rvec n) (a b : A), (v *c a) *c b == v *c (a * b)%T.
  Proof. intros. apply rvmulc_assoc. Qed.

  (** (v *c a) *c b = (v *c b) c* a *)
  Lemma rvmulc_perm : forall {n} (V : rvec n) (a b : A), (v *c a) *c b == (v *c b) *c a.
  Proof. intros. apply rvmulc_perm. Qed.


  (* ==================================== *)
  (** ** Vector dot product *)

  (** dot production of two vectors. *)
  Definition rvdot {n : nat} (v1 v2 : rvec n) : A := @rvdot _ Tadd Azero Tmul _ v1 v2.
  Notation "< a , b >" := (rvdot a b) : rvec_scope.

  (** <v1,v2> = <v2,v1> *)
  Lemma rvdot_comm : forall {n} (v1 v2 : rvec n), (<v1,v2> == <v2,v1>)%T.
  Proof. intros. apply rvdot_comm. Qed.

  (** <v1 + v2,v3> = <v1,v3> + <v2,v3> *)
  Lemma rvdot_vadd_distr_l : forall {n} (v1 v2 v3 : rvec n),
      (<(v1 + v2)%RV,v3> == <v1,v3> + <v2,v3>)%T.
  Proof. intros. apply rvdot_add_distr_l. Qed.

  (** <v1, v2 + v3> = <v1,v2> + <v1,v3> *)
  Lemma rvdot_vadd_distr_r : forall {n} (v1 v2 v3 : rvec n),
      (<v1,(v2 + v3)%RV> == <v1,v2> + <v1,v3>)%T.
  Proof. intros. apply rvdot_add_distr_r. Qed.

  (** <a c* v1, v2> = a * <v1,v2> *)
  Lemma rvdot_vcmul_l : forall {n} (v1 v2 : rvec n) (a : A),
      (<a c* v1,v2> == a * <v1,v2>)%T.
  Proof. intros. apply rvdot_cmul_l. Qed.

  (** <v1, a c* v2> == a * <v1,v2> *)
  Lemma rvdot_vcmul_r : forall {n} (v1 v2 : rvec n) (a : A),
      (<v1, a c* v2> == a * <v1,v2>)%T.
  Proof. intros. apply rvdot_cmul_r. Qed.

  (** <0,v> = 0 *)
  Lemma rvdot_0_l : forall {n} (V : rvec n), (<rvec0,v> == Azero)%T.
  Proof. intros. apply rvdot_0_l. Qed.

  (** <v,0> = 0 *)
  Lemma rvdot_0_r : forall {n} (V : rvec n), (<v,rvec0> == Azero)%T.
  Proof. intros. apply rvdot_0_r. Qed.

  
  (** ######################################################################### *)
  (** * (Column Vector part) *)
  
  Open Scope cvec_scope.

  (* ==================================== *)
  (** ** Vector addition *)

  Definition cvadd {n} (v1 v2 : cvec n) : cvec n := @cvadd _ Tadd _ v1 v2.
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
  Lemma cvadd_0_l : forall {n} (V : cvec n), cvec0 + v == V.
  Proof. intros. apply cvadd_0_l. Qed.

  (** v + vec0 = v *)
  Lemma cvadd_0_r : forall {n} (V : cvec n), v + cvec0 == V.
  Proof. intros. apply cvadd_0_r. Qed.


  (* ==================================== *)
  (** ** Vector opposition *)

  Definition cvopp {n} (V : cvec n) : cvec n := @cvopp _ Topp _ V.
  Notation "- v" := (cvopp V) : cvec_scope.

  (** (- V) + v = vec0 *)
  Lemma cvadd_vopp_l : forall {n} (V : cvec n), (- V) + v == cvec0.
  Proof. intros. apply cvadd_vopp_l. Qed.

  (** v + (- V) = vec0 *)
  Lemma cvadd_vopp_r : forall {n} (V : cvec n), v + (- V) == cvec0.
  Proof. intros. apply cvadd_vopp_r. Qed.

  (** - (v1 + v2) = (- v1) + (- v2) *)
  Lemma cvopp_vadd : forall {n} (v1 v2 : cvec n), - (v1 + v2) == (- v1) + (- v2).
  Proof. intros. apply cvopp_vadd. Qed.

  (** - (- V) = v *)
  Lemma cvopp_vopp : forall {n} (V : cvec n), - (- V) == V.
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
  Lemma cvsub_0_l : forall {n} (V : cvec n), cvec0 - v == - V.
  Proof. intros. apply cvsub_0_l. Qed.

  (** v - vec0 = v *)
  Lemma cvsub_0_r : forall {n} (V : cvec n), v - cvec0 == V.
  Proof. intros. apply cvsub_0_r. Qed.

  (** v - v = vec0 *)
  Lemma cvsub_self : forall {n} (V : cvec n), v - v == cvec0.
  Proof. intros. apply cvsub_self. Qed.


  (* ==================================== *)
  (** ** Vector scalar multiplication *)

  (** Left scalar multiplication *)
  Definition cvcmul {n} a (V : cvec n) : cvec n := @cvcmul _ Tmul _ a V.
  Infix "c*" := cvcmul : cvec_scope.

  (** (a * V)[i] = a * [i] *)
  Lemma cvcmul_nth : forall {n} (V : cvec n) (a : A) i,
      i < n -> (a c* V)$i = (a * (v$i))%T.
  Proof. intros. apply cvcmul_nth; auto. Qed.

  (** a c* (b c* V) = (a * b) c* v *)
  Lemma cvcmul_assoc : forall {n} a b (V : cvec n), a c* (b c* V) == (a * b)%T c* V.
  Proof. intros. apply cvcmul_assoc. Qed.

  (** a c* (b c* V) = b c* (a c* V) *)
  Lemma cvcmul_perm : forall {n} a b (V : cvec n), a c* (b c* V) == b c* (a c* V).
  Proof. intros. apply cvcmul_perm. Qed.

  (** (a + b) c* v = (a c* V) + (b c* V) *)
  Lemma cvcmul_add_distr : forall {n} a b (V : cvec n),
      (a + b)%T c* v == (a c* V) + (b c* V).
  Proof. intros. apply cvcmul_add_distr. Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma cvcmul_vadd_distr : forall {n} a (v1 v2 : cvec n), 
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply cvcmul_vadd_distr. Qed.

  (** 1 c* v = v *)
  Lemma cvcmul_1_l : forall {n} (V : cvec n), T1 c* v == V.
  Proof. intros. apply cvcmul_1_l. Qed.

  (** 0 c* v = cvec0 *)
  Lemma cvcmul_0_l : forall {n} (V : cvec n), Azero c* v == cvec0.
  Proof. intros. apply cvcmul_0_l. Qed.

  (** a c* 0 = cvec0 *)
  Lemma cvcmul_0_r : forall {n} a, a c* cvec0 == (@Vector.cvec0 _ Azero n).
  Proof. intros. apply cvcmul_0_r. Qed.

  (** - (a c* V) = (-a) c* v *)
  Lemma cvopp_vcmul : forall {n} a (V : cvec n), - (a c* V) == (-a)%T c* V.
  Proof. intros. apply cvopp_cmul. Qed.

  (** a c* (v1 - v2) = (a c* v1) - (a c* v2) *)
  Lemma cvcmul_vsub : forall {n} a (v1 v2 : cvec n),
      a c* (v1 - v2) == (a c* v1) - (a c* v2).
  Proof. intros. apply cvcmul_sub. Qed.

  (** a c* (m * V) = (a c* m) * v *)
  Lemma cvcmul_mmul_assoc_l : forall {r c} (a : A) (m : mat r c) (V : cvec c), 
      a c* (m * V) == (a c* m)%M * V.
  Proof. intros. apply cvcmul_mmul_assoc_l. Qed.

  (** a c* (m * V) = m c* (a c* V) *)
  Lemma cvcmul_mmul_assoc_r : forall {r c} (a : A) (m : mat r c) (V : cvec c), 
      a c* (m * V) == m * (a c* V).
  Proof. intros. apply cvcmul_mmul_assoc_r. Qed.

  (** Right scalar multiplication *)
  Definition cvmulc {n} (V : cvec n) a : cvec n := @cvmulc _ Tmul _ v a.
  Infix "*c" := cvmulc : cvec_scope.

  (** v *c a = a c* v *)
  Lemma cvmulc_eq_vcmul : forall {n} a (V : cvec n), (v *c a) == (a c* V).
  Proof. intros. apply cvmulc_eq_vcmul. Qed.

  (** (v *c a) *c b = v *c (a * b) *)
  Lemma cvmulc_assoc : forall {n} (V : cvec n) (a b : A), (v *c a) *c b == v *c (a * b)%T.
  Proof. intros. apply cvmulc_assoc. Qed.

  (** (v *c a) *c b = (v *c b) c* a *)
  Lemma cvmulc_perm : forall {n} (V : cvec n) (a b : A), (v *c a) *c b == (v *c b) *c a.
  Proof. intros. apply cvmulc_perm. Qed.

  
  (* ==================================== *)
  (** ** Vector dot product *)

  (** dot production of two vectors. *)
  Definition cvdot {n : nat} (v1 v2 : cvec n) : A := @cvdot _ Tadd Azero Tmul _ v1 v2.
  Notation "< a , b >" := (cvdot a b) : cvec_scope.

  (** <row(m1,i)\T, col(m2,j)> = [m1 * m2].ij *)
  Lemma cvdot_row_col_eq_mnth : forall {r c s} (m1 : mat r c) (m2 : mat c s) i j,
      i < r -> j < s -> (<(mrow m1 i)\T, mcol m2 j> == (m1 * m2)%M $ i $ j)%T.
  Proof. intros. apply cvdot_row_col_eq_mnth; auto. Qed.

  (** <v1,v2> = v1\T * v2 *)
  Lemma cvdot_eq_mul_trans : forall {n} (v1 v2 : cvec n),
      (<v1,v2> == scalar_of_mat (v1\T * v2)%M)%T.
  Proof. intros. apply cvdot_eq_mul_trans. Qed.

  (** <v1,v2> = <v2,v1> *)
  Lemma cvdot_comm : forall {n} (v1 v2 : cvec n), (<v1,v2> == <v2,v1>)%T.
  Proof. intros. apply cvdot_comm. Qed.

  (** <v1 + v2, v3> = <v1,v3> + <v2,v3> *)
  Lemma cvdot_vadd_distr_l : forall {n} (v1 v2 v3 : cvec n),
      (<(v1 + v2)%CV,v3> == <v1,v3> + <v2,v3>)%T.
  Proof. intros. apply cvdot_add_distr_l. Qed.

  (** <v1, v2 + v3> = <v1,v2> + <v1,v3> *)
  Lemma cvdot_vadd_distr_r : forall {n} (v1 v2 v3 : cvec n),
      (<v1, (v2 + v3)%CV> == <v1,v2> + <v1,v3>)%T.
  Proof. intros. apply cvdot_add_distr_r. Qed.

  (** <a c* v1, v2> = a * <v1,v2> *)
  Lemma cvdot_vcmul_l : forall {n} (v1 v2 : cvec n) (a : A),
      (<a c* v1, v2> == a * <v1,v2>)%T.
  Proof. intros. apply cvdot_vcmul_l. Qed.

  (** <v1, a c* v2> == a * <v1,v2> *)
  Lemma cvdot_vcmul_r : forall {n} (v1 v2 : cvec n) (a : A),
      (<v1, a c* v2> == a * <v1,v2>)%T.
  Proof. intros. apply cvdot_vcmul_r. Qed.

  (** <0,v> = 0 *)
  Lemma cvdot_0_l : forall {n} (V : cvec n), (<cvec0,v> == Azero)%T.
  Proof. intros. apply cvdot_0_l. Qed.

  (** <v,0> = 0 *)
  Lemma cvdot_0_r : forall {n} (V : cvec n), (<v,cvec0> == Azero)%T.
  Proof. intros. apply cvdot_0_r. Qed.
  
  (** < - v1, v2> = - <v1,v2> *)
  Lemma cvdot_vopp_l : forall {n} (v1 v2 : cvec n), (< (-v1)%CV, v2> == - <v1,v2>)%T.
  Proof. intros. apply cvdot_vopp_l. Qed.
  
  (** < v1, - v2> = - <v1,v2> *)
  Lemma cvdot_vopp_r : forall {n} (v1 v2 : cvec n), (< v1, (-v2)%CV> == - <v1,v2>)%T.
  Proof. intros. apply cvdot_vopp_r. Qed.


  (* ==================================== *)
  (** ** Comparison of matrix left or right multiply to a vector *)
  
  (* (** M * v = v * M\T *) *)
  (* Lemma mmv_eq_vmmt : forall {r c : nat} (M : mat r c) (V : cvec c), *)
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
  (* Lemma mvm_eq_mtmv : forall {r c : nat} (V : rvec r) (M : mat r c), *)
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
