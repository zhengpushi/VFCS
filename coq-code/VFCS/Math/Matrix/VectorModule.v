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
  * BasicVectorTheory, vector theory on element with equivalence relaton.
  * MonoidVectorTheory, vector theory on element with monoid structure.
  * RingVectorTheory, vector theory on element with ring structure.
  * OrderedRingVectorTheory, `RingVectorTheory` with order relation.
  * FieldVectorTheory, vector theory on element with field structure.
  * OrderedFieldVectorTheory, `FieldVectorTheory` with order relation.
  * NormedOrderedFieldVectorTheory, `OrderedFieldVectorTheory` with norm.
 *)

Require Export Vector.
Require Export ElementType.


(* ######################################################################### *)
(** * Basic Vector Theory *)
Module BasicVectorTheory (E : ElementType).
  Export E.
  
  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope vec_scope.

  Definition vec (n : nat) := @vec A n.

  (** veq, iff vnth *)
  Lemma veq_iff_vnth : forall {n} (u v : vec n), u = v <-> (forall i, u $ i = v $ i).
  Proof. intros. apply veq_iff_vnth. Qed.

  #[export] Instance veq_dec : forall {n}, Dec (@eq (vec n)).
  Proof. intros. apply (veq_dec (Azero:=0)). Qed.

  (** Convert between function and vector *)
  Definition f2v {n} (f : nat -> A) : vec n := f2v f.
  Definition v2f {n} (v : vec n) : nat -> A := v2f 0 v.

  (** a :: v *)
  Definition vconsH {n} (a : A) (v : vec n) : vec (S n) := vconsH (Azero:=0) a v.
  (** v ++ [a] *)
  Definition vconsT {n} (v : vec n) (a : A) : vec (S n) := vconsT (Azero:=0) v a.

  (** Convert between list and vector *)
  Definition v2l {n} (v : vec n) : list A := v2l v.
  Definition l2v {n} (l : list A) : vec n := l2v 0 _ l.
  
  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof. intros. apply v2l_length. Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> (v2l (@l2v n l) = l).
  Proof. intros. apply v2l_l2v_id; auto. Qed.

  Lemma l2v_v2l_id : forall {n} (v : vec n), @l2v n (v2l v) = v.
  Proof. intros. apply l2v_v2l_id. Qed.

  (** Make concrete vector *)
  Definition mkvec1 (a1 : A) : vec 1 := mkvec1 (Azero:=0) a1.
  Definition mkvec2 (a1 a2 : A) : vec 2 := mkvec2 (Azero:=0) a1 a2.
  Definition mkvec3 (a1 a2 a3 : A) : vec 3 := mkvec3 (Azero:=0) a1 a2 a3.
  Definition mkvec4 (a1 a2 a3 a4 : A) : vec 4 := mkvec4 (Azero:=0) a1 a2 a3 a4.

  (** Vector mapping *)
  Definition vmap {n} (v : vec n) (f : A -> A) : vec n := vmap f v.
  Definition vmap2 {n} (u v : vec n) (f : A -> A -> A) : vec n := vmap2 f u v.
  
  (** Sum of a vector (also named folding) (generic version) *)
  Definition vsumG {n} (v : vec n) (f : A -> A -> A) (b : A) : A := @vsum _ f b _ v.

  (** Make a zero vector *)
  Definition vzero {n} : vec n := vzero 0.
  
End BasicVectorTheory.


(* ######################################################################### *)
(** * Monoid vector theory *)
Module MonoidVectorTheory (E : MonoidElementType).

  Include (BasicVectorTheory E).

  (** *** Vector addition *)
  
  Definition vadd {n} := vadd (Aadd:=Aadd) (n:=n).
  Infix "+" := vadd : vec_scope.

  (** (u + v) + w = u + (v + w) *)
  Lemma vadd_assoc : forall {n} (u v w : vec n), (u + v) + w = u + (v + w).
  Proof. intros. apply vadd_assoc. Qed.

  (** u + v = v + u *)
  Lemma vadd_comm : forall {n} (u v : vec n), u + v = v + u.
  Proof. intros. apply vadd_comm. Qed.

  (** 0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), vzero + v = v.
  Proof. intros. apply vadd_0_l. Qed.

  (** v + 0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + vzero = v.
  Proof. intros. apply vadd_0_r. Qed.

  #[export] Instance vadd_AMonoid : forall n, AMonoid (@vadd n) vzero.
  Proof. apply vadd_AMonoid. Qed.

End MonoidVectorTheory.


(* ######################################################################### *)
(** * Ring vector theory *)
Module RingVectorTheory (E : RingElementType).

  Include (MonoidVectorTheory E).

  (** *** Vector opposition *)

  Definition vopp {n} (v : vec n) : vec n := vopp (Aopp:=Aopp) v.
  Notation "- v" := (vopp v) : vec_scope.

  (** - v + v = 0 *)
  Lemma vadd_vopp_l : forall {n} (v : vec n), v + (- v) = vzero.
  Proof. intros. apply vadd_vopp_l. Qed.

  (** v + - v = 0 *)
  Lemma vadd_vopp_r : forall {n} (v : vec n), (- v) + v = vzero.
  Proof. intros. apply vadd_vopp_r. Qed.

  #[export] Instance vadd_AGroup : forall n, AGroup (@vadd n) vzero vopp.
  Proof. intros. apply vadd_AGroup. Qed.

  (** - (- v) = v *)
  Lemma vopp_vopp : forall {n} (v : vec n), - (- v) = v.
  Proof. intros. apply vopp_vopp. Qed.

  (** - u = v <-> u = - v *)
  Lemma vopp_exchange : forall {n} (u v : vec n), - u = v <-> u = - v.
  Proof. intros. apply vopp_exchange. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n}, - (@vzero n) = vzero.
  Proof. intros. apply vopp_vzero. Qed.

  (** - (u + v) = (- u) + (- v) *)
  Lemma vopp_vadd : forall {n} (u v : vec n), - (u + v) = (- u) + (- v).
  Proof. intros. apply vopp_vadd. Qed.


  (** *** Vector subtraction *)

  Definition vsub {n} (u v : vec n) : vec n := u + (- v).
  Infix "-" := vsub : vec_scope.

  Lemma vsub_self : forall (n : nat) v, v - v = (@vzero n).
  Proof. intros. apply vsub_self. Qed.
  
  Lemma vsub_0_l : forall (n : nat) v, (@vzero n) - v = - v.
  Proof. intros. apply vsub_0_l. Qed.
  
  Lemma vsub_comm : forall (n : nat) (u v : vec n), u - v = - (v - u).
  Proof. intros. apply vsub_comm. Qed.
    
  Lemma vsub_assoc : forall (n : nat) (u v w : vec n), (u - v) - w = u - (v + w).
  Proof. intros. apply vsub_assoc. Qed.
    
  Lemma vsub_assoc1 : forall (n : nat) (u v w : vec n), (u + v) - w = u + (v - w).
  Proof. intros. apply vsub_assoc1. Qed.
    
  Lemma vsub_assoc2 : forall (n : nat) (u v w : vec n), (u - v) - w = (u - w) - v.
  Proof. intros. apply vsub_assoc2. Qed.


  (** *** Vector scalar multiplication *)

  Definition vcmul {n} k (v : vec n) : vec n := vcmul (Amul:=Amul) k v.
  Infix "\.*" := vcmul : vec_scope.

  (** (k * v)[i] = k * v[i] *)
  Lemma vnth_vcmul : forall {n} (v : vec n) k i, (k \.* v) $ i = k * (v $ i).
  Proof. intros. cbv. auto. Qed.

  (** k \.* (l \.* v) = (k * l) \.* v *)
  Lemma vcmul_assoc : forall {n} k l (v : vec n), k \.* (l \.* v) = (k * l)%A \.* v.
  Proof. intros. apply vcmul_assoc. Qed.

  (** k \.* (l \.* v) = l \.* (k \.* v) *)
  Lemma vcmul_perm : forall {n} k l (v : vec n), k \.* (l \.* v) = l \.* (k \.* v).
  Proof. intros. apply vcmul_perm. Qed.

  (** (k + l) \.* v = (k \.* v) + (l \.* v) *)
  Lemma vcmul_add : forall {n} k l (v : vec n),
      (k + l)%A \.* v = (k \.* v) + (l \.* v).
  Proof. intros. apply vcmul_add. Qed.

  (** k \.* (u + v) = (k \.* u) + (k \.* v) *)
  Lemma vcmul_vadd : forall {n} k (u v : vec n),
      k \.* (u + v) = (k \.* u) + (k \.* v).
  Proof. intros. apply vcmul_vadd. Qed.

  (** 1 \.* v = v *)
  Lemma vcmul_1_l : forall {n} (v : vec n), Aone \.* v = v.
  Proof. intros. apply vcmul_1_l. Qed.

  (** 0 \.* v = 0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), Azero \.* v = vzero.
  Proof. intros. apply vcmul_0_l. Qed.

  (** k \.* 0 = 0 *)
  Lemma vcmul_0_r : forall {n} k, k \.* (@vzero n) = vzero.
  Proof. intros. apply vcmul_0_r. Qed.
  
  (** (-a) * v = - (a * v) *)
  Lemma vcmul_opp : forall {n} a (v : vec n), (- a)%A \.* v = - (a \.* v).
  Proof. intros. apply vcmul_opp. Qed.
  
  (** a * (- v) = - (a * v) *)
  Lemma vcmul_vopp : forall {n} a (v : vec n), a \.* (- v) = - (a \.* v).
  Proof. intros. apply vcmul_vopp. Qed.

  (** (-a) * (- v) = a * v *)
  Lemma vcmul_opp_vopp : forall {n} a (v : vec n), (- a)%A \.* (- v) = a \.* v.
  Proof. intros. apply vcmul_opp_vopp. Qed.

  (** a \.* (u - v) = (a \.* u) - (a \.* v) *)
  Lemma vcmul_vsub : forall {n} a (u v : vec n),
      a \.* (u - v) = (a \.* u) - (a \.* v).
  Proof. intros. apply vcmul_vsub. Qed.

  (** k * u = v -> k <> 0 *)
  Lemma vcmul_eq_imply_k_neq0 : forall {n} (u v : vec n) k,
      k \.* u = v -> u <> vzero -> v <> vzero -> k <> 0.
  Proof. intros. apply vcmul_eq_imply_k_neq0 in H; auto. Qed.


  (** *** Vector dot product *)

  Definition vdot {n : nat} (u v : vec n) : A := @vdot _ Aadd 0 Amul _ u v.
  Notation "< u , v >" := (vdot u v) : vec_scope.

  (** <u, v> = <v, u> *)
  Lemma vdot_comm : forall {n} (u v : vec n), <u, v> = <v, u>.
  Proof. intros. apply vdot_comm. Qed.

  (** <vzero, v> = 0 *)
  Lemma vdot_0_l : forall {n} (v : vec n), <vzero, v> = 0.
  Proof. intros. apply vdot_0_l. Qed.

  (** <v, vzero> = 0 *)
  Lemma vdot_0_r : forall {n} (v : vec n), <v, vzero> = 0.
  Proof. intros. apply vdot_0_r. Qed.

  (** <u + v, w> = <u, w> + <v, w> *)
  Lemma vdot_vadd_l : forall {n} (u v w : vec n),
      <u + v, w> = (<u, w> + <v, w>)%A.
  Proof. intros. apply vdot_vadd_l. Qed.

  (** <u, v + w> = <u, v> + <u, w> *)
  Lemma vdot_vadd_r : forall {n} (u v w : vec n),
      <u, v + w> = (<u, v> + <u, w>)%A.
  Proof. intros. apply vdot_vadd_r. Qed.

  (** <- u, v> = - <u, v> *)
  Lemma vdot_vopp_l : forall {n} (u v : vec n), < - u, v> = (- <u, v>)%A.
  Proof. intros. apply vdot_vopp_l. Qed.

  (** <u, - v> = - <u, v> *)
  Lemma vdot_vopp_r : forall {n} (u v : vec n), <u, - v> = (- <u, v>)%A.
  Proof. intros. apply vdot_vopp_r. Qed.

  (** <u - v, w> = <u, w> - <v, w> *)
  Lemma vdot_vsub_l : forall {n} (u v w : vec n),
      <u - v, w> = (<u, w> - <v, w>)%A.
  Proof. intros. apply vdot_vsub_l. Qed.

  (** <u, v - w> = <u, v> - <u, w> *)
  Lemma vdot_vsub_r : forall {n} (u v w : vec n),
      <u, v - w> = (<u, v> - <u, w>)%A.
  Proof. intros. apply vdot_vsub_r. Qed.

  (** <a \.* u, v> = a * <u, v> *)
  Lemma vdot_vcmul_l : forall {n} (u v : vec n) (a : A), <a \.* u, v> = a * <u, v>.
  Proof. intros. apply vdot_vcmul_l. Qed.

  (** <u, a \.* v> = a * <u, v> *)
  Lemma vdot_vcmul_r : forall {n} (u v : vec n) (a : A), <u, a \.* v> = a * <u, v>.
  Proof. intros. apply vdot_vcmul_r. Qed.
  
  (** <u, v> <> 0 -> u <> 0 *)
  Lemma vdot_neq0_imply_neq0_l : forall {n} (u v : vec n), <u, v> <> 0 -> u <> vzero.
  Proof. intros. apply vdot_neq0_imply_neq0_l in H; auto. Qed.

  (** <u, v> <> 0 -> v <> 0 *)
  Lemma vdot_neq0_imply_neq0_r : forall {n} (u v : vec n), <u, v> <> 0 -> v <> vzero.
  Proof. intros. apply vdot_neq0_imply_neq0_r in H; auto. Qed.

  
  (** *** vsum *)
  Definition vsum {n} (v : vec n) := @vsum _ Aadd Azero _ v.

  (** (∀ i, u.i = k * v.i) -> Σu = k * Σv *)
  Lemma vsum_vcmul : forall {n} (u v : vec n) k,
      (forall i, u $ i = k * v $ i) -> vsum u = k * vsum v.
  Proof. intros. apply vsum_vcmul; auto. Qed.
  

  (** *** Unit vector *)
  
  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec. *)
  Definition vunit {n} (v : vec n) : Prop := @vunit _ Aadd 0 Amul 1 _ v.

  (** vunit v <-> vunit (vopp u). *)
  Lemma vopp_vunit : forall {n} (v : vec n), vunit (vopp v) <-> vunit v.
  Proof. intros. apply vopp_vunit. Qed.


  (** *** Orthogonal vectors *)

  (* Two vectors, u and v, in an inner product space v, are orthogonal (also called 
     perpendicular) if their inner-product is zero. It can be denoted as `u ⟂ v` *)
  
  Definition vorth {n} (u v : vec n) : Prop := <u, v> = 0.
  Infix "_|_" := vorth (at level 50).

  (** u _|_ v -> v _|_ u *)
  Lemma vorth_comm : forall {n} (u v : vec n), u _|_ v -> v _|_ u.
  Proof. intros. apply vorth_comm; auto. Qed.

  
  (** *** Two vectors are parallel (or called collinear) *)

  (** Two non-zero vectors are parallel, when their components are proportional *)
  Definition vpara {n} (u v : vec n) : Prop := @vpara _ Azero Amul _ u v.
  Infix "//" := vpara : vec_scope.

  (** v // v *)
  Lemma vpara_refl : forall {n} (v : vec n), v <> vzero -> v // v.
  Proof. intros. apply vpara_refl; auto. Qed.

  (** u // v -> v // w -> u // w *)
  Lemma vpara_trans : forall {n} (u v w: vec n), u // v -> v // w -> u // w.
  Proof. intros. apply vpara_trans with v; auto. Qed.
  
End RingVectorTheory.


(* ######################################################################### *)
(** * Ordered ring vector theory *)
Module OrderedRingVectorTheory (E : OrderedRingElementType).

  Include (RingVectorTheory E).
  
  (** 0 <= <v, v> *)
  Lemma vdot_ge0 : forall {n} (v : vec n), 0 <= (<v, v>).
  Proof. intros. apply vdot_ge0. Qed.
  
  (** <u, v> ² <= <u, u> * <v, v> *)
  Lemma vdot_sqr_le : forall {n} (u v : vec n), (<u, v> ²) <= <u, u> * <v, v>.
  Proof. intros. apply vdot_sqr_le. Qed.

  (** (v i)² <= <v, v> *)
  Lemma vnth_sqr_le_vdot : forall {n} (v : vec n) (i : fin n), (v i) ² <= <v, v>.
  Proof. intros. apply vnth_sqr_le_vdot. Qed.

  (** (∀ i, 0 <= v.i) -> v.i <= ∑v *)
  Lemma vsum_ge_any : forall {n} (v : vec n) i, (forall i, Azero <= v $ i) -> v $ i <= vsum v.
  Proof. intros. apply vsum_ge_any; auto. Qed.
  
  (** (∀ i, 0 <= v.i) -> 0 <= ∑v *)
  Lemma vsum_ge0 : forall {n} (v : vec n), (forall i, Azero <= v $ i) -> Azero <= vsum v.
  Proof. intros. apply vsum_ge0; auto. Qed.
  
  (** (∀ i, 0 <= v.i) -> (∃ i, v.i <> 0) -> 0 < ∑v *)
  Lemma vsum_gt0 : forall {n} (v : vec n),
      (forall i, Azero <= v $ i) -> (exists i, v $ i <> Azero) -> Azero < vsum v.
  Proof. intros. apply vsum_gt0; auto. Qed.

End OrderedRingVectorTheory.


(* ######################################################################### *)
(** * Field vector theory *)
Module FieldVectorTheory (E : FieldElementType).
  
  Include (RingVectorTheory E).
  
  (** k * v = 0 -> (k = 0) \/ (v = 0) *)
  Lemma vcmul_eq0_imply_k0_or_v0 : forall {n} k (v : vec n),
      k \.* v = vzero -> (k = Azero) \/ (v = vzero).
  Proof. intros. apply vcmul_eq0_imply_k0_or_v0; auto. Qed.

  (** k * v = 0 -> v <> 0 -> k = 0 *)
  Corollary vcmul_eq0_imply_k0 : forall {n} k (v : vec n),
      k \.* v = vzero -> v <> vzero -> k = Azero.
  Proof. intros. apply (vcmul_eq0_imply_k0 k v); auto. Qed.

  (** k * v = 0 -> k <> 0 -> v = 0 *)
  Corollary vcmul_eq0_imply_v0 : forall {n} k (v : vec n),
      k \.* v = vzero -> k <> Azero -> v = vzero.
  Proof. intros. apply (vcmul_eq0_imply_v0 k v); auto. Qed.
  
  (** k * v = v -> k = 1 \/ v = 0 *)
  Lemma vcmul_same_imply_k1_or_v0 : forall {n} k (v : vec n),
      k \.* v = v -> (k = Aone \/ v = vzero).
  Proof. intros. apply vcmul_same_imply_k1_or_v0; auto. Qed.
  
  (** k = 1 \/ v = 0 -> k * v = v *)
  Lemma vcmul_same_if_k1_or_v0 : forall {n} k (v : vec n),
      (k = Aone \/ v = vzero) -> k \.* v = v.
  Proof.
    intros. destruct H; subst. apply vcmul_1_l; auto. apply vcmul_0_r; auto.
  Qed.
  
  (** k * v = v -> v <> 0 -> k = 1 *)
  Corollary vcmul_same_imply_k1 : forall {n} k (v : vec n),
      k \.* v = v -> v <> vzero -> k = Aone.
  Proof. intros. apply (vcmul_same_imply_k1 k v); auto. Qed.
  
  (** k * v = v -> k <> 1 -> v = 0 *)
  Corollary vcmul_same_imply_v0 : forall {n} k (v : vec n),
      k \.* v = v -> k <> Aone -> v = vzero.
  Proof. intros. apply (vcmul_same_imply_v0 k v); auto. Qed.

  (* k1 * v = k2 * v -> (k1 = k2 \/ v = 0) *)
  Lemma vcmul_sameV_imply_eqK_or_v0 : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> (k1 = k2 \/ v = vzero).
  Proof. intros. apply vcmul_sameV_imply_eqK_or_v0; auto. Qed.

  (* k1 * v = k2 * v -> v <> 0 -> k1 = k2 *)
  Corollary vcmul_sameV_imply_eqK : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> v <> vzero -> k1 = k2.
  Proof. intros. apply vcmul_sameV_imply_eqK in H; auto. Qed.

  (* k1 * v = k2 * v -> k1 <> k2 -> v = 0 *)
  Corollary vcmul_sameV_imply_v0 : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> k1 <> k2 -> v = vzero.
  Proof. intros. apply vcmul_sameV_imply_v0 in H; auto. Qed.

  (** The unit vector cannot be zero vector *)
  Lemma vunit_neq0 : forall {n} (v : vec n), vunit v -> v <> vzero.
  Proof. intros. apply vunit_neq0; auto. Qed.

  (** (k \.* u) _|_ v <-> u _|_ v *)
  Lemma vorth_vcmul_l : forall {n} k (u v : vec n), k <> 0 -> ((k \.* u) _|_ v <-> u _|_ v).
  Proof. intros. apply vorth_vcmul_l; auto. Qed.
  
  (** u _|_ (k \.* v) <-> u _|_ v *)
  Lemma vorth_vcmul_r : forall {n} k (u v : vec n), k <> 0 -> (u _|_ (k \.* v) <-> u _|_ v).
  Proof. intros. apply vorth_vcmul_r; auto. Qed.

  
  (** *** Projection component of a vector onto another *)
  
  (** The projection component of a onto b *)
  Definition vproj {n} (u v : vec n) : vec n := @vproj _ Aadd 0 Amul Ainv _ u v.

  (* u // v -> v // u *)
  Lemma vpara_sym : forall {n} (u v : vec n), u // v -> v // u.
  Proof. intros. apply vpara_sym; auto. Qed.

  (** u // v => ∃! k, k * u = v *)
  Lemma vpara_imply_uniqueK : forall {n} (u v : vec n), u // v -> (exists ! k, k \.* u = v).
  Proof. intros. apply vpara_imply_uniqueK; auto. Qed.

  (** u // v -> (k \.* u) // v *)
  Lemma vcmul_vpara_l : forall {n} k (u v : vec n), k <> 0 -> u // v -> k \.* u // v.
  Proof. intros. apply vcmul_vpara_l; auto. Qed.

  (** u // v -> u // (k \.* v) *)
  Lemma vcmul_vpara_r : forall {n} k (u v : vec n), k <> 0 -> u // v -> u // (k \.* v).
  Proof. intros. apply vcmul_vpara_r; auto. Qed.


  (** *** Perpendicular component of a vector respect to another *)
  
  (** The perpendicular component of u respect to u *)
  Definition vperp {n} (u v : vec n) : vec n :=
    @vperp _ Aadd 0 Aopp Amul Ainv _ u v.

  (** u _|_ v -> vperp u v = u *)
  Lemma vorth_imply_vperp_eq_l : forall {n} (u v : vec n),
      v <> vzero -> u _|_ v -> vperp u v = u.
  Proof. intros. apply vorth_imply_vperp_eq_l; auto. Qed.
  
End FieldVectorTheory.


(* ######################################################################### *)
(** * Ordered field vector theory *)
Module OrderedFieldVectorTheory (E : OrderedFieldElementType).

  Include (FieldVectorTheory E).

  Section THESE_CODE_ARE_COPIED_FROM_OrderedRingVectorTheroy.
    
    (** 0 <= <v, v> *)
    Lemma vdot_ge0 : forall {n} (v : vec n), 0 <= (<v, v>).
    Proof. intros. apply vdot_ge0. Qed.
    
    (** <u, v> ² <= <u, u> * <v, v> *)
    Lemma vdot_sqr_le : forall {n} (u v : vec n), (<u, v> ²) <= <u, u> * <v, v>.
    Proof. intros. apply vdot_sqr_le. Qed.

    (** (v i)² <= <v, v> *)
    Lemma vnth_sqr_le_vdot : forall {n} (v : vec n) (i : fin n), (v i) ² <= <v, v>.
    Proof. intros. apply vnth_sqr_le_vdot. Qed.

    (** (∀ i, 0 <= v.i) -> v.i <= ∑v *)
    Lemma vsum_ge_any : forall {n} (v : vec n) i, (forall i, Azero <= v $ i) -> v $ i <= vsum v.
    Proof. intros. apply vsum_ge_any; auto. Qed.
    
    (** (∀ i, 0 <= v.i) -> 0 <= ∑v *)
    Lemma vsum_ge0 : forall {n} (v : vec n), (forall i, Azero <= v $ i) -> Azero <= vsum v.
    Proof. intros. apply vsum_ge0; auto. Qed.
    
    (** (∀ i, 0 <= v.i) -> (∃ i, v.i <> 0) -> 0 < ∑v *)
    Lemma vsum_gt0 : forall {n} (v : vec n),
        (forall i, Azero <= v $ i) -> (exists i, v $ i <> Azero) -> Azero < vsum v.
    Proof. intros. apply vsum_gt0; auto. Qed.
    
  End THESE_CODE_ARE_COPIED_FROM_OrderedRingVectorTheroy.

  (** v = 0 -> <v, v> = 0 *)
  Lemma vdot_same_eq0_if_vzero : forall {n} (v : vec n), v = vzero -> <v, v> = 0.
  Proof. intros. apply vdot_same_eq0_if_vzero; auto. Qed.
  
  (** <v, v> = 0 -> v = 0 *)
  Lemma vdot_same_eq0_then_vzero : forall {n} (v : vec n), <v, v> = 0 -> v = vzero.
  Proof. intros. apply vdot_same_eq0_then_vzero; auto. Qed.

  (** v <> vzero -> <v, v> <> 0 *)
  Lemma vdot_same_neq0_if_vnonzero : forall {n} (v : vec n), v <> vzero -> <v, v> <> 0.
  Proof. intros. apply vdot_same_neq0_if_vnonzero; auto. Qed.
  
  (** <v, v> <> 0 -> v <> vzero *)
  Lemma vdot_same_neq0_then_vnonzero : forall {n} (v : vec n), <v, v> <> 0 -> v <> vzero.
  Proof. intros. apply vdot_same_neq0_then_vnonzero; auto. Qed.

  (** 0 < <v, v> *)
  Lemma vdot_gt0 : forall {n} (v : vec n), v <> vzero -> Alt Azero (<v, v>).
  Proof. intros. apply vdot_gt0; auto. Qed.
  
  (** <u, v>² / (<u, u> * <v, v>) <= 1. *)
  Lemma vdot_sqr_le_form2 : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> <u, v>² / (<u, u> * <v, v>) <= 1.
  Proof. intros. apply vdot_sqr_le_form2; auto. Qed.

  (** vproj (u + v) w = vproj u w + vproj v w *)
  Lemma vproj_vadd : forall {n} (u v w : vec n),
      w <> vzero -> (vproj (u + v) w = vproj u w + vproj v w)%V.
  Proof. intros. apply vproj_vadd; auto. Qed.
  
  (** vproj (k \.* u) v = k * (vproj u v) *)
  Lemma vproj_vcmul : forall {n} (u v : vec n) k,
      v <> vzero -> (vproj (k \.* u) v = k \.* (vproj u v))%V.
  Proof. intros. apply vproj_vcmul; auto. Qed.

  (** vproj v v = v *)
  Lemma vproj_same : forall {n} (v : vec n), v <> vzero -> vproj v v = v.
  Proof. intros. apply vproj_same; auto. Qed.

  (** vproj _|_ vperp *)
  Lemma vorth_vproj_vperp : forall {n} (u v : vec n), v <> vzero -> vproj u v _|_ vperp u v.
  Proof. intros. apply vorth_vproj_vperp; auto. Qed.

  (** vperp (u + v) w = vperp u w + vperp v w *)
  Lemma vperp_vadd : forall {n} (u v w : vec n),
      w <> vzero -> (vperp (u + v) w = vperp u w + vperp v w)%V.
  Proof. intros. apply vperp_vadd; auto. Qed.

  (** vperp (k * u) v = k * (vperp u v) *)
  Lemma vperp_vcmul : forall {n} (k : A) (u v : vec n),
      v <> vzero -> (vperp (k \.* u) v = k \.* (vperp u v))%V.
  Proof. intros. apply vperp_vcmul; auto. Qed.

  (** vperp v v = vzero *)
  Lemma vperp_same : forall {n} (v : vec n), v <> vzero -> vperp v v = vzero.
  Proof. intros. apply vperp_same; auto. Qed.
  
End OrderedFieldVectorTheory.


(* ######################################################################### *)
(** * Normed ordered field vector theory *)
Module NormedOrderedFieldVectorTheory (E : NormedOrderedFieldElementType).
  Include (OrderedFieldVectorTheory E).

  (** Length of a vector *)
  Definition vlen {n} (v : vec n) : R := @vlen _ Aadd 0 Amul a2r _ v.
  Notation "|| v ||" := (vlen v) : vec_scope.

  (** ||vzero|| = 0 *)
  Lemma vlen_vzero : forall {n:nat}, || @vzero n || = 0%R.
  Proof. intros. apply vlen_vzero. Qed.

  (** 0 <= ||v|| *)
  Lemma vlen_ge0 : forall {n} (v : vec n), (0 <= || v ||)%R.
  Proof. intros. apply vlen_ge0. Qed.
  
  (** ||u|| = ||v|| <-> <u, u> = <v, v> *)
  Lemma vlen_eq_iff_dot_eq : forall {n} (u v : vec n), ||u|| = ||v|| <-> <u, u> = <v, v>.
  Proof. intros. apply vlen_eq_iff_dot_eq. Qed.

  (** <v, v> = ||v||² *)
  Lemma vdot_same : forall {n} (v : vec n), a2r (<v, v>) = (||v||²)%R.
  Proof. intros. apply vdot_same. Qed.

  (** |v i| <= ||v|| *)
  Lemma vnth_le_vlen : forall {n} (v : vec n) (i : fin n),
      v <> vzero -> (a2r (|v i|%A) <= ||v||)%R.
  Proof. intros. apply vnth_le_vlen; auto. Qed.

  (** || v || = 1 <-> <v, v> = 1 *)
  Lemma vlen_eq1_iff_vdot1 : forall {n} (v : vec n), ||v|| = 1%R <-> <v, v> = 1.
  Proof. intros. apply vlen_eq1_iff_vdot1. Qed.

  (** || - v|| = || v || *)
  Lemma vlen_vopp : forall n (v : vec n), || - v || = || v ||.
  Proof. intros. apply vlen_vopp. Qed.

  (** ||k \.* v|| = |k| * ||v|| *)
  Lemma vlen_vcmul : forall n k (v : vec n), || k \.* v || = ((a2r (|k|))%A * ||v||)%R.
  Proof. intros. apply vlen_vcmul. Qed.

  (** ||u + v||² = ||u||² + ||v||² + 2 * <u, v> *)
  Lemma vlen_sqr_vadd : forall {n} (u v : vec n),
      (||(u + v)%V||² = ||u||² + ||v||² + 2 * a2r (<u,v>))%R.
  Proof. intros. apply vlen_sqr_vadd. Qed.

  (** ||u - v||² = ||u||² + ||v||² - 2 * <u, v> *)
  Lemma vlen_sqr_vsub : forall {n} (u v : vec n),
      (||(u - v)%V||² = ||u||² + ||v||² - 2 * a2r (<u, v>))%R.
  Proof. intros. apply vlen_sqr_vsub. Qed.

  (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
  (** |<u, v>| <= ||u|| * ||v|| *)
  Lemma vdot_abs_le : forall {n} (u v : vec n), (|a2r (<u, v>)| <= ||u|| * ||v||)%R.
  Proof. intros. apply vdot_abs_le. Qed.

  (** <u, v> <= ||u|| * ||v|| *)
  Lemma vdot_le_mul_vlen : forall {n} (u v : vec n), (a2r (<u, v>) <= ||u|| * ||v||)%R.
  Proof. intros. apply vdot_le_mul_vlen. Qed.

  (** - ||u|| * ||v|| <= <u, v> *)
  Lemma vdot_ge_mul_vlen_neg : forall {n} (u v : vec n), (- (||u|| * ||v||) <= a2r (<u, v>))%R.
  Proof. intros. apply vdot_ge_mul_vlen_neg. Qed.

  (* 任意维度“三角形”两边长度之和大于第三边长度 *)
  (** ||u + v|| <= ||u|| + ||v|| *)
  Lemma vlen_vadd_le : forall {n} (u v : vec n), (||(u + v)%V|| <= ||u|| + ||v||)%R.
  Proof. intros. apply vlen_vadd_le. Qed.

  (** ||v|| = 0 <-> v = 0 *)
  Lemma vlen_eq0_iff_eq0 : forall {n} (v : vec n), ||v|| = 0%R <-> v = vzero.
  Proof. intros. apply vlen_eq0_iff_eq0. Qed.

  (** ||v|| <> 0 <-> v <> 0 *)
  Lemma vlen_neq0_iff_neq0 : forall {n} (v : vec n), ||v|| <> 0%R <-> v <> vzero.
  Proof. intros. apply vlen_neq0_iff_neq0. Qed.

  (** v <> vzero -> 0 < ||v|| *)
  Lemma vlen_gt0 : forall {n} (v : vec n), v <> vzero -> (0 < ||v||)%R.
  Proof. intros. apply vlen_gt0; auto. Qed.
      
  (** 0 <= <v, v> *)
  Lemma vdot_same_ge0 : forall {n} (v : vec n), (0 <= <v, v>)%A.
  Proof. intros. apply vdot_same_ge0. Qed.

  (** Verify the definition is reasonable *)
  Lemma vunit_spec : forall {n} (v : vec n), vunit v <-> ||v|| = 1%R.
  Proof. intros. apply vunit_spec. Qed.

End NormedOrderedFieldVectorTheory.

