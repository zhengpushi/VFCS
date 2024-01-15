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
  * OrderedRingVectorTheory, `RingVectorTheory` with order relation
  * FieldVectorTheory, vector theory on element with field structure.
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
  Proof. intros. apply (veq_dec Azero AeqDec). Qed.

  (** Convert between function and vector *)
  Definition f2v {n} (f : nat -> A) : vec n := f2v f.
  Definition v2f {n} (v : vec n) : nat -> A := v2f Azero v.

  (** a :: v *)
  Definition vconsH {n} (a : A) (v : vec n) : vec (S n) := @vconsH _ Azero _ a v.
  (** v ++ [a] *)
  Definition vconsT {n} (v : vec n) (a : A) : vec (S n) := @vconsT _ Azero _ v a.

  (** Convert between list and vector *)
  Definition v2l {n} (v : vec n) : list A := v2l v.
  Definition l2v {n} (l : list A) : vec n := l2v Azero _ l.
  
  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof. intros. apply v2l_length. Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> (v2l (@l2v n l) = l).
  Proof. intros. apply v2l_l2v_id; auto. Qed.

  Lemma l2v_v2l_id : forall {n} (v : vec n), @l2v n (v2l v) = v.
  Proof. intros. apply l2v_v2l_id. Qed.

  (** Make concrete vector *)
  Definition mkvec1 (a1 : A) : vec 1 := @mkvec1 _ Azero a1.
  Definition mkvec2 (a1 a2 : A) : vec 2 := @mkvec2 _ Azero a1 a2.
  Definition mkvec3 (a1 a2 a3 : A) : vec 3 := @mkvec3 _ Azero a1 a2 a3.
  Definition mkvec4 (a1 a2 a3 a4 : A) : vec 4 := @mkvec4 _ Azero a1 a2 a3 a4.

  (** Vector mapping *)
  Definition vmap {n} (v : vec n) (f : A -> A) : vec n := vmap f v.
  Definition vmap2 {n} (u v : vec n) (f : A -> A -> A) : vec n := vmap2 f u v.
  
  (** Sum of a vector (also named folding) *)
  Definition vsum {n} (v : vec n) (f : A -> A -> A) (b : A) : A := @vsum _ f b _ v.

  (** Make a zero vector *)
  Definition vzero {n} : vec n := vzero Azero.
  
End BasicVectorTheory.


(* ######################################################################### *)
(** * Monoid vector theory *)
Module MonoidVectorTheory (E : MonoidElementType).

  Include (BasicVectorTheory E).
  
  (** *** Vector addition *)
  
  Definition vadd {n} (u v : vec n) : vec n := vadd (Aadd:=Aadd) u v.
  Infix "+" := vadd : vec_scope.

  (** u + v = v + u *)
  #[export] Instance vadd_Commutative : forall n, Commutative (@vadd n).
  Proof. apply vadd_Commutative. Qed.

  (** (u + v) + V3 = u + (v + V3) *)
  #[export] Instance vadd_Associative : forall n, Associative (@vadd n).
  Proof. apply vadd_Associative. Qed.

  (** 0 + v = v *)
  #[export] Instance vadd_IdentityLeft : forall n, IdentityLeft (@vadd n) vzero.
  Proof. apply vadd_IdentityLeft. Qed.

  (** v + 0 = v *)
  #[export] Instance vadd_IdentityRight : forall n, IdentityRight (@vadd n) vzero.
  Proof. apply vadd_IdentityRight. Qed.

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
  #[export] Instance vadd_InverseLeft : forall {n}, InverseLeft (@vadd n) vzero vopp.
  Proof. intros. apply vadd_InverseLeft. Qed.

  (** v + - v = 0 *)
  #[export] Instance vadd_InverseRight : forall {n}, InverseRight (@vadd n) vzero vopp.
  Proof. intros. apply vadd_InverseRight. Qed.

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
      k \.* u = v -> u <> vzero -> v <> vzero -> k <> Azero.
  Proof. intros. apply vcmul_eq_imply_k_neq0 in H; auto. Qed.


  (** *** Vector dot product *)

  Definition vdot {n : nat} (u v : vec n) : A := @vdot _ Aadd Azero Amul _ u v.
  Notation "< u , v >" := (vdot u v) : vec_scope.

  (** <u, v> = <v, u> *)
  Lemma vdot_comm : forall {n} (u v : vec n), <u, v> = <v, u>.
  Proof. intros. apply vdot_comm. Qed.

  (** <vzero, v> = vzero *)
  Lemma vdot_0_l : forall {n} (v : vec n), <vzero, v> = Azero.
  Proof. intros. apply vdot_0_l. Qed.

  (** <v, vzero> = vzero *)
  Lemma vdot_0_r : forall {n} (v : vec n), <v, vzero> = Azero.
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
  
End RingVectorTheory.


(* ######################################################################### *)
(** * Ordered ring vector theory *)
Module OrderedRingVectorTheory (E : OrderedRingElementType).

  Include (RingVectorTheory E).
  
  (** 0 <= <v, v> *)
  Lemma vdot_ge0 : forall {n} (v : vec n), Ale Azero (<v, v>).
  Proof.
    intros. apply vdot_ge0.
    apply Ale_refl. apply Azero_le_sqr. apply Aadd_le_compat.
  Qed.

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

End FieldVectorTheory.


(* ######################################################################### *)
(** * Ordered field vector theory *)
Module OrderedFieldVectorTheory (E : OrderedFieldElementType).

  Include (FieldVectorTheory E).
  
  (** 0 <= <v, v> *)
  Lemma vdot_ge0 : forall {n} (v : vec n), Ale Azero (<v, v>).
  Proof.
    intros. apply vdot_ge0.
    apply Ale_refl. apply Azero_le_sqr. apply Aadd_le_compat.
  Qed.

  (** <v, v> = 0 <-> v = 0 *)
  Lemma vdot_eq0_iff_vzero : forall {n} (v : vec n), <v, v> = Azero <-> v = vzero.
  Proof.
    intros. apply (vdot_eq0_iff_vzero (Ale:=Ale)).
    apply Ale_refl. apply Azero_le_sqr.
    intros. apply field_sqr_eq0_imply_eq0 in H; auto. apply AeqDec.
    intros. apply Aadd_le_compat; auto.
    intros. apply Aadd_eq_0_reg_l in H1; auto.
  Qed.

  (** <v, v> <> 0 <-> v <> vzero *)
  Lemma vdot_neq0_iff_vnonzero : forall {n} (v : vec n), <v, v> <> Azero <-> v <> vzero.
  Proof. intros. rewrite vdot_eq0_iff_vzero. easy. Qed.

  (** <u, v> <> 0 -> u <> 0 *)
  Lemma vdot_neq0_imply_neq0_l : forall {n} (u v : vec n), <u, v> <> Azero -> u <> vzero.
  Proof. intros. apply vdot_neq0_imply_neq0_l in H; auto. Qed.
  
  (** <u, v> <> 0 -> v <> 0 *)
  Lemma vdot_neq0_imply_neq0_r : forall {n} (u v : vec n), <u, v> <> Azero -> v <> vzero.
  Proof. intros. apply vdot_neq0_imply_neq0_r in H; auto. Qed.

  (** 0 < <v, v> *)
  Lemma vdot_gt0 : forall {n} (v : vec n), v <> vzero -> Alt Azero (<v, v>).
  Proof.
    intros. apply (vdot_gt0 (Ale:=Ale)(Alt:=Alt)); auto.
    apply Ale_refl. apply Azero_le_sqr.
    intros. apply field_sqr_eq0_imply_eq0 in H0; auto. apply AeqDec.
    intros. apply Aadd_le_compat; auto.
    intros. apply Alt_le_compat; auto.
    intros. apply Aadd_eq_0_reg_l in H2; auto.
  Qed.

End OrderedFieldVectorTheory.
