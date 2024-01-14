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
  Lemma veq_iff_vnth : forall {n} (V1 V2 : vec n), V1 = V2 <-> (forall i, V1$i = V2$i).
  Proof. intros. apply veq_iff_vnth. Qed.

  #[export] Instance veq_dec : forall {n}, Dec (@eq (vec n)).
  Proof. intros. apply (veq_dec Azero AeqDec). Qed.

  (** Convert between function and vector *)
  Definition f2v {n} (f : nat -> A) : vec n := f2v f.
  Definition v2f {n} (V : vec n) : nat -> A := v2f Azero V.

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
  
End BasicVectorTheory.


(* ######################################################################### *)
(** * Monoid vector theory *)
Module MonoidVectorTheory (E : MonoidElementType).

  Include (BasicVectorTheory E).
  
  (** *** Vector addition *)
  
  Definition vadd {n} (V1 V2 : vec n) : vec n := vadd (Aadd:=Aadd) V1 V2.
  Infix "+" := vadd : vec_scope.

  (** V1 + V2 = V2 + V1 *)
  #[export] Instance vadd_Commutative : forall n, Commutative (@vadd n).
  Proof. apply vadd_Commutative. Qed.

  (** (V1 + V2) + V3 = V1 + (V2 + V3) *)
  #[export] Instance vadd_Associative : forall n, Associative (@vadd n).
  Proof. apply vadd_Associative. Qed.

  (** 0 + V = V *)
  #[export] Instance vadd_IdentityLeft : forall n, IdentityLeft (@vadd n) vzero.
  Proof. apply vadd_IdentityLeft. Qed.

  (** V + 0 = V *)
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

  Definition vopp {n} (V : vec n) : vec n := vopp (Aopp:=Aopp) V.
  Notation "- V" := (vopp V) : vec_scope.

  (** -V + V = 0 *)
  #[export] Instance vadd_InverseLeft : forall {n}, InverseLeft (@vadd n) vzero vopp.
  Proof. intros. apply vadd_InverseLeft. Qed.

  (** V + -V = 0 *)
  #[export] Instance vadd_InverseRight : forall {n}, InverseRight (@vadd n) vzero vopp.
  Proof. intros. apply vadd_InverseRight. Qed.

  #[export] Instance vadd_AGroup : forall n, AGroup (@vadd n) vzero vopp.
  Proof. intros. apply vadd_AGroup. Qed.

  (** - (- V) = V *)
  Lemma vopp_vopp : forall {n} (V : vec n), - (- V) = V.
  Proof. intros. apply vopp_vopp. Qed.

  (** -V1 = V2 <-> V1 = -V2 *)
  Lemma vopp_exchange : forall {n} (V1 V2 : vec n), -V1 = V2 <-> V1 = -V2.
  Proof. intros. apply vopp_exchange. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n:nat}, - (@vzero n) = vzero.
  Proof. intros. apply vopp_vzero. Qed.

  (** - (V1 + V2) = (-V1) + (-V2) *)
  Lemma vopp_vadd : forall {n} (V1 V2 : vec n), - (V1 + V2) = (-V1) + (-V2).
  Proof. intros. apply vopp_vadd. Qed.


  (** *** Vector subtraction *)

  Definition vsub {n} (V1 V2 : vec n) : vec n := V1 + (-V2).
  Infix "-" := vsub : vec_scope.

  Lemma vsub_self : forall (n : nat) V, V - V = (@vzero n).
  Proof. intros. apply vsub_self. Qed.
  
  Lemma vsub_0_l : forall (n : nat) V, (@vzero n) - V = -V.
  Proof. intros. apply vsub_0_l. Qed.
  
  Lemma vsub_comm : forall (n : nat) (V1 V2 : vec n), V1 - V2 = -(V2 - V1).
  Proof. intros. apply vsub_comm. Qed.
    
  Lemma vsub_assoc : forall (n : nat) (V1 V2 V3 : vec n), (V1 - V2) - V3 = V1 - (V2 + V3).
  Proof. intros. apply vsub_assoc. Qed.
    
  Lemma vsub_assoc1 : forall (n : nat) (V1 V2 V3 : vec n), (V1 + V2) - V3 = V1 + (V2 - V3).
  Proof. intros. apply vsub_assoc1. Qed.
    
  Lemma vsub_assoc2 : forall (n : nat) (V1 V2 V3 : vec n), (V1 - V2) - V3 = (V1 - V3) - V2.
  Proof. intros. apply vsub_assoc2. Qed.


  (** *** Vector scalar multiplication *)

  Definition vcmul {n} k (V : vec n) : vec n := vcmul (Amul:=Amul) k V.
  Infix "c*" := vcmul : vec_scope.

  (** (k * V)[i] = k * V[i] *)
  Lemma vnth_vcmul : forall {n} (V : vec n) k i, (k c* V)$i = k * (V$i).
  Proof. intros. cbv. auto. Qed.

  (** k c* (l c* V) = (k * l) c* V *)
  Lemma vcmul_assoc : forall {n} k l (V : vec n), k c* (l c* V) = (k * l)%A c* V.
  Proof. intros. apply vcmul_assoc. Qed.

  (** k c* (l c* V) = l c* (k c* V) *)
  Lemma vcmul_perm : forall {n} k l (V : vec n), k c* (l c* V) = l c* (k c* V).
  Proof. intros. apply vcmul_perm. Qed.

  (** (k + l) c* V = (k c* V) + (l c* V) *)
  Lemma vcmul_add : forall {n} k l (V : vec n),
      (k + l)%A c* V = (k c* V) + (l c* V).
  Proof. intros. apply vcmul_add. Qed.

  (** k c* (V1 + V2) = (k c* V1) + (k c* V2) *)
  Lemma vcmul_vadd : forall {n} k (V1 V2 : vec n),
      k c* (V1 + V2) = (k c* V1) + (k c* V2).
  Proof. intros. apply vcmul_vadd. Qed.

  (** 1 c* V = V *)
  Lemma vcmul_1_l : forall {n} (V : vec n), Aone c* V = V.
  Proof. intros. apply vcmul_1_l. Qed.

  (** 0 c* V = 0 *)
  Lemma vcmul_0_l : forall {n} (V : vec n), Azero c* V = vzero.
  Proof. intros. apply vcmul_0_l. Qed.

  (** k c* 0 = 0 *)
  Lemma vcmul_0_r : forall {n} k, k c* (@vzero n) = vzero.
  Proof. intros. apply vcmul_0_r. Qed.
  
  (** (-a) * V = - (a * V) *)
  Lemma vcmul_opp : forall {n} a (V : vec n), (- a)%A c* V = - (a c* V).
  Proof. intros. apply vcmul_opp. Qed.
  
  (** a * (-V) = - (a * V) *)
  Lemma vcmul_vopp : forall {n} a (V : vec n), a c* (-V) = - (a c* V).
  Proof. intros. apply vcmul_vopp. Qed.

  (** (-a) * (- V) = a * V *)
  Lemma vcmul_opp_vopp : forall {n} a (V : vec n), (- a)%A c* (- V) = a c* V.
  Proof. intros. apply vcmul_opp_vopp. Qed.

  (** a c* (V1 - V2) = (a c* V1) - (a c* V2) *)
  Lemma vcmul_vsub : forall {n} a (V1 V2 : vec n),
      a c* (V1 - V2) = (a c* V1) - (a c* V2).
  Proof. intros. apply vcmul_vsub. Qed.

  (** (V1 <> 0 /\ V2 <> 0 /\ k * V1 = V2) -> k <> 0 *)
  Lemma vcmul_eq_imply_k_neq0 : forall {n} (V1 V2 : vec n) k,
      k c* V1 = V2 -> V1 <> vzero -> V2 <> vzero -> k <> Azero.
  Proof. intros. apply vcmul_eq_imply_k_neq0 in H; auto. Qed.

  (*   (* k c* V1 = V2 -> k <> 0 *) *)
  (* Lemma vnonzero_vcmul_eq_imply_k_neq0 : forall {n} k (V1 V2 : vnonzero n), *)
  (*     k c* V1 = V2 -> k <> Azero. *)
  (* Proof. intros. apply (vcmul_eq_imply_k_neq0 V1 V2); auto. apply V1. apply V2. Qed. *)

  

  (** *** Vector dot product *)

  Definition vdot {n : nat} (V1 V2 : vec n) : A := @vdot _ Aadd Azero Amul _ V1 V2.
  Notation "< V1 , V2 >" := (vdot V1 V2) : vec_scope.

  (** <V1, V2> = <V2, V1> *)
  Lemma vdot_comm : forall {n} (V1 V2 : vec n), <V1, V2> = <V2, V1>.
  Proof. intros. apply vdot_comm. Qed.

  (** <vzero, V> = vzero *)
  Lemma vdot_0_l : forall {n} (V : vec n), <vzero, V> = Azero.
  Proof. intros. apply vdot_0_l. Qed.

  (** <V, vzero> = vzero *)
  Lemma vdot_0_r : forall {n} (V : vec n), <V, vzero> = Azero.
  Proof. intros. apply vdot_0_r. Qed.

  (** <V1 + V2, V3> = <V1, V3> + <V2, V3> *)
  Lemma vdot_vadd_l : forall {n} (V1 V2 V3 : vec n),
      <V1 + V2, V3> = (<V1, V3> + <V2, V3>)%A.
  Proof. intros. apply vdot_vadd_l. Qed.

  (** <V1, V2 + V3> = <V1, V2> + <V1, V3> *)
  Lemma vdot_vadd_r : forall {n} (V1 V2 V3 : vec n),
      <V1, V2 + V3> = (<V1, V2> + <V1, V3>)%A.
  Proof. intros. apply vdot_vadd_r. Qed.

  (** <-V1, V2> = - <V1,V2> *)
  Lemma vdot_vopp_l : forall {n} (V1 V2 : vec n), < -V1, V2> = (- <V1,V2>)%A.
  Proof. intros. apply vdot_vopp_l. Qed.

  (** <V1, -V2> = - <V1,V2> *)
  Lemma vdot_vopp_r : forall {n} (V1 V2 : vec n), <V1, -V2> = (- <V1,V2>)%A.
  Proof. intros. apply vdot_vopp_r. Qed.

  (** <V1 - V2, V3> = <V1, V3> - <V2, V3> *)
  Lemma vdot_vsub_l : forall {n} (V1 V2 V3 : vec n),
      <V1 - V2, V3> = (<V1, V3> - <V2, V3>)%A.
  Proof. intros. apply vdot_vsub_l. Qed.

  (** <V1, V2 - V3> = <V1, V2> - <V1, V3> *)
  Lemma vdot_vsub_r : forall {n} (V1 V2 V3 : vec n),
      <V1, V2 - V3> = (<V1, V2> - <V1, V3>)%A.
  Proof. intros. apply vdot_vsub_r. Qed.

  (** <a c* V1, V2> = a * <V1, V2> *)
  Lemma vdot_vcmul_l : forall {n} (V1 V2 : vec n) (a : A), <a c* V1, V2> = a * <V1, V2>.
  Proof. intros. apply vdot_vcmul_l. Qed.

  (** <V1, a c* V2> = a * <V1, V2> *)
  Lemma vdot_vcmul_r : forall {n} (V1 V2 : vec n) (a : A), <V1, a c* V2> = a * <V1, V2>.
  Proof. intros. apply vdot_vcmul_r. Qed.
  
End RingVectorTheory.


(* ######################################################################### *)
(** * Ordered ring vector theory *)
Module OrderedRingVectorTheory (E : OrderedRingElementType).

  Include (RingVectorTheory E).
  
  (** 0 <= <V,V> *)
  Lemma vdot_ge0 : forall {n} (V : vec n), Ale Azero (<V,V>).
  Proof.
    intros. apply vdot_ge0.
    apply Ale_refl. apply Azero_le_sqr. apply Aadd_le_compat.
  Qed.

End OrderedRingVectorTheory.


(* ######################################################################### *)
(** * Field vector theory *)
Module FieldVectorTheory (E : FieldElementType).
  
  Include (RingVectorTheory E).
  
  (** k * V = 0 -> (k = 0) \/ (V = 0) *)
  Lemma vcmul_eq0_imply_k0_or_V0 : forall {n} k (V : vec n),
      k c* V = vzero -> (k = Azero) \/ (V = vzero).
  Proof. intros. apply vcmul_eq0_imply_k0_or_V0; auto. Qed.

  (** k * V = 0 -> V <> 0 -> k = 0 *)
  Corollary vcmul_eq0_imply_k0 : forall {n} k (V : vec n),
      k c* V = vzero -> V <> vzero -> k = Azero.
  Proof. intros. apply (vcmul_eq0_imply_k0 k V); auto. Qed.

  (** k * V = 0 -> k <> 0 -> V = 0 *)
  Corollary vcmul_eq0_imply_V0 : forall {n} k (V : vec n),
      k c* V = vzero -> k <> Azero -> V = vzero.
  Proof. intros. apply (vcmul_eq0_imply_V0 k V); auto. Qed.
  
  (** k * V = V -> k = 1 \/ V = 0 *)
  Lemma vcmul_same_imply_k1_or_V0 : forall {n} k (V : vec n),
      k c* V = V -> (k = Aone \/ V = vzero).
  Proof. intros. apply vcmul_same_imply_k1_or_V0; auto. Qed.
  
  (** k = 1 \/ V = 0 -> k * V = V *)
  Lemma vcmul_same_if_k1_or_V0 : forall {n} k (V : vec n),
      (k = Aone \/ V = vzero) -> k c* V = V.
  Proof.
    intros. destruct H; subst. apply vcmul_1_l; auto. apply vcmul_0_r; auto.
  Qed.
  
  (** k * V = V -> V <> 0 -> k = 1 *)
  Corollary vcmul_same_imply_k1 : forall {n} k (V : vec n),
      k c* V = V -> V <> vzero -> k = Aone.
  Proof. intros. apply (vcmul_same_imply_k1 k V); auto. Qed.
  
  (** k * V = V -> k <> 1 -> V = 0 *)
  Corollary vcmul_same_imply_V0 : forall {n} k (V : vec n),
      k c* V = V -> k <> Aone -> V = vzero.
  Proof. intros. apply (vcmul_same_imply_V0 k V); auto. Qed.

  (* k1 * V = k2 * V -> (k1 = k2 \/ V = 0) *)
  Lemma vcmul_sameV_imply_eqK_or_V0 : forall {n} k1 k2 (V : vec n), 
      k1 c* V = k2 c* V -> (k1 = k2 \/ V = vzero).
  Proof. intros. apply vcmul_sameV_imply_eqK_or_V0; auto. Qed.

  (* k1 * V = k2 * V -> V <> 0 -> k1 = k2 *)
  Corollary vcmul_sameV_imply_eqK : forall {n} k1 k2 (V : vec n), 
      k1 c* V = k2 c* V -> V <> vzero -> k1 = k2.
  Proof. intros. apply vcmul_sameV_imply_eqK in H; auto. Qed.

  (* k1 * V = k2 * V -> k1 <> k2 -> V = 0 *)
  Corollary vcmul_sameV_imply_V0 : forall {n} k1 k2 (V : vec n), 
      k1 c* V = k2 c* V -> k1 <> k2 -> V = vzero.
  Proof. intros. apply vcmul_sameV_imply_V0 in H; auto. Qed.

End FieldVectorTheory.


(* ######################################################################### *)
(** * Ordered field vector theory *)
Module OrderedFieldVectorTheory (E : OrderedFieldElementType).

  Include (FieldVectorTheory E).
  
  (** 0 <= <V,V> *)
  Lemma vdot_ge0 : forall {n} (V : vec n), Ale Azero (<V,V>).
  Proof.
    intros. apply vdot_ge0.
    apply Ale_refl. apply Azero_le_sqr. apply Aadd_le_compat.
  Qed.

  (** <V,V> = 0 <-> V = 0 *)
  Lemma vdot_eq0_iff_vzero : forall {n} (V : vec n), <V,V> = Azero <-> V = vzero.
  Proof.
    intros. apply (vdot_eq0_iff_vzero (Ale:=Ale)).
    apply Ale_refl. apply Azero_le_sqr.
    intros. apply field_sqr_eq0_imply_eq0 in H; auto. apply AeqDec.
    intros. apply Aadd_le_compat; auto.
    intros. apply Aadd_eq_0_reg_l in H1; auto.
  Qed.

  (** <V, V> <> 0 <-> V <> vzero *)
  Lemma vdot_neq0_iff_vnonzero : forall {n} (V : vec n), <V,V> <> Azero <-> V <> vzero.
  Proof. intros. rewrite vdot_eq0_iff_vzero. easy. Qed.

  (** 0 < <V,V> *)
  Lemma vdot_gt0 : forall {n} (V : vec n), V <> vzero -> Alt Azero (<V,V>).
  Proof.
    intros. apply (vdot_gt0 (Ale:=Ale)(Alt:=Alt)); auto.
    apply Ale_refl. apply Azero_le_sqr.
    intros. apply field_sqr_eq0_imply_eq0 in H0; auto. apply AeqDec.
    intros. apply Aadd_le_compat; auto.
    intros. apply Alt_le_compat; auto.
    intros. apply Aadd_eq_0_reg_l in H2; auto.
  Qed.

End OrderedFieldVectorTheory.
