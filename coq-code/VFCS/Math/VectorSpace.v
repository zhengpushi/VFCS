(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vectro space
  author    : ZhengPu Shi
  date      : 2024.01
  
  remark    :
  1. ref : https://www.maths.tcd.ie/~dwilkins/Courses/111/vspace.pdf
 *)

Require Export Hierarchy.
Require Import Vector.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope VectorSpace_scope.
Delimit Scope VectorSpace_scope with VS.
Open Scope A_scope.
Open Scope VS.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Adiv Alt Ale
  V Vadd Vzero Vopp Vcmul
  W Wadd Wzero Wopp Wcmul.
Generalizable Variables B Badd Bzero.


Section vsum.
  Context `{AMonoid : Monoid A Aadd Azero}.
  Context `{BMonoid : Monoid B Badd Bzero}.

  (** f (∑v) = ∑(f(v.i)) *)
  Lemma vsum_vmap : forall {n} (f : A -> B) (v : @vec A n),
      (f Azero = Bzero) ->
      (forall a b : A, f (Aadd a b) = Badd (f a) (f b)) ->
      f (@vsum _ Aadd Azero _ v) = @vsum _ Badd Bzero _ (vmap f v).
  Proof.
    intros. unfold vec in *. induction n.
    - cbv. auto.
    - rewrite vsumS_tail. rewrite H0. rewrite IHn.
      rewrite vsumS_tail. unfold vmap. auto.
  Qed.
  
End vsum.


(* ===================================================================== *)
(** ** Vector Space (Linear Space) *)

Class VectorSpace `{F : Field} {V : Type}
  (Vadd : V -> V -> V) (Vzero : V) (Vopp : V -> V) (Vcmul : A -> V -> V) := {
    vs_vaddC :: Commutative Vadd;
    vs_vaddA :: Associative Vadd;
    vs_vadd_0_r :: IdentityRight Vadd Vzero;
    vs_vadd_vopp_r :: InverseRight Vadd Vzero Vopp;
    vs_vcmul_1_l : forall v : V, Vcmul Aone v = v;
    vs_vcmul_assoc : forall a b v, Vcmul (Amul a b) v = Vcmul a (Vcmul b v);
    vs_vcmul_aadd : forall a b v, Vcmul (Aadd a b) v = Vadd (Vcmul a v) (Vcmul b v);
    vs_vcmul_vadd : forall a u v, Vcmul a (Vadd u v) = Vadd (Vcmul a u) (Vcmul a v);
  }.


(** A field itself is a vector space *)
Section field_VectorSpace.
  Context `{HField : Field}.
  Add Field field_inst : (make_field_theory HField).
  
  #[export] Instance field_VectorSpace : VectorSpace Aadd Azero Aopp Amul.
  split_intro; try field. Qed.
End field_VectorSpace.

(** a real function is a vector space *)

Section props.
  Context `{VS : VectorSpace}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/b)).
  Infix "/" := Adiv : A_scope.

  Infix "+" := Vadd : VectorSpace_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation "- v" := (Vopp v) : VectorSpace_scope.
  Notation Vsub u v := (u + -v).
  Infix "-" := Vsub : VectorSpace_scope.
  Infix "\.*" := Vcmul : VectorSpace_scope.

  (** 0 + v = v *)
  #[export] Instance vs_vadd_0_l : IdentityLeft Vadd 0.
  Proof.
    (* 0 + v = v + 0 = v *)
    constructor; intros. rewrite commutative, identityRight; auto.
  Qed.
  
  (** -v + v = 0 *)
  #[export] Instance vs_vadd_vopp_l : InverseLeft Vadd 0 Vopp.
  Proof.
    (* -v + v = v + -v = 0 *)
    constructor; intros. rewrite commutative, inverseRight; auto.
  Qed.
  
  (** We can get an abelian-group <Vadd,Vzero,Vopp> *)
  #[export] Instance vs_vadd_AGroup : AGroup Vadd 0 Vopp.
  Proof.
    repeat constructor; intros;
      try apply vs_vaddA;
      try apply vs_vadd_0_l;
      try apply vs_vadd_0_r;
      try apply vs_vadd_vopp_l;
      try apply vs_vadd_vopp_r;
      try apply vs_vaddC.
  Qed.

  (** Cancellation law *)
  Theorem vs_cancel_l : forall u v w, u + v = u + w -> v = w.
  Proof. intros. apply group_cancel_l in H; auto. Qed.
  Theorem vs_cancel_r : forall u v w, v + u = w + u -> v = w.
  Proof. intros. apply group_cancel_r in H; auto. Qed.
  
  (** Vzero is unique *)
  Theorem vs_vzero_uniq_l : forall v0, (forall v, v0 + v = v) -> v0 = 0.
  Proof. intros. apply group_id_uniq_l; auto. Qed.
  Theorem vs_vzero_uniq_r : forall v0, (forall v, v + v0 = v) -> v0 = 0.
  Proof. intros. apply group_id_uniq_r; auto. Qed.

  (** (-v) is unique *)
  Theorem vs_vopp_uniq_l : forall v v', v + v' = 0 -> -v = v'.
  Proof. intros. eapply group_opp_uniq_l; auto. Qed.
  Theorem vs_vopp_uniq_r : forall v v', v' + v = 0 -> -v = v'.
  Proof. intros. eapply group_opp_uniq_r; auto. Qed.
  
  (** 0 .* v = 0 *)
  Theorem vs_vcmul_0_l : forall v : V, 0%A \.* v = 0.
  Proof.
    (* 0 * v = (0 + 0) * v = 0*v + 0*v, 0 * v = 0 + 0*v,
       Hence, 0*v + 0*v = 0 + 0*v. By the cancellation law, then ... *)
    intros.
    assert (0%A \.* v = 0%A \.* v + 0%A \.* v).
    { rewrite <- vs_vcmul_aadd. f_equal. group. }
    assert (0%A \.* v = 0%A \.* v + 0). group.
    rewrite H in H0 at 1. apply vs_cancel_l in H0. auto.
  Qed.

  (** a .* 0 = 0 *)
  Theorem vs_vcmul_0_r : forall a : A, a \.* 0 = 0.
  Proof.
    (* a*0 = a*0 + 0, a*0 = a*(0 + 0) = a*0 + a*0,
       Thus, a*0 + 0 = a*0 + a*0. By the cancellation law, then ... *)
    intros.
    assert (a \.* 0 = a \.* 0 + a \.* 0).
    { rewrite <- vs_vcmul_vadd. f_equal. group. }
    assert (a \.* 0 = a \.* 0 + 0). group.
    rewrite H in H0 at 1. apply vs_cancel_l in H0. auto.
  Qed.

  (** u + v = w -> u = w + - v *)
  Theorem vs_sol_l : forall u v w, u + v = w -> u = w + - v.
  Proof. intros. apply group_sol_l; auto. Qed.

  (** u + v = w -> v = - u + w *)
  Theorem vs_sol_r : forall u v w, u + v = w -> v = - u + w.
  Proof. intros. apply group_sol_r; auto. Qed.
  
  (** (- c) * v = - (c * v) *)
  Theorem vs_vcmul_opp : forall c v, (- c)%A \.* v = - (c \.* v).
  Proof.
    (* c*v + (-c)*v = 0, So, ... *)
    intros. symmetry. apply vs_vopp_uniq_l; auto.
    rewrite <- vs_vcmul_aadd. rewrite inverseRight, vs_vcmul_0_l; auto.
  Qed.
  
  (** c * (- v) = - (c * v) *)
  Theorem vs_vcmul_vopp : forall c v, c \.* (- v) = - (c \.* v).
  Proof.
    (* c*v + c*(-v) = 0, So, ... *)
    intros. symmetry. apply vs_vopp_uniq_l; auto.
    rewrite <- vs_vcmul_vadd. rewrite inverseRight, vs_vcmul_0_r; auto.
  Qed.
  
  (** (-1) * v = - v *)
  Theorem vs_vcmul_opp1 : forall v : V, (-(1))%A \.* v = -v.
  Proof. intros. rewrite vs_vcmul_opp, vs_vcmul_1_l; auto. Qed.

  (** v - v = 0 *)
  Theorem vs_vsub_self : forall v : V, v - v = 0.
  Proof. intros. group. Qed.

  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.
    
    (** a .* v = 0 -> a = 0 \/ v = 0 *)
    Theorem vs_vcmul_eq0_imply_k0_or_v0 : forall a v, a \.* v = 0 -> a = 0%A \/ v = 0.
    Proof.
      intros. destruct (Aeqdec a 0%A); auto. right.
      assert (/a \.* (a \.* v) = /a \.* 0).
      { rewrite H. auto. }
      rewrite <- vs_vcmul_assoc in H0.
      rewrite field_mulInvL in H0; auto. rewrite vs_vcmul_1_l, vs_vcmul_0_r in H0. auto.
    Qed.

    (** a <> 0 -> v <> 0 -> a .* v <> 0 *)
    Corollary vs_vcmul_neq0_if_neq0_neq0 : forall a v, a <> 0%A -> v <> 0 -> a \.* v <> 0.
    Proof.
      intros. intro. apply vs_vcmul_eq0_imply_k0_or_v0 in H1. destruct H1; auto.
    Qed.
  End AeqDec.
  
End props.



(* ===================================================================== *)
(** ** Vector Subspace *)

(* A subset of vectors H ⊆ V from a vector space (V,F) forms a vector subspace if 
   the following three properties hold:
   1. The zero vector of V is in H
   2. H is closed under vector addition.
   3. H is closed under scalar multiplication.
 *)

Section SubVectorSpace.
  Context `{VS : VectorSpace}.
  Context (P : V -> Prop).

  Let H := {v | P v}.
  Context (Hzero_keep : P Vzero).
  Context (Hadd_closed : forall u v : H, P (Vadd u.val v.val)).
  Context (Hcmul_closed : forall (a : A) (v : H), P (Vcmul a v.val)).
  
  Let Hadd (u v : H) : H := exist _ (Vadd u.val v.val) (Hadd_closed _ _).
  Let Hzero : H := exist _ Vzero Hzero_keep.
  Let Hcmul (a : A) (v : H) : H := exist _ (Vcmul a v.val) (Hcmul_closed _ _).
  Let Hopp (v : H) : H.
    refine (exist _ (Vopp v.val) _). rewrite <- vs_vcmul_opp1. apply Hcmul_closed.
  Defined.
  
  #[export] Instance SubVectorSpace : VectorSpace Hadd Hzero Hopp Hcmul.
  Proof.
    repeat constructor; unfold Hadd, Hcmul; intros.
    - apply sig_eq_iff. apply commutative.
    - apply sig_eq_iff. simpl. apply associative.
    - destruct a. apply sig_eq_iff. simpl. apply identityRight.
    - destruct a. apply sig_eq_iff. simpl. apply vs_vadd_vopp_r.
    - destruct v. apply sig_eq_iff. simpl. apply vs_vcmul_1_l.
    - destruct v. apply sig_eq_iff. simpl. apply vs_vcmul_assoc.
    - destruct v. apply sig_eq_iff. simpl. apply vs_vcmul_aadd.
    - destruct v. apply sig_eq_iff. simpl. apply vs_vcmul_vadd.
  Qed.
End SubVectorSpace.

(* Class SubVectorSpace `{VS : VectorSpace} (P : V -> Prop) := *)
(*   { *)
(*     svs_zero : exists Hzero : H, h2v Hzero = Vzero; *)
(*     svs_vadd_closed : forall u v : H, exists w, Vadd (h2v u) (h2v v) = h2v w; *)
(*     svs_vcmul_closed : forall (a : A) (v : H), exists w, Vcmul a (h2v v) = h2v w; *)
(*   }. *)

(* Section props. *)
(*   Context `{svs : SubVectorSpace}. *)
(*   Notation Hadd := (fun u v => Vadd (h2v u) (h2v v)). *)
(*   Notation Hcmul := (fun a v => Vcmul a (h2v v)). *)
(* End props. *)


(* ===================================================================== *)
(** ** Linearly combination *)
Section vlcomb.
  Context `{HVectorSpace : VectorSpace}.

  Notation "0" := Azero : A_scope.
  Notation vzero := (vzero 0%A).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.

  Infix "+" := Vadd : VectorSpace_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation "- v" := (Vopp v) : VectorSpace_scope.
  Notation Vsub u v := (u + -v).
  Infix "-" := Vsub : VectorSpace_scope.
  Notation vsum := (@vsum _ Vadd 0 _).
  
  (* Linear combination of v1,v2, ..., vn by coefficients c1,c2, ..., cn *)
  Definition vlcomb {n} (cs : @vec A n) (vs : @vec V n) : V :=
    vsum (vmap2 Vcmul cs vs).

  (* 0 * v1 + 0 * v2 + ... + 0 * vn = 0 *)
  Lemma vlcomb_c0_eq0 : forall {n} (vs : @vec V n), vlcomb vzero vs = 0.
  Proof.
    intros. unfold vlcomb. apply vsum_eq0. intros. rewrite vnth_vmap2.
    rewrite vnth_vzero. rewrite vs_vcmul_0_l. auto.
  Qed.

  (** (c1 + c2) * v = c1 * v + c2 * v *)
  Lemma vlcomb_coef_add : forall {n} (vs : @vec V n) c1 c2,
      vlcomb (c1 + c2)%V vs = vlcomb c1 vs + vlcomb c2 vs.
  Proof.
    intros. unfold vlcomb. apply vsum_add. intros. rewrite !vnth_vmap2.
    rewrite vs_vcmul_aadd. auto.
  Qed.

  (** (- c) * v = - (c * v) *)
  Lemma vlcomb_coef_opp : forall {n} (vs : @vec V n) c,
      vlcomb (- c)%V vs = - (vlcomb c vs).
  Proof.
    intros. unfold vlcomb. apply vsum_opp. intros. rewrite !vnth_vmap2.
    rewrite vnth_vopp. rewrite vs_vcmul_opp. auto.
  Qed.

  (** (c1 - c2) * v = c1 * v - c2 * v *)
  Lemma vlcomb_coef_sub : forall {n} (vs : @vec V n) c1 c2,
      vlcomb (c1 - c2)%V vs = vlcomb c1 vs - vlcomb c2 vs.
  Proof.
    intros. unfold vsub. rewrite vlcomb_coef_add. rewrite vlcomb_coef_opp. auto.
  Qed.
  
End vlcomb.


(** ** 向量(向量组)可由向量组“线性表示(线性表出)”  *)
Section vrepr.
  Context `{HVectorSpace : VectorSpace}.

  Notation "0" := Azero : A_scope.
  Notation vzero := (vzero 0%A).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.

  Infix "+" := Vadd : VectorSpace_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation "- v" := (Vopp v) : VectorSpace_scope.
  Notation Vsub u v := (u + -v).
  Infix "-" := Vsub : VectorSpace_scope.
  Notation vsum := (@vsum _ Vadd 0 _).
  Notation vlcomb := (@vlcomb _ _ Vadd Vzero Vcmul).

  (* 向量组 vs 可线性表示向量 u *)
  Definition vlrepr {n} (vs : @vec V n) (u : V) : Prop :=
    exists (cs : @vec A n), u = vlcomb cs vs.

  (* 向量组 vs 可线性表示向量组 us  *)
  Definition vlreprs {r s} (vs : @vec V s) (us : @vec V r) : Prop :=
    vforall us (vlrepr vs).

  (* vreprs是等价关系 *)
  (* Lemma vreprs_refl : forall {r} (vs : @vec V r), vreprs vs vs. *)
  (* Proof. *)
  (*   intros. hnf. intros. rewrite vnth_vmap. hnf. *)
  (*   exists (fun j => if finEqdec i j then Aone else Azero). *)
  (*   unfold vlcomb. rewrite vsum_unique with (a:=vs i)(i:=i); auto. *)
  (*   - rewrite vnth_vmap2. destruct (finEqdec i i). apply vs_vcmul_1_l. easy. *)
  (*   - intros. rewrite vnth_vmap2. destruct (finEqdec i j). *)
  (*     subst. easy. apply vs_vcmul_0_l. *)
  (* Qed. *)

  (* Lemma vreprs_sym : forall {r s} (us : @vec V r) (vs : @vec V s), *)
  (*     vreprs us vs -> vreprs vs us. *)
  (* Proof. *)
  (*   intros. destruct (lt_eq_lt_dec r s) as [[Hlt|Heq]|Hgt]. *)
  (*   -  *)
  (*   destruct (r ??< s). *)
  (*   hnf. hnf in H. intros. rewrite vnth_vmap. *)
    
  (*   hnf. *)
  (*   exists (fun j => if finEqdec i j then Aone else Azero). *)
  (*   unfold vlcomb. rewrite vsum_unique with (a:=vs i)(i:=i); auto. *)
  (*   - rewrite vnth_vmap2. destruct (finEqdec i i). apply vs_vcmul_1_l. easy. *)
  (*   - intros. rewrite vnth_vmap2. destruct (finEqdec i j). *)
  (*     subst. easy. apply vs_vcmul_0_l. *)
  (* Qed. *)
  
End vrepr.
          
(* 延长组相关，则缩短组必相关 *)
(* 缩短组无关，则延长组必无关   *)
(* 列多可由列少线性表出，则列多相关 *)

(* ===================================================================== *)
(** ** Linear Dependent, Linear Independent *)
Section vldep.
  Context `{HVectorSpace : VectorSpace}.
  Context {AeqDec : Dec (@eq A)}.

  Notation "0" := Azero : A_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation vsum := (@vsum _ Vadd 0 _).
  Notation vzero := (vzero 0%A).
  Notation vsub := (@vsub _ Aadd Aopp).
  Infix "-" := vsub : vec_scope.
  Notation vlcomb := (@vlcomb _ _ Vadd Vzero Vcmul).

  (* Vectors v1, v2, ..., vn are linearly dependent *)
  (* 存在一组不全为0的系数，使得线性组合为0 *)
  Definition vldep {n} (vs : @vec V n) : Prop :=
    exists (cs : @vec A n), cs <> vzero /\ vlcomb cs vs = 0.

  (* Vectors v1, v2, ..., vn are linearly independent *)
  Definition vlindep {n} (vs : @vec V n) : Prop := ~ (vldep vs).

  (* 向量线性无关，iff，线性组合的方程组只有唯一的零解。即：只要有解，必都为0。*)
  Lemma vlindep_iff_unique0 : forall {n} (vs : @vec V n),
      vlindep vs <-> forall cs, vlcomb cs vs = 0 -> cs = vzero.
  Proof.
    intros. unfold vlindep, vldep. split; intros.
    - apply not_ex_all_not with (n:=cs) in H. apply not_and_or in H.
      destruct H; try easy. apply NNPP in H. auto.
    - intro. destruct H0 as [c [H0 H0']]. specialize (H c H0'). easy.
  Qed.

  (** If two linearly independent vectors represents a same vector, then the 
      coefficents must be unique *)
  Lemma vlindep_imply_coef_uniq : forall {n} (vs : @vec V n),
      vlindep vs -> (forall c1 c2, vlcomb c1 vs = vlcomb c2 vs -> c1 = c2).
  Proof.
    intros. rewrite vlindep_iff_unique0 in H. specialize (H (c1 - c2)).
    apply vsub_eq0_iff_eq. apply H. rewrite vlcomb_coef_sub. rewrite H0.
    apply vs_vadd_vopp_r.
  Qed.

End vldep.


(* ===================================================================== *)
(** ** Span *)
Section vspan.
  Context `{HVectorSpace : VectorSpace}.
  Notation vlcomb := (@vlcomb _ _ Vadd Vzero Vcmul).

  (** Elements v1,v2,...,vn of V are said to span V *)
  Definition vspan {n} (vs : @vec V n) : Prop :=
    forall (u : V), (exists (cs : @vec A n), vlcomb cs vs = u).
End vspan.


(* ===================================================================== *)
(** ** Basis *)
Section vbasis.
  Context `{HVectorSpace : VectorSpace}.
  Notation vlcomb := (@vlcomb _ _ Vadd Vzero Vcmul).
  Notation vlindep := (@vlindep _ Azero _ Vadd Vzero Vcmul).
  Notation vspan := (@vspan _ _ Vadd Vzero Vcmul).

  (** Elements v1,v2,...,vn of V are said to consistute a basis of V *)
  Definition vbasis {n} (vs : @vec V n) : Prop :=
    vlindep vs /\ vspan vs.

  (** Elements v1, v2, . . . , vn of a vector space V constitute a basis of 
      that vector space if and only if, given any element u of V , there exist 
      uniquely determined scalars c1, c2, . . . , cn such that
      u = c1v1 + c2v2 + · · · + cnvn  *)
  Theorem vbasis_if_unique_cs : forall {n} (vs : @vec V n),
      vbasis vs <-> forall u : V, exists! (cs : @vec A n), vlcomb cs vs = u.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [H H']. hnf in H'. specialize (H' u).
      rewrite <- unique_existence. split; auto.
      hnf. intros c1 c2 H1 H2. rewrite <- H2 in H1.
      apply vlindep_imply_coef_uniq in H1; auto.
    - hnf. split.
      + apply vlindep_iff_unique0. intros. specialize (H Vzero).
        apply unique_existence in H. destruct H. hnf in H1.
        erewrite H1; auto. apply vlcomb_c0_eq0.
      + unfold vspan. intros. specialize (H u). destruct H as [c [H H']].
        exists c; auto.
  Qed.
    
End vbasis.


(** ** Linear Transformations *)
Section vltrans.
  Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
  Context `(HV : @VectorSpace A Aadd Azero Aopp Amul Aone Ainv HField
                   V Vadd Vzero Vopp Vcmul).
  Context `(HW : @VectorSpace A Aadd Azero Aopp Amul Aone Ainv HField
                   W Wadd Wzero Wopp Wcmul).
  Notation Vsub u v := (Vadd u (Vopp v)).
  Notation Wsub u v := (Wadd u (Wopp v)).

  (* Let V and W be vector spaces over some field K. A function T : V → W is said 
     to be a linear transformation if T (u + v) = T (u) + T (v) and T (cv) = cT (v) 
     for all elements u and v of V and for all elements c of K. *)
  Definition vltrans (T : V -> W) : Prop :=
    (forall u v, T (Vadd u v) = Wadd (T u) (T v)) /\ (forall v c, T (Vcmul c v) = Wcmul c (T v)).

  (** vltrans T -> T(u + v) = T(u) + T(v) *)
  Lemma vltrans_add : forall (T : V -> W),
      vltrans T -> forall u v, T (Vadd u v) = Wadd (T u) (T v).
  Proof. intros. hnf in H. destruct H; auto. Qed.

  (** vltrans T -> T(a * v) = a * T(v) *)
  Lemma vltrans_cmul : forall (T : V -> W),
      vltrans T -> forall a v, T (Vcmul a v) = Wcmul a (T v).
  Proof. intros. hnf in H. destruct H; auto. Qed.

  (** vltrans T -> T(- v) = - T(v) *)
  Lemma vltrans_opp : forall (T : V -> W),
      vltrans T -> forall v, T (Vopp v) = Wopp (T v).
  Proof.
    intros. hnf in H. destruct H; auto.
    rewrite <- !vs_vcmul_opp1. rewrite H0. rewrite vs_vcmul_opp1. auto.
  Qed.

  (** vltrans T -> T(u - v) = T(u) - T(v) *)
  Lemma vltrans_sub : forall (T : V -> W),
      vltrans T -> forall u v, T (Vsub u v) = Wsub (T u) (T v).
  Proof.
    intros. hnf in H. rewrite vltrans_add; auto. rewrite vltrans_opp; auto.
  Qed.
  
  (** vltrans T -> T(0) = 0 *)
  Lemma vltrans_zero : forall (T : V -> W), vltrans T -> T Vzero = Wzero.
  Proof.
    intros. hnf in H.
    replace (Vzero) with (Vsub Vzero Vzero) by group.
    rewrite vltrans_sub; auto. group.
  Qed.
    
  (** T (c1v1 + c2v2 + · · · + cnvn) 
      = T (c1v1) + T (c2v2) + · · · + T (cnvn)
      = c1w1 + c2w2 + · · · + cnwn *)
  Lemma vltrans_linear : forall {n} (T : V -> W) (cs : @vec A n)
                           (v : @vec V n) (w : @vec W n),
      vltrans T -> (forall i, w$i = T(v$i)) ->
      T (vlcomb (Vadd:=Vadd)(Vzero:=Vzero)(Vcmul:=Vcmul) cs v) =
        vlcomb (Vadd:=Wadd)(Vzero:=Wzero)(Vcmul:=Wcmul) cs w.
  Proof.
    intros. unfold vlcomb.
    apply eq_trans with
      (vsum (Aadd:=Wadd)(Azero:=Wzero) (vmap T (vmap2 Vcmul cs v))).
    - rewrite <- (vsum_vmap (Aadd:=Vadd)(Azero:=Vzero)); auto.
      apply vltrans_zero; auto. apply vltrans_add; auto.
    - apply vsum_eq; intros. rewrite !vnth_vmap, !vnth_vmap2.
      rewrite vltrans_cmul; auto. rewrite H0. auto.
  Qed.
  
End vltrans.


(** ** 向量的范数，赋范向量空间 *)
