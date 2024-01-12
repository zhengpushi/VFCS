(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector implemented with Record-List model
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. High-dimensional vectors can be expressed by repeating the `vec` structure.
  2. Four forms of a "list/function/vector"
     
     FF --- vec
     | \  / |
     |  \/  |
     |  /\  |
     | /  \ |
     F ---- list
     
     FF: Fin-indexing-Function,
     F : natural-number-indexing-Function
     vec : vector has given length, made be list
     list : a list of data
     
     These forms have conversion functions between each other.
 *)


Require Export TupleExt Hierarchy.
Require Export ListExt.
Require Export Fin Sequence Fsequence.
Require Import Extraction.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.


(* ======================================================================= *)
(** ** Definition of vector type [vec] *)
Section def.
  Context {A : Type}.

  (* structural-style *)
  (* Record vec_old (n : nat) :=  *)
  (*   mkvec { *)
  (*       vdata : list A; *)
  (*       vlength : length vdata = n; *)
  (*     }. *)

  (* functional-style *)
  Definition vec (n : nat) := fin n -> A.
  
End def.


(* ======================================================================= *)
(** ** Equality of vector *)

Lemma veq_iff_vnth : forall {A} {n} (V1 V2 : @vec A n),
    V1 = V2 <-> forall (i : fin n), V1 i = V2 i.
Proof. intros. unfold vec in *. apply ffeq_iff_nth. Qed.

Lemma veq_iff_vnth_nat : forall {A} {n} (V1 V2 : @vec A n),
    V1 = V2 <-> forall (i : nat) (H: i < n), V1 (nat2fin i H) = V2 (nat2fin i H).
Proof. intros. unfold vec in *. apply ffeq_iff_nth_nat. Qed.

#[export] Instance veq_dec : forall {A n} (Azero : A),
    Dec (@eq A) -> Dec (@eq (@vec A n)).
Proof.
  intros. constructor. intros.
  apply (@fseqeq_dec _ Azero). apply Aeqdec.
Qed.


(* ======================================================================= *)
(** ** Get element of a vector *)

Notation vnth A n := (fun (V: fin n -> A) (i:fin n) => V i).

Notation "V $ i " := (vnth _ _ V i) : vec_scope.

(* Note that: these notatiosn are dangerous.
   For example, `@nat2finS 3 0` ~ `@nat2finS 3 3` are all expected index.
   but `@nat2finS 3 4` ~ `...` will become `@nat2finS 3 0`, its error index.
 *)
Notation "V .1" := (V $ nat2finS 0) : vec_scope.
Notation "V .2" := (V $ nat2finS 1) : vec_scope.
Notation "V .3" := (V $ nat2finS 2) : vec_scope.
Notation "V .4" := (V $ nat2finS 3) : vec_scope.


(** ** Vector with same elements *)
Section vrepeat.
  Context {A} {Azero : A} {n : nat}.
  
  Definition vrepeat (a : A) : @vec A n := fun _ => a.

  Lemma vnth_vrepeat : forall a i, vrepeat a $ i = a.
  Proof. intros. unfold vrepeat; auto. Qed.

End vrepeat.


(** ** Zero vector *)
Section vzero.
  Context {A} (Azero : A) {n : nat}.
  
  Definition vzero : @vec A n := vrepeat Azero.

  Lemma vnth_vzero : forall i, vzero $ i = Azero.
  Proof. intros. apply vnth_vrepeat. Qed.

End vzero.


(** ** Convert between nat-index-function (f) and vector (v) *)
Section f2v_v2f.
  Context {A} (Azero : A).

  Definition f2v {n} (f : nat -> A) : @vec A n := f2ff f.
  
  (** (f2v f)[i] = f i *)
  Lemma vnth_f2v : forall {n} f i, (@f2v n f)$i = f (fin2nat i).
  Proof. intros. unfold f2v. rewrite nth_f2ff; auto. Qed.
    
  Definition v2f {n} (V : vec n) : (nat -> A) := @ff2f _ Azero _ V.

  (* (v2f V)[i] = V[i] *)
  Lemma nth_v2f : forall {n} (V : vec n) i (H:i<n), (v2f V) i = V$(nat2fin i H).
  Proof. intros. unfold v2f. erewrite nth_ff2f; auto. Qed.

  Lemma f2v_v2f_id : forall {n} (V : vec n), (@f2v n (v2f V)) = V.
  Proof. intros. unfold f2v,v2f. apply f2ff_ff2f_id. Qed.

  Lemma v2f_f2v_id : forall {n} (f : nat -> A) i, i < n -> v2f (@f2v n f) i = f i.
  Proof. intros. unfold v2f,f2v; simpl. apply ff2f_f2ff_id; auto. Qed.

End f2v_v2f.


(** ** Convert between list and vector *)
Section l2v_v2l.
  Context {A : Type} (Azero : A).

  Definition l2v (n : nat) (l : list A) : vec n := @l2ff _ Azero _ l.

  Lemma vnth_l2v : forall {n} (l : list A) i, (l2v n l) $ i = nth (fin2nat i) l Azero.
  Proof. intros. unfold l2v. rewrite nth_l2ff. auto. Qed.
  
  Lemma l2v_inj : forall {n} (l1 l2 : list A),
      length l1 = n -> length l2 = n ->
      l2v n l1 = l2v n l2 -> l1 = l2.
  Proof. intros. unfold l2v. apply l2ff_inj in H1; auto. Qed.
  
  Lemma l2v_surj : forall {n} (V : vec n), (exists l, l2v n l = V).
  Proof. intros. unfold l2v,vec in *. apply l2ff_surj. Qed.

  Definition v2l {n} (V : vec n) : list A := ff2l V.

  Lemma v2l_length : forall {n} (V : vec n), length (v2l V) = n.
  Proof. intros. unfold v2l. apply ff2l_length. Qed.

  Lemma v2l_inj : forall {n} (V1 V2 : vec n), v2l V1 = v2l V2 -> V1 = V2.
  Proof. intros. unfold v2l in *. apply ff2l_inj in H; auto. Qed.

  Lemma v2l_surj : forall {n} (l : list A), length l = n -> (exists V : vec n, v2l V = l).
  Proof. intros. unfold v2l. apply (@ff2l_surj _ Azero); auto. Qed.

  Lemma l2v_v2l_id : forall {n} (V : vec n), (@l2v n (v2l V)) = V.
  Proof. intros. unfold l2v,v2l. apply l2ff_ff2l_id. Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> v2l (@l2v n l) = l.
  Proof. intros. unfold l2v,v2l. apply ff2l_l2ff_id; auto. Qed.

  Lemma nth_v2l : forall {n} (V : vec n) (i : nat) (H: i < n),
      i < n -> nth i (v2l V) Azero = V (nat2fin i H).
  Proof. intros. unfold v2l. rewrite nth_ff2l with (H:=H). f_equal. Qed.

End l2v_v2l.


(** ** vector with specific size *)
Section vec_specific.
  Context {A} {Azero : A}.
  Variable a1 a2 a3 a4 : A.
  
  Definition mkvec0 : @vec A 0 := vzero Azero. (* anything is ok *)
  Definition mkvec1 : @vec A 1 := l2v Azero _ [a1].
  Definition mkvec2 : @vec A 2 := l2v Azero _ [a1;a2].
  Definition mkvec3 : @vec A 3 := l2v Azero _ [a1;a2;a3].
  Definition mkvec4 : @vec A 4 := l2v Azero _ [a1;a2;a3;a4].
End vec_specific.

  
(** ** Construct vector with one element and a vector *)
Section vcons.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).

  (* cons at head *)
  (* Definition vconsH_old {n} (a : A) (V : @vec A n) : @vec A (S n). *)
  (*   intro i. destruct (0 ??< fin2nat i). refine (V (fin2Pred i l)). apply a. *)
  (* Defined. *)

  Definition vconsH {n} (a : A) (V : @vec A n) : @vec A (S n) :=
    f2v (fun i => if 0 ??= i then a else (v2f V (pred i))).

  (* i = 0 -> [a;V].i = a *)
  Lemma nth_vconsH_idx_0 : forall {n} a (V : @vec A n) i,
      i = 0 -> v2f (vconsH a V) i = a.
  Proof. intros. subst. unfold vconsH,v2f,ff2f,f2v,f2ff; simpl. auto. Qed.

  Lemma vnth_vconsH_idx_0 : forall {n} a (V : @vec A n) i,
      i = fin0 -> (vconsH a V)$i = a.
  Proof.
    intros. unfold vconsH,f2v,v2f,f2ff,ff2f. destruct i; simpl.
    apply fin_eq_iff in H. subst; simpl. auto.
  Qed.

  (* 0 < i < n -> [a;V].i = V.(pred i) *)
  Lemma nth_vconsH_idx_gt0 : forall {n} a (V : @vec A n) i,
      0 < i < n -> v2f (vconsH a V) i = v2f V (pred i).
  Proof.
    intros. unfold vconsH,v2f,f2v,ff2f,f2ff; simpl.
    destruct (i ??< S n),(pred i ??< n);try lia. destruct i; auto. lia.
  Qed.
    
  Lemma vnth_vconsH_idx_gt0 : forall {n} a (V : @vec A n) i (H: 0 < fin2nat i),
      (vconsH a V)$i = V$(fin2PredRangePred i H).
  Proof.
    intros. unfold vconsH,f2v,f2ff. destruct i; simpl in *.
    destruct x; subst; simpl; try lia. erewrite nth_v2f.  f_equal.
    apply fin_eq_iff; auto. Unshelve. lia.
  Qed.

  (* cons at tail *)
  (* Definition vconsT_old {n} (V : @vec A n) (a : A) : @vec A (S n). *)
  (*   intro i. destruct (fin2nat i ??< n). refine (V (fin2ExtendPred i l)). apply a. *)
  (* Defined. *)

  Definition vconsT {n} (V : @vec A n) (a : A) : @vec A (S n) :=
    f2v (fun i => if i ??< n then v2f V i else a).

  (* i = n -> [V;a].i = a *)
  Lemma nth_vconsT_idx_n : forall {n} a (V : @vec A n) i,
      i = n -> v2f (vconsT V a) i = a.
  Proof.
    intros. subst. unfold vconsT,v2f,ff2f,f2v,f2ff; simpl.
    destruct (_??<_); try lia. destruct (_??<_);auto. lia.
  Qed.

  Lemma vnth_vconsT_idx_n : forall {n} a (V : @vec A n) i,
      fin2nat i = n -> (vconsT V a)$i = a.
  Proof.
    intros. unfold vconsT,v2f,ff2f,f2v,f2ff; simpl.
    destruct (_??<_); auto; try lia.
  Qed.

  (* 0 < i < n -> [a;V].i = V.(pred i) *)
  Lemma nth_vconsT_idx_lt_n : forall {n} a (V : @vec A n) i,
      i < n -> v2f (vconsT V a) i = v2f V i.
  Proof.
    intros. unfold vconsT,f2v,v2f,f2ff,ff2f.
    destruct (_??<_),(_??<_); simpl; auto; try lia.
    rewrite fin2nat_nat2fin_id in *. lia.
  Qed.

  Lemma vnth_vconsT_idx_lt_n : forall {n} a (V : @vec A n) i (H: fin2nat i < n),
      (vconsT V a)$i = V (fin2PredRange i H).
  Proof.
    intros. unfold vconsT,f2v,v2f,f2ff,ff2f.
    destruct (_??<_); simpl; try lia. f_equal. apply fin_eq_iff; auto.
  Qed.
    
End vcons.

  
(** ** Construct vector with two vectors *)
Section vapp.
  Context {A} {Azero : A}.

  (* Append *)
  Definition vapp {n1 n2} (V1:@vec A n1) (V2:@vec A n2) : @vec A (n1 + n2) :=
    f2v (fun i => if i <? n1 then v2f Azero V1 i else v2f Azero V2 (n1 + i)).
  
End vapp.


(** ** Vector of fin sequence *)
Section vfinseq.

  Definition vfinseq (n : nat) : @vec (fin n) n := (fun i: fin n => i).

  Lemma vnth_vfinseq : forall {n} i, (vfinseq n)$i = i.
  Proof. intros. unfold vfinseq. auto. Qed.
  
End vfinseq.


(** ** Mapping of a vector *)
Section vmap.
  Context {A B} (Azero : A) (Bzero : B).
  Variable f : A -> B.
  Hypotheses f_keep0 : Bzero = f Azero.
  
  Definition vmap {n} (V : @vec A n) : @vec B n := fun i => f (V i).

  Lemma vnth_vmap : forall {n} (V : vec n) i, (vmap V)$i = f(V$i).
  Proof. intros. unfold vmap; auto. Qed.

End vmap.


(** ** Mapping of two vectors *)
Section vmap2.
  Context {A B C} (Azero : A) (Bzero : B) (Czero : C).
  Variable f : A -> B -> C.
  Hypotheses f_keep0 : Czero = f Azero Bzero.
  
  Definition vmap2 {n} (V1 : @vec A n) (V2 : @vec B n) : @vec C n :=
    fun i => f (V1$i) (V2$i).

  Lemma vnth_vmap2 : forall {n} (V1 V2 : vec n) i, (vmap2 V1 V2) i = f (V1$i) (V2$i).
  Proof. intros. unfold vmap2; auto. Qed.

  Lemma vmap2_eq_vmap : forall {n} (V1 : @vec A n) (V2 : @vec B n),
      vmap2 V1 V2 = vmap (fun i => f (V1$i) (V2$i)) (fun i => i).
  Proof. intros. unfold vmap2. auto. Qed.
  
End vmap2.


(** ** vmap2 on same type *)
Section vmap2_sametype.
  Context `{ASGroup}.
  
  Lemma vmap2_comm : forall {n} (V1 V2 : vec n),
      vmap2 Aadd V1 V2 = vmap2 Aadd V2 V1.
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. asemigroup. Qed.
  
  Lemma vmap2_assoc : forall {n} (V1 V2 V3 : vec n),
      vmap2 Aadd (vmap2 Aadd V1 V2) V3 = vmap2 Aadd V1 (vmap2 Aadd V2 V3).
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. asemigroup. Qed.
  
End vmap2_sametype.


(** ** Sum of a vector *)
Section vsum.
  Context `{AM : AMonoid}.
  Infix "+" := Aadd.
  Notation seqsum := (@seqsum _ Aadd Azero).

  Definition vsum {n} (V : @vec A n) := @fseqsum _ Aadd Azero _ V.
  (* Notation "'\sum' f" := (vsum (ff2v f)). *)

  (* (∀ i, V1[i] = V2[i]) -> ΣV1 = ΣV2  *)
  Lemma vsum_eq : forall {n} (V1 V2 : @vec A n), (forall i, V1$i = V2$i) -> vsum V1 = vsum V2.
  Proof. intros. apply fseqsum_eq. auto. Qed.

  (** Σ(ai+bi) = Σ(ai) + Σ(bi) *)
  Lemma vsum_add : forall {n} (V V1 V2 : @vec A n),
      (forall i, V$i = V1$i + V2$i) -> vsum V = vsum V1 + vsum V2.
  Proof. intros. unfold vsum. apply fseqsum_add. auto. Qed.

  
  Context `{G:Group A Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.
  
  (** Σ(-ai) = - Σ(ai) *)
  Lemma vsum_opp : forall {n} (V1 V2 : @vec A n),
      (forall i, V1$i = - V2$i) -> vsum V1 = - vsum V2.
  Proof. intros. unfold vsum. apply fseqsum_opp; auto. Qed.

  
  Context `{HARing:ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := (Amul) : A_scope.

  
  (* (** Σ(k * ai) = k * Σ(ai) *) *)
  Lemma vsum_cmul : forall {n} (V1 V2 : @vec A n) k,
      (forall i, V1$i = k * V2$i) -> vsum V1 = k * vsum V2.
  Proof. intros. unfold vsum. apply fseqsum_cmul. auto. Qed.

End vsum.


(** ** vector algebra *)
(* addition,opposition,subtraction, scalar multiplication, product *)
Section alg.

  (* Let's have an Abelian-Monoid *)
  Context `{AMonoid}.
  Infix "+" := Aadd : A_scope.
  Notation vec := (@vec A).
  Notation vzero := (vzero Azero).
  Notation vsum := (@vsum _ Aadd Azero).
  
  (** *** Vector addition *)
  Definition vadd {n} (V1 V2 : vec n) : vec n := vmap2 Aadd V1 V2.
  Infix "+" := vadd : vec_scope.

  Instance vadd_Associative : forall n, Associative (@vadd n).
  Proof. intros. constructor. apply vmap2_assoc. Qed.

  Instance vadd_Commutative : forall n, Commutative (@vadd n).
  Proof. intros. constructor. apply vmap2_comm. Qed.

  (** 0 + V = V *)
  Instance vadd_IdentityLeft : forall n, IdentityLeft (@vadd n) vzero.
  Proof.
    intros. constructor. intros. unfold vadd.
    apply veq_iff_vnth; intros. rewrite vnth_vmap2. group.
  Qed.

  (** V + 0 = V *)
  Instance vadd_IdentityRight : forall n, IdentityRight (@vadd n) vzero.
  Proof. intros. constructor. intros. rewrite commutative. apply identityLeft. Qed.
  
  Instance vadd_AMonoid : forall n, AMonoid (@vadd n) vzero.
  Proof.
    intros. repeat constructor; intros;
      try apply commutative;
      try apply associative;
      try apply identityLeft;
      try apply identityRight.
  Qed.

  (** (V1 + V2)[i] = V1[i] + V2[i] *)
  Lemma vnth_vadd : forall {n} (V1 V2 : vec n) i, (V1 + V2)$i = (V1$i + V2$i)%A.
  Proof. intros. unfold vadd. rewrite vnth_vmap2. auto. Qed.
  
  (** (V1 + V2) + V3 = (V1 + V3) + V2 *)
  Lemma vadd_perm : forall {n} (V1 V2 V3 : vec n), (V1 + V2) + V3 = (V1 + V3) + V2.
  Proof. intros. rewrite !associative. f_equal. apply commutative. Qed.

  
  (* Let's have an Abelian-Group *)
  Context `{AGroup A Aadd Azero}.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b)).
  Infix "-" := Asub : A_scope.

  (** *** Vector opposition *)
  
  Definition vopp {n} (V : vec n) : vec n := vmap Aopp V.
  Notation "- V" := (vopp V) : vec_scope.

  (** -V + V = 0 *)
  Instance vadd_InverseLeft : forall {n}, InverseLeft (@vadd n) vzero vopp.
  Proof. intros. constructor. intros. apply veq_iff_vnth; intros. cbv. group. Qed.

  (** V + -V = 0 *)
  Instance vadd_InverseRight : forall {n}, InverseRight (@vadd n) vzero vopp.
  Proof. intros. constructor. intros. apply veq_iff_vnth; intros. cbv. group. Qed.

  Instance vadd_AGroup : forall n, @AGroup (vec n) vadd vzero vopp.
  Proof.
    intros. repeat constructor;
      try apply associative;
      try apply identityLeft;
      try apply identityRight;
      try apply inverseLeft;
      try apply inverseRight;
      try apply commutative.
  Qed.

  (* Now, we ca use group theory on <vadd, vzero, vopp, vsub> *)

  (** - (- V) = V *)
  Lemma vopp_vopp : forall {n} (V : vec n), - (- V) = V.
  Proof. intros. apply group_inv_inv. Qed.

  (** -V1 = V2 <-> V1 = -V2 *)
  Lemma vopp_exchange : forall {n} (V1 V2 : vec n), -V1 = V2 <-> V1 = -V2.
  Proof. intros. split; intros; subst; rewrite vopp_vopp; auto. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n:nat}, - (@Vector.vzero _ Azero n) = vzero.
  Proof. intros. apply group_inv_id. Qed.

  (** - (V1 + V2) = (-V1) + (-V2) *)
  Lemma mopp_vadd : forall {n} (V1 V2 : vec n), - (V1 + V2) = (-V1) + (-V2).
  Proof. intros. rewrite group_inv_distr. apply commutative. Qed.
  
  
  (** *** Vatrix Subtraction *)
  
  Definition vsub {n} (V1 V2 : vec n) : vec n := V1 + (-V2).
  Infix "-" := vsub : vec_scope.

  (** V1 - V2 = - (V2 - V1) *)
  Lemma vsub_comm : forall {n} (V1 V2 : vec n), V1 - V2 = - (V2 - V1).
  Proof.
    intros. unfold vsub. rewrite group_inv_distr. rewrite group_inv_inv. auto.
  Qed.

  (** (V1 - V2) - V3 = V1 - (V2 + V3) *)
  Lemma vsub_assoc : forall {n} (V1 V2 V3 : vec n),
      (V1 - V2) - V3 = V1 - (V2 + V3).
  Proof.
    intros. unfold vsub. rewrite associative.
    f_equal. rewrite group_inv_distr. apply commutative.
  Qed.

  (** (V1 + V2) - V3 = V1 + (V2 - V3) *)
  Lemma vsub_assoc1 : forall {n} (V1 V2 V3 : vec n), (V1 + V2) - V3 = V1 + (V2 - V3).
  Proof. intros. unfold vsub. group. Qed.

  (** (V1 - V2) - V3 = V1 - (V3 - V2) *)
  Lemma vsub_assoc2 : forall {n} (V1 V2 V3 : vec n), (V1 - V2) - V3 = (V1 - V3) - V2.
  Proof. intros. unfold vsub. group. f_equal. apply commutative. Qed.
  
  (** 0 - V = - V *)
  Lemma vsub_0_l : forall {n} (V : vec n), vzero - V = - V.
  Proof. intros. unfold vsub. group. Qed.
  
  (** V - 0 = V *)
  Lemma vsub_0_r : forall {n} (V : vec n), V - vzero = V.
  Proof.
    intros. unfold vsub. rewrite (@group_inv_id _ vadd vzero); auto.
    group. apply vadd_AGroup.
  Qed.
  
  (** V - V = 0 *)
  Lemma vsub_self : forall {n} (V : vec n), V - V = vzero.
  Proof. intros. unfold vsub. group. Qed.

  
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  
  (** *** Vector scalar multiplication *)
  
  Definition vcmul {n : nat} (a : A) (V : vec n) : vec n := vmap (fun x => Amul a x) V.
  Infix "c*" := vcmul : vec_scope.

  (** (a * V)[i] = a * V[i] *)
  Lemma vnth_vcmul : forall {n} (V : vec n) a i, (a c* V)$i = a * (V$i).
  Proof. intros. cbv. ring. Qed.

  (** a1 * (a2 * V) = (a1 * a2) * V *)
  Lemma vcmul_assoc : forall {n} (V : vec n) a1 a2,
      a1 c* (a2 c* V) = (a1 * a2)%A c* V.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** a1 * (a2 * V) = a2 * (a1 * V) *)
  Lemma vcmul_perm : forall {n} (V : vec n) a1 a2,
      a1 c* (a2 c* V) = a2 c* (a1 c* V).
  Proof. intros. rewrite !vcmul_assoc. f_equal. ring. Qed.

  (** a * (V1 + V2) = (a * V1) + (a * V2) *)
  Lemma vcmul_vadd_distr : forall {n} a (V1 V2 : vec n),
      a c* (V1 + V2) = (a c* V1) + (a c* V2).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** (a1 + a2) * V = (a1 * V) + (a2 * V) *)
  Lemma vcmul_add_distr : forall {n} a1 a2 (V : vec n),
      (a1 + a2)%A c* V = (a1 c* V) + (a2 c* V).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* 0 c* V = vzero *)
  Lemma vcmul_0_l : forall {n} (V : vec n), Azero c* V = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** a c* vzero = vzero *)
  Lemma vcmul_0_r : forall {n} a, a c* vzero = (@Vector.vzero _ Azero n).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (* 1 c* A = A *)
  Lemma vcmul_1_l : forall {n} (V : vec n), Aone c* V = V.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (* (-a) * V = - (a * V) *)
  Lemma vcmul_opp : forall {n} a (V : vec n), (- a)%A c* V = - (a c* V).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (* a * (-V) = - (a * V) *)
  Lemma vcmul_vopp : forall {n} a (V : vec n), a c* (-V) = - (a c* V).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* Tips: these proofs show that, we can prove properties of vector by traditional
     derivation, or by computation, due to the Fin-Function model .*)
  
  (* (-a) * (- V) = a * V *)
  Lemma vcmul_opp_vopp : forall {n} a (V : vec n), (- a)%A c* (- V) = a c* V.
  Proof. intros. rewrite vcmul_vopp, vcmul_opp. rewrite vopp_vopp. auto. Qed.

  (** a c* (V1 - V2) = (a c* V1) - (a c* V2) *)
  Lemma vcmul_vsub : forall {n} a (V1 V2 : vec n),
      a c* (V1 - V2) = (a c* V1) - (a c* V2).
  Proof.
    intros. unfold vsub. rewrite vcmul_vadd_distr. rewrite vcmul_vopp. auto.
  Qed.

  
  (** *** Dot product *)

  Definition vdot {n : nat} (V1 V2 : vec n) : A := vsum (vmap2 Amul V1 V2).
  
  Notation "< V1 , V2 >" := (vdot V1 V2) : vec_scope.

  Lemma vdot_comm : forall {n} (V1 V2 : vec n), <V1, V2> = <V2, V1>.
  Proof. intros. apply vsum_eq; intros. rewrite vmap2_comm; auto. Qed.

  Lemma vdot_vadd_distr_l : forall {n} (V1 V2 V3 : vec n),
      <V1 + V2, V3> = (<V1, V3> + <V2, V3>)%A.
  Proof. intros. unfold vdot. apply vsum_add; intros. cbv. ring. Qed.

  Lemma vdot_vadd_distr_r : forall {n} (V1 V2 V3 : vec n),
      <V1, V2 + V3> = (<V1, V2> + <V1, V3>)%A.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vadd_distr_l. f_equal; apply vdot_comm.
  Qed.

  (* <0, V> = 0 *)
  Lemma vdot_0_l : forall {n} (V : vec n), <vzero, V> = Azero.
  Proof.
    intros. unfold vdot,vsum. apply fseqsum_eq0; intros.
    rewrite vnth_vmap2, vnth_vzero. ring.
  Qed.
  
  (* <V, 0> = 0 *)
  Lemma vdot_0_r : forall {n} (V : vec n), <V, vzero> = Azero.
  Proof. intros. rewrite vdot_comm, vdot_0_l; auto. Qed.

  (** <-V1, V2> = - <V1,V2> *)
  Lemma vdot_vopp_l : forall {n} (V1 V2 : vec n), < -V1, V2> = (- <V1,V2>)%A.
  Proof. intros. unfold vdot. apply vsum_opp; intros. cbv. ring. Qed.

  (** <V1, -V2> = - <V1,V2> *)
  Lemma vdot_vopp_r : forall {n} (V1 V2 : vec n), <V1, -V2> = (- <V1,V2>)%A.
  Proof. intros. rewrite vdot_comm, vdot_vopp_l, vdot_comm. auto. Qed.

  (* <k * V1, V2> = k * <V1, V2> *)
  Lemma vdot_vcmul_l : forall {n} (V1 V2 : vec n) k, <k c* V1, V2> = k * <V1,V2>.
  Proof. intros. unfold vdot. apply vsum_cmul; intros. cbv. ring. Qed.
  
  (* <V1, k * V2> = k * <V1, V2> *)
  Lemma vdot_vcmul_r : forall {n} (V1 V2 : vec n) k, <V1, k c* V2> = k * <V1,V2>.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vcmul_l. f_equal; apply vdot_comm.
  Qed.

  
  Context {AeqDec : Dec (@eq A)}.

  
  (** k * V1 = V2 -> V1 <> 0 -> V2 <> 0 -> k <> 0 *)
  Lemma vcmul_eq_imply_k_neq0 : forall {n} k (V1 V2 : vec n),
      k c* V1 = V2 -> V1 <> vzero -> V2 <> vzero -> k <> Azero.
  Proof.
    intros. destruct (Aeqdec k Azero); auto. exfalso. subst.
    rewrite vcmul_0_l in H3. easy.
  Qed.
 
  
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.

  
  (** k * V = 0 -> (k = 0) \/ (V = 0) *)
  Lemma vcmul_eq0_imply_k0_or_V0 : forall {n} k (V : vec n),
      k c* V = vzero -> (k = Azero) \/ (V = vzero).
  Proof.
    intros. destruct (Aeqdec k Azero); auto. right.
    apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H1. specialize (H1 i).
    cbv in H1. cbv. apply field_mul_eq0_imply_a0_or_b0 in H1; auto. tauto.
  Qed.

  (** k * V = 0 -> V <> 0 -> k = 0 *)
  Corollary vcmul_eq0_imply_k0 : forall {n} k (V : vec n),
      k c* V = vzero -> V <> vzero -> k = Azero.
  Proof. intros. apply (vcmul_eq0_imply_k0_or_V0 k V) in H1; tauto. Qed.

  (** k * V = 0 -> k <> 0 -> V = 0 *)
  Corollary vcmul_eq0_imply_V0 : forall {n} k (V : vec n),
      k c* V = vzero -> k <> Azero -> V = vzero.
  Proof. intros. apply (vcmul_eq0_imply_k0_or_V0 k V) in H1; tauto. Qed.

  (* k <> 0 -> V <> 0 -> k c* V <> 0 *)
  Corollary vcmul_neq0_neq0_neq0 : forall {n} k (V : vec n),
      k <> Azero -> V <> vzero -> k c* V <> vzero.
  Proof. intros. intro. apply vcmul_eq0_imply_k0_or_V0 in H3; tauto. Qed.
  
  (** k * V = V -> k = 1 \/ V = 0 *)
  Lemma vcmul_same_imply_k1_or_V0 : forall {n} k (V : vec n),
      k c* V = V -> (k = Aone) \/ (V = vzero).
  Proof.
    intros. destruct (Aeqdec k Aone); auto. right.
    apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H1. specialize (H1 i).
    cbv in H1. cbv. apply field_mul_eq_imply_a1_or_b0 in H1; auto. tauto.
  Qed.
  
  (** k * V = V -> V <> 0 -> k = 1 *)
  Corollary vcmul_same_imply_k1 : forall {n} k (V : vec n),
      k c* V = V -> V <> vzero -> k = Aone.
  Proof. intros. apply (vcmul_same_imply_k1_or_V0 k V) in H1; tauto. Qed.
  
  (** k * V = V -> k <> 1 -> V = 0 *)
  Corollary vcmul_same_imply_V0 : forall {n} k (V : vec n),
      k c* V = V -> k <> Aone -> V = vzero.
  Proof. intros. apply (vcmul_same_imply_k1_or_V0 k V) in H1; tauto. Qed.

  (* k1 * V = k2 * V -> (k1 = k2 \/ V = 0) *)
  Lemma vcmul_sameV_imply_eqK_or_V0 : forall {n} k1 k2 (V : vec n), 
      k1 c* V = k2 c* V -> (k1 = k2 \/ V = vzero).
  Proof.
    intros. destruct (Aeqdec k1 k2); auto. right. rewrite veq_iff_vnth in H1.
    rewrite veq_iff_vnth. intros. specialize (H1 i). rewrite !vnth_vcmul in H1.
    destruct (Aeqdec (V i) Azero); auto.
    apply field_mul_cancel_r in H1; tauto.
  Qed.

  (* k1 * V = k2 * V -> V <> 0 -> k1 = k2 *)
  Corollary vcmul_sameV_imply_eqK : forall {n} k1 k2 (V : vec n), 
      k1 c* V = k2 c* V -> V <> vzero -> k1 = k2.
  Proof. intros. apply vcmul_sameV_imply_eqK_or_V0 in H1; tauto. Qed.

  (* k1 * V = k2 * V -> k1 <> k2 -> V = 0 *)
  Corollary vcmul_sameV_imply_V0 : forall {n} k1 k2 (V : vec n), 
      k1 c* V = k2 c* V -> k1 <> k2 -> V = vzero.
  Proof. intros. apply vcmul_sameV_imply_eqK_or_V0 in H1; tauto. Qed.
  
End alg.


(** ** Vector theory on ordered ring structure *)
Section orderedRing.

  Context `{ARing}.
  Infix "+" := Aadd.
  Infix "*" := Amul.
  Notation "0" := Azero.
  Notation "< V1 , V2 >" := (@vdot _ Aadd Azero Amul _ V1 V2).
  Notation vzero := (vzero Azero).
  
  Context `{AleDec : Dec A Ale}.
  Infix "<=" := Ale.
  
  Context (Ale_refl : forall a : A, a <= a).
  Context (Azero_le_sqr : forall a : A, 0 <= a * a).
  Context (Asqr_eq_0_reg : forall a : A, a * a = 0 -> a = 0).
  Context (Aadd_le_compat : forall a1 b1 a2 b2 : A,
              a1 <= a2 -> b1 <= b2 -> a1 + b1 <= a2 + b2).
  Context (Aadd_eq_0_reg_l : forall a b : A, 0 <= a -> 0 <= b -> a + b = 0 -> a = 0).
  
  (** 0 <= <V,V> *)
  Lemma vdot_ge0 : forall {n} (V : vec n), 0 <= (<V,V>).
  Proof.
    intros. unfold vdot, vsum, fseqsum, vmap2, ff2f.
    apply seqsum_ge0; intros.
    apply Ale_refl. apply Aadd_le_compat; auto.
    destruct (_??<_). apply Azero_le_sqr. apply Ale_refl.
  Qed.

  (** <V,V> = 0 <-> V = 0 *)
  Lemma vdot_eq0_iff_vzero : forall {n} (V : vec n), <V,V> = 0 <-> V = vzero.
  Proof.
    intros. split; intros.
    - unfold vdot,vsum,fseqsum in H0.
      apply veq_iff_vnth; intros.
      apply @seqsum_eq0_imply_seq0 with (i:=fin2nat i)(Ale:=Ale) in H0; auto.
      + rewrite nth_ff2f with (H:=fin2nat_lt _) in H0.
        rewrite vnth_vmap2 in H0. rewrite nat2fin_fin2nat_id in H0.
        apply Asqr_eq_0_reg in H0. auto.
      + apply H.
      + intros. rewrite nth_ff2f with (H:=H1). rewrite vnth_vmap2.
        apply Azero_le_sqr.
      + apply fin2nat_lt.
    - rewrite H0. rewrite vdot_0_l. auto.
  Qed.
      
  (** <V, V> <> 0 <-> V <> vzero *)
  Lemma vdot_neq0_iff_vnonzero : forall {n} (V : vec n), <V, V> <> 0 <-> V <> vzero.
  Proof. intros. rewrite vdot_eq0_iff_vzero. easy. Qed.
  
End orderedRing.
