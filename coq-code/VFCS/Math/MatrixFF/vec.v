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
Require Export fin seq fseq fin.
Require Import Extraction.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.


(* ======================================================================= *)
(** ** Definition of vector type [vec] *)
Section def.
  Context {A : Type}.

  (* structural-style *)
  Record vec_s (n : nat) := 
    mkvec {
        vdata : list A;
        vlength : length vdata = n;
      }.

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


(* ======================================================================= *)
(** ** Get element of a vector *)

Notation vnth := (fun {A n} (V: fin n -> A) (i:fin n) => V i).

(* Global Hint Unfold vnth : core. *)
Notation "V $ i " := (vnth _ _ V i) : vec_scope.
(* Notation "V .1" := (V $ 0) : vec_scope. *)
(* Notation "V .2" := (V $ 1) : vec_scope. *)
(* Notation "V .3" := (V $ 2) : vec_scope. *)
(* Notation "V .4" := (V $ 3) : vec_scope. *)


(* Simplify equality of two vectors (linear matrix algebra) *)
(* Ltac lva := *)
(*   repeat match goal with *)
(*     (* V1 = V2 ==> vdata V1 = vdata V2 *) *)
(*     | |- @eq (vec _) _ _ => rewrite veq_iff; simpl *)
(*     (* cons a1 t1 = cons a2 t2 ==> a1 = a2 /\ t1 = t2 *) *)
(*     | |- cons _ _ = cons _ _ => f_equal *)
(*     end. *)


(** ** vector with specific size *)
Section vec_specific.
  Context {A} {Azero : A}.
  Variable a1 a2 a3 a4 : A.

  Definition mkvec0 : @vec A 0 := fun _ => Azero.
  Definition mkvec1 : @vec A 1 := @l2ff _ Azero _ [a1].
  Definition mkvec2 : @vec A 2 := @l2ff _ Azero _ [a1;a2].
  Definition mkvec3 : @vec A 3 := @l2ff _ Azero _ [a1;a2;a3].
  Definition mkvec4 : @vec A 4 := @l2ff _ Azero _ [a1;a2;a3;a4].
End vec_specific.


(** ** Convert between list and vector *)
Section l2v_v2l.
  Context {A : Type} (Azero : A).

  Definition l2v (n : nat) (l : list A) : vec n := @l2ff _ Azero _ l.
  
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

End l2v_v2l.


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

  
(** ** Construct vector with one element and a vector *)
Section vcons.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).

  (* cons at head *)
  Definition vconsH_old {n} (a : A) (V : @vec A n) : @vec A (S n).
    intro i. destruct (0 ??< fin2nat i). refine (V (fin2Pred i l)). apply a.
  Defined.

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
      (vconsH a V)$i = V$(fin2Pred i H).
  Proof.
    intros. unfold vconsH,f2v,f2ff. destruct i; simpl in *.
    destruct x; subst; simpl; try lia. erewrite nth_v2f.  f_equal.
    apply fin_eq_iff; auto. Unshelve. lia.
  Qed.

  (* cons at tail *)
  Definition vconsT_old {n} (V : @vec A n) (a : A) : @vec A (S n).
    intro i. destruct (fin2nat i ??< n). refine (V (fin2ExtendPred i l)). apply a.
  Defined.

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
      (vconsT V a)$i = V (fin2ExtendPred i H).
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


(** ** nil vector (A vector which length is 0) *)
Section vnil.
  Context {A} (Azero : A).
  
  Definition vnil : @vec A 0 := fun _ => Azero.

End vnil.


(** ** Vector with same elements *)
Section vrepeat.
  Context {A} {Azero : A} {n : nat}.
  
  Definition vrepeat (a : A) : @vec A n := f2v (fun _ => a).

  Lemma vnth_vrepeat : forall a i, vrepeat a $ i = a.
  Proof. intros. unfold vrepeat. rewrite vnth_f2v. auto. Qed.

End vrepeat.


(** ** Zero vector *)
Section vzero.
  Context {A} (Azero : A) {n : nat}.
  
  Definition vzero : @vec A n := vrepeat Azero.

  Lemma vnth_vzero : forall i, vzero $ i = Azero.
  Proof. intros. apply vnth_vrepeat. Qed.

End vzero.


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
  Context `{AGroup}.
  (* Context `{AG:AGroup A Aadd Azero Aopp} {Aone : A}. *)
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b)).
  Infix "-" := Asub : A_scope.
  Notation vec := (@vec A).
  Notation vzero := (vzero Azero).
  Notation vsum := (@vsum _ Aadd Azero).
  (* Notation seqsum := (@seqsum _ Aadd Azero). *)
  
  (** *** Vector addition *)
  Definition vadd {n} (V1 V2 : vec n) : vec n := vmap2 Aadd V1 V2.
  Infix "+" := vadd : vec_scope.

  (** 0 + V = V *)
  Lemma vadd_0_l : forall {n} (V : vec n), vzero + V = V.
  Proof.
    intros. unfold vadd. apply veq_iff_vnth; intros. rewrite vnth_vmap2. group.
  Qed.

  (** V + 0 = V *)
  Lemma vadd_0_r : forall {n} (V : vec n), V + vzero = V.
  Proof. intros. unfold vadd. rewrite vmap2_comm. apply vadd_0_l. Qed.
  
  Instance Associative_vadd : forall n, @Associative (vec n) vadd.
  Proof. intros. constructor. apply vmap2_assoc. Qed.

  Instance Commutative_vadd : forall n, @Commutative (vec n) vadd.
  Proof. intros. constructor. apply vmap2_comm. Qed.

  Instance IdentityLeft_vadd : forall n, @IdentityLeft (vec n) vadd vzero.
  Proof. intros. constructor. apply vadd_0_l. Qed.

  Instance IdentityRight_vadd : forall n, @IdentityRight (vec n) vadd vzero.
  Proof. intros. constructor. apply vadd_0_r. Qed.

  Instance Monoid_vadd : forall n, Monoid (@vadd n) vzero.
  Proof.
    intros. repeat constructor; intros;
      try apply associative;
      try apply identityLeft;
      try apply identityRight.
  Qed.

  (** (V1 + V2)[i] = V1[i] + V2[i] *)
  Lemma vnth_vadd : forall {n} (V1 V2 : vec n) i, (V1 + V2)$i = (V1$i + V2$i)%A.
  Proof. intros. unfold vadd. rewrite vnth_vmap2. auto. Qed.


  (** *** Vector opposition *)
  
  Definition vopp {n} (V : vec n) : vec n := vmap Aopp V.
  Notation "- V" := (vopp V) : vec_scope.
  
  (* Lemma vadd_vopp_l : forall {n} (V : vec n), (-V) + V = (vzero n). *)
  (* Proof. *)
  (*   intros. destruct V; apply veq_iff; simpl. *)
  (*   rewrite (list_eq_iff_nth Azero n). *)
  (*   - intros. rewrite nth_map2 with (n:=n)(Azero:=Azero)(Bzero:=Azero); auto. *)
  (*     + erewrite nth_map with (n:=n); auto. rewrite nth_repeat, inverseLeft; auto. *)
  (*     + rewrite map_length. lia. *)
  (*   - rewrite map2_length with (n:=n); auto. rewrite map_length; lia. *)
  (*   - rewrite repeat_length; auto. *)
  (* Qed. *)
    
  (* Lemma vadd_vopp_r : forall {n} (V : vec n), V + (-V) = (vzero n). *)
  (* Proof. intros. rewrite commutative. apply vadd_vopp_l. Qed. *)

  (* Instance InverseLeft_vadd : forall n, @InverseLeft (vec n) vadd (vzero n) vopp. *)
  (* Proof. intros. constructor. apply vadd_vopp_l. Qed. *)

  (* Instance InverseRight_vadd : forall n, @InverseRight (vec n) vadd (vzero n) vopp. *)
  (* Proof. intros. constructor. apply vadd_vopp_r. Qed. *)

  (* Instance AGroup_vadd : forall n, @AGroup (vec n) vadd (vzero n) vopp. *)
  (* Proof. *)
  (*   intros. repeat constructor; *)
  (*     try apply associative; *)
  (*     try apply identityLeft; *)
  (*     try apply identityRight; *)
  (*     try apply inverseLeft; *)
  (*     try apply inverseRight; *)
  (*     try apply commutative. *)
  (* Qed. *)

  (* Now, we ca use group theory on <vadd, vzero, vopp, vsub> *)

  (* (** (V1 + V2) + V3 = (V1 + V3) + V2 *) *)
  (* Lemma vadd_perm : forall {n} (V1 V2 V3 : vec n), (V1 + V2) + V3 = (V1 + V3) + V2. *)
  (* Proof. intros. rewrite !associative. f_equal. apply commutative. Qed. *)
  
  (* (** - (- V) = V *) *)
  (* Lemma vopp_vopp : forall {n} (V : vec n), - (- V) = V. *)
  (* Proof. intros. apply group_inv_inv. Qed. *)

  (* (** -V1 = V2 <-> V1 = -V2 *) *)
  (* Lemma vopp_exchange : forall {n} (V1 V2 : vec n), -V1 = V2 <-> V1 = -V2. *)
  (* Proof. *)
  (*   intros. split; intros. *)
  (*   - rewrite <- H. rewrite vopp_vopp; auto. *)
  (*   - rewrite H. rewrite vopp_vopp; auto. *)
  (* Qed. *)

  (* (** - (vzero) = vzero *) *)
  (* Lemma vopp_vzero : forall {n}, - (vzero n) = (vzero n). *)
  (* Proof. intros. apply group_inv_id. Qed. *)

  (* (** - (V1 + V2) = (-V1) + (-V2) *) *)
  (* Lemma mopp_vadd : forall {n} (V1 V2 : vec n), - (V1 + V2) = (-V1) + (-V2). *)
  (* Proof. intros. rewrite group_inv_distr. apply commutative. Qed. *)
  
  
  (** *** Vatrix Subtraction *)
  
  Definition vsub {n} (V1 V2 : vec n) : vec n := V1 + (-V2).
  Infix "-" := vsub : vec_scope.

  (* (** V1 - V2 = - (V2 - V1) *) *)
  (* Lemma vsub_comm : forall {n} (V1 V2 : vec n), V1 - V2 = - (V2 - V1). *)
  (* Proof. *)
  (*   intros. unfold vsub. rewrite group_inv_distr. rewrite group_inv_inv. auto. *)
  (* Qed. *)

  (* (** (V1 - V2) - V3 = V1 - (V2 + V3) *) *)
  (* Lemma vsub_assoc : forall {n} (V1 V2 V3 : vec n), *)
  (*     (V1 - V2) - V3 = V1 - (V2 + V3). *)
  (* Proof. *)
  (*   intros. unfold vsub. rewrite associative. f_equal. *)
  (*   rewrite group_inv_distr. apply commutative. *)
  (* Qed. *)

  (* (** (V1 + V2) - V3 = V1 + (V2 - V3) *) *)
  (* Lemma vsub_assoc1 : forall {n} (V1 V2 V3 : vec n), (V1 + V2) - V3 = V1 + (V2 - V3). *)
  (* Proof. intros. unfold vsub. group. Qed. *)

  (* (** (V1 - V2) - V3 = V1 - (V3 - V2) *) *)
  (* Lemma vsub_assoc2 : forall {n} (V1 V2 V3 : vec n), (V1 - V2) - V3 = (V1 - V3) - V2. *)
  (* Proof. intros. unfold vsub. group. f_equal. apply commutative. Qed. *)
  
  (* (** 0 - V = - V *) *)
  (* Lemma vsub_0_l : forall {n} (V : vec n), (vzero n) - V = - V. *)
  (* Proof. intros. unfold vsub. group. Qed. *)
  
  (* (** V - 0 = V *) *)
  (* Lemma vsub_0_r : forall {n} (V : vec n), V - (vzero n) = V. *)
  (* Proof. *)
  (*   intros. unfold vsub. rewrite (@group_inv_id _ vadd (vzero n)); auto. *)
  (*   group. apply AGroup_vadd. *)
  (* Qed. *)
  
  (* (** V - V = 0 *) *)
  (* Lemma vsub_self : forall {n} (V : vec n), V - V = (vzero n). *)
  (* Proof. intros. unfold vsub. group. Qed. *)

  
  Context `{AR : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : make_ring_theory.
  
  
  (** *** Vector scalar multiplication *)
  
  Definition vcmul {n : nat} (a : A) (V : vec n) : vec n := vmap (fun x => Amul a x) V.
  Infix "c*" := vcmul : vec_scope.

  (* (** a1 * (a2 * V) = (a1 * a2) * V *) *)
  (* Lemma vcmul_assoc : forall {n} (V : vec n) a1 a2, *)
  (*     a1 c* (a2 c* V) = (a1 * a2)%A c* V. *)
  (* Proof. *)
  (*   intros. destruct V. apply veq_iff; simpl. *)
  (*   rewrite map_map. apply map_ext. intros. ring. *)
  (* Qed. *)
  
  (* (** a1 * (a2 * V) = a2 * (a1 * V) *) *)
  (* Lemma vcmul_perm : forall {n} (V : vec n) a1 a2, *)
  (*     a1 c* (a2 c* V) = a2 c* (a1 c* V). *)
  (* Proof. intros. rewrite !vcmul_assoc. f_equal. ring. Qed. *)

  (* (** a * (V1 + V2) = (a * V1) + (a * V2) *) *)
  (* Lemma vcmul_vadd_distr : forall {n} a (V1 V2 : vec n), *)
  (*     a c* (V1 + V2) = (a c* V1) + (a c* V2). *)
  (* Proof. *)
  (*   intros. destruct V1,V2. apply veq_iff; simpl. *)
  (*   rewrite map2_map_hom; auto. intros. ring. *)
  (* Qed. *)
  
  (* (** (a1 + a2) * V = (a1 * V) + (a2 * V) *) *)
  (* Lemma vcmul_add_distr : forall {n} a1 a2 (V : vec n), *)
  (*     (a1 + a2)%A c* V = (a1 c* V) + (a2 c* V). *)
  (* Proof. *)
  (*   intros. destruct V. apply veq_iff; simpl. *)
  (*   erewrite map2_map_map; auto. intros. simpl. ring. *)
  (* Qed. *)

  (* (** (a * V)[i] = a * V[i] *) *)
  (* Lemma vnth_vcmul : forall {n} (V : vec n) a i, (a c* V)$i = a * (V$i). *)
  (* Proof. intros. unfold vcmul. erewrite vnth_vmap; auto. Qed. *)

  (* (* 0 c* V = vzero *) *)
  (* Lemma vcmul_0_l : forall {n} (V : vec n), Azero c* V = (vzero n). *)
  (* Proof. *)
  (*   intros. destruct V. apply veq_iff; simpl. *)
  (*   rewrite (list_eq_iff_nth Azero); auto. *)
  (*   - intros. rewrite nth_map with (n:=n)(Azero:=Azero); auto. *)
  (*     rewrite nth_repeat. ring. rewrite map_length in H. lia. *)
  (*   - rewrite repeat_length, map_length; auto. *)
  (* Qed. *)

  (* (** a c* vzero = vzero *) *)
  (* Lemma vcmul_0_r : forall {n} a, a c* (vzero n) = (vzero n). *)
  (* Proof. *)
  (*   intros. unfold vzero; apply veq_iff; simpl. *)
  (*   rewrite map_repeat. f_equal. ring. *)
  (* Qed. *)
  
  (* (* 1 c* A = A *) *)
  (* Lemma vcmul_1 : forall {n} (V : vec n), Aone c* V = V. *)
  (* Proof. *)
  (*   intros. destruct V. apply veq_iff; simpl. apply map_id. intros. ring. *)
  (* Qed. *)
  
  (* (* (-a) * V = - (a * V) *) *)
  (* Lemma vcmul_opp : forall {n} a (V : vec n), (- a)%A c* V = - (a c* V). *)
  (* Proof. *)
  (*   intros. destruct V. apply veq_iff; simpl. *)
  (*   rewrite map_map. apply map_ext. intros. ring. *)
  (* Qed. *)
  
  (* (* a * (-V) = - (a * V) *) *)
  (* Lemma vcmul_vopp : forall {n} a (V : vec n), a c* (-V) = - (a c* V). *)
  (* Proof. *)
  (*   intros. destruct V. apply veq_iff; simpl. *)
  (*   rewrite !map_map. apply map_ext. intros. ring. *)
  (* Qed. *)
  
  (* (* (-a) * (- V) = a * V *) *)
  (* Lemma vcmul_opp_vopp : forall {n} a (V : vec n), (- a)%A c* (- V) = a c* V. *)
  (* Proof. intros. rewrite vcmul_vopp, vcmul_opp. rewrite vopp_vopp. auto. Qed. *)

  (* (** a c* (V1 - V2) = (a c* V1) - (a c* V2) *) *)
  (* Lemma vcmul_vsub : forall {n} a (V1 V2 : vec n), *)
  (*     a c* (V1 - V2) = (a c* V1) - (a c* V2). *)
  (* Proof. *)
  (*   intros. unfold vsub. rewrite vcmul_vadd_distr. rewrite vcmul_vopp. auto. *)
  (* Qed. *)

  
  (** *** Dot product *)

  Definition vdot {n : nat} (V1 V2 : vec n) : A := vsum (vmap2 Amul V1 V2).
  
  Notation "< v1 , v2 >" := (vdot v1 v2) : vec_scope.

  (* (* Commutative law *) *)
  (* Lemma vdot_comm : forall {n} (V1 V2 : vec n), <V1,V2> = <V2,V1>. *)
  (* Proof. *)
  (*   intros. unfold vdot. apply seqsum_eq; intros. ring. *)
  (* Qed. *)

  (* (* Distributive law *) *)
  (* Lemma vdot_distr_l : forall {n} (V1 V2 V3 : vec n), *)
  (*     <V1+V2,V3> = (<V1,V3> + <V2,V3>)%A. *)
  (* Proof. *)
  (*   intros. unfold vdot,vadd. apply seqsum_add; intros. unfold vnthNat; simpl. *)
  (*   rewrite nth_map2 with (n:=n)(Azero:=Azero)(Bzero:=Azero); auto. *)
  (*   ring. apply vlength. apply vlength. *)
  (* Qed. *)

  (* Lemma vdot_distr_r : forall {n} (V1 V2 V3 : vec n), *)
  (*     <V1,V2+V3> = (<V1,V2> + <V1,V3>)%A. *)
  (* Proof. *)
  (*   intros. rewrite vdot_comm. rewrite vdot_distr_l. f_equal; apply vdot_comm. *)
  (* Qed. *)
  
  (* (* Associative law on scalar multiplication *) *)
  (* Lemma vdot_assoc_cmul_l : forall {n} (V1 V2 : vec n) k, <k c* V1, V2> = k * <V1,V2>. *)
  (* Proof. *)
  (*   intros. unfold vdot,vcmul. apply seqsum_cmul; intros. unfold vnthNat; simpl. *)
  (*   rewrite nth_map with (n:=n)(Azero:=Azero); auto. *)
  (*   ring. apply vlength. *)
  (* Qed. *)
  
  (* Lemma vdot_assoc_cmul_r : forall {n} (V1 V2 : vec n) k, <V1, k c* V2> = k * <V1,V2>. *)
  (* Proof. *)
  (*   intros. rewrite vdot_comm. rewrite vdot_assoc_cmul_l. f_equal; apply vdot_comm. *)
  (* Qed. *)

  
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Context `{ADec : Dec A}.

  
  (* (** k * V = 0 -> (k = 0) \/ (V = 0) *) *)
  (* Lemma vcmul_eq0_imply_k0_or_vzero : forall {n} (V : vec n) k, *)
  (*     k c* V = (vzero _) -> (k = Azero)%A \/ (V = (vzero _)). *)
  (* Proof. *)
  (*   intros. destruct V. *)
  (*   unfold vcmul in H. apply veq_iff in H. simpl in H. *)
  (*   pose proof (lcmul_eq0_imply_k0_or_lzero vdata0 vlength0 k). *)
  (*   unfold lcmul, lzero in H0. apply H0 in H. destruct H; auto. *)
  (*   right. apply veq_iff; auto. *)
  (* Qed. *)

  (* (** (V <> 0 /\ k * V = 0) -> K = 0 *) *)
  (* Lemma vcmul_nonzero_eq0_imply_k0 : forall {n} (V : vec n) k, *)
  (*     V <> (vzero _) -> k c* V = (vzero _) -> (k = Azero)%A. *)
  (* Proof. intros. apply vcmul_eq0_imply_k0_or_vzero in H0; auto. tauto. Qed. *)

  (* (** k * V = V -> k = 1 \/ V = 0 *) *)
  (* Lemma vcmul_same_imply_coef1_or_vzero : forall {n} k (V : vec n), *)
  (*     k c* V = V -> (k = Aone)%A \/ (V = (vzero _)). *)
  (* Proof. *)
  (*   intros. destruct V. *)
  (*   unfold vcmul in H. apply veq_iff in H. simpl in H. *)
  (*   pose proof (lcmul_fixpoint_imply_k1_or_lzero vdata0 vlength0 k). *)
  (*   unfold lcmul, lzero in H0. apply H0 in H. destruct H; auto. *)
  (*   right. apply veq_iff; auto. *)
  (* Qed. *)
  
  (* (** (V1 <> 0 /\ V2 <> 0 /\ k * V1 = V2) -> k <> 0 *) *)
  (* Lemma vcmul_eq_implfy_not_k0 : forall {n} (V1 V2 : vec n) k, *)
  (*     V1 <> (vzero _) -> V2 <> (vzero _) -> k c* V1 = V2 -> k <> Azero. *)
  (* Proof. *)
  (*   intros. intro. destruct V1,V2. *)
  (*   rewrite <- veq_iff in H,H0,H1; simpl in *. rewrite H2 in *. *)
  (*   rewrite (map_eq_zero) with (Azero:=Azero)(n:=n) in H1; auto. intros; ring. *)
  (* Qed. *)
  
End alg.
