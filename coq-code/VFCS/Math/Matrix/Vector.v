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

Lemma veq_iff_vnth : forall {A} {n} (u v : @vec A n),
    u = v <-> forall (i : fin n), u i = v i.
Proof. intros. unfold vec in *. apply ffeq_iff_nth. Qed.

Lemma veq_iff_vnth_nat : forall {A} {n} (u v : @vec A n),
    u = v <-> forall (i : nat) (H: i < n), u (nat2fin i H) = v (nat2fin i H).
Proof. intros. unfold vec in *. apply ffeq_iff_nth_nat. Qed.

#[export] Instance veq_dec : forall {A n} (Azero : A),
    Dec (@eq A) -> Dec (@eq (@vec A n)).
Proof.
  intros. constructor. intros.
  apply (@fseqeq_dec _ Azero). apply Aeqdec.
Qed.

Lemma vnth_sameIdx_imply : forall {A n} {u v : @vec A n} {i} {H1 H2 H3 H4 : i < n},
    u (exist _ i H1) = v (exist _ i H2) ->
    u (exist _ i H3) = v (exist _ i H4).
Proof.
  intros.
  replace (exist _ i H3:fin n) with (exist _ i H1:fin n).
  replace (exist _ i H4:fin n) with (exist _ i H2:fin n); auto.
  apply fin_eq_iff; auto. apply fin_eq_iff; auto.
Qed.


(* ======================================================================= *)
(** ** Get element of a vector *)

Notation vnth A n := (fun (v : fin n -> A) (i : fin n) => v i).

Notation "v $ i " := (vnth _ _ v i) : vec_scope.

(* Note that: these notatiosn are dangerous.
   For example, `@nat2finS 3 0` ~ `@nat2finS 3 3` are all expected index.
   but `@nat2finS 3 4` ~ `...` will become `@nat2finS 3 0`, its error index.
 *)
Notation "v .1" := (v $ nat2finS 0) : vec_scope.
Notation "v .2" := (v $ nat2finS 1) : vec_scope.
Notation "v .3" := (v $ nat2finS 2) : vec_scope.
Notation "v .4" := (v $ nat2finS 3) : vec_scope.
Notation "v .x" := (v $ nat2finS 0) : vec_scope.
Notation "v .y" := (v $ nat2finS 1) : vec_scope.
Notation "v .z" := (v $ nat2finS 2) : vec_scope.


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
  Lemma vnth_f2v : forall {n} f i, (@f2v n f) $ i = f (fin2nat i).
  Proof. intros. unfold f2v. rewrite nth_f2ff; auto. Qed.
    
  Definition v2f {n} (v : vec n) : (nat -> A) := @ff2f _ Azero _ v.

  (* (v2f v)[i] = v[i] *)
  Lemma nth_v2f : forall {n} (v : vec n) i (H:i<n), (v2f v) i = v $ (nat2fin i H).
  Proof. intros. unfold v2f. erewrite nth_ff2f; auto. Qed.

  (** v [|i] = v2f v i *)
  Lemma vnth_to_nth : forall {n} (v : vec n) (i : nat) (H : i < n),
      v (exist _ i H) = v2f v i.
  Proof. intros. rewrite nth_v2f with (H:=H). f_equal. Qed.

  Lemma f2v_v2f_id : forall {n} (v : vec n), (@f2v n (v2f v)) = v.
  Proof. intros. unfold f2v,v2f. apply f2ff_ff2f_id. Qed.

  Lemma v2f_f2v_id : forall {n} (f : nat -> A) i, i < n -> v2f (@f2v n f) i = f i.
  Proof. intros. unfold v2f,f2v; simpl. apply ff2f_f2ff_id; auto. Qed.

End f2v_v2f.


(** Convert `vnth of vec` to `nth of nat-fun` *)
Ltac v2f Azero :=
  unfold v2f in *;
  ff2f Azero.

Section test.

  (* This example shows how to convert `vnth` to `nat-fun` *)
  Example ex_vnth2nth : forall (v : @vec nat 10), v.1 + v.2 + v.3 = v.3 + v.1 + v.2.
  Proof. intros. cbn. v2f 0. lia. Qed.
  
End test.


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
  
  Lemma l2v_surj : forall {n} (v : vec n), (exists l, l2v n l = v).
  Proof. intros. unfold l2v,vec in *. apply l2ff_surj. Qed.

  Definition v2l {n} (v : vec n) : list A := ff2l v.

  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof. intros. unfold v2l. apply ff2l_length. Qed.

  Lemma v2l_inj : forall {n} (u v : vec n), v2l u = v2l v -> u = v.
  Proof. intros. unfold v2l in *. apply ff2l_inj in H; auto. Qed.

  Lemma v2l_surj : forall {n} (l : list A), length l = n -> (exists v : vec n, v2l v = l).
  Proof. intros. unfold v2l. apply (@ff2l_surj _ Azero); auto. Qed.

  Lemma l2v_v2l_id : forall {n} (v : vec n), (@l2v n (v2l v)) = v.
  Proof. intros. unfold l2v,v2l. apply l2ff_ff2l_id. Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> v2l (@l2v n l) = l.
  Proof. intros. unfold l2v,v2l. apply ff2l_l2ff_id; auto. Qed.

  Lemma nth_v2l : forall {n} (v : vec n) (i : nat) (H: i < n),
      i < n -> nth i (v2l v) Azero = v (nat2fin i H).
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
  (* Definition vconsH_old {n} (a : A) (v : @vec A n) : @vec A (S n). *)
  (*   intro i. destruct (0 ??< fin2nat i). refine (v (fin2Pred i l)). apply a. *)
  (* Defined. *)

  Definition vconsH {n} (a : A) (v : @vec A n) : @vec A (S n) :=
    f2v (fun i => if 0 ??= i then a else (v2f v (pred i))).

  (* i = 0 -> [a; v].i = a *)
  Lemma nth_vconsH_idx_0 : forall {n} a (v : @vec A n) i,
      i = 0 -> v2f (vconsH a v) i = a.
  Proof. intros. subst. unfold vconsH,v2f,ff2f,f2v,f2ff; simpl. auto. Qed.

  Lemma vnth_vconsH_idx_0 : forall {n} a (v : @vec A n) i,
      i = fin0 -> (vconsH a v) $ i = a.
  Proof.
    intros. unfold vconsH,f2v,v2f,f2ff,ff2f. destruct i; simpl.
    apply fin_eq_iff in H. subst; simpl. auto.
  Qed.

  (* 0 < i < n -> [a; v].i = v.(pred i) *)
  Lemma nth_vconsH_idx_gt0 : forall {n} a (v : @vec A n) i,
      0 < i < n -> v2f (vconsH a v) i = v2f v (pred i).
  Proof.
    intros. unfold vconsH,v2f,f2v,ff2f,f2ff; simpl.
    destruct (i ??< S n),(pred i ??< n);try lia. destruct i; auto. lia.
  Qed.
    
  Lemma vnth_vconsH_idx_gt0 : forall {n} a (v : @vec A n) i (H: 0 < fin2nat i),
      (vconsH a v) $ i = v $ (fin2PredRangePred i H).
  Proof.
    intros. unfold vconsH,f2v,f2ff. destruct i; simpl in *.
    destruct x; subst; simpl; try lia. erewrite nth_v2f.  f_equal.
    apply fin_eq_iff; auto. Unshelve. lia.
  Qed.

  (* cons at tail *)
  (* Definition vconsT_old {n} (v : @vec A n) (a : A) : @vec A (S n). *)
  (*   intro i. destruct (fin2nat i ??< n). refine (v (fin2ExtendPred i l)). apply a. *)
  (* Defined. *)

  Definition vconsT {n} (v : @vec A n) (a : A) : @vec A (S n) :=
    f2v (fun i => if i ??< n then v2f v i else a).

  (* i = n -> [v; a].i = a *)
  Lemma nth_vconsT_idx_n : forall {n} a (v : @vec A n) i,
      i = n -> v2f (vconsT v a) i = a.
  Proof.
    intros. subst. unfold vconsT,v2f,ff2f,f2v,f2ff; simpl.
    destruct (_??<_); try lia. destruct (_??<_);auto. lia.
  Qed.

  Lemma vnth_vconsT_idx_n : forall {n} a (v : @vec A n) i,
      fin2nat i = n -> (vconsT v a) $ i = a.
  Proof.
    intros. unfold vconsT,v2f,ff2f,f2v,f2ff; simpl.
    destruct (_??<_); auto; try lia.
  Qed.

  (* 0 < i < n -> [a; v].i = v.(pred i) *)
  Lemma nth_vconsT_idx_lt_n : forall {n} a (v : @vec A n) i,
      i < n -> v2f (vconsT v a) i = v2f v i.
  Proof.
    intros. unfold vconsT,f2v,v2f,f2ff,ff2f.
    destruct (_??<_),(_??<_); simpl; auto; try lia.
    rewrite fin2nat_nat2fin_id in *. lia.
  Qed.

  Lemma vnth_vconsT_idx_lt_n : forall {n} a (v : @vec A n) i (H: fin2nat i < n),
      (vconsT v a) $ i = v (fin2PredRange i H).
  Proof.
    intros. unfold vconsT,f2v,v2f,f2ff,ff2f.
    destruct (_??<_); simpl; try lia. f_equal. apply fin_eq_iff; auto.
  Qed.
    
End vcons.

  
(** ** Construct vector with two vectors *)
Section vapp.
  Context {A} {Azero : A}.

  (* Append *)
  Definition vapp {n1 n2} (u : @vec A n1) (v : @vec A n2) : @vec A (n1 + n2) :=
    f2v (fun i => if i <? n1 then v2f Azero u i else v2f Azero v (n1 + i)).
  
End vapp.


(** ** Vector of fin sequence *)
Section vfinseq.

  Definition vfinseq (n : nat) : @vec (fin n) n := (fun i : fin n => i).

  Lemma vnth_vfinseq : forall {n} i, (vfinseq n) $ i = i.
  Proof. intros. unfold vfinseq. auto. Qed.
  
End vfinseq.


(** ** Mapping of a vector *)
Section vmap.
  Context {A B} (Azero : A) (Bzero : B).
  Variable f : A -> B.
  Hypotheses f_keep0 : Bzero = f Azero.
  
  Definition vmap {n} (v : @vec A n) : @vec B n := fun i => f (v i).

  Lemma vnth_vmap : forall {n} (v : vec n) i, (vmap v) $ i = f (v $ i).
  Proof. intros. unfold vmap; auto. Qed.

End vmap.


(** ** Mapping of two vectors *)
Section vmap2.
  Context {A B C} (Azero : A) (Bzero : B) (Czero : C).
  Variable f : A -> B -> C.
  Hypotheses f_keep0 : Czero = f Azero Bzero.
  
  Definition vmap2 {n} (u : @vec A n) (v : @vec B n) : @vec C n :=
    fun i => f (u $ i) (v $ i).

  Lemma vnth_vmap2 : forall {n} (u v : vec n) i, (vmap2 u v) i = f (u $ i) (v $ i).
  Proof. intros. unfold vmap2; auto. Qed.

  Lemma vmap2_eq_vmap : forall {n} (u : @vec A n) (v : @vec B n),
      vmap2 u v = vmap (fun i => f (u $ i) (v $ i)) (fun i => i).
  Proof. intros. unfold vmap2. auto. Qed.
  
End vmap2.


(** ** vmap2 on same type *)
Section vmap2_sametype.
  Context `{ASGroup}.
  
  Lemma vmap2_comm : forall {n} (u v : vec n),
      vmap2 Aadd u v = vmap2 Aadd v u.
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. asemigroup. Qed.
  
  Lemma vmap2_assoc : forall {n} (u v w : vec n),
      vmap2 Aadd (vmap2 Aadd u v) w = vmap2 Aadd u (vmap2 Aadd v w).
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. asemigroup. Qed.
  
End vmap2_sametype.


(** ** Sum of a vector *)
Section vsum.
  Context `{AM : AMonoid}.
  Infix "+" := Aadd.
  Notation seqsum := (@seqsum _ Aadd Azero).

  Definition vsum {n} (v : @vec A n) := @fseqsum _ Aadd Azero _ v.
  (* Notation "'\sum' f" := (vsum (ff2v f)). *)

  (* (∀ i, u[i] = v[i]) -> Σu = Σv  *)
  Lemma vsum_eq : forall {n} (u v : @vec A n), (forall i, u $ i = v $ i) -> vsum u = vsum v.
  Proof. intros. apply fseqsum_eq. auto. Qed.

  (** Σ(ai+bi) = Σ(ai) + Σ(bi) *)
  Lemma vsum_add : forall {n} (u v w : @vec A n),
      (forall i, u $ i = v $ i + w $ i) -> vsum u = vsum v + vsum w.
  Proof. intros. unfold vsum. apply fseqsum_add. auto. Qed.

  
  Context `{G:Group A Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.
  
  (** Σ(-ai) = - Σ(ai) *)
  Lemma vsum_opp : forall {n} (u v : @vec A n),
      (forall i, u $ i = - v $ i) -> vsum u = - vsum v.
  Proof. intros. unfold vsum. apply fseqsum_opp; auto. Qed.

  
  Context `{HARing:ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := (Amul) : A_scope.

  
  (* (** Σ(k * ai) = k * Σ(ai) *) *)
  Lemma vsum_cmul : forall {n} (u v : @vec A n) k,
      (forall i, u $ i = k * v $ i) -> vsum u = k * vsum v.
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
  Definition vadd {n} (u v : vec n) : vec n := vmap2 Aadd u v.
  Infix "+" := vadd : vec_scope.

  Instance vadd_Associative : forall n, Associative (@vadd n).
  Proof. intros. constructor. apply vmap2_assoc. Qed.

  Instance vadd_Commutative : forall n, Commutative (@vadd n).
  Proof. intros. constructor. apply vmap2_comm. Qed.

  (** 0 + v = v *)
  Instance vadd_IdentityLeft : forall n, IdentityLeft (@vadd n) vzero.
  Proof.
    intros. constructor. intros. unfold vadd.
    apply veq_iff_vnth; intros. rewrite vnth_vmap2. group.
  Qed.

  (** v + 0 = v *)
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

  (** (u + v)[i] = u[i] + v[i] *)
  Lemma vnth_vadd : forall {n} (u v : vec n) i, (u + v) $ i = (u $ i + v $ i)%A.
  Proof. intros. unfold vadd. rewrite vnth_vmap2. auto. Qed.
  
  (** (u + v) + w = (u + w) + v *)
  Lemma vadd_perm : forall {n} (u v w : vec n), (u + v) + w = (u + w) + v.
  Proof. intros. rewrite !associative. f_equal. apply commutative. Qed.

  
  (* Let's have an Abelian-Group *)
  Context `{AGroup A Aadd Azero}.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.


  (** *** Vector opposition *)
  
  Definition vopp {n} (v : vec n) : vec n := vmap Aopp v.
  Notation "- v" := (vopp v) : vec_scope.

  (** - v + v = 0 *)
  Instance vadd_InverseLeft : forall {n}, InverseLeft (@vadd n) vzero vopp.
  Proof. intros. constructor. intros. apply veq_iff_vnth; intros. cbv. group. Qed.

  (** v + - v = 0 *)
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

  (** - (- v) = v *)
  Lemma vopp_vopp : forall {n} (v : vec n), - (- v) = v.
  Proof. intros. apply group_inv_inv. Qed.

  (** - u = v <-> u = -v *)
  Lemma vopp_exchange : forall {n} (u v : vec n), - u = v <-> u = - v.
  Proof. intros. split; intros; subst; rewrite vopp_vopp; auto. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n:nat}, - (@Vector.vzero _ Azero n) = vzero.
  Proof. intros. apply group_inv_id. Qed.

  (** - (u + v) = (- u) + (- v) *)
  Lemma vopp_vadd : forall {n} (u v : vec n), - (u + v) = (- u) + (- v).
  Proof. intros. rewrite group_inv_distr. apply commutative. Qed.
  
  
  (** *** Vatrix Subtraction *)
  
  Definition vsub {n} (u v : vec n) : vec n := u + (- v).
  Infix "-" := vsub : vec_scope.

  (** u - v = - (v - u) *)
  Lemma vsub_comm : forall {n} (u v : vec n), u - v = - (v - u).
  Proof.
    intros. unfold vsub. rewrite group_inv_distr. rewrite group_inv_inv. auto.
  Qed.

  (** (u - v) - w = u - (v + w) *)
  Lemma vsub_assoc : forall {n} (u v w : vec n),
      (u - v) - w = u - (v + w).
  Proof.
    intros. unfold vsub. rewrite associative.
    f_equal. rewrite group_inv_distr. apply commutative.
  Qed.

  (** (u + v) - w = u + (v - w) *)
  Lemma vsub_assoc1 : forall {n} (u v w : vec n), (u + v) - w = u + (v - w).
  Proof. intros. unfold vsub. group. Qed.

  (** (u - v) - w = u - (w - v) *)
  Lemma vsub_assoc2 : forall {n} (u v w : vec n), (u - v) - w = (u - w) - v.
  Proof. intros. unfold vsub. group. f_equal. apply commutative. Qed.
  
  (** 0 - v = - v *)
  Lemma vsub_0_l : forall {n} (v : vec n), vzero - v = - v.
  Proof. intros. unfold vsub. group. Qed.
  
  (** v - 0 = v *)
  Lemma vsub_0_r : forall {n} (v : vec n), v - vzero = v.
  Proof.
    intros. unfold vsub. rewrite (@group_inv_id _ vadd vzero); auto.
    group. apply vadd_AGroup.
  Qed.
  
  (** v - v = 0 *)
  Lemma vsub_self : forall {n} (v : vec n), v - v = vzero.
  Proof. intros. unfold vsub. group. Qed.

  
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  
  (** *** Vector scalar multiplication *)
  
  Definition vcmul {n : nat} (a : A) (v : vec n) : vec n := vmap (fun x => Amul a x) v.
  Infix "\.*" := vcmul : vec_scope.

  (** (a * v)[i] = a * v[i] *)
  Lemma vnth_vcmul : forall {n} (v : vec n) a i, (a \.* v) $ i = a * (v $ i).
  Proof. intros. cbv. ring. Qed.

  (** a * (b * v) = (b * a) * v *)
  Lemma vcmul_assoc : forall {n} (v : vec n) a b,
      a \.* (b \.* v) = (a * b)%A \.* v.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** a * (b * v) = b * (a * v) *)
  Lemma vcmul_perm : forall {n} (v : vec n) a b,
      a \.* (b \.* v) = b \.* (a \.* v).
  Proof. intros. rewrite !vcmul_assoc. f_equal. ring. Qed.
  
  (** (a + b) * v = (a * v) + (b * v) *)
  Lemma vcmul_add : forall {n} a b (v : vec n),
      (a + b)%A \.* v = (a \.* v) + (b \.* v).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** a * (u + v) = (a * u) + (a * v) *)
  Lemma vcmul_vadd : forall {n} a (u v : vec n),
      a \.* (u + v) = (a \.* u) + (a \.* v).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* 0 \.* v = vzero *)
  Lemma vcmul_0_l : forall {n} (v : vec n), Azero \.* v = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** a \.* vzero = vzero *)
  Lemma vcmul_0_r : forall {n} a, a \.* vzero = (@Vector.vzero _ Azero n).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (* 1 \.* A = A *)
  Lemma vcmul_1_l : forall {n} (v : vec n), Aone \.* v = v.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (* (-a) * v = - (a * v) *)
  Lemma vcmul_opp : forall {n} a (v : vec n), (- a)%A \.* v = - (a \.* v).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (* a * (- v) = - (a * v) *)
  Lemma vcmul_vopp : forall {n} a (v : vec n), a \.* (- v) = - (a \.* v).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* Tips: these proofs show that, we can prove properties of vector by traditional
     derivation, or by computation, due to the Fin-Function model .*)
  
  (* (-a) * (- v) = a * v *)
  Lemma vcmul_opp_vopp : forall {n} a (v : vec n), (- a)%A \.* (- v) = a \.* v.
  Proof. intros. rewrite vcmul_vopp, vcmul_opp. rewrite vopp_vopp. auto. Qed.

  (** a \.* (u - v) = (a \.* u) - (a \.* v) *)
  Lemma vcmul_vsub : forall {n} a (u v : vec n),
      a \.* (u - v) = (a \.* u) - (a \.* v).
  Proof.
    intros. unfold vsub. rewrite vcmul_vadd. rewrite vcmul_vopp. auto.
  Qed.

  
  (** *** Dot product *)

  Definition vdot {n : nat} (u v : vec n) : A := vsum (vmap2 Amul u v).
  
  Notation "< u , v >" := (vdot u v) : vec_scope.

  (** <u, v> = <v, u> *)
  Lemma vdot_comm : forall {n} (u v : vec n), <u, v> = <v, u>.
  Proof. intros. apply vsum_eq; intros. rewrite vmap2_comm; auto. Qed.

  (** <vzero, v> = vzero *)
  Lemma vdot_0_l : forall {n} (v : vec n), <vzero, v> = Azero.
  Proof.
    intros. unfold vdot,vsum. apply fseqsum_eq0; intros.
    rewrite vnth_vmap2, vnth_vzero. ring.
  Qed.
  
  (** <v, vzero> = vzero *)
  Lemma vdot_0_r : forall {n} (v : vec n), <v, vzero> = Azero.
  Proof. intros. rewrite vdot_comm, vdot_0_l; auto. Qed.

  (** <u + v, w> = <u, w> + <v, w> *)
  Lemma vdot_vadd_l : forall {n} (u v w : vec n),
      <u + v, w> = (<u, w> + <v, w>)%A.
  Proof. intros. unfold vdot. apply vsum_add; intros. cbv. ring. Qed.

  (** <u, v + w> = <u, v> + <u, w> *)
  Lemma vdot_vadd_r : forall {n} (u v w : vec n),
      <u, v + w> = (<u, v> + <u, w>)%A.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vadd_l. f_equal; apply vdot_comm.
  Qed.

  (** <- u, v> = - <u, v> *)
  Lemma vdot_vopp_l : forall {n} (u v : vec n), < - u, v> = (- <u, v>)%A.
  Proof. intros. unfold vdot. apply vsum_opp; intros. cbv. ring. Qed.

  (** <u, - v> = - <u, v> *)
  Lemma vdot_vopp_r : forall {n} (u v : vec n), <u, - v> = (- <u, v>)%A.
  Proof. intros. rewrite vdot_comm, vdot_vopp_l, vdot_comm. auto. Qed.

  (** <u - v, w> = <u, w> - <v, w> *)
  Lemma vdot_vsub_l : forall {n} (u v w : vec n),
      <u - v, w> = (<u, w> - <v, w>)%A.
  Proof.
    intros. unfold vsub. rewrite vdot_vadd_l. f_equal. apply vdot_vopp_l.
  Qed.

  (** <u, v - w> = <u, v> - <u, w> *)
  Lemma vdot_vsub_r : forall {n} (u v w : vec n),
      <u, v - w> = (<u, v> - <u, w>)%A.
  Proof.
    intros. unfold vsub. rewrite vdot_vadd_r. f_equal. apply vdot_vopp_r.
  Qed.

  (** <k * u, v> = k * <u, v> *)
  Lemma vdot_vcmul_l : forall {n} (u v : vec n) k, <k \.* u, v> = k * <u, v>.
  Proof. intros. unfold vdot. apply vsum_cmul; intros. cbv. ring. Qed.
  
  (** <u, k * v> = k * <u, v> *)
  Lemma vdot_vcmul_r : forall {n} (u v : vec n) k, <u, k \.* v> = k * <u, v>.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vcmul_l. f_equal; apply vdot_comm.
  Qed.

  
  Context {AeqDec : Dec (@eq A)}.

  
  (** k * u = v -> u <> 0 -> v <> 0 -> k <> 0 *)
  Lemma vcmul_eq_imply_k_neq0 : forall {n} k (u v : vec n),
      k \.* u = v -> u <> vzero -> v <> vzero -> k <> Azero.
  Proof.
    intros. destruct (Aeqdec k Azero); auto. exfalso. subst.
    rewrite vcmul_0_l in H3. easy.
  Qed.
 
  
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.

  
  (** k * v = 0 -> (k = 0) \/ (v = 0) *)
  Lemma vcmul_eq0_imply_k0_or_v0 : forall {n} k (v : vec n),
      k \.* v = vzero -> (k = Azero) \/ (v = vzero).
  Proof.
    intros. destruct (Aeqdec k Azero); auto. right.
    apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H1. specialize (H1 i).
    cbv in H1. cbv. apply field_mul_eq0_imply_a0_or_b0 in H1; auto. tauto.
  Qed.

  (** k * v = 0 -> v <> 0 -> k = 0 *)
  Corollary vcmul_eq0_imply_k0 : forall {n} k (v : vec n),
      k \.* v = vzero -> v <> vzero -> k = Azero.
  Proof. intros. apply (vcmul_eq0_imply_k0_or_v0 k v) in H1; tauto. Qed.

  (** k * v = 0 -> k <> 0 -> v = 0 *)
  Corollary vcmul_eq0_imply_v0 : forall {n} k (v : vec n),
      k \.* v = vzero -> k <> Azero -> v = vzero.
  Proof. intros. apply (vcmul_eq0_imply_k0_or_v0 k v) in H1; tauto. Qed.

  (* k <> 0 -> v <> 0 -> k \.* v <> 0 *)
  Corollary vcmul_neq0_neq0_neq0 : forall {n} k (v : vec n),
      k <> Azero -> v <> vzero -> k \.* v <> vzero.
  Proof. intros. intro. apply vcmul_eq0_imply_k0_or_v0 in H3; tauto. Qed.
  
  (** k * v = v -> k = 1 \/ v = 0 *)
  Lemma vcmul_same_imply_k1_or_v0 : forall {n} k (v : vec n),
      k \.* v = v -> (k = Aone) \/ (v = vzero).
  Proof.
    intros. destruct (Aeqdec k Aone); auto. right.
    apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H1. specialize (H1 i).
    cbv in H1. cbv. apply field_mul_eq_imply_a1_or_b0 in H1; auto. tauto.
  Qed.
  
  (** k * v = v -> v <> 0 -> k = 1 *)
  Corollary vcmul_same_imply_k1 : forall {n} k (v : vec n),
      k \.* v = v -> v <> vzero -> k = Aone.
  Proof. intros. apply (vcmul_same_imply_k1_or_v0 k v) in H1; tauto. Qed.
  
  (** k * v = v -> k <> 1 -> v = 0 *)
  Corollary vcmul_same_imply_v0 : forall {n} k (v : vec n),
      k \.* v = v -> k <> Aone -> v = vzero.
  Proof. intros. apply (vcmul_same_imply_k1_or_v0 k v) in H1; tauto. Qed.

  (* k1 * v = k2 * v -> (k1 = k2 \/ v = 0) *)
  Lemma vcmul_sameV_imply_eqK_or_v0 : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> (k1 = k2 \/ v = vzero).
  Proof.
    intros. destruct (Aeqdec k1 k2); auto. right. rewrite veq_iff_vnth in H1.
    rewrite veq_iff_vnth. intros. specialize (H1 i). rewrite !vnth_vcmul in H1.
    destruct (Aeqdec (v i) Azero); auto.
    apply field_mul_cancel_r in H1; tauto.
  Qed.

  (* k1 * v = k2 * v -> v <> 0 -> k1 = k2 *)
  Corollary vcmul_sameV_imply_eqK : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> v <> vzero -> k1 = k2.
  Proof. intros. apply vcmul_sameV_imply_eqK_or_v0 in H1; tauto. Qed.

  (* k1 * v = k2 * v -> k1 <> k2 -> v = 0 *)
  Corollary vcmul_sameV_imply_v0 : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> k1 <> k2 -> v = vzero.
  Proof. intros. apply vcmul_sameV_imply_eqK_or_v0 in H1; tauto. Qed.
  
End alg.


(** ** Vector theory on ordered ring structure *)
Section orderedRing.

  Context `{ARing}.
  Infix "+" := Aadd.
  Infix "*" := Amul.
  Notation "0" := Azero.
  Notation "< u , v >" := (@vdot _ Aadd Azero Amul _ u v).
  Notation vzero := (vzero Azero).
  
  Context {AeqDec : Dec (@eq A)}.
  Context `{AleDec : Dec A Ale}.
  Infix "<=" := Ale.
  Context `{AltDec : Dec A Alt}.
  Infix "<" := Alt.
  
  Context (Ale_refl : forall a : A, a <= a).
  Context (Azero_le_sqr : forall a : A, 0 <= a * a).
  Context (Asqr_eq_0_reg : forall a : A, a * a = 0 -> a = 0).
  Context (Aadd_le_compat : forall a1 b1 a2 b2 : A,
              a1 <= a2 -> b1 <= b2 -> a1 + b1 <= a2 + b2).
  Context {Alt_le_compat : forall a : A, Ale Azero a <-> Alt Azero a \/ a = Azero}.
  Context (Aadd_eq_0_reg_l : forall a b : A, 0 <= a -> 0 <= b -> a + b = 0 -> a = 0).
  
  (** 0 <= <v, v> *)
  Lemma vdot_ge0 : forall {n} (v : vec n), 0 <= (<v, v>).
  Proof.
    intros. unfold vdot, vsum, fseqsum, vmap2, ff2f.
    apply seqsum_ge0; intros.
    apply Ale_refl. apply Aadd_le_compat; auto.
    destruct (_??<_). apply Azero_le_sqr. apply Ale_refl.
  Qed.

  (** <v, v> = 0 <-> v = 0 *)
  Lemma vdot_eq0_iff_vzero : forall {n} (v : vec n), <v, v> = 0 <-> v = vzero.
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
      
  (** <v, v> <> 0 <-> v <> vzero *)
  Lemma vdot_neq0_iff_vnonzero : forall {n} (v : vec n), <v, v> <> 0 <-> v <> vzero.
  Proof. intros. rewrite vdot_eq0_iff_vzero. easy. Qed.

  (** <u, v> <> 0 -> u <> 0 *)
  Lemma vdot_neq0_imply_neq0_l : forall {n} (u v : vec n), <u, v> <> 0 -> u <> vzero.
  Proof.
    intros.
    pose proof (@veq_dec _ n Azero AeqDec).
    destruct (Aeqdec u vzero); auto. subst. rewrite vdot_0_l in H0. easy.
  Qed.
  
  (** <u, v> <> 0 -> v <> 0 *)
  Lemma vdot_neq0_imply_neq0_r : forall {n} (u v : vec n), <u, v> <> 0 -> v <> vzero.
  Proof.
    intros.
    pose proof (@veq_dec _ n Azero AeqDec).
    destruct (Aeqdec v vzero); auto. subst. rewrite vdot_0_r in H0. easy.
  Qed.
  
  (** 0 < <v, v> *)
  Lemma vdot_gt0 : forall {n} (v : vec n), v <> vzero -> 0 < (<v, v>).
  Proof.
    intros.
    apply vdot_neq0_iff_vnonzero in H0. pose proof (vdot_ge0 v).
    apply Alt_le_compat in H1. destruct H1; auto. easy.
  Qed.
  
End orderedRing.
