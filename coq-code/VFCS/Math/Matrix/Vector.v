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


Require Export TupleExt ListExt Hierarchy.
Require Export RExt RealFunction.
Require Export Fin Sequence Fsequence.
Require Import Extraction.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.

(** Control the scope *)
Open Scope R_scope.
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.

(* ======================================================================= *)
(** ** Definition of vector type [vec] *)

Definition vec {A : Type} (n : nat) := fin n -> A.


(* ======================================================================= *)
(** ** Equality of vector *)

(** u = v <-> forall i, u i = v i *)
Lemma veq_iff_vnth : forall {A} {n} (u v : @vec A n),
    u = v <-> forall (i : fin n), u i = v i.
Proof. intros. unfold vec in *. apply ffeq_iff_nth. Qed.

(** u = v <-> forall i, i < n -> u i = v i *)
Lemma veq_iff_vnth_nat : forall {A} {n} (u v : @vec A n),
    u = v <-> forall (i : nat) (H: i < n), u (nat2fin i H) = v (nat2fin i H).
Proof. intros. unfold vec in *. apply ffeq_iff_nth_nat. Qed.

(** u[(i,H1)] = v[(i,H2)] -> u[(i,H3)] = v[(i,H4)] *)
Lemma vnth_sameIdx_imply : forall {A n} {u v : @vec A n} {i} {H1 H2 H3 H4 : i < n},
    u (exist _ i H1) = v (exist _ i H2) ->
    u (exist _ i H3) = v (exist _ i H4).
Proof.
  intros.
  replace (exist _ i H3:fin n) with (exist _ i H1:fin n).
  replace (exist _ i H4:fin n) with (exist _ i H2:fin n); auto.
  apply fin_eq_iff; auto. apply fin_eq_iff; auto.
Qed.

(** {u = v} + {u <> v} *)
#[export] Instance veq_dec : forall {A n} {AeqDec : Dec (@eq A)} {Azero : A},
    Dec (@eq (@vec A n)).
Proof. intros. constructor. apply Aeqdec. Qed.


(* ======================================================================= *)
(** ** Get element of a vector *)

(** v.i *)
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


(** The equality of 1-D vector *)
Lemma v1eq_iff : forall {A} (u v : @vec A 1),
    u = v <-> u.1 = v.1.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H)|].
  lia.
Qed.

(** The equality of 2-D vector *)
Lemma v2eq_iff : forall {A} (u v : @vec A 2),
    u = v <-> u.1 = v.1 /\ u.2 = v.2.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 H2].
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  lia.
Qed.

(** The equality of 3-D vector *)
Lemma v3eq_iff : forall {A} (u v : @vec A 3),
    u = v <-> u.1 = v.1 /\ u.2 = v.2 /\ u.3 = v.3.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 [H2 H3]].
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  destruct n; [apply (vnth_sameIdx_imply H3)|].
  lia.
Qed.

(** The equality of 4-D vector *)
Lemma v4eq_iff : forall {A} (u v : @vec A 4),
    u = v <-> u.1 = v.1 /\ u.2 = v.2 /\ u.3 = v.3 /\ u.4 = v.4.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 [H2 [H3 H4]]].
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  destruct n; [apply (vnth_sameIdx_imply H3)|].
  destruct n; [apply (vnth_sameIdx_imply H4)|].
  lia.
Qed.


(* ======================================================================= *)
(** ** Vector with same elements *)
Section vrepeat.
  Context {A} {Azero : A} {n : nat}.
  
  Definition vrepeat (a : A) : @vec A n := fun _ => a.

  (** (repeat a).i = a *)
  Lemma vnth_vrepeat : forall a i, vrepeat a $ i = a.
  Proof. intros. unfold vrepeat; auto. Qed.

End vrepeat.


(* ======================================================================= *)
(** ** Zero vector *)
Section vzero.
  Context {A} (Azero : A) {n : nat}.
  
  Definition vzero : @vec A n := vrepeat Azero.

  (** vzero.i = 0 *)
  Lemma vnth_vzero : forall i, vzero $ i = Azero.
  Proof. intros. apply vnth_vrepeat. Qed.

End vzero.


(* ======================================================================= *)
(** ** Convert between nat-index-function (f) and vector (v) *)
Section f2v_v2f.
  Context {A} (Azero : A).

  Definition f2v {n} (f : nat -> A) : @vec A n := f2ff f.    
  Definition v2f {n} (v : vec n) : (nat -> A) := @ff2f _ Azero _ v.
  
  (** (f2v f).i = f i *)
  Lemma vnth_f2v : forall {n} f i, (@f2v n f) $ i = f (fin2nat i).
  Proof. intros. unfold f2v. rewrite nth_f2ff; auto. Qed.

  (** (v2f v).i = v.i *)
  Lemma nth_v2f : forall {n} (v : vec n) i (H:i<n), (v2f v) i = v $ (nat2fin i H).
  Proof. intros. unfold v2f. erewrite nth_ff2f; auto. Qed.

  (** v [|i] = v2f v i *)
  Lemma vnth_to_nth : forall {n} (v : vec n) (i : nat) (H : i < n),
      v (exist _ i H) = v2f v i.
  Proof. intros. rewrite nth_v2f with (H:=H). f_equal. Qed.

  (** f2v (v2f v) = v *)
  Lemma f2v_v2f_id : forall {n} (v : vec n), (@f2v n (v2f v)) = v.
  Proof. intros. unfold f2v,v2f. apply f2ff_ff2f_id. Qed.

  (** v2f (f2v f) = f *)
  Lemma v2f_f2v_id : forall {n} (f : nat -> A) i, i < n -> v2f (@f2v n f) i = f i.
  Proof. intros. unfold v2f,f2v; simpl. apply ff2f_f2ff_id; auto. Qed.

End f2v_v2f.


(* ======================================================================= *)
(** ** Automation for equalities of vector *)

(** Convert `vnth of vec` to `nth of nat-fun` *)
Ltac v2f Azero :=
  unfold v2f in *;
  ff2f Azero.

Section test.

  (* This example shows how to convert `vnth` to `nat-fun` *)
  Example ex_vnth2nth : forall (v : @vec nat 10), v.1 + v.2 + v.3 = v.3 + v.1 + v.2.
  Proof. intros. cbn. v2f 0. lia. Qed.
  
End test.


(* ======================================================================= *)
(** ** Convert between list and vector *)
Section l2v_v2l.
  Context {A} (Azero : A).

  Definition l2v (n : nat) (l : list A) : vec n := @l2ff _ Azero _ l.
  Definition v2l {n} (v : vec n) : list A := ff2l v.

  (** (l2v l).i = nth i l *)
  Lemma vnth_l2v : forall {n} (l : list A) i, (l2v n l) $ i = nth (fin2nat i) l Azero.
  Proof. intros. unfold l2v. rewrite nth_l2ff. auto. Qed.

  (** l2v l1 = l2v l2 -> l1 = l2 *)
  Lemma l2v_inj : forall {n} (l1 l2 : list A),
      length l1 = n -> length l2 = n -> l2v n l1 = l2v n l2 -> l1 = l2.
  Proof. intros. unfold l2v. apply l2ff_inj in H1; auto. Qed.

  (** ∀ v, (∃ l, l2v l = v) *)
  Lemma l2v_surj : forall {n} (v : vec n), (exists l, l2v n l = v).
  Proof. intros. unfold l2v,vec in *. apply l2ff_surj. Qed.

  (** length (v2l v) = n *)
  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof. intros. unfold v2l. apply ff2l_length. Qed.

  (** nth i (v2l v) = v.i *)
  Lemma nth_v2l : forall {n} (v : vec n) (i : nat) (H: i < n),
      i < n -> nth i (v2l v) Azero = v (nat2fin i H).
  Proof. intros. unfold v2l. rewrite nth_ff2l with (H:=H). f_equal. Qed.

  (** v2l u = v2l v -> u = v *)
  Lemma v2l_inj : forall {n} (u v : vec n), v2l u = v2l v -> u = v.
  Proof. intros. unfold v2l in *. apply ff2l_inj in H; auto. Qed.

  (** ∀ l, (∃ v, v2l v = l) *)
  Lemma v2l_surj : forall {n} (l : list A), length l = n -> (exists v : vec n, v2l v = l).
  Proof. intros. unfold v2l. apply (@ff2l_surj _ Azero); auto. Qed.

  (** l2v (v2l v) = v *)
  Lemma l2v_v2l_id : forall {n} (v : vec n), (@l2v n (v2l v)) = v.
  Proof. intros. unfold l2v,v2l. apply l2ff_ff2l_id. Qed.

  (** v2l (l2v l) = l *)
  Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> v2l (@l2v n l) = l.
  Proof. intros. unfold l2v,v2l. apply ff2l_l2ff_id; auto. Qed.

End l2v_v2l.


(* ======================================================================= *)
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

  
(* ======================================================================= *)
(** ** Construct vector with one element and a vector *)
Section vcons.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).

  (** cons at head: [a; v] *)
  Definition vconsH {n} (a : A) (v : @vec A n) : @vec A (S n) :=
    f2v (fun i => if (i ??= 0)%nat then a else (v2f v (pred i))).
  (** cons at tail: [v; a] *)
  Definition vconsT {n} (v : @vec A n) (a : A) : @vec A (S n) :=
    f2v (fun i => if (i ??< n)%nat then v2f v i else a).

  (** i = 0 -> (v2f [a; v]) i = a *)
  Lemma nth_vconsH_idx_0 : forall {n} a (v : @vec A n) i,
      i = 0 -> v2f (vconsH a v) i = a.
  Proof.
    intros. subst. unfold vconsH,v2f,ff2f,f2v,f2ff; simpl; auto.
  Qed.

  (** i = 0 -> [a; v].i = a *)
  Lemma vnth_vconsH_idx_0 : forall {n} a (v : @vec A n) i,
      i = fin0 -> (vconsH a v) $ i = a.
  Proof.
    intros. unfold vconsH,f2v,v2f,f2ff,ff2f. destruct i; simpl.
    apply fin_eq_iff in H. subst; simpl. auto.
  Qed.

  (** 0 < i < n -> [a; v].i = v.(pred i) *)
  Lemma nth_vconsH_idx_gt0 : forall {n} a (v : @vec A n) i,
      0 < i < n -> v2f (vconsH a v) i = v2f v (pred i).
  Proof.
    intros. unfold vconsH,v2f,f2v,ff2f,f2ff; simpl.
    destruct (_??<_); try lia. destruct i; auto. lia.
  Qed.
  
  (** 0 < i -> [a; v].i = v.(pred i)  *)
  Lemma vnth_vconsH_idx_gt0 : forall {n} a (v : @vec A n) i (H: 0 < fin2nat i),
      (vconsH a v) $ i = v $ (fin2PredRangePred i H).
  Proof.
    intros. unfold vconsH,f2v,f2ff. destruct i; simpl in *.
    destruct x; subst; simpl; try lia. erewrite nth_v2f.  f_equal.
    apply fin_eq_iff; auto. Unshelve. lia.
  Qed.

  (** i = n -> (v2f [v; a]) i = a *)
  Lemma nth_vconsT_idx_n : forall {n} a (v : @vec A n) i,
      i = n -> v2f (vconsT v a) i = a.
  Proof.
    intros. subst. unfold vconsT,v2f,ff2f,f2v,f2ff; simpl.
    destruct (_??<_); try lia. destruct (_??<_)%nat; auto. lia.
  Qed.

  (** i = n -> [v; a].i = a *)
  Lemma vnth_vconsT_idx_n : forall {n} a (v : @vec A n) i,
      fin2nat i = n -> (vconsT v a) $ i = a.
  Proof.
    intros. unfold vconsT,v2f,ff2f,f2v,f2ff; simpl.
    rewrite H. destruct (_??<_); auto. lia.
  Qed.

  (** i < n -> (v2f [a; v]) i = v.(pred i) *)
  Lemma nth_vconsT_idx_lt_n : forall {n} a (v : @vec A n) i,
      i < n -> v2f (vconsT v a) i = v2f v i.
  Proof.
    intros. unfold vconsT,f2v,v2f,f2ff,ff2f.
    destruct (_??<_); auto; try lia. destruct (_??<_); auto.
    rewrite fin2nat_nat2fin_id in *. lia.
  Qed.

  (** i < n -> [a; v].i = v.(pred i) *)
  Lemma vnth_vconsT_idx_lt_n : forall {n} a (v : @vec A n) i (H: fin2nat i < n),
      (vconsT v a) $ i = v (fin2PredRange i H).
  Proof.
    intros. unfold vconsT,f2v,v2f,f2ff,ff2f. destruct (_??<_); auto; try lia.
    f_equal. apply fin_eq_iff; auto.
  Qed.
    
End vcons.

  
(* ======================================================================= *)
(** ** Construct vector with two vectors *)
Section vapp.
  Context {A} {Azero : A}.

  (** Append two vectors *)
  Definition vapp {n1 n2} (u : @vec A n1) (v : @vec A n2) : @vec A (n1 + n2) :=
    f2v (fun i => if i ??< n1 then v2f Azero u i else v2f Azero v (n1 + i)).
  
End vapp.


(* ======================================================================= *)
(** ** Mapping of a vector *)
Section vmap.
  Context {A B : Type} (f : A -> B).
  
  Definition vmap {n} (v : @vec A n) : @vec B n := fun i => f (v i).

  (** (vmap f v).i = f (v.i) *)
  Lemma vnth_vmap : forall {n} (v : vec n) i, (vmap v) $ i = f (v $ i).
  Proof. intros. unfold vmap; auto. Qed.

End vmap.


(* ======================================================================= *)
(** ** Mapping of two vectors *)
Section vmap2.
  Context {A B C : Type} (f : A -> B -> C).
  
  Definition vmap2 {n} (u : @vec A n) (v : @vec B n) : @vec C n :=
    fun i => f (u $ i) (v $ i).

  (** (vmap2 f u v).i = f (u.i) (v.i) *)
  Lemma vnth_vmap2 : forall {n} (u v : vec n) i, (vmap2 u v) i = f (u $ i) (v $ i).
  Proof. intros. unfold vmap2; auto. Qed.
  
End vmap2.


(** vmap2 on same type *)
Section vmap2_sametype.
  Context `{ASGroup}.

  (** vmap2 f u v = vmap2 f v u *)
  Lemma vmap2_comm : forall {n} (u v : vec n),
      vmap2 Aadd u v = vmap2 Aadd v u.
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. asemigroup. Qed.
  
  (** vmap2 f (vmap2 f u v) w = vmap2 f u (vmap2 f v w) *)
  Lemma vmap2_assoc : forall {n} (u v w : vec n),
      vmap2 Aadd (vmap2 Aadd u v) w = vmap2 Aadd u (vmap2 Aadd v w).
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. asemigroup. Qed.
End vmap2_sametype.


(* ======================================================================= *)
(** ** Sum of a vector *)
Section vsum.
  Context `{HAMonoid : AMonoid}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation seqsum := (@seqsum _ Aadd 0).

  (** ∑v = v.0 + v.1 + ... + v.(n-1) *)
  Definition vsum {n} (v : @vec A n) := @fseqsum _ Aadd 0 _ v.

  (** (∀ i, u.i = v.i) -> Σu = Σv *)
  Lemma vsum_eq : forall {n} (u v : @vec A n), (forall i, u $ i = v $ i) -> vsum u = vsum v.
  Proof. intros. apply fseqsum_eq. auto. Qed.

  (** (∀ i, v.i = 0) -> Σv = 0 *)
  Lemma vsum_eq0 : forall {n} (v : @vec A n), (forall i, v $ i = 0) -> vsum v = 0.
  Proof. intros. unfold vsum. apply fseqsum_eq0. auto. Qed.

  (** Convert `vsum` to `seqsum` *)
  Lemma vsum_to_seqsum : forall {n} (v : @vec A n) (g : nat -> A),
      (forall i, v $ i = g (fin2nat i)) -> vsum v = seqsum g n.
  Proof. intros. apply fseqsum_to_seqsum; auto. Qed.

  (** Convert `vsum` to `seqsum` (succ form) *)
  Lemma vsum_to_seqsum_succ : forall {n} (v : @vec A (S n)),
      vsum v = seqsum (fun i => v $ (nat2finS i)) n + v $ (nat2finS n).
  Proof. intros. apply fseqsum_to_seqsum_succ. Qed.
  
  (** `vsum` of (S n) elements, equal to addition of Sum and tail *)
  Lemma vsumS_tail : forall {n} (v : @vec A (S n)),
      vsum v = vsum (fun i => v $ (fin2SuccRange i)) + v $ (nat2finS n).
  Proof. intros. apply fseqsumS_tail; auto. Qed.

  (** `vsum` of (S n) elements, equal to addition of head and Sum *)
  Lemma vsumS_head : forall {n} (v : @vec A (S n)),
      vsum v = v $ (nat2finS 0) + vsum (fun i => v $ (fin2SuccRangeSucc i)).
  Proof. intros. apply fseqsumS_head; auto. Qed.

  (** (∀ i, u.i = v.i + w.i) -> Σu = Σv + Σw *)
  Lemma vsum_add : forall {n} (u v w : @vec A n),
      (forall i, u $ i = v $ i + w $ i) -> vsum u = vsum v + vsum w.
  Proof. intros. unfold vsum. apply fseqsum_add. auto. Qed.
  
  (** `vsum` which only one item is nonzero, then got this item. *)
  Lemma vsum_unique : forall {n} (v : @vec A n) (a : A) i,
      v $ i = a -> (forall j, i <> j -> v $ j = Azero) -> vsum v = a.
  Proof. intros. apply fseqsum_unique with (i:=i); auto. Qed.

  (** `vsum` of the m+n elements equal to plus of two parts.
      (i < m -> f.i = g.i) ->
      (i < n -> f.(m+i) = h.i) ->
      Σ[0,(m+n)] f = Σ[0,m] g + Σ[m,m+n] h. *)
  Lemma vsum_plusIdx : forall m n (f : @vec A (m + n)) (g : @vec A m) (h : @vec A n),
      (forall i : fin m, f $ (fin2AddRangeR i) = g $ i) ->
      (forall i : fin n, f $ (fin2AddRangeAddL i) = h $ i) ->
      vsum f = vsum g + vsum h.
  Proof. intros. apply fseqsum_plusIdx; auto. Qed.

  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] v_ij) = 
      v00 + v01 + ... + v0c + 
      v10 + v11 + ... + v1c + 
      ...
      vr0 + vr1 + ... + vrc = 
      ∑[j,0,c](∑[i,0,r] v_ij) *)
  Lemma vsum_vsum_exchg : forall r c (v : @vec (@vec A c) r),
      vsum (fun i => vsum (fun j => v $ i $ j)) =
        vsum (fun j => vsum (fun i => v $ i $ j)).
  Proof. intros. apply fseqsum_fseqsum_exchg. Qed.
  
  (* If equip a `Group` *)
  Section Group.
    Context `{HGroup:Group A Aadd Azero Aopp}.
    Notation "- a" := (Aopp a) : A_scope.
    
    (** (∀ i, u.i = - v.i) -> Σu = - Σv *)
    Lemma vsum_opp : forall {n} (u v : @vec A n),
        (forall i, u $ i = - v $ i) -> vsum u = - vsum v.
    Proof. intros. unfold vsum. apply fseqsum_opp; auto. Qed.
  End Group.

  (* If equip a `ARing` *)
  Section ARing.
    Context `{HARing:ARing A Aadd Azero Aopp Amul Aone}.
    Infix "*" := (Amul) : A_scope.

    (** (∀ i, u.i = k * v.i) -> Σu = k * Σv *)
    Lemma vsum_vcmul : forall {n} (u v : @vec A n) k,
        (forall i, u $ i = k * v $ i) -> vsum u = k * vsum v.
    Proof. intros. unfold vsum. apply fseqsum_cmul. auto. Qed.
  End ARing.

  (* if equip a `OrderedARing` *)
  Section OrderedARing.
    Context `{HOrderedARing : OrderedARing A Aadd Azero Aopp Amul Aone Alt Ale}.
    Infix "*" := (Amul) : A_scope.
    Infix "<" := Alt.
    Infix "<=" := Ale.

    (** (∀ i, 0 <= v.i) -> v.i <= ∑v *)
    Lemma vsum_ge_any : forall {n} (v : @vec A n) i, (forall i, Azero <= v $ i) -> v $ i <= vsum v.
    Proof.
      intros. unfold vsum, fseqsum.
      replace (v i) with (ff2f (Azero:=Azero) v (fin2nat i)).
      - apply seqsum_ge_any.
        + intros. specialize (H (nat2fin i0 H0)). rewrite nth_ff2f with (H:=H0). auto.
        + apply fin2nat_lt.
      - rewrite nth_ff2f with (H:=fin2nat_lt _). rewrite nat2fin_fin2nat_id. auto.
    Qed.

    (** (∀ i, 0 <= v.i) -> 0 <= ∑v *)
    Lemma vsum_ge0 : forall {n} (v : @vec A n), (forall i, Azero <= v $ i) -> Azero <= vsum v.
    Proof.
      intros. pose proof (vsum_ge_any v). destruct n.
      - cbv. apply le_refl.
      - apply le_trans with (v.1); auto.
    Qed.
      
    (** (∀ i, 0 <= v.i) -> (∃ i, v.i <> 0) -> 0 < ∑v *)
    Lemma vsum_gt0 : forall {n} (v : @vec A n),
        (forall i, Azero <= v $ i) -> (exists i, v $ i <> Azero) -> Azero < vsum v.
    Proof.
      intros. destruct H0 as [i H0].
      pose proof (vsum_ge0 v H). pose proof (vsum_ge_any v i H).
      assert (Azero < v$i). apply lt_if_le_and_neq; auto.
      apply lt_trans_lt_le with (v$i); auto.
    Qed.
    
  End OrderedARing.

End vsum.


(* ======================================================================= *)
(** ** Vector addition *)
Section vadd.
  Context `{AMonoid}.
  Infix "+" := Aadd : A_scope.
  
  Notation vec := (@vec A).
  Notation vzero := (vzero Azero).

  Definition vadd {n} (u v : vec n) : vec n := vmap2 Aadd u v.
  Infix "+" := vadd : vec_scope.

  (** (u + v) + w = u + (v + w) *)
  Lemma vadd_assoc : forall {n} (u v w : vec n), (u + v) + w = u + (v + w).
  Proof. intros. apply vmap2_assoc. Qed.

  (** u + v = v + u *)
  Lemma vadd_comm : forall {n} (u v : vec n), u + v = v + u.
  Proof. intros. apply vmap2_comm. Qed.

  (** 0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), vzero + v = v.
  Proof.
    intros. apply veq_iff_vnth; intros. unfold vadd. rewrite vnth_vmap2. group.
  Qed.

  (** v + 0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + vzero = v.
  Proof. intros. rewrite vadd_comm. apply vadd_0_l. Qed.

  (** <vadd,vzero> is an abelian monoid *)
  #[export] Instance vadd_AMonoid : forall n, AMonoid (@vadd n) vzero.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_assoc;
      try apply vadd_comm;
      try apply vadd_0_l;
      try apply vadd_0_r.
  Qed.

  (** (u + v).i = u.i + v.i *)
  Lemma vnth_vadd : forall {n} (u v : vec n) i, (u + v) $ i = (u $ i + v $ i)%A.
  Proof. intros. unfold vadd. rewrite vnth_vmap2. auto. Qed.
  
  (** (u + v) + w = (u + w) + v *)
  Lemma vadd_perm : forall {n} (u v w : vec n), (u + v) + w = (u + w) + v.
  Proof. intros. rewrite !associative. f_equal. apply commutative. Qed.

End vadd.

Section vadd_extra.
  Context `{AMonoid}.

  (** (∑vv).j = ∑(vv.j), which vv is a vector of vector *)
  (* 所有向量相加后取第j个分量 = 取出向量的第j个分量后再相加 *)
  Lemma vnth_vsum : forall {r c} (vv : @vec (@vec A c) r) j,
      (@vsum _ (@vadd _ Aadd _) (vzero Azero) _ vv) $ j =
        @vsum _ Aadd Azero _ (fun i => vv $ i $ j).
  Proof.
    intros. unfold vsum. induction r. cbv. auto. unfold vec in *.
    rewrite fseqsumS_tail with (g:=fun i => vv (fin2SuccRange i)); auto.
    rewrite vnth_vadd. rewrite IHr.
    rewrite fseqsumS_tail with (g:=fun i => vv (fin2SuccRange i) j); auto.
  Qed.
End vadd_extra.


(** ** Vector opposition *)
Section vopp.
  
  (* Let's have an Abelian-Group *)
  Context `{AGroup A Aadd Azero}.
  Notation "- a" := (Aopp a) : A_scope.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.

  Definition vopp {n} (v : vec n) : vec n := vmap Aopp v.
  Notation "- v" := (vopp v) : vec_scope.

  (** (- v).i = - (v.i) *)
  Lemma vnth_vopp : forall {n} (v : vec n) i, (- v) $ i = (- (v $ i))%A.
  Proof. intros. cbv. auto. Qed.
  
  (** - v + v = 0 *)
  Lemma vadd_vopp_l : forall {n} (v : vec n), v + (- v) = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. group. Qed.

  (** v + - v = 0 *)
  Lemma vadd_vopp_r : forall {n} (v : vec n), (- v) + v = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. group. Qed.

  (** <vadd,vzero,vopp> is an abelian group *)
  #[export] Instance vadd_AGroup : forall n, @AGroup (vec n) vadd vzero vopp.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_AMonoid;
      try apply vadd_vopp_l;
      try apply vadd_vopp_r.
  Qed.

  (* Now, we ca use group theory on this instance *)

  (** - (- v) = v *)
  Lemma vopp_vopp : forall {n} (v : vec n), - (- v) = v.
  Proof. intros. apply group_opp_opp. Qed.

  (** - u = v <-> u = -v *)
  Lemma vopp_exchange : forall {n} (u v : vec n), - u = v <-> u = - v.
  Proof. intros. split; intros; subst; rewrite vopp_vopp; auto. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n:nat}, - (@Vector.vzero _ Azero n) = vzero.
  Proof. intros. apply group_opp_0. Qed.

  (** - (u + v) = (- u) + (- v) *)
  Lemma vopp_vadd : forall {n} (u v : vec n), - (u + v) = (- u) + (- v).
  Proof. intros. rewrite group_opp_distr. apply commutative. Qed.

End vopp.


(** ** Vector subtraction *)
Section vsub.

  (* Let's have an Abelian-Group *)
  Context `{AGroup A Aadd Azero}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  
  Definition vsub {n} (u v : vec n) : vec n := u + (- v).
  Infix "-" := vsub : vec_scope.

  (** (u - v).i = (u.i) - (v.i) *)
  Lemma vnth_vsub : forall {n} (u v : vec n) i, (u - v) $ i = ((u $ i) - (v $ i))%A.
  Proof. intros. cbv. auto. Qed.

  (** u - v = - (v - u) *)
  Lemma vsub_comm : forall {n} (u v : vec n), u - v = - (v - u).
  Proof.
    intros. unfold vsub. rewrite group_opp_distr. rewrite group_opp_opp. auto.
  Qed.

  (** (u - v) - w = u - (v + w) *)
  Lemma vsub_assoc : forall {n} (u v w : vec n),
      (u - v) - w = u - (v + w).
  Proof.
    intros. unfold vsub. rewrite associative.
    f_equal. rewrite group_opp_distr. apply commutative.
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
  Proof. intros. unfold vsub. rewrite vopp_vzero. group. Qed.
  
  (** v - v = 0 *)
  Lemma vsub_self : forall {n} (v : vec n), v - v = vzero.
  Proof. intros. unfold vsub. group. Qed.

  (** u - v = 0 <-> u = v *)
  Lemma vsub_eq0_iff_eq : forall {n} (u v : vec n), u - v = vzero <-> u = v.
  Proof. intros. apply group_sub_eq0_iff_eq. Qed.

End vsub.


(** ** Vector scalar multiplication *)
Section vcmul.
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.
  
  Definition vcmul {n : nat} (a : A) (v : vec n) : vec n := vmap (fun x => Amul a x) v.
  Infix "\.*" := vcmul : vec_scope.

  (** (a * v).i = a * v.i *)
  Lemma vnth_vcmul : forall {n} (v : vec n) a i, (a \.* v) $ i = a * (v $ i).
  Proof. intros. cbv. auto. Qed.

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

  (** 0 \.* v = vzero *)
  Lemma vcmul_0_l : forall {n} (v : vec n), Azero \.* v = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** a \.* vzero = vzero *)
  Lemma vcmul_0_r : forall {n} a, a \.* vzero = (@Vector.vzero _ Azero n).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** 1 \.* A = A *)
  Lemma vcmul_1_l : forall {n} (v : vec n), Aone \.* v = v.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** (-a) * v = - (a * v) *)
  Lemma vcmul_opp : forall {n} a (v : vec n), (- a)%A \.* v = - (a \.* v).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* Tips: this proof shows a proof by computation, due to the Fin-Function model. *)
  (** a * (- v) = - (a * v) *)
  Lemma vcmul_vopp : forall {n} a (v : vec n), a \.* (- v) = - (a \.* v).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* Tips: this proof shows a proof by derivation *)
  (** (-a) * (- v) = a * v *)
  Lemma vcmul_opp_vopp : forall {n} a (v : vec n), (- a)%A \.* (- v) = a \.* v.
  Proof. intros. rewrite vcmul_vopp, vcmul_opp. rewrite vopp_vopp. auto. Qed.

  (** a \.* (u - v) = (a \.* u) - (a \.* v) *)
  Lemma vcmul_vsub : forall {n} a (u v : vec n), a \.* (u - v) = (a \.* u) - (a \.* v).
  Proof. intros. unfold vsub. rewrite vcmul_vadd. rewrite vcmul_vopp. auto. Qed.

  (** <vadd,vzero,vopp> is an abelian group *)
  #[export] Instance vec_AGroup : forall n, @AGroup (vec n) vadd vzero vopp.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_AMonoid;
      try apply vadd_vopp_l;
      try apply vadd_vopp_r.
  Qed.
  
  (* If equip a `Dec` *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.

    (** k * u = v -> k <> 0 *)
    Lemma vcmul_eq_imply_k_neq0 : forall {n} k (u v : vec n),
        u <> vzero -> v <> vzero -> k \.* u = v -> k <> Azero.
    Proof.
      intros. destruct (Aeqdec k Azero); auto. exfalso. subst.
      rewrite vcmul_0_l in H0. easy.
    Qed.
  End AeqDec.

  (* If equip a `Dec` and a `Field` *)
  Section Dec_Field.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** k * v = 0 -> (k = 0) \/ (v = 0) *)
    Lemma vcmul_eq0_imply_k0_or_v0 : forall {n} k (v : vec n),
        k \.* v = vzero -> (k = Azero) \/ (v = vzero).
    Proof.
      intros. destruct (Aeqdec k Azero); auto. right.
      apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H. specialize (H i).
      cbv in H. cbv. apply field_mul_eq0_reg in H; auto. tauto.
    Qed.

    (** k * v = 0 -> v <> 0 -> k = 0 *)
    Corollary vcmul_eq0_imply_k0 : forall {n} k (v : vec n),
        k \.* v = vzero -> v <> vzero -> k = Azero.
    Proof. intros. apply (vcmul_eq0_imply_k0_or_v0 k v) in H; tauto. Qed.

    (** k * v = 0 -> k <> 0 -> v = 0 *)
    Corollary vcmul_eq0_imply_v0 : forall {n} k (v : vec n),
        k \.* v = vzero -> k <> Azero -> v = vzero.
    Proof. intros. apply (vcmul_eq0_imply_k0_or_v0 k v) in H; tauto. Qed.

    (* k <> 0 -> v <> 0 -> k \.* v <> 0 *)
    Corollary vcmul_neq0_neq0_neq0 : forall {n} k (v : vec n),
        k <> Azero -> v <> vzero -> k \.* v <> vzero.
    Proof. intros. intro. apply vcmul_eq0_imply_k0_or_v0 in H1; tauto. Qed.
    
    (** k * v = v -> k = 1 \/ v = 0 *)
    Lemma vcmul_same_imply_k1_or_v0 : forall {n} k (v : vec n),
        k \.* v = v -> (k = Aone) \/ (v = vzero).
    Proof.
      intros. destruct (Aeqdec k Aone); auto. right.
      apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H. specialize (H i).
      cbv in H. cbv. apply field_mul_eq_imply_a1_or_b0 in H; auto. tauto.
    Qed.
    
    (** k * v = v -> v <> 0 -> k = 1 *)
    Corollary vcmul_same_imply_k1 : forall {n} k (v : vec n),
        k \.* v = v -> v <> vzero -> k = Aone.
    Proof. intros. apply (vcmul_same_imply_k1_or_v0 k v) in H; tauto. Qed.
    
    (** k * v = v -> k <> 1 -> v = 0 *)
    Corollary vcmul_same_imply_v0 : forall {n} k (v : vec n),
        k \.* v = v -> k <> Aone -> v = vzero.
    Proof. intros. apply (vcmul_same_imply_k1_or_v0 k v) in H; tauto. Qed.

    (* k1 * v = k2 * v -> (k1 = k2 \/ v = 0) *)
    Lemma vcmul_sameV_imply_eqK_or_v0 : forall {n} k1 k2 (v : vec n), 
        k1 \.* v = k2 \.* v -> (k1 = k2 \/ v = vzero).
    Proof.
      intros. destruct (Aeqdec k1 k2); auto. right. rewrite veq_iff_vnth in H.
      rewrite veq_iff_vnth. intros. specialize (H i). rewrite !vnth_vcmul in H.
      destruct (Aeqdec (v i) Azero); auto. apply field_mul_cancel_r in H; tauto.
    Qed.

    (* k1 * v = k2 * v -> v <> 0 -> k1 = k2 *)
    Corollary vcmul_sameV_imply_eqK : forall {n} k1 k2 (v : vec n), 
        k1 \.* v = k2 \.* v -> v <> vzero -> k1 = k2.
    Proof. intros. apply vcmul_sameV_imply_eqK_or_v0 in H; tauto. Qed.

    (* k1 * v = k2 * v -> k1 <> k2 -> v = 0 *)
    Corollary vcmul_sameV_imply_v0 : forall {n} k1 k2 (v : vec n), 
        k1 \.* v = k2 \.* v -> k1 <> k2 -> v = vzero.
    Proof. intros. apply vcmul_sameV_imply_eqK_or_v0 in H; tauto. Qed.
  End Dec_Field.
  
End vcmul.



(** ** Dot product *)
Section vdot.
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone.
  Notation "a ²" := (a * a) : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation seqsum := (@seqsum _ Aadd Azero).
  Notation vsum := (@vsum _ Aadd Azero).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  
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
  Lemma vdot_vadd_l : forall {n} (u v w : vec n), <u + v, w> = (<u, w> + <v, w>)%A.
  Proof. intros. unfold vdot. apply vsum_add; intros. cbv. ring. Qed.

  (** <u, v + w> = <u, v> + <u, w> *)
  Lemma vdot_vadd_r : forall {n} (u v w : vec n), <u, v + w> = (<u, v> + <u, w>)%A.
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
  Lemma vdot_vsub_l : forall {n} (u v w : vec n), <u - v, w> = (<u, w> - <v, w>)%A.
  Proof. intros. unfold vsub. rewrite vdot_vadd_l. f_equal. apply vdot_vopp_l. Qed.

  (** <u, v - w> = <u, v> - <u, w> *)
  Lemma vdot_vsub_r : forall {n} (u v w : vec n), <u, v - w> = (<u, v> - <u, w>)%A.
  Proof. intros. unfold vsub. rewrite vdot_vadd_r. f_equal. apply vdot_vopp_r. Qed.

  (** <k * u, v> = k * <u, v> *)
  Lemma vdot_vcmul_l : forall {n} (u v : vec n) k, <k \.* u, v> = k * <u, v>.
  Proof. intros. unfold vdot. apply vsum_vcmul; intros. cbv. ring. Qed.
  
  (** <u, k * v> = k * <u, v> *)
  Lemma vdot_vcmul_r : forall {n} (u v : vec n) k, <u, k \.* v> = k * <u, v>.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vcmul_l. f_equal; apply vdot_comm.
  Qed.

  
  (* If (@eq A) is decidable *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.

    (** <u, v> <> 0 -> u <> 0 *)
    Lemma vdot_neq0_imply_neq0_l : forall {n} (u v : vec n), <u, v> <> 0 -> u <> vzero.
    Proof.
      intros. destruct (Aeqdec u vzero); auto. subst. rewrite vdot_0_l in H. easy.
    Qed.
    
    (** <u, v> <> 0 -> v <> 0 *)
    Lemma vdot_neq0_imply_neq0_r : forall {n} (u v : vec n), <u, v> <> 0 -> v <> vzero.
    Proof.
      intros. destruct (Aeqdec v vzero); auto. subst. rewrite vdot_0_r in H. easy.
    Qed.
  End AeqDec.


  (* If equip an ordered-abelian-ring *)
  Section OrderedARing.
    Context `{HOrderedARing : OrderedARing A Aadd Azero Aopp Amul Aone}.
    Infix "<" := Alt.
    Infix "<=" := Ale.
    
    (** 0 <= <v, v> *)
    Lemma vdot_ge0 : forall {n} (v : vec n), 0 <= (<v, v>).
    Proof.
      intros. unfold vdot, vsum, fseqsum, vmap2, ff2f. apply seqsum_ge0; intros.
      destruct (_??<_); auto. apply sqr_ge0. apply le_refl.
    Qed.

    (** <u, v> ² <= <u, u> * <v, v> *)
    Lemma vdot_sqr_le : forall {n} (u v : vec n), (<u, v> ²) <= <u, u> * <v, v>.
    Proof.
      intros. unfold vdot,vsum,vmap2. destruct n.
      - cbv. apply le_refl.
      - (* Convert dependent "vec" to non-dependent "nat -> A", by "Abstraction" *)
        remember (fun i => u (nat2finS i)) as f.
        remember (fun i => v (nat2finS i)) as g.
        replace (fseqsum (fun i => (u i * v i)))
          with (seqsum (fun i => f i * g i) (S n)); auto.
        2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_succ. auto. }
        replace (fseqsum (fun i => u i * u i))
          with (seqsum (fun i => f i * f i) (S n)).
        2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_succ. auto. }
        replace (fseqsum (fun i => v i * v i))
          with (seqsum (fun i => g i * g i) (S n)).
        2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_succ. auto. }
        apply seqsum_SqrMul_le_MulSqr.
    Qed.

    (** (v i)² <= <v, v> *)
    Lemma vnth_sqr_le_vdot : forall {n} (v : vec n) (i : fin n), (v i) ² <= <v, v>.
    Proof.
      intros. unfold vdot.
      pose ((fun i => (v$i) * (v$i)) : vec n) as u.
      replace (v i)² with (u i). replace (vmap2 Amul v v) with u.
      apply vsum_ge_any.
      - intros. unfold u. apply sqr_ge0.
      - unfold u. auto.
      - unfold u. auto.
    Qed.
    
  End OrderedARing.

  
  (* If equip an ordered-field and `Dec` *)
  Section OrderedField_Dec.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone}.
    Notation "/ a" := (Ainv a).
    Notation Adiv := (fun x y => x * / y).
    Infix "/" := Adiv.
    Infix "<" := Alt.
    Infix "<=" := Ale.
    
    (** v = 0 -> <v, v> = 0 *)
    Lemma vdot_same_eq0_if_vzero : forall {n} (v : vec n), v = vzero -> <v, v> = 0.
    Proof. intros. subst. rewrite vdot_0_l; auto. Qed.
    
    (** <v, v> = 0 -> v = 0 *)
    Lemma vdot_same_eq0_then_vzero : forall {n} (v : vec n), <v, v> = 0 -> v = vzero.
    Proof.
      intros. unfold vdot,vsum,fseqsum in H. apply veq_iff_vnth; intros.
      apply seqsum_eq0_imply_seq0 with (i:=fin2nat i) in H.
      - rewrite nth_ff2f with (H:=fin2nat_lt _) in H.
        rewrite nat2fin_fin2nat_id in H. rewrite vnth_vmap2 in H.
        apply field_sqr_eq0_reg in H; auto.
      - intros. rewrite nth_ff2f with (H:=H0). rewrite vnth_vmap2. apply sqr_ge0.
      - apply fin2nat_lt.
    Qed.
      
    (** v <> vzero -> <v, v> <> 0 *)
    Lemma vdot_same_neq0_if_vnonzero : forall {n} (v : vec n), v <> vzero -> <v, v> <> 0.
    Proof. intros. intro. apply vdot_same_eq0_then_vzero in H0; auto. Qed.
      
    (** <v, v> <> 0 -> v <> vzero *)
    Lemma vdot_same_neq0_then_vnonzero : forall {n} (v : vec n), <v, v> <> 0 -> v <> vzero.
    Proof. intros. intro. apply vdot_same_eq0_if_vzero in H0; auto. Qed.
    
    (** 0 < <v, v> *)
    Lemma vdot_gt0 : forall {n} (v : vec n), v <> vzero -> Azero < (<v, v>).
    Proof.
      intros. apply vdot_same_neq0_if_vnonzero in H. pose proof (vdot_ge0 v).
      apply lt_if_le_and_neq; auto.
    Qed.

    (** <u, v>² / (<u, u> * <v, v>) <= 1. *)
    Lemma vdot_sqr_le_form2 : forall {n} (u v : vec n),
        u <> vzero -> v <> vzero -> <u, v>² / (<u, u> * <v, v>) <= 1.
    Proof.
      intros.
      pose proof (vdot_gt0 u H). pose proof (vdot_gt0 v H0).
      pose proof (vdot_sqr_le u v).
      destruct (Aeqdec (<u, v>) 0) as [H4|H4].
      - rewrite H4. ring_simplify. apply le_0_1.
      - apply le_imply_div_le_1 in H3; auto. apply sqr_gt0. auto.
    Qed.

  End OrderedField_Dec.

End vdot.


(* ======================================================================= *)
(** ** Euclidean norm (L2 norm), Length of vector *)
Section vlen.
  (* Euclidean norm == Euclidean length (distance) = L2 norm == L2 distance *)
  
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Context `{HConvertToR
      : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb a2r}.

  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Infix "*" := Amul : A_scope.
  (* Notation "a ²" := (a * a) : A_scope. *)
  Notation "1" := Aone : A_scope.
  Notation "| a |" := (@Aabs _ 0 Aopp Aleb a) : A_scope.
  
  Notation vzero := (@vzero _ Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< u , v >" := (vdot u v) : vec_scope.

  (** Length (magnitude) of a vector, is derived by inner-product *)
  Definition vlen {n} (v : vec n) : R := R_sqrt.sqrt (a2r (<v, v>)).
  Notation "|| v ||" := (vlen v) : vec_scope.

  (** ||vzero|| = 0 *)
  Lemma vlen_vzero : forall {n:nat}, || @Vector.vzero _ Azero n || = 0%R.
  Proof. intros. unfold vlen. rewrite vdot_0_l. rewrite a2r_0 at 1. ra. Qed.
  
  Section OrderedARing.
    Context `{HOrderedARing
        : OrderedARing A Aadd Azero Aopp Amul Aone Alt Ale Altb Aleb}.
    Infix "<" := Alt : A_scope.
    Infix "<=" := Ale : A_scope.
    
    (** 0 <= ||v|| *)
    Lemma vlen_ge0 : forall {n} (v : vec n), (0 <= || v ||)%R.
    Proof. intros. unfold vlen. ra. Qed.
    
    (** ||u|| = ||v|| <-> <u, u> = <v, v> *)
    Lemma vlen_eq_iff_dot_eq : forall {n} (u v : vec n), ||u|| = ||v|| <-> <u, u> = <v, v>.
    Proof.
      intros. unfold vlen. split; intros H; try rewrite H; auto.
      apply sqrt_inj in H.
      rewrite a2r_eq_iff in H; auto.
      apply a2r_ge0_iff; apply vdot_ge0.
      apply a2r_ge0_iff; apply vdot_ge0.
    Qed.

    (** <v, v> = ||v||² *)
    Lemma vdot_same : forall {n} (v : vec n), a2r (<v, v>) = (||v||²)%R.
    Proof.
      intros. unfold vlen. rewrite Rsqr_sqrt; auto.
      apply a2r_ge0_iff. apply vdot_ge0.
    Qed.

    (** |v i| <= ||v|| *)
    Lemma vnth_le_vlen : forall {n} (v : vec n) (i : fin n),
        v <> vzero -> (a2r (|v i|%A) <= ||v||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      2:{ apply vlen_ge0. }
      rewrite <- vdot_same. unfold Rsqr. rewrite <- a2r_mul. apply a2r_le_iff.
      replace (|v i| * |v i|) with (v i * v i). apply vnth_sqr_le_vdot.
      rewrite <- Aabs_mul. rewrite Aabs_right; auto. apply sqr_ge0.
    Qed.

    (** || v || = 1 <-> <v, v> = 1 *)
    Lemma vlen_eq1_iff_vdot1 : forall {n} (v : vec n), ||v|| = 1%R <-> <v, v> = 1.
    Proof.
      intros. unfold vlen. rewrite sqrt_eq1_iff. rewrite a2r_eq1_iff. easy.
    Qed.

    (** || - v|| = || v || *)
    Lemma vlen_vopp : forall n (v : vec n), || - v || = || v ||.
    Proof.
      intros. unfold vlen. f_equal. f_equal. rewrite vdot_vopp_l,vdot_vopp_r. ring.
    Qed.

    (** ||k \.* v|| = |k| * ||v|| *)
    Lemma vlen_vcmul : forall n k (v : vec n), || k \.* v || = ((a2r (|k|))%A * ||v||)%R.
    Proof.
      intros. unfold vlen.
      rewrite commutative.
      replace (a2r (|k|)%A) with (|(a2r k)|)%R.
      2:{ rewrite a2r_Aabs. auto. }
      rewrite <- sqrt_square_abs. rewrite <- sqrt_mult_alt.
      - f_equal. rewrite vdot_vcmul_l, vdot_vcmul_r, <- associative.
        rewrite a2r_mul. rewrite commutative. f_equal. rewrite a2r_mul. auto.
      - apply a2r_ge0_iff. apply vdot_ge0.
    Qed.

    (** ||u + v||² = ||u||² + ||v||² + 2 * <u, v> *)
    Lemma vlen_sqr_vadd : forall {n} (u v : vec n),
        ||(u + v)||² = (||u||² + ||v||² + 2 * a2r (<u,v>))%R.
    Proof.
      intros. rewrite <- !vdot_same. rewrite !vdot_vadd_l, !vdot_vadd_r.
      rewrite (vdot_comm v u). rewrite !a2r_add. ring.
    Qed.

    (** ||u - v||² = ||u||² + ||v||² - 2 * <u, v> *)
    Lemma vlen_sqr_vsub : forall {n} (u v : vec n),
        ||(u - v)||² = (||u||² + ||v||² - 2 * a2r (<u, v>))%R.
    Proof.
      intros. rewrite <- !vdot_same. unfold vsub. rewrite !vdot_vadd_l, !vdot_vadd_r.
      rewrite !vdot_vopp_l, !vdot_vopp_r. rewrite (vdot_comm v u).
      rewrite !a2r_add, !a2r_opp at 1. ring.
    Qed.

    (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
    (** |<u, v>| <= ||u|| * ||v|| *)
    Lemma vdot_abs_le : forall {n} (u v : vec n), (|a2r (<u, v>)| <= ||u|| * ||v||)%R.
    Proof.
      intros. pose proof (vdot_sqr_le u v).
      apply a2r_le_iff in H. rewrite !a2r_mul in H.
      rewrite (vdot_same u) in H. rewrite (vdot_same v) in H.
      replace (||u||² * ||v||²)%R with ((||u|| * ||v||)²) in H; [| cbv;ring].
      apply Rsqr_le_abs_0 in H.
      replace (|(||u|| * ||v||)|)%R with (||u|| * ||v||)%R in H; auto.
      rewrite !Rabs_right; auto.
      pose proof (vlen_ge0 u). pose proof (vlen_ge0 v). ra.
    Qed.

    (** <u, v> <= ||u|| * ||v|| *)
    Lemma vdot_le_mul_vlen : forall {n} (u v : vec n), (a2r (<u, v>) <= ||u|| * ||v||)%R.
    Proof. intros. pose proof (vdot_abs_le u v). apply Rabs_le_rev in H. ra. Qed.

    (** - ||u|| * ||v|| <= <u, v> *)
    Lemma vdot_ge_mul_vlen_neg : forall {n} (u v : vec n), (- (||u|| * ||v||) <= a2r (<u, v>))%R.
    Proof. intros. pose proof (vdot_abs_le u v). apply Rabs_le_rev in H. ra. Qed.

    (* 任意维度“三角形”两边长度之和大于第三边长度 *)
    (** ||u + v|| <= ||u|| + ||v|| *)
    Lemma vlen_vadd_le : forall {n} (u v : vec n), (||(u + v)%V|| <= ||u|| + ||v||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      2:{ unfold vlen; ra. }
      rewrite Rsqr_plus. rewrite <- !vdot_same.
      replace (a2r (<u + v, u + v>))
        with (a2r (<u, u>) + a2r (<v, v>) + (2 * a2r (<u, v>)))%R.
      2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
          rewrite (vdot_comm v u). rewrite !a2r_add at 1. ra. }
      apply Rplus_le_compat_l.
      rewrite !associative. apply Rmult_le_compat_l; ra.
      pose proof (vdot_abs_le u v). unfold Rabs in H.
      destruct Rcase_abs; ra.
    Qed.

  End OrderedARing.

  Section OrderedField_Dec.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv Alt Ale}.
    Context {AeqDec : Dec (@eq A)}.
    Infix "<=" := Ale : A_scope.
    
    (** ||v|| = 0 <-> v = 0 *)
    Lemma vlen_eq0_iff_eq0 : forall {n} (v : vec n), ||v|| = 0%R <-> v = vzero.
    Proof.
      intros. unfold vlen. split; intros.
      - apply vdot_same_eq0_then_vzero. apply sqrt_eq_0 in H; auto.
        apply a2r_eq0_iff; auto. apply a2r_ge0_iff; apply vdot_ge0.
      - rewrite H. rewrite vdot_0_l. rewrite a2r_0 at 1. ra.
    Qed.
    
    (** ||v|| <> 0 <-> v <> 0 *)
    Lemma vlen_neq0_iff_neq0 : forall {n} (v : vec n), ||v|| <> 0%R <-> v <> vzero.
    Proof. intros. rewrite vlen_eq0_iff_eq0. easy. Qed.

    (** v <> vzero -> 0 < ||v|| *)
    Lemma vlen_gt0 : forall {n} (v : vec n), v <> vzero -> (0 < ||v||)%R.
    Proof. intros. pose proof (vlen_ge0 v). apply vlen_neq0_iff_neq0 in H; ra. Qed.
      
    (** 0 <= <v, v> *)
    Lemma vdot_same_ge0 : forall {n} (v : vec n), (Azero <= <v, v>)%A.
    Proof.
      intros. destruct (Aeqdec v vzero) as [H|H].
      - subst. rewrite vdot_0_l. apply le_refl.
      - apply le_if_lt. apply vdot_gt0; auto.
    Qed.
    
  End OrderedField_Dec.
  
End vlen.

#[export] Hint Resolve vlen_ge0 : vec.


(* ======================================================================= *)
(** ** Unit vector *)

Section vunit.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Notation "1" := Aone.
  Notation vzero := (vzero Azero).
  Notation vopp := (@vopp _ Aopp).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation "< u , v >" := (vdot u v) : vec_scope.
  
  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec.
   *)
  Definition vunit {n} (v : vec n) : Prop := <v, v> = 1.
  
  (** vunit v <-> vunit (vopp u). *)
  Lemma vopp_vunit : forall {n} (v : vec n), vunit (vopp v) <-> vunit v.
  Proof.
    intros. unfold vunit. rewrite vdot_vopp_l, vdot_vopp_r.
    rewrite group_opp_opp. easy.
  Qed.

  Section Field.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** The unit vector cannot be zero vector *)
    Lemma vunit_neq0 : forall {n} (v : vec n), vunit v -> v <> vzero.
    Proof.
      intros. intro. rewrite H0 in H. unfold vunit in H.
      rewrite vdot_0_l in H. apply field_1_neq_0. easy.
    Qed.
    
  End Field.

  Section ConvertToR.
    Context `{HConvertToR : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale}.

    Notation vlen := (@vlen _ Aadd Azero Amul a2r).
    Notation "|| v ||" := (vlen v) : vec_scope.

    (** Verify the definition is reasonable *)
    Lemma vunit_spec : forall {n} (v : vec n), vunit v <-> ||v|| = 1%R.
    Proof. intros. split; intros; apply vlen_eq1_iff_vdot1; auto. Qed.

  End ConvertToR.

(** If column of a and column of b all are unit, 
    then column of (a * b) is also unit *)
  (*   a : mat 2 2 *)
  (* a1 : vunit (mat2col a 0) *)
  (* a2 : vunit (mat2col a 1) *)
  (* a3 : vorth (mat2col a 0) (mat2col a 1) *)
  (* b1 : vunit (mat2col b 0) *)
  (* b2 : vunit (mat2col b 1) *)
  (* b3 : vorth (mat2col b 0) (mat2col b 1) *)
  (* ============================ *)
  (* vunit (mat2col (a * b) 0) *)
End vunit.


(* ======================================================================= *)
(** ** Orthogonal vectors *)
Section vorth.
  (* Two vectors, u and v, in an inner product space v, are orthogonal (also called 
     perpendicular) if their inner-product is zero. It can be denoted as `u ⟂ v` *)
   
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< u , v >" := (vdot u v) : vec_scope.
  
  Definition vorth {n} (u v : vec n) : Prop := <u, v> = Azero.
  Infix "_|_" := vorth : vec_scope.

  (** u _|_ v -> v _|_ u *)
  Lemma vorth_comm : forall {n} (u v : vec n), u _|_ v -> v _|_ u.
  Proof. intros. unfold vorth in *. rewrite vdot_comm; auto. Qed.


  (* If equip a `Dec` and a `Field` *)
  Section Dec_Field.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** (k \.* u) _|_ v <-> u _|_ v *)
    Lemma vorth_vcmul_l : forall {n} k (u v : vec n),
        k <> Azero -> ((k \.* u) _|_ v <-> u _|_ v).
    Proof.
      intros. unfold vorth in *. rewrite vdot_vcmul_l. split; intros.
      - apply field_mul_eq0_reg in H0. destruct H0; auto. easy.
      - rewrite H0. ring.
    Qed.
    
    (** u _|_ (k \.* v) <-> u _|_ v *)
    Lemma vorth_vcmul_r : forall {n} k (u v : vec n),
        k <> Azero -> (u _|_ (k \.* v) <-> u _|_ v).
    Proof.
      intros. split; intros.
      - apply vorth_comm in H0. apply vorth_comm. apply vorth_vcmul_l in H0; auto.
      - apply vorth_comm in H0. apply vorth_comm. apply vorth_vcmul_l; auto.
    Qed.
  End Dec_Field.

  
  (* (** vnorm u _|_ v <-> u _|_ v *) *)
  (* Lemma vorth_vnorm_l : forall {n} (u v : vec n), u <> vzero -> vnorm u _|_ v <-> u _|_ v. *)
  (* Proof. *)
  (*   intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l. autounfold with A. *)
  (*   assert (1 * / (||u||) <> 0)%R; ra. *)
  (*   apply Rmult_integral_contrapositive_currified; ra. *)
  (*   apply Rinv_neq_0_compat; auto. *)
  (*   apply vlen_neq0_iff_neq0; auto. *)
  (* Qed. *)

  (* (** u _|_ vnorm v <-> u _|_ v *) *)
  (* Lemma vorth_vnorm_r : forall {n} (u v : vec n), v <> vzero -> u _|_ vnorm v -> u _|_ v. *)
  (* Proof. *)
  (*   intros. apply vorth_comm. apply vorth_comm in H0. apply vorth_vnorm_l; auto. *)
  (* Qed. *)
  
End vorth.



(** ** Projection component of a vector onto another *)
Section vproj.
  
  (* Let's have an field *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory F).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< u , v >" := (vdot u v) : vec_scope.
  Infix "_|_" := vorth : vec_scope.
  
  (** The projection component of a onto b *)
  Definition vproj {n} (u v : vec n) : vec n := (<u, v> / <v, v>) \.* v.

  (** u _|_ v -> vproj u v = vzero *)
  Lemma vorth_imply_vproj_eq0 : forall {n} (u v : vec n),
      v <> vzero -> u _|_ v -> vproj u v = vzero.
  Proof.
    intros. unfold vorth in H0. unfold vproj. rewrite H0.
    replace (Azero * / (<v,v>)) with Azero. apply vcmul_0_l.
    rewrite ring_mul_0_l; auto.
  Qed.

  (* If equip a `Field` *)
  Section OrderedField.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** vproj (u + v) w = vproj u w + vproj v w *)
    Lemma vproj_vadd : forall {n} (u v w : vec n),
        w <> vzero -> (vproj (u + v) w = vproj u w + vproj v w)%V.
    Proof.
      intros. unfold vproj. rewrite vdot_vadd_l. rewrite <- vcmul_add. f_equal.
      field. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
  
    (** vproj (k \.* u) v = k * (vproj u v) *)
    Lemma vproj_vcmul : forall {n} (u v : vec n) k,
        v <> vzero -> (vproj (k \.* u) v = k \.* (vproj u v))%V.
    Proof.
      intros. unfold vproj. rewrite vdot_vcmul_l. rewrite vcmul_assoc. f_equal.
      field. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
    
    (** vproj v v = v *)
    Lemma vproj_same : forall {n} (v : vec n), v <> vzero -> vproj v v = v.
    Proof.
      intros. unfold vproj. replace (<v, v> / <v, v>) with Aone; try field.
      apply vcmul_1_l. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
  End OrderedField.

End vproj.


(* ======================================================================= *)
(** ** Perpendicular component of a vector respect to another *)
Section vperp.
  
  (* Let's have an field *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory F).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation vproj := (@vproj _ Aadd Azero Amul Ainv).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< u , v >" := (vdot u v) : vec_scope.
  Infix "_|_" := vorth : vec_scope.
  
  (** The perpendicular component of u respect to u *)
  Definition vperp {n} (u v : vec n) : vec n := u - vproj u v.
  
  (** u _|_ v -> vperp u v = u *)
  Lemma vorth_imply_vperp_eq_l : forall {n} (u v : vec n),
      v <> vzero -> u _|_ v -> vperp u v = u.
  Proof.
    intros. unfold vperp. rewrite vorth_imply_vproj_eq0; auto. apply vsub_0_r.
  Qed.
  
  (* If equip a `OrderedField` *)
  Section OrderedField.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv}.

    (** vproj _|_ vperp *)
    Lemma vorth_vproj_vperp : forall {n} (u v : vec n),
        v <> vzero -> vproj u v _|_ vperp u v.
    Proof.
      intros. unfold vorth, vperp, vproj.
      rewrite !vdot_vcmul_l. rewrite vdot_vsub_r. rewrite !vdot_vcmul_r.
      rewrite (vdot_comm v u). field_simplify. rewrite ring_mul_0_l; auto.
      apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
    
    (** vperp (u + v) w = vperp u w + vperp v w *)
    Lemma vperp_vadd : forall {n} (u v w : vec n),
        w <> vzero -> (vperp (u + v) w = vperp u w + vperp v w)%V.
    Proof.
      intros. unfold vperp. rewrite vproj_vadd; auto.
      unfold vsub. asemigroup. rewrite vopp_vadd. auto.
    Qed.

    (** vperp (k * u) v = k * (vperp u v) *)
    Lemma vperp_vcmul : forall {n} (k : A) (u v : vec n),
        v <> vzero -> (vperp (k \.* u) v = k \.* (vperp u v))%V.
    Proof.
      intros. unfold vperp. rewrite vproj_vcmul; auto. rewrite vcmul_vsub. easy.
    Qed.

    (** vperp v v = vzero *)
    Lemma vperp_same : forall {n} (v : vec n), v <> vzero -> vperp v v = vzero.
    Proof.
      intros. unfold vperp. rewrite vproj_same; auto; auto. apply vsub_self.
    Qed.
  End OrderedField.
  
End vperp.


(* ======================================================================= *)
(** ** Two vectors are parallel (on vnonzero version) *)

(* 这是使用了子类型 `vnonzero` 来实现 `vpara` 的版本。
   这种做法的特点是：
   1. `vpara`成了等价关系（因为排除了非零向量，而且将非零的条件封装到了类型中）
   2. 同时也带来了一些构造上的繁琐性。因为返回该类型的函数必须要证明其满足非零的条件。
   3. 同时也使得其他相关的函数都要使用 vnonzero 版本，可能过于复杂。
   所以，当一个概念特别有应用需求时，才考虑用这种子类型的方式。
 *)
Module vpara_on_vnonzero.
  Context `{HARing : ARing}.
  Notation vcmul := (@vcmul _ Amul).
  Infix "\.*" := vcmul : vec_scope.

  (** Non-zero element *)
  Record Anonzero :=
    mknonzero {
        nonzero :> A;
        cond_nonzero : nonzero <> Azero
      }.
  
  (** Non-zero vector *)
  Record vnonzero n :=
    mkvnonzero {
        vnonzeroV :> @vec A n ;
        vnonzero_cond : vnonzeroV <> vzero Azero
      }.

  Arguments mkvnonzero {n}.
  Arguments vnonzeroV {n}.
  Arguments vnonzero_cond {n}.

  Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory HField).
  Context {AeqDec : Dec (@eq A)}.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun x y => x * / y).
  Infix "/" := Adiv : A_scope.

  (** Vector scalar multiplication on `vnonzero` *)
  Definition vnonzero_cmul {n} (k : Anonzero) (v : vnonzero n) : vnonzero n.
    refine (mkvnonzero (k \.* v) _).
    intro. apply vcmul_eq0_imply_k0_or_v0 in H. destruct k, v, H; auto.
  Defined.

  Section vpara.

    (** Two non-zero vectors are parallel, when their components are proportional *)
    Definition vpara {n} (u v : vnonzero n) : Prop :=
      exists k : A, k \.* u = v.

    (* Note: if the coefficient `k` is limited to positive, then two vectors have
     same direction *)

    Infix "//" := vpara : vec_scope.

    (** vparallel is an equivalence relation *)

    Lemma vpara_refl : forall {n} (v : vnonzero n), v // v.
    Proof. intros. exists Aone. apply vcmul_1_l. Qed.

    Lemma vpara_sym : forall {n} (u v : vnonzero n), u // v -> v // u.
    Proof.
      intros. destruct H as [k H]. exists (Aone/k). rewrite <- H.
      rewrite vcmul_assoc. symmetry. rewrite <- vcmul_1_l at 1. f_equal.
      field. apply vcmul_eq_imply_k_neq0 in H; auto. apply u. apply v.
    Qed.

    Lemma vpara_trans : forall {n} (u v w : vnonzero n), u // v -> v // w -> u // w.
    Proof.
      intros. destruct H as [k1 H1], H0 as [k2 H2].
      exists (k2 * k1). rewrite <- H2,<- H1. rewrite vcmul_assoc. auto.
    Qed.

    (** u // v -> (k \.* u) // v *)
    Lemma vcmul_vpara_l : forall {n} (k : Anonzero) (u v : vnonzero n),
        u // v -> (vnonzero_cmul k u) // v.
    Proof.
      intros. destruct H as [x H]. exists (x/k); simpl. rewrite <- H.
      rewrite vcmul_assoc. f_equal. destruct k. cbv in *. field. auto.
    Qed.

    (** u // v -> u // (k \.* v) *)
    Lemma vcmul_vpara_r : forall {n} (k : Anonzero) (u v : vnonzero n),
        u // v -> u // (vnonzero_cmul k v).
    Proof.
      intros. apply vpara_sym. apply vcmul_vpara_l; auto. apply vpara_sym; auto.
    Qed.

    (** u // v => ∃! k, k * u = v *)
    Lemma vpara_imply_uniqueK : forall {n} (u v : vnonzero n),
        u // v -> (exists ! k, k \.* u = v).
    Proof.
      intros. destruct H as [k H]. exists k. split; auto.
      intros. rewrite <- H in H0. apply vcmul_sameV_imply_eqK in H0; auto.
      apply u.
    Qed.

  End vpara.

  Infix "//" := vpara : vec_scope.

End vpara_on_vnonzero.


(* ======================================================================= *)
(** ** Two vectors are parallel (or called collinear) *)
Section vpara.
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Infix "+" := vadd : vec_scope.
  Notation "0" := Azero.
  Notation "1" := Aone.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  
  (** Two non-zero vectors are parallel, when their components are proportional *)
  Definition vpara {n} (u v : vec n) : Prop :=
    u <> vzero /\ v <> vzero /\ exists k : A, k \.* u = v.

  (* Note: if the coefficient `k` is limited to positive, then two vectors have
     same direction *)

  Infix "//" := vpara : vec_scope.

  (** vpara is almost an equivalence relation (but the reflexivity law not hold) *)

  (** v // v *)
  Lemma vpara_refl : forall {n} (v : vec n), v <> vzero -> v // v.
  Proof. intros. unfold vpara. repeat split; auto. exists 1. apply vcmul_1_l. Qed.

  (** u // v -> v // w -> u // w *)
  Lemma vpara_trans : forall {n} (u v w: vec n), u // v -> v // w -> u // w.
  Proof.
    intros. destruct H as [H1 [H2 [k1 H3]]], H0 as [H4 [H5 [k2 H6]]].
    repeat split; auto.
    exists (k2 * k1). rewrite <- H6,<- H3. rewrite vcmul_assoc. auto.
  Qed.
  
  Section Field_Dec.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    Context {AeqDec : Dec (@eq A)}.
    Add Field field_inst : (make_field_theory HField).
    Notation "/ a" := (Ainv a) : A_scope.
    Notation Adiv := (fun x y => x * / y).
    Infix "/" := Adiv : A_scope.
    
    (* u // v -> v // u *)
    Lemma vpara_sym : forall {n} (u v : vec n), u // v -> v // u.
    Proof.
      intros. destruct H as [H1 [H2 [k H3]]]. repeat split; auto.
      exists (1/k). rewrite <- H3.
      rewrite vcmul_assoc. symmetry. rewrite <- vcmul_1_l at 1. f_equal.
      field. apply vcmul_eq_imply_k_neq0 in H3; auto.
    Qed.

    (** u // v => ∃! k, k * u = v *)
    Lemma vpara_imply_uniqueK : forall {n} (u v : vec n),
        u // v -> (exists ! k, k \.* u = v).
    Proof.
      intros. destruct H as [H1 [H2 [k H3]]]. exists k. split; auto.
      intros. rewrite <- H3 in H. apply vcmul_sameV_imply_eqK in H; auto.
    Qed.

    (** u // v -> (k \.* u) // v *)
    Lemma vcmul_vpara_l : forall {n} k (u v : vec n),
        k <> 0 -> u // v -> k \.* u // v.
    Proof.
      intros. destruct H0 as [H1 [H2 [k1 H3]]]. repeat split; auto.
      - intro. apply vcmul_eq0_imply_k0_or_v0 in H0. destruct H0; auto.
      - exists (k1/k); simpl. rewrite <- H3. rewrite vcmul_assoc. f_equal.
        cbv. field. auto.
    Qed.

    (** u // v -> u // (k \.* v) *)
    Lemma vcmul_vpara_r : forall {n} k (u v : vec n),
        k <> 0 -> u // v -> u // (k \.* v).
    Proof.
      intros. apply vpara_sym. apply vcmul_vpara_l; auto.
      apply vpara_sym; auto.
    Qed.
    
  End Field_Dec.
End vpara.
