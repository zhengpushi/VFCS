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
Generalizable Variable B Badd Bzero.

(** Control the scope *)
Open Scope R_scope.
Open Scope nat_scope.
Open Scope fin_scope.
Open Scope A_scope.
Open Scope vec_scope.

(* ======================================================================= *)
(** ** Definition of vector type [vec] *)

Definition vec {A : Type} (n : nat) := fin n -> A.


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
  apply sig_eq_iff; auto. apply sig_eq_iff; auto.
Qed.

(** {u = v} + {u <> v} *)
#[export] Instance veq_dec : forall {A n} {AeqDec : Dec (@eq A)} {Azero : A},
    Dec (@eq (@vec A n)).
Proof. intros. constructor. apply Aeqdec. Qed.

(** The equality of 0-D vector *)
Lemma v0eq : forall {A} (u v : @vec A 0), u = v.
Proof. intros. apply veq_iff_vnth. intros. exfalso. apply fin0_False; auto. Qed.

Lemma v0neq : forall {A} (u v : @vec A 0), u <> v -> False.
Proof. intros. destruct H. apply v0eq. Qed.

(** The equality of 1-D vector *)
Lemma v1eq_iff : forall {A} (u v : @vec A 1), u = v <-> u.1 = v.1.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H)|]. lia.
Qed.

Lemma v1neq_iff : forall {A} (u v : @vec A 1), u <> v <-> u.1 <> v.1.
Proof. intros. rewrite v1eq_iff. tauto. Qed.

(** The equality of 2-D vector *)
Lemma v2eq_iff : forall {A} (u v : @vec A 2), u = v <-> u.1 = v.1 /\ u.2 = v.2.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 H2].
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  lia.
Qed.

Lemma v2neq_iff : forall {A} (u v : @vec A 2), u <> v <-> (u.1 <> v.1 \/ u.2 <> v.2).
Proof. intros. rewrite v2eq_iff. tauto. Qed.

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

Lemma v3neq_iff : forall {A} (u v : @vec A 3),
    u <> v <-> (u.1 <> v.1 \/ u.2 <> v.2 \/ u.3 <> v.3).
Proof. intros. rewrite v3eq_iff. tauto. Qed.

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

Lemma v4neq_iff : forall {A} (u v : @vec A 4),
    u <> v <-> (u.1 <> v.1 \/ u.2 <> v.2 \/ u.3 <> v.3 \/ u.4 <> v.4).
Proof. intros. rewrite v4eq_iff. tauto. Qed.

(** u <> v <-> ∃ i, u $ i <> v $ i *)
Lemma vneq_iff_exist_vnth_neq : forall {A n} (u v : @vec A n), u <> v <-> exists i, u $ i <> v $ i.
Proof.
  intros. rewrite veq_iff_vnth. split; intros.
  - apply not_all_ex_not; auto.
  - apply ex_not_not_all; auto.
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
  Lemma f2v_v2f : forall {n} (v : vec n), (@f2v n (v2f v)) = v.
  Proof. intros. unfold f2v,v2f. apply f2ff_ff2f. Qed.

  (** v2f (f2v f) = f *)
  Lemma v2f_f2v : forall {n} (f : nat -> A) i, i < n -> v2f (@f2v n f) i = f i.
  Proof. intros. unfold v2f,f2v; simpl. apply ff2f_f2ff; auto. Qed.

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
  Lemma l2v_v2l : forall {n} (v : vec n), (@l2v n (v2l v)) = v.
  Proof. intros. unfold l2v,v2l. apply l2ff_ff2l. Qed.

  (** v2l (l2v l) = l *)
  Lemma v2l_l2v : forall {n} (l : list A), length l = n -> v2l (@l2v n l) = l.
  Proof. intros. unfold l2v,v2l. apply ff2l_l2ff; auto. Qed.

End l2v_v2l.


(* ======================================================================= *)
(** ** vector with specific size *)
Section vec_specific.
  Context {A} {Azero : A}.
  Variable a1 a2 a3 a4 : A.
  
  Definition mkvec0 : @vec A 0 := fun _ => Azero. (* anything is ok *)
  Definition mkvec1 : @vec A 1 := l2v Azero _ [a1].
  Definition mkvec2 : @vec A 2 := l2v Azero _ [a1;a2].
  Definition mkvec3 : @vec A 3 := l2v Azero _ [a1;a2;a3].
  Definition mkvec4 : @vec A 4 := l2v Azero _ [a1;a2;a3;a4].
End vec_specific.


(* ======================================================================= *)
(** ** 自然基的基向量 *)
Section veye.
  Context {A} (Azero Aone : A).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation vzero := (vzero 0).
  Context {one_neq_zero : 1 <> 0}.

  Definition veye {n} (i : fin n) : @vec A n := fun j => if i ??= j then 1 else 0.

  (** (veye i).i = 1 *)
  Lemma vnth_veye_eq : forall {n} i, (@veye n i) $ i = 1.
  Proof. intros. unfold veye. destruct (_??=_); easy. Qed.

  (** (veye i).j = 0 *)
  Lemma vnth_veye_neq : forall {n} i j, i <> j -> (@veye n i) $ j = 0.
  Proof. intros. unfold veye. destruct (_??=_); easy. Qed.
  
  (** veye <> 0 *)
  Lemma veye_neq0 : forall {n} i, @veye n i <> vzero.
  Proof.
    intros. intro. rewrite veq_iff_vnth in H. specialize (H i).
    rewrite vnth_veye_eq, vnth_vzero in H. easy.
  Qed.
  
End veye.


(* ======================================================================= *)
(** ** natural basis, 自然基（最常见的一种标准正交基) *)
Section veyes.
  Context {A} (Azero Aone : A).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation vzero := (vzero 0).
  Context {one_neq_zero : 1 <> 0}.

  Definition veyes (n : nat) : @vec (@vec A n) n := fun i => veye Azero Aone i.

  (** veyes.ii = 1 *)
  Lemma vnth_veyes_eq : forall {n} i, (veyes n) $ i $ i = 1.
  Proof. intros. unfold veyes. apply vnth_veye_eq. Qed.

  (** veyes.ij = 0 *)
  Lemma vnth_veyes_neq : forall {n} i j, i <> j -> (veyes n) $ i $ j = 0.
  Proof. intros. unfold veyes. apply vnth_veye_neq; auto. Qed.
  
End veyes.



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

  (* vmap2 f u v = vmap id (fun i => f u.i v.i) *)
  Lemma vmap2_eq_vmap : forall {n} (u v : vec n),
      vmap2 u v = vmap (fun a => a) (fun i => f (u $ i) (v $ i)).
  Proof. intros. auto. Qed.
  
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
(** ** A proposition which all elements of the vector hold *)
Section vforall.
  Context {A : Type}.

  (** Every element of `v` satisfy the `P` *)
  Definition vforall {n} (v : @vec A n) (P : A -> Prop) : Prop := forall i, P (v $ i).
  
End vforall.


(* ======================================================================= *)
(** ** A proposition which at least one element of the vector holds *)
Section vexist.
  Context {A : Type}.

  (** There exist element of `v` satisfy the `P` *)
  Definition vexist {n} (v : @vec A n) (P : A -> Prop) : Prop := exists i, P (v $ i).
  
End vexist.


(* ======================================================================= *)
(** ** An element belongs to the vector *)
Section vmem.
  Context {A : Type}.

  (** Element `a` belongs to the vector `v` *)
  Definition vmem {n} (v : @vec A n) (a : A) : Prop := vexist v (fun x => x = a).
  
End vmem.


(* ======================================================================= *)
(** ** An vector belongs to another vector *)
Section vmems.
  Context {A : Type}.

  (** Every element of vector `u` belongs to vector `v` *)
  Definition vmems {r s} (u : @vec A r) (v : @vec A s) : Prop :=
    vforall u (fun x => vmem v x).
  
End vmems.


(* (* ======================================================================= *) *)
(* (** ** An vector belongs to one but not belong to another *) *)
(* Section vdiff. *)
(*   Context {A : Type}. *)

(*   (** Elements belong to vector `u` but not belongs to vector `v` *) *)
(*   Definition vdiff {r s} (u : @vec A r) (v : @vec A s) : Prop. *)
(*     Check fun i => vmem  *)
(*     vforall u (fun x => vmem v x). *)
  
(* End vmems. *)


(* ======================================================================= *)
(** ** Get column of a 2D vector *)
Section vcol.
  Context {A} {Azero : A}.

  (** Set i-th element vector `vs` *)
  Definition vcol {n r} (vs : @vec (@vec A n) r) (i : fin n) : @vec A r :=
    vmap (fun v => v $ i) vs.

  (** (vcol vs i).j = v.j.i *)
  Lemma vnth_vcol : forall {n r} (vs : @vec (@vec A n) r) (i : fin n) (j : fin r),
      (vcol vs i) $ j = vs $ j $ i.
  Proof. intros. unfold vcol. auto. Qed.
  
End vcol.


(* ======================================================================= *)
(** ** Set element of a vector *)
Section vset.
  Context {A} {Azero : A}.

  (** Set i-th element vector `v` *)
  Definition vset {n} (v : @vec A n) (i : fin n) (a : A) : @vec A n :=
    fun j => if j ??= i then a else v $ j.

  (** (vset v i a).i = a *)
  Lemma vnth_vset_eq : forall {n} (v : @vec A n) (i : fin n) (a : A),
      (vset v i a) $ i = a.
  Proof. intros. unfold vset. destruct (_??=_); auto. easy. Qed.
  
  (** (vset v i a).j = v $ j *)
  Lemma vnth_vset_neq : forall {n} (v : @vec A n) (i j : fin n) (a : A),
      i <> j -> (vset v i a) $ j = v $ j.
  Proof. intros. unfold vset. destruct (_??=_); auto. subst. easy. Qed.
  
End vset.


(* ======================================================================= *)
(** ** Insert element to a vector *)
Section vinsert.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).
  
  (** Insert element to vector `v` at i-th position *)
  Definition vinsert {n} (v : @vec A n) (i : fin (S n)) (a : A) : @vec A (S n).
    intros j. destruct (lt_eq_lt_dec (fin2nat j) (fin2nat i)) as [[H|]|H].
    - refine (v $ (fin2PredRange j _)). apply Nat.lt_le_trans with (fin2nat i); auto.
      apply PeanoNat.lt_n_Sm_le. apply fin2nat_lt.
    - apply a.
    - refine (v $ (fin2PredRangePred j _)).
      apply Nat.lt_lt_0 in H; auto.
  Defined.

  (* Another definition, which have simpler logic, but need `Azero`. *)
  Definition vinsert' {n} (v : @vec A n) (i : fin (S n)) (a : A) : @vec A (S n) :=
    f2v (fun j => if (j ??< fin2nat i)%nat
                then (v2f v) j
                else (if (j ??= fin2nat i)%nat
                      then a
                      else (v2f v) (pred j))).

  (* These two definitions are equivalent *)
  Lemma vinsert_eq_vinsert' : forall {n} (v : @vec A n) (i : fin (S n)) (a : A),
      vinsert v i a = vinsert' v i a.
  Proof.
    intros. apply veq_iff_vnth; intros j.
    unfold vinsert, vinsert', f2v, f2ff, v2f,ff2f.
    unfold fin2PredRange, fin2PredRangePred.
    destruct i as [i Hi], j as [j Hj]; simpl.
    destruct (lt_eq_lt_dec j i) as [[H|H]|H]; simpl.
    - destruct (_??<_), (_??<_); try lia. f_equal. apply sig_eq_iff; auto.
    - destruct (_??<_); try lia. destruct (_??=_)%nat; try lia. auto.
    - destruct (_??<_); try lia. destruct (_??=_)%nat; try lia.
      destruct (_??<_); try lia. f_equal. apply sig_eq_iff; auto.
  Qed.

  (** j < i -> (vinsert v i a).j = v.i *)
  Lemma vinsert_spec1 : forall {n} (v : @vec A n) (i : fin (S n)) (a : A) (j : nat),
      j < fin2nat i -> v2f (vinsert v i a) j = v2f v j.
  Proof.
    intros. rewrite vinsert_eq_vinsert'. pose proof (fin2nat_lt i).
    unfold vinsert',v2f,f2v,f2ff,ff2f. destruct i as [i Hi]. simpl in *.
    destruct (_??<_),(_??<_); try lia; simpl.
    destruct (_??<_); try lia. auto.
  Qed.

  (** j = i -> (vinsert v i a).j = a *)
  Lemma vinsert_spec2 : forall {n} (v : @vec A n) (i : fin (S n)) (a : A) (j : nat),
      j = fin2nat i -> v2f (vinsert v i a) j = a.
  Proof.
    intros. rewrite vinsert_eq_vinsert'. rewrite H. pose proof (fin2nat_lt i).
    unfold vinsert',v2f,f2v,f2ff,ff2f. destruct i as [i Hi]. simpl in *.
    destruct (_??<_); try lia; simpl.
    destruct (_??<_); try lia. destruct (_??=_)%nat; try lia. auto.
  Qed.
  
  (** i < j -> j <= n -> (vinsert v i a).j = v.(S i) *)
  Lemma vinsert_spec3 : forall {n} (v : @vec A n) (i : fin (S n)) (a : A) (j : nat),
      fin2nat i < j -> j <= n -> v2f (vinsert v i a) j = v2f v (pred j).
  Proof.
    intros. rewrite vinsert_eq_vinsert'. pose proof (fin2nat_lt i).
    unfold vinsert',v2f,f2v,f2ff,ff2f. destruct i as [i Hi]. simpl in *.
    destruct (_??<_),(_??<_); try lia. destruct (_??=_)%nat; auto; try lia.
  Qed.
  
  (** j < i -> (vinsert v i a).j = v.j *)
  Lemma vnth_vinsert_lt : forall {n} (v : @vec A n) (i : fin (S n)) a (j : fin n) j',
      fin2nat j < fin2nat i -> j' = fin2SuccRange j -> (vinsert v i a) $ j' = v $ j.
  Proof.
    intros. subst.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    pose proof (vinsert_spec1 v i a (fin2nat j) H).
    destruct i as [i Hi], j as [j Hj]. simpl in *. v2f Azero. rewrite <- H2.
    unfold v2f,ff2f,nat2fin,fin2SuccRange in *.
    destruct (_??<_),(_??<_); try lia. f_equal. simpl. apply nat2finS_eq.
  Qed.

  (** (vinsert v i a).i = a *)
  Lemma vnth_vinsert_eq : forall {n} (v : @vec A n) (i : fin (S n)) a,
      (vinsert v i a) $ i = a.
  Proof.
    intros. pose proof (vinsert_spec2 v i a (fin2nat i) eq_refl).
    v2f Azero. rewrite ff2f_fin2nat in *. auto.
  Qed.

  (** i <= j -> j < n -> (vinsert v i a).j = v.(pred j) *)
  Lemma vnth_vinsert_gt : forall {n} (v : @vec A n) (i : fin (S n)) a (j : fin n) j',
      fin2nat i <= fin2nat j -> fin2nat j < n -> j' = fin2SuccRangeSucc j ->
      (vinsert v i a) $ j' = v $ j.
  Proof.
    intros. subst. pose proof (vinsert_spec3 v i a (S (fin2nat j))).
    assert (fin2nat i < S (fin2nat j)); try lia.
    assert (S (fin2nat j) <= n). pose proof (fin2nat_lt j); lia.
    specialize (H1 H2 H3). clear H2 H3. simpl in *. v2f Azero.
    rewrite ff2f_fin2nat in H1. rewrite <- H1.
    erewrite <- !nth_ff_to_nth_f. f_equal. destruct j. cbv. apply sig_eq_iff; auto.
    Unshelve. pose proof (fin2nat_lt j). lia.
  Qed.
    
  (** i < j -> j <= n -> (vinsert v i a).j = v.(pred j) *)
  Lemma vnth_vinsert_gt_old : forall {n} (v : @vec A n) (i : fin (S n)) a (j : fin n) j',
      fin2nat i < fin2nat j -> fin2nat j <= n -> j' = fin2SuccRangeSucc j ->
      (vinsert v i a) $ j' = v $ j.
  Proof.
    intros. subst. pose proof (vinsert_spec3 v i a (S (fin2nat j))).
    assert (fin2nat i < S (fin2nat j)); try lia.
    assert (S (fin2nat j) <= n). pose proof (fin2nat_lt j); lia.
    specialize (H1 H2 H3). clear H2 H3. simpl in *. v2f Azero.
    rewrite ff2f_fin2nat in H1. rewrite <- H1.
    erewrite <- !nth_ff_to_nth_f. f_equal. destruct j. cbv. apply sig_eq_iff; auto.
    Unshelve. pose proof (fin2nat_lt j). lia.
  Qed.

  (** (vzero <<- Azero) = vzero *)
  Lemma vinsert_v0_a0 : forall {n} i, @vinsert n vzero i Azero = vzero.
  Proof.
    intros. rewrite vinsert_eq_vinsert'.
    apply veq_iff_vnth; intros j. rewrite vnth_vzero.
    destruct i as [i Hi], j as [j Hj].
    unfold vinsert',f2v,f2ff,v2f,ff2f; simpl.
    destruct (_??<_). destruct (_??<_); auto.
    destruct (_??=_)%nat; auto. destruct (_??<_); auto.
  Qed.

  (** (v <<- a) = vzero -> a = Azero *)
  Lemma vinsert_eq0_imply_a0 {AeqDec : Dec (@eq A)} : forall {n} (v : @vec A n) i a,
      vinsert v i a = vzero -> a = Azero.
  Proof.
    intros. rewrite veq_iff_vnth in *. specialize (H i).
    rewrite vnth_vzero in H. rewrite <- H.
    symmetry. apply vnth_vinsert_eq.
  Qed.

  (** (v <<- a) = vzero -> v = vzero *)
  Lemma vinsert_eq0_imply_v0 {AeqDec : Dec (@eq A)} : forall {n} (v : @vec A n) i a,
      vinsert v i a = vzero -> v = vzero.
  Proof.
    intros.
    pose proof (vinsert_eq0_imply_a0 v i a H). subst.
    rewrite !veq_iff_vnth in *. intros j.
    destruct (fin2nat j ??< fin2nat i) as [Hlt|Hlt].
    - specialize (H (fin2SuccRange j)).
      rewrite vnth_vinsert_lt with (j:=j) in H; auto.
    - destruct (fin2nat j ??> fin2nat i) as [Hgt|Hgt].
      + specialize (H (fin2SuccRangeSucc j)).
        rewrite vnth_vinsert_gt with (j:=j) in H; auto.
        pose proof (fin2nat_lt j). lia. apply fin2nat_lt.
      + assert (fin2nat i = fin2nat j). lia. rewrite vnth_vzero.
        rewrite vinsert_eq_vinsert' in H.
        unfold vinsert',f2v,f2ff,v2f,ff2f in H.
        specialize (H (fin2SuccRangeSucc j)).
        destruct i as [i Hi], j as [j Hj]; simpl in *.
        rewrite vnth_vzero in H.
        destruct (_??<_); try lia.
        destruct (_??=_)%nat; try lia.
        destruct (_??<_); try lia.
        rewrite <- H. f_equal. cbv. apply sig_eq_iff; auto.
  Qed.

  (** (v <<- a) = vzero <-> v = vzero /\ a = Azero  *)
  Lemma vinsert_eq0_iff {AeqDec : Dec (@eq A)} : forall {n} (v : @vec A n) i a,
      vinsert v i a = vzero <-> (v = vzero /\ a = Azero).
  Proof.
    intros. destruct (Aeqdec v vzero) as [Hv|Hv], (Aeqdec a Azero) as [Ha|Ha]; auto.
    - subst. split; intros; auto. apply vinsert_v0_a0.
    - subst. split; intros.
      + exfalso. rewrite veq_iff_vnth in H. specialize (H i).
        rewrite vnth_vinsert_eq in H. cbv in H. easy.
      + destruct H. easy.
    - subst. split; intro.
      + split; auto. apply vinsert_eq0_imply_v0 in H; auto.
      + destruct H. subst. apply vinsert_v0_a0.
    - split; intros.
      + split. apply vinsert_eq0_imply_v0 in H; auto.
        apply vinsert_eq0_imply_a0 in H; auto.
      + destruct H; subst. apply vinsert_v0_a0.
  Qed.

  (** (v <<- a) <> vzero <-> v <> vzero \/ a <> Azero  *)
  Lemma vinsert_neq0_iff {AeqDec : Dec (@eq A)} : forall {n} (v : @vec A n) i a,
      vinsert v i a <> vzero <-> (v <> vzero \/ a <> Azero).
  Proof. intros. rewrite vinsert_eq0_iff. tauto. Qed.

End vinsert.

Section test.
  Let n := 5.
  Let v1 := l2v 9 n [1;2;3;4;5].
  (* Compute v2l (vinsert v1 (nat2finS 1) 7). *)
  (* Compute v2l (vinsert v1 (nat2finS 5) 7). *)
End test.    


(* ======================================================================= *)
(** ** Remove one element *)
Section vremove.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).

  (** A vector that removes i-th element from `v` *)
  Definition vremove {n} (v : @vec A (S n)) (i : fin (S n)) : @vec A n :=
    fun j => if fin2nat j ??< fin2nat i
           then v (fin2SuccRange j)
           else v (fin2SuccRangeSucc j). 

  (* Another definition, which have simpler logic, but need `Azero`. *)
  Definition vremove' {n} (v : @vec A (S n)) (i : fin (S n)) : @vec A n :=
    f2v (fun j => if j ??< (fin2nat i) then v2f v j else v2f v (S j)).
  
  (* These two definitions are equivalent *)
  Lemma vremove_eq_vremove' : forall {n} (v : @vec A (S n)) (i : fin (S n)),
      vremove v i = vremove' v i.
  Proof.
    intros. apply veq_iff_vnth; intros j.
    unfold vremove, vremove', f2v, f2ff, v2f,ff2f.
    unfold fin2SuccRange, fin2SuccRangeSucc. erewrite nat2finS_eq.
    destruct i as [i Hi], j as [j Hj]; simpl.
    destruct (_??<_), (_??<_); cbv; try lia; f_equal; cbv; apply sig_eq_iff; auto.
    Unshelve. pose proof (fin2nat_lt j). lia.
  Qed.

  (** j < i -> (vremove v i).j = v.j *)
  Lemma vremove_spec1 : forall {n} (v : @vec A (S n)) (i : fin (S n)) (j : nat),
      j < fin2nat i -> v2f (vremove v i) j = v2f v j.
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold v2f,vremove',f2v,f2ff,ff2f.
    destruct i as [i Hi]; simpl in *.
    destruct (_??<_),(_??<_); auto; try lia.
  Qed.
  
  (** i <= j -> j < n -> (vremove v i).j = v.(S j) *)
  Lemma vremove_spec2 : forall {n} (v : @vec A (S n)) (i : fin (S n)) (j : nat),
      fin2nat i <= j -> j < n -> v2f (vremove v i) j = v2f v (S j).
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f,f2ff,ff2f.
    destruct i as [i Hi]; simpl in *.
    destruct (_??<_),(_??<_); auto; try lia.
  Qed.

  (** j < i -> (vremove v i).j = v.j *)
  Lemma vnth_vremove_lt : forall {n} (v : @vec A (S n)) (i : fin (S n)) (j : fin n),
      fin2nat j < fin2nat i -> (vremove v i) $ j = v2f v (fin2nat j).
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f,f2ff,ff2f.
    destruct i as [i Hi], j as [j Hj]; simpl in *.
    destruct (_??<_),(_??<_); auto; try lia.
  Qed.
  
  (** i <= j -> j < n -> (vremove v i).j = v.(S j) *)
  Lemma vnth_vremove_ge : forall {n} (v : @vec A (S n)) (i : fin (S n)) (j : fin n),
      fin2nat i <= fin2nat j -> fin2nat j < n ->
      (vremove v i) $ j = v2f v (S (fin2nat j)).
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f,f2ff,ff2f.
    destruct i as [i Hi], j as [j Hj]; simpl in *.
    destruct (_??<_),(_??<_); auto; try lia.
  Qed.

  (** vremove (vinsert v i a) i = v *)
  Lemma vremove_vinsert : forall {n} (v : @vec A n) (i : fin (S n)) (a : A),
      vremove (vinsert v i a) i = v.
  Proof.
    intros. rewrite vremove_eq_vremove', (vinsert_eq_vinsert' (Azero:=Azero)).
    apply veq_iff_vnth; intros j.
    destruct i as [i Hi], j as [j Hj].
    unfold vremove',vinsert',f2v,v2f,f2ff,ff2f; simpl in *.
    destruct (_??<_),(_??<_); try lia.
    - destruct (_??<_); try lia. f_equal. cbv. apply sig_eq_iff; auto.
    - destruct (_??<_); try lia. destruct (_??=_)%nat; try lia.
      destruct (_??<_); try lia. f_equal. cbv. apply sig_eq_iff; auto.
  Qed.
  
  (** vinsert (vremove v i) (v $ i) = v *)
  Lemma vinsert_vremove : forall {n} (v : @vec A (S n)) (i : fin (S n)),
      vinsert (vremove v i) i (v $ i) = v.
  Proof.
    intros. rewrite vremove_eq_vremove', (vinsert_eq_vinsert' (Azero:=Azero)).
    apply veq_iff_vnth; intros j.
    destruct i as [i Hi], j as [j Hj].
    unfold vremove',vinsert',f2v,v2f,f2ff,ff2f; simpl in *.
    destruct (_??<_),(_??<_); try lia.
    - destruct (_??<_); try lia. f_equal. cbv. apply sig_eq_iff; auto.
    - destruct (_??=_)%nat; try lia.
      + subst. f_equal. cbv. apply sig_eq_iff; auto.
      + destruct (_??<_); try lia. destruct (_??<_); try lia.
        f_equal. cbv. apply sig_eq_iff; auto. destruct j; lia.
    - destruct (_??=_)%nat; try lia. f_equal. cbv. apply sig_eq_iff; auto.
  Qed.

  (* (** i <> j -> vremove (vset v i a) j = vremove v j *) *)
  (* Lemma vremove_vset : forall {n} (v : @vec A (S n)) (i j : fin (S n)) (a : A), *)
  (*     i <> j -> vremove (vset v i a) j = vremove v j. *)
  (* Proof. *)
  (*   intros. apply veq_iff_vnth; intros k. *)
  (*   pose proof (fin2nat_lt i). pose proof (fin2nat_lt j). pose proof (fin2nat_lt k). *)
  (*   destruct (fin2nat k ??< fin2nat j). *)
  (*   - rewrite !vnth_vremove_lt; auto. *)
  (*     assert (fin2nat k < S n). lia. *)
  (*     rewrite !nth_v2f with (H:=H3). *)
  (*     destruct k as [k Hk]. simpl. *)
  (*     rewrite nat2fin_fin2nat. *)
  (*     unfold vset. *)
  (*     rewrite vnth_vset_neq; auto. *)
  (*     destruct i, j, k. simpl in *. intro. apply sig_eq_iff in H4. subst. lia. *)
  (*     ? *)
  (*     rewrite nat2fin_fin2nat. *)
  (*   H2 : i <> j *)
  (* ============================ *)
  (* vremove vs j = vremove (vset vs i (lcomb cs vs)) j *)

  
End vremove.

Section vmap_vinsert_vremove.
  Context {A B C : Type} {Azero : A} {Bzero : B} {Czero : C}.
  Context (f1 : A -> B).
  Context (f2 : A -> B -> C).

  (** vmap2 (vinsert u i ui) v = vinsert (vmap2 u (vremove v i)) i (f ui v.i) *)
  Lemma vmap2_vinsert_l : forall {n} (u : @vec A n) (v : @vec B (S n)) i (ui : A),
      vmap2 f2 (vinsert u i ui) v = vinsert (vmap2 f2 u (vremove v i)) i (f2 ui (v$i)).
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    destruct (lt_eq_lt_dec (fin2nat j) (fin2nat i)) as [[H|H]|H].
    - assert (fin2nat j < n). pose proof (fin2nat_lt i). lia.
      rewrite (@vnth_vinsert_lt _ Czero) with (j:=fin2PredRange j H0); auto.
      + rewrite vnth_vmap2. f_equal.
        * apply (@vnth_vinsert_lt _ Azero). rewrite fin2nat_fin2PredRange. auto.
          rewrite fin2SuccRange_fin2PredRange; auto.
        * rewrite (vnth_vremove_lt (Azero:=Bzero)); auto. simpl.
          assert (fin2nat j < S n) by lia.
          rewrite nth_v2f with (H:=H1). f_equal. rewrite nat2fin_fin2nat; auto.
      + rewrite fin2SuccRange_fin2PredRange; auto.
    - assert (i = j). apply fin2nat_inj; auto. rewrite <- H0.
      rewrite (@vnth_vinsert_eq _ Azero). rewrite (@vnth_vinsert_eq _ Czero). auto.
    - pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
      assert (0 < fin2nat j) by lia.
      rewrite (@vnth_vinsert_gt _ Azero) with (j:=fin2PredRangePred j H2);
        simpl in *; try lia.
      2:{ rewrite fin2SuccRangeSucc_fin2PredRangePred; auto. }
      rewrite (@vnth_vinsert_gt _ Czero) with (j:=fin2PredRangePred j H2);
        simpl in *; try lia.
      2:{ rewrite fin2SuccRangeSucc_fin2PredRangePred; auto. }
      rewrite vnth_vmap2. f_equal.
      rewrite (@vnth_vremove_ge _ Bzero); simpl in *; try lia.
      destruct j as [j Hj]. simpl.
      assert (S (pred j) < S n). lia. rewrite nth_v2f with (H:=H3). f_equal.
      apply sig_eq_iff. rewrite Nat.succ_pred_pos; auto.
  Qed.
    
  (** vmap2 u (vinsert v i vi) = vinsert (vmap2 (vremove u i) v) i (f u.i vi) *)
  Lemma vmap2_vinsert_r : forall {n} (u : @vec A (S n)) (v : @vec B n) i (vi : B),
      vmap2 f2 u (vinsert v i vi) = vinsert (vmap2 f2 (vremove u i) v) i (f2 (u$i) vi).
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    destruct (lt_eq_lt_dec (fin2nat j) (fin2nat i)) as [[H|H]|H].
    - assert (fin2nat j < n). pose proof (fin2nat_lt i). lia.
      rewrite (@vnth_vinsert_lt _ Czero) with (j:=fin2PredRange j H0); auto.
      + rewrite vnth_vmap2. f_equal.
        * rewrite (vnth_vremove_lt (Azero:=Azero)); auto. simpl.
          assert (fin2nat j < S n) by lia.
          rewrite nth_v2f with (H:=H1). f_equal. rewrite nat2fin_fin2nat; auto.
        * apply (@vnth_vinsert_lt _ Bzero). rewrite fin2nat_fin2PredRange. auto.
          rewrite fin2SuccRange_fin2PredRange; auto.
      + rewrite fin2SuccRange_fin2PredRange; auto.
    - assert (i = j). apply fin2nat_inj; auto. rewrite <- H0.
      rewrite (@vnth_vinsert_eq _ Bzero). rewrite (@vnth_vinsert_eq _ Czero). auto.
    - pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
      assert (0 < fin2nat j) by lia.
      rewrite (@vnth_vinsert_gt _ Bzero) with (j:=fin2PredRangePred j H2);
        simpl in *; try lia.
      2:{ rewrite fin2SuccRangeSucc_fin2PredRangePred; auto. }
      rewrite (@vnth_vinsert_gt _ Czero) with (j:=fin2PredRangePred j H2);
        simpl in *; try lia.
      2:{ rewrite fin2SuccRangeSucc_fin2PredRangePred; auto. }
      rewrite vnth_vmap2. f_equal.
      rewrite (@vnth_vremove_ge _ Azero); simpl in *; try lia.
      destruct j as [j Hj]. simpl.
      assert (S (pred j) < S n). lia. rewrite nth_v2f with (H:=H3). f_equal.
      apply sig_eq_iff. rewrite Nat.succ_pred_pos; auto.
  Qed.

  (** vmap f (vremove v i) = vremove (vmap f v) i *)
  Lemma vmap_vremove : forall {n} (v : @vec A (S n)) i,
      vmap f1 (vremove v i) = vremove (vmap f1 v) i.
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (fin2nat j ??< fin2nat i).
    - rewrite (vnth_vremove_lt (Azero:=Azero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Bzero)); auto.
      erewrite !nth_v2f. unfold vmap. auto.
    - rewrite (vnth_vremove_ge (Azero:=Azero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Bzero)); try lia.
      erewrite !nth_v2f. unfold vmap. auto.
      Unshelve. lia. lia.
  Qed.

  (** vmap2 f (vremove u i) (vremove v i) = vremove (vmap2 u v) i *)
  Lemma vmap2_vremove_vremove : forall {n} (u : @vec A (S n)) (v : @vec B (S n)) i,
      vmap2 f2 (vremove u i) (vremove v i) = vremove (vmap2 f2 u v) i.
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (fin2nat j ??< fin2nat i).
    - rewrite (vnth_vremove_lt (Azero:=Azero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Bzero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Czero)); auto.
      erewrite !nth_v2f. rewrite vnth_vmap2. auto.
    - rewrite (vnth_vremove_ge (Azero:=Azero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Bzero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Czero)); try lia.
      erewrite !nth_v2f. rewrite vnth_vmap2. auto.
      Unshelve. lia. lia.
  Qed.

End vmap_vinsert_vremove.


(* ======================================================================= *)
(** ** Get head or tail element *)
Section vhead_vtail.
  Context {A} {Azero : A}.

  (** Get head element *)
  Definition vhead {n} (v : @vec A (S n)) : A := v $ fin0.

  (** vhead v is = v.0 *)
  Lemma vhead_spec : forall {n} (v : @vec A (S n)), vhead v = (v2f Azero v) 0.
  Proof.
    intros. unfold vhead. erewrite nth_v2f. f_equal.
    apply sig_eq_iff; auto. Unshelve. lia.
  Qed.

  (** vhead v = v $ 0 *)
  Lemma vhead_eq : forall {n} (v : @vec A (S n)), vhead v = v $ fin0.
  Proof. auto. Qed.

  
  (** Get tail element *)
  Definition vtail {n} (v : @vec A (S n)) : A := v $ (nat2finS n).

  (** vtail v is = v.(n - 1) *)
  Lemma vtail_spec : forall {n} (v : @vec A (S n)), vtail v = (v2f Azero v) n.
  Proof.
    intros. unfold vtail. erewrite nth_v2f. erewrite nat2finS_eq. f_equal.
    apply sig_eq_iff; auto. Unshelve. all: lia.
  Qed.

  (** vtail v = v $ (n - 1) *)
  Lemma vtail_eq : forall {n} (v : @vec A (S n)), vtail v = v $ (nat2finS n).
  Proof.
    intros. rewrite vtail_spec. erewrite nth_v2f. erewrite nat2finS_eq. f_equal.
    apply sig_eq_iff; auto. Unshelve. all: lia.
  Qed.

End vhead_vtail.


(* ======================================================================= *)
(** ** Get head or tail elements *)
Section vheadN_vtailN.
  Context {A} {Azero : A}.

  (** Get head elements *)
  Definition vheadN {m n} (v : @vec A (m + n)) : @vec A m :=
    fun i => v $ (fin2AddRangeR i).

  (* i < m -> (vheadN v).i = (v2f v).i *)
  Lemma vheadN_spec : forall {m n} (v : @vec A (m + n)) i,
      i < m -> v2f Azero (vheadN v) i = (v2f Azero v) i.
  Proof.
    intros. unfold vheadN. erewrite !nth_v2f. f_equal.
    apply fin2nat_imply_nat2fin. simpl. auto.
    Unshelve. all: try lia.
  Qed.

  (** (vheadN v).i = v.i *)
  Lemma vnth_vheadN : forall {m n} (v : @vec A (m + n)) i,
      (vheadN v) $ i = v $ (fin2AddRangeR i).
  Proof. auto. Qed.

  
  (** Get tail elements *)
  Definition vtailN {m n} (v : @vec A (m + n)) : @vec A n :=
    fun i => v $ (fin2AddRangeAddL i).

  (** i < n -> (vtailN v).i = (v2f v).(m + i) *)
  Lemma vtailN_spec : forall {m n} (v : @vec A (m + n)) i,
      i < n -> v2f Azero (vtailN v) i = (v2f Azero v) (m + i).
  Proof.
    intros. unfold vtailN. erewrite !nth_v2f. f_equal.
    apply fin2nat_imply_nat2fin. simpl. auto.
    Unshelve. all: try lia.
  Qed.

  (** (vtailN v).i = v.(n + i) *)
  Lemma vnth_vtailN : forall {m n} (v : @vec A (m + n)) i,
      (vtailN v) $ i = v $ (fin2AddRangeAddL i).
  Proof. auto. Qed.

End vheadN_vtailN.


(* ======================================================================= *)
(** ** Remove exact one element at head or tail *)
Section vremoveH_vremoveT.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).

  (** *** vremoveH *)
  
  (** Remove head element *)
  Definition vremoveH {n} (v : @vec A (S n)) : @vec A n :=
    fun i => v $ (fin2SuccRangeSucc i).

  (** i < n -> (vremoveH v).i = v.(S i) *)
  Lemma vremoveH_spec : forall {n} (v : @vec A (S n)) (i : nat),
      i < n -> v2f (vremoveH v) i = v2f v (S i).
  Proof.
    intros. unfold vremoveH,v2f,ff2f.
    destruct (_??<_),(_??<_); auto; try lia. f_equal. apply sig_eq_iff; auto.
  Qed.
  
  (** (vremoveH v).i = v.(S i) *)
  Lemma vnth_vremoveH : forall {n} (v : @vec A (S n)) (i : fin n),
      (vremoveH v) $ i = v $ (fin2SuccRangeSucc i).
  Proof. intros. unfold vremoveH. auto. Qed.
  
  (** v <> 0 -> vhead v = 0 -> vremoveH v <> 0 *)
  Lemma vremoveH_neq0_if : forall {n} (v : @vec A (S n)),
      v <> vzero Azero -> vhead v = Azero -> vremoveH v <> vzero Azero.
  Proof.
    intros. intro. destruct H. apply veq_iff_vnth; intros.
    rewrite veq_iff_vnth in H1. unfold vremoveH in H1. rewrite vhead_eq in H0.
    destruct (fin2nat i ??= 0)%nat.
    - assert (i = fin0).
      { eapply fin2nat_imply_nat2fin in e. rewrite <- e. apply sig_eq_iff; auto. }
      rewrite H,H0. cbv. auto.
    - assert (0 < fin2nat i). pose proof (fin2nat_lt i). lia.
      specialize (H1 (fin2PredRangePred i H)).
      rewrite fin2SuccRangeSucc_fin2PredRangePred in H1. rewrite H1. cbv. auto.
      Unshelve. lia.
  Qed.

  
  (** *** vremoveT *)

  (** Remove tail element *)
  Definition vremoveT {n} (v : @vec A (S n)) : @vec A n :=
    fun i => v $ (fin2SuccRange i).

  (** i < n -> (vremoveT v).i = v.i *)
  Lemma vremoveT_spec : forall {n} (v : @vec A (S n)) (i : nat),
      i < n -> v2f (vremoveT v) i = v2f v i.
  Proof.
    intros. unfold vremoveT,v2f,ff2f.
    destruct (_??<_),(_??<_); auto; try lia. f_equal.
    rewrite fin2SuccRange_nat2fin with (H0:=l0). apply sig_eq_iff; auto.
  Qed.
  
  (** (vremoveT v).i = v.i *)
  Lemma vnth_vremoveT : forall {n} (v : @vec A (S n)) (i : fin n),
      (vremoveT v) $ i = v $ (fin2SuccRange i).
  Proof. intros. unfold vremoveT. auto. Qed.
  
  (** v <> 0 -> vtail v = 0 -> vremoveT v <> 0 *)
  Lemma vremoveT_neq0_if : forall {n} (v : @vec A (S n)),
      v <> vzero Azero -> vtail v = Azero -> vremoveT v <> vzero Azero.
  Proof.
    intros. intro. destruct H. apply veq_iff_vnth; intros.
    rewrite veq_iff_vnth in H1. unfold vremoveT in H1.
    rewrite (vtail_eq (Azero:=Azero)) in H0.
    destruct (fin2nat i ??= n)%nat.
    - assert (i = nat2finS n).
      { eapply fin2nat_imply_nat2fin in e. rewrite <- e.
        erewrite nat2finS_eq. apply sig_eq_iff; auto. }
      rewrite H,H0. cbv. auto.
    - assert (fin2nat i < n). pose proof (fin2nat_lt i). lia.
      specialize (H1 (fin2PredRange i H)).
      rewrite fin2SuccRange_fin2PredRange in H1. rewrite H1. cbv. auto.
      Unshelve. all: lia.
  Qed.

End vremoveH_vremoveT.


(* ======================================================================= *)
(** ** Remove elements at head or tail *)
Section vremoveHN_vremoveTN.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).

  (** *** vremoveHN *)
  
  (** Remove head elements *)
  Definition vremoveHN {m n} (v : @vec A (m + n)) : @vec A n :=
    fun i => v $ (fin2AddRangeAddL i).

  (** i < n -> (vremoveHN v).i = v.(m + i) *)
  Lemma vremoveHN_spec : forall {m n} (v : @vec A (m + n)) (i : nat),
      i < n -> v2f (vremoveHN v) i = v2f v (m + i).
  Proof.
    intros. unfold vremoveHN. erewrite !nth_v2f. f_equal.
    apply fin2nat_imply_nat2fin; simpl. auto.
    Unshelve. all: lia.
  Qed.
  
  (** (vremoveHN v).i = v.(m + i) *)
  Lemma vnth_vremoveHN : forall {m n} (v : @vec A (m + n)) (i : fin n),
      (vremoveHN v) $ i = v $ (fin2AddRangeAddL i).
  Proof. auto. Qed.
  
  (** v <> 0 -> vheadN v = 0 -> vremoveHN v <> 0 *)
  Lemma vremoveHN_neq0_if : forall {m n} (v : @vec A (m + n)),
      v <> vzero Azero -> vheadN v = vzero Azero -> vremoveHN v <> vzero Azero.
  Proof.
    intros. intro.
    rewrite veq_iff_vnth in H0. unfold vheadN in H0.
    rewrite veq_iff_vnth in H1. unfold vremoveHN in H1.
    destruct H. apply veq_iff_vnth; intros.
    destruct (m ??<= fin2nat i)%nat.
    - specialize (H1 (fin2AddRangeAddL' i l)).
      rewrite fin2AddRangeAddL_fin2AddRangeAddL' in H1. rewrite H1. cbv. auto.
    - assert (fin2nat i < m). lia.
      specialize (H0 (fin2AddRangeR' i H)).
      rewrite fin2AddRangeR_fin2AddRangeR' in H0. rewrite H0. cbv. auto.
  Qed.
  
  
  (** *** vremoveTN *)

  (** Remove tail elements *)
  Definition vremoveTN {m n} (v : @vec A (m + n)) : @vec A m :=
    fun i => v $ (fin2AddRangeR i).

  (** i < n -> (vremoveTN v).i = v.i *)
  Lemma vremoveTN_spec : forall {m n} (v : @vec A (m + n)) (i : nat),
      i < m -> v2f (vremoveTN v) i = v2f v i.
  Proof.
    intros. unfold vremoveTN,v2f,ff2f.
    destruct (_??<_),(_??<_); auto; try lia. f_equal. apply sig_eq_iff; auto.
  Qed.
  
  (** (vremoveTN v).i = v.i *)
  Lemma vnth_vremoveTN : forall {m n} (v : @vec A (m + n)) (i : fin m),
      (vremoveTN v) $ i = v $ (fin2AddRangeR i).
  Proof. intros. auto. Qed.
  
  (** v <> 0 -> vtailN v = 0 -> vremoveTN v <> 0 *)
  Lemma vremoveTN_neq0_if : forall {m n} (v : @vec A (m + n)),
      v <> vzero Azero -> vtailN v = vzero Azero -> vremoveTN v <> vzero Azero.
  Proof.
    intros. intro.
    rewrite veq_iff_vnth in H0. unfold vtailN in H0.
    rewrite veq_iff_vnth in H1. unfold vremoveTN in H1.
    destruct H. apply veq_iff_vnth; intros.
    destruct (m ??<= fin2nat i)%nat.
    - specialize (H0 (fin2AddRangeAddL' i l)).
      rewrite fin2AddRangeAddL_fin2AddRangeAddL' in H0. rewrite H0. cbv. auto.
    - assert (fin2nat i < m). lia.
      specialize (H1 (fin2AddRangeR' i H)).
      rewrite fin2AddRangeR_fin2AddRangeR' in H1. rewrite H1. cbv. auto.
  Qed.

End vremoveHN_vremoveTN.


(* ======================================================================= *)
(** ** Construct vector with one element at the head or tail position *)
Section vconsH_vconsT.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).

  (** *** vconsH *)

  (** cons at head: [a; v] *)
  Definition vconsH {n} (a : A) (v : @vec A n) : @vec A (S n).
    intros i. destruct (fin2nat i ??= 0)%nat. exact a.
    assert (0 < fin2nat i). apply neq_0_lt_stt. auto.
    apply (v $ (fin2PredRangePred i H)).
  Defined.

  (** i = 0 -> (v2f [a; v]) i = a *)
  Lemma vconsH_spec_0 : forall {n} a (v : @vec A n) (i : nat),
      i = 0 -> v2f (vconsH a v) i = a.
  Proof. intros. subst. unfold vconsH,v2f,ff2f; simpl. auto. Qed.

  (** 0 < i -> i < n -> [a; v].i = v.(pred i) *)
  Lemma vconsH_spec_gt0 : forall {n} a (v : @vec A n) (i : nat),
      0 < i -> i < n -> v2f (vconsH a v) i = v2f v (pred i).
  Proof.
    intros. unfold vconsH,v2f,ff2f; simpl. 
    destruct (_??<_),(_??<_); try lia. destruct (_??=_)%nat; try lia.
    f_equal. apply sig_eq_iff. simpl. auto.
  Qed.

  (** i = 0 -> [a; v].i = a *)
  Lemma vnth_vconsH_0 : forall {n} a (v : @vec A n) i,
      i = fin0 -> (vconsH a v) $ i = a.
  Proof. intros. subst. unfold vconsH. simpl. auto. Qed.
  
  (** 0 < i -> [a; v].i = v.(pred i)  *)
  Lemma vnth_vconsH_gt0 : forall {n} a (v : @vec A n) i (H: 0 < fin2nat i),
      (vconsH a v) $ i = v $ (fin2PredRangePred i H).
  Proof.
    intros. unfold vconsH. destruct (_??=_)%nat; try lia. f_equal.
    apply sig_eq_iff; auto.
  Qed.

  (** (a; v) = 0 <-> a = 0 /\ v = 0 *)
  Lemma vconsH_eq0_iff : forall {n} (v : @vec A n) a,
      vconsH a v = vzero Azero <-> a = Azero /\ v = vzero Azero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros; auto.
      + specialize (H fin0). rewrite vnth_vconsH_0 in H; auto.
      + specialize (H (fin2SuccRangeSucc i)). rewrite vnth_vzero in *. rewrite <- H.
        erewrite vnth_vconsH_gt0. f_equal.
        rewrite fin2PredRangePred_fin2SuccRangeSucc. auto.
    - destruct H. subst. destruct (fin2nat i ??= 0)%nat.
      + rewrite vnth_vconsH_0; auto. rewrite <- nat2fin_iff_fin2nat in e.
        rewrite <- e. apply sig_eq_iff. auto.
      + erewrite vnth_vconsH_gt0; auto.
        Unshelve. all: try lia. rewrite fin2nat_fin2SuccRangeSucc. lia.
  Qed.
  
  (** (a; v) <> 0 <-> a <> 0 \/ v <> 0 *)
  Lemma vconsH_neq0_iff : forall {n} (v : @vec A n) a,
      vconsH a v <> vzero Azero <-> a <> Azero \/ v <> vzero Azero.
  Proof.
    intros. rewrite vconsH_eq0_iff. split; intros.
    apply not_and_or in H; auto. apply or_not_and; auto.
  Qed.

  (** v = vconsH (vhead v) (vremoveH v) *)
  Lemma vconsH_vhead_vremoveH : forall {n} (v : @vec A (S n)),
      v = vconsH (vhead v) (vremoveH v).
  Proof.
    intros. apply veq_iff_vnth; intros. destruct (fin2nat i ??= 0)%nat as [H|H].
    - destruct i as [i Hi]. simpl in *. subst. rewrite vnth_vconsH_0.
      + rewrite vhead_eq. f_equal. apply sig_eq_iff; auto.
      + apply sig_eq_iff; auto.
    - erewrite vnth_vconsH_gt0. rewrite vnth_vremoveH. f_equal.
      rewrite fin2SuccRangeSucc_fin2PredRangePred. auto.
      Unshelve. lia.
  Qed.

  (** {a ∈ v} + {a ∈ ∉ v} *)
  Lemma vmem_dec : forall {AeqDec:Dec (@eq A)} {n} (v : @vec A n) (a : A),
      {vmem v a} + {~vmem v a}.
  Proof.
    intros. unfold vmem. unfold vexist. induction n.
    - right. intro. destruct H as [i H]. apply fin0_False; auto.
    - rewrite (vconsH_vhead_vremoveH v).
      destruct (Aeqdec (vhead v) a) as [H|H].
      + left. exists fin0. rewrite vnth_vconsH_0; auto.
      + destruct (IHn (vremoveH v)) as [H1|H1].
        * left. destruct H1 as [i H1]. exists (fin2SuccRangeSucc i).
          erewrite vnth_vconsH_gt0. rewrite fin2PredRangePred_fin2SuccRangeSucc. auto.
        * right. intro. destruct H1. destruct H0 as [i H0].
          destruct (i ??= fin0).
          ** rewrite vnth_vconsH_0 in H0; auto. easy.
          ** erewrite vnth_vconsH_gt0 in H0.
             eexists (fin2PredRangePred i _). apply H0.
             Unshelve. rewrite fin2nat_fin2SuccRangeSucc. lia.
             destruct i. simpl in *. assert (x <> 0); try lia.
             intro. destruct n0. apply sig_eq_iff; auto.
  Qed.

  (** {u ⊆ v} + {~(u \subseteq v)} *)
  Lemma vmems_dec : forall {AeqDec:Dec (@eq A)} {r s} (u : @vec A r)  (v : @vec A s),
      {vmems u v} + {~vmems u v}.
  Proof.
    intros. unfold vmems. unfold vforall.
  (*   induction n. *)
  (*   - right. intro. destruct H as [i H]. apply fin0_False; auto. *)
  (*   - rewrite (vconsH_vhead_vremoveH v). *)
  (*     destruct (Aeqdec (vhead v) a) as [H|H]. *)
  (*     + left. exists fin0. rewrite vnth_vconsH_0; auto. *)
  (*     + destruct (IHn (vremoveH v)) as [H1|H1]. *)
  (*       * left. destruct H1 as [i H1]. exists (fin2SuccRangeSucc i). *)
  (*         erewrite vnth_vconsH_gt0. rewrite fin2PredRangePred_fin2SuccRangeSucc. auto. *)
  (*       * right. intro. destruct H1. destruct H0 as [i H0]. *)
  (*         destruct (i ??= fin0). *)
  (*         ** rewrite vnth_vconsH_0 in H0; auto. easy. *)
  (*         ** erewrite vnth_vconsH_gt0 in H0. *)
  (*            eexists (fin2PredRangePred i _). apply H0. *)
  (*            Unshelve. rewrite fin2nat_fin2SuccRangeSucc. lia. *)
  (*            destruct i. simpl in *. assert (x <> 0); try lia. *)
  (*            intro. destruct n0. apply sig_eq_iff; auto. *)
    (* Qed. *)
  Admitted.
  
  (** *** vconsT *)

  (** cons at tail: [v; a] *)
  Definition vconsT {n} (v : @vec A n) (a : A) : @vec A (S n).
    intros i. destruct (fin2nat i ??< n). apply (v $ (fin2PredRange i l)). apply a.
  Defined.
  
  (** i = n -> (v2f [v; a]) i = a *)
  Lemma vconsT_spec_n : forall {n} a (v : @vec A n) (i : nat),
      i = n -> v2f (vconsT v a) i = a.
  Proof.
    intros. subst. unfold vconsT,v2f,ff2f; simpl.
    destruct (_??<_); try lia. destruct (_??<_); try lia. auto.
  Qed.

  (** i < n -> (v2f [v; a]) i = v.(pred i) *)
  Lemma vconsT_spec_lt : forall {n} a (v : @vec A n) (i : nat),
      i < n -> v2f (vconsT v a) i = v2f v i.
  Proof.
    intros. unfold vconsT,v2f,ff2f; simpl.
    destruct (_??<_); try lia. destruct (_??<_); try lia. f_equal.
  Qed.

  (** i = n -> [v; a].i = a *)
  Lemma vnth_vconsT_n : forall {n} a (v : @vec A n) i,
      fin2nat i = n -> (vconsT v a) $ i = a.
  Proof. intros. unfold vconsT. destruct (_??<_); try lia. auto. Qed.

  (** i < n -> [v; a].i = v.(pred i) *)
  Lemma vnth_vconsT_lt : forall {n} a (v : @vec A n) i (H: fin2nat i < n),
      (vconsT v a) $ i = v (fin2PredRange i H).
  Proof.
    intros. unfold vconsT. destruct (_??<_); try lia. f_equal.
    apply sig_eq_iff; auto.
  Qed.

  (** (v; a) = 0 <-> v = 0 /\ a = 0*)
  Lemma vconsT_eq0_iff : forall {n} (v : @vec A n) a,
      vconsT v a = vzero Azero <-> v = vzero Azero /\ a = Azero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros; auto.
      + specialize (H (fin2SuccRange i)). rewrite vnth_vzero in *. rewrite <- H.
        erewrite vnth_vconsT_lt. f_equal.
        rewrite fin2PredRange_fin2SuccRange. auto.
      + specialize (H (nat2finS n)). rewrite vnth_vconsT_n in H; auto.
        rewrite fin2nat_nat2finS; auto.
    - pose proof (fin2nat_lt i).
      destruct H. subst. destruct (fin2nat i ??= n)%nat.
      + rewrite vnth_vconsT_n; auto.
      + erewrite vnth_vconsT_lt; auto.
        Unshelve. all: try lia. rewrite fin2nat_fin2SuccRange. apply fin2nat_lt.
  Qed.
  
  (** (v; a) <> 0 <-> v <> 0 \/ a <> 0*)
  Lemma vconsT_neq0_iff : forall {n} (v : @vec A n) a,
      vconsT v a <> vzero Azero <-> v <> vzero Azero \/ a <> Azero.
  Proof.
    intros. rewrite vconsT_eq0_iff. split; intros.
    apply not_and_or in H; auto. apply or_not_and; auto.
  Qed.

  (** v = vconsT (vremoveT v) (vtail v) *)
  Lemma vconsT_vremoveT_vtail : forall {n} (v : @vec A (S n)),
      v = vconsT (vremoveT v) (vtail v).
  Proof.
    intros. apply veq_iff_vnth; intros. destruct (fin2nat i ??= n)%nat as [H|H].
    - destruct i as [i Hi]. simpl in *. subst. rewrite vnth_vconsT_n; auto.
      rewrite (vtail_eq (Azero:=Azero)). f_equal. erewrite nat2finS_eq.
      apply sig_eq_iff; auto.
    - erewrite vnth_vconsT_lt. rewrite vnth_vremoveT. f_equal.
      rewrite fin2SuccRange_fin2PredRange. auto.
      Unshelve. all: try lia. pose proof (fin2nat_lt i). lia.
  Qed.
    
End vconsH_vconsT.


(* ======================================================================= *)
(** * 找出向量中从第i个元素开始起的第1个满足谓词P的元素的序号 *)
Section vfirstIdx.
  Context {A : Type}.
  
  Fixpoint vfirstIdxFromAux {n} (P : A -> bool) (v : @vec A n) (i : fin n) (fuel : nat)
    : option (fin n) :=
    match fuel with
    | O => None
    | S fuel' =>
        if P (v $ i)
        then Some i
        else
          if S (fin2nat i) ??< n
          then vfirstIdxFromAux P v (fin2SameRangeSucc i) fuel'
          else None
    end.

  Lemma vfirstIdxFromAux_spec_Some
    : forall (fuel : nat) (n : nat) (P : A -> bool) (v : @vec A n) (i j : fin n),
      fuel >= n ->
      (forall k : fin n, fin2nat i <= fin2nat k < fin2nat j -> ~ P (v $ k)) /\ P (v $ j) ->
      vfirstIdxFromAux P v i fuel = Some j.
  Proof.
  Admitted.

  Lemma vfirstIdxFromAux_spec_None
    : forall (fuel : nat) (n : nat) (P : A -> bool) (v : @vec A n) (i : fin n),
      (forall k : fin n, fin2nat i <= fin2nat k -> P (v $ k) = false) ->
      vfirstIdxFromAux P v i fuel = None.
  Proof.
  Admitted.
  
  Definition vfirstIdxFrom {n} (P : A -> bool) (v : @vec A n) (i : fin n)
    : option (fin n) :=
    vfirstIdxFromAux P v i n.

  Lemma vfirstIdxFrom_spec_None : forall {n} (P : A -> bool) (v : @vec A n) (i : fin n),
      (forall k : fin n, fin2nat i <= fin2nat k -> P (v $ k) = false) ->
      vfirstIdxFrom P v i = None.
  Proof. intros. unfold vfirstIdxFrom. apply vfirstIdxFromAux_spec_None; auto. Qed.

  Lemma vfirstIdxFrom_spec_Some : forall {n} (P : A -> bool) (v : @vec A n) (i j : fin n),
      (forall k : fin n, fin2nat i <= fin2nat k < fin2nat j -> ~ P (v $ k)) /\ P (v $ j) ->
      vfirstIdxFrom P v i = Some j.
  Proof. intros. unfold vfirstIdxFrom. apply vfirstIdxFromAux_spec_Some; auto. Qed.

  Definition vfirstIdx {n} (P : A -> bool) (v : @vec A n) : option (fin n).
    destruct n.
    - exact None.
    - exact (vfirstIdxFrom P v fin0).
  Defined.
End vfirstIdx.

(* ======================================================================= *)
(** ** Index of first nonzero element *)
Section vfirstNonZero.
  Context `{AeqDec : Dec _ (@eq A)}.
  Context {Azero : A}.

  Notation Aeqb := (@Acmpb _ (@eq A) _).
  
  (* 计算从第i个元素开始起的第1个非零元素的序号 *)
  Definition vfirstNonZeroFrom {n} (v : @vec A n) (i : fin n) : option (fin n) :=
    vfirstIdxFrom (fun a => negb (Aeqb a Azero)) v i.
  
  (* 计算第1个非零元素的序号 *)
  Definition vfirstNonZero {n} (v : @vec A n) : option (fin n) :=
    vfirstIdx (fun a => negb (Aeqb a Azero)) v.

End vfirstNonZero.


(* ======================================================================= *)
(** ** Construct vector with two vectors *)
Section vapp.
  Context {A} {Azero : A}.

  (** Append two vectors *)
  Definition vapp {m n} (u : @vec A m) (v : @vec A n) : @vec A (m + n).
    intros i. destruct (fin2nat i ??< m) as [H|H].
    - exact (u $ (fin2AddRangeR' i H)).
    - assert (m <= fin2nat i). apply Nat.nlt_ge; auto.
      exact (v $ (fin2AddRangeAddL' i H0)).
  Defined.

  (** i < m -> (vapp u v).i = u.i *)
  Lemma vapp_spec_L : forall {m n} (u : @vec A m) (v : @vec A n) (i : nat),
      i < m -> v2f Azero (vapp u v) i = v2f Azero u i.
  Proof.
    intros. unfold vapp.
    assert (i < m + n). lia.
    rewrite nth_v2f with (H:=H0). rewrite nth_v2f with (H:=H).
    destruct (_ ??< _); simpl in *; try lia. f_equal. apply sig_eq_iff; auto.
  Qed.
  
  (** m <= i -> i < m + n -> (vapp u v).i = v.(i - m) *)
  Lemma vapp_spec_R : forall {m n} (u : @vec A m) (v : @vec A n) (i : nat),
      m <= i -> i < m + n -> v2f Azero (vapp u v) i = v2f Azero v (i - m).
  Proof.
    intros. unfold vapp.
    rewrite nth_v2f with (H:=H0).
    assert (i - m < n). lia. rewrite nth_v2f with (H:=H1).
    destruct (_ ??< _); simpl in *; try lia. f_equal.
    apply sig_eq_iff; auto.
  Qed.
    
  (** i < m -> (vapp u v).i = u.i *)
  Lemma vnth_vapp_L : forall {m n} (u : @vec A m) (v : @vec A n) i (H: fin2nat i < m),
      (vapp u v) $ i = u $ (fin2AddRangeR' i H).
  Proof.
    intros. destruct i as [i Hi]. unfold vapp.
    destruct (_??<_); simpl in *; try lia. f_equal. apply sig_eq_iff; auto.
  Qed.
      
  (** m <= i -> (vapp u v).i = v.i *)
  Lemma vnth_vapp_R : forall {m n} (u : @vec A m) (v : @vec A n) i (H : m <= fin2nat i),
      (vapp u v) $ i = v $ (fin2AddRangeAddL' i H).
  Proof.
    intros. destruct i as [i Hi]. unfold vapp.
    destruct (_??<_); simpl in *; try lia. f_equal. apply sig_eq_iff; auto.
  Qed.

  (** {us,vs} = 0 <-> us = 0 /\ vs = 0 *)
  Lemma vapp_eq0_iff : forall {m n} (u : @vec A m) (v : @vec A n),
      vapp u v = vzero Azero <-> u = vzero Azero /\ v = vzero Azero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros.
      + specialize (H (fin2AddRangeR i)).
        erewrite vnth_vapp_L in H. rewrite fin2AddRangeR'_fin2AddRangeR in H.
        rewrite H. cbv. auto.
      + specialize (H (fin2AddRangeAddL i)).
        erewrite vnth_vapp_R in H. erewrite fin2AddRangeAddL'_fin2AddRangeAddL in H.
        rewrite H. cbv. auto.
    - destruct H. destruct (fin2nat i ??< m).
      + erewrite vnth_vapp_L. rewrite H. cbv. auto.
      + erewrite vnth_vapp_R. rewrite H0. cbv. auto.
        Unshelve.
        all: try lia.
        * rewrite fin2nat_fin2AddRangeR. apply fin2nat_lt.
        * rewrite fin2nat_fin2AddRangeAddL. lia.
  Qed.
  
  (** vapp (vheadN v) (vtailN v) = v *)
  Lemma vapp_vheadN_vtailN : forall {m n} (v : @vec A (m + n)),
      vapp (vheadN v) (vtailN v) = v.
  Proof.
    intros. apply veq_iff_vnth; intros.
    destruct (fin2nat i ??< m).
    - erewrite vnth_vapp_L. rewrite vnth_vheadN.
      rewrite fin2AddRangeR_fin2AddRangeR'. auto.
    - erewrite vnth_vapp_R. rewrite vnth_vtailN.
      rewrite fin2AddRangeAddL_fin2AddRangeAddL'. auto.
      Unshelve. auto. lia.
  Qed.

End vapp.

Section vapp_extra.
  Context {A B C : Type}.
  
  Lemma vmap2_vapp_vapp :
    forall {n m} (f : A -> B -> C)
      (cs : @vec A n) (ds : @vec A m) (us : @vec B n) (vs : @vec B m),
      vmap2 f (vapp cs ds) (vapp us vs) =
        vapp (vmap2 f cs us) (vmap2 f ds vs).
  Proof.
    intros. unfold vmap2. apply veq_iff_vnth. intros.
    destruct (fin2nat i ??< n).
    - erewrite !vnth_vapp_L. auto.
    - erewrite !vnth_vapp_R. auto.
      Unshelve. auto. lia.
  Qed.

End vapp_extra.


(* ======================================================================= *)
(** ** Construct vector from parts of a vector *)
Section vslice.
  Context {A} {Azero : A}.

  (** {i<n}, {j<n}, {k:=S j-i} -> {i+k < n} *)
  Definition vslice_idx {n} (i j : fin n)
    (k : fin (S (fin2nat j) - (fin2nat i))) : fin n.
    refine (nat2fin (fin2nat i + fin2nat k) _).
    pose proof (fin2nat_lt k). pose proof (fin2nat_lt j). lia.
  Defined.
  
  (** Get a slice from vector `v` which contain elements from v$i to v$j.
      1. Include the i-th and j-th element
      2. If i > i, then the result is `vec 0` *)
  Definition vslice {n} (v : @vec A n) (i j : fin n) :
    @vec A (S (fin2nat j) - (fin2nat i)) :=
    fun k => v $ (vslice_idx i j k).

  Lemma vnth_vslice : forall {n} (v : @vec A n) (i j : fin n) k,
      (vslice v i j) $ k = v $ (vslice_idx i j k).
  Proof. intros. auto. Qed.
  
End vslice.

Section test.
  Let n := 5.
  Let v1 := l2v 9 n [1;2;3;4;5].
  (* Compute v2l (vslice v1 (nat2finS 1) (nat2finS 3)). *)
End test.

(* ======================================================================= *)
(** ** Folding of a vector *)
Section vfold.
  Context {A B : Type} {Azero : A} {Bzero : B}. 

  (** ((a + v.1) + v.2) + ... *)
  Definition vfoldl {n} (v : @vec A n) (b : B) (f : B -> A -> B) : B :=
    seqfoldl (ff2f (Azero:=Azero) v) n b f.
  
  (** ... + (v.(n-1) + (v.n + a)) *)
  Definition vfoldr {n} (v : @vec A n) (b : B) (f : A -> B -> B) : B :=
    seqfoldr (ff2f (Azero:=Azero) v) n b f.

  (** Convert `vfoldl` to `seqfoldl` *)
  Lemma vfoldl_to_seqfoldl :
    forall {n} (v : @vec A n) (b : B) (f : B -> A -> B) (s : nat -> A),
      (forall i, v $ i = s (fin2nat i)) -> vfoldl v b f = seqfoldl s n b f.
  Proof.
    intros. unfold vfoldl. apply seqfoldl_eq; auto.
    intros. rewrite nth_ff2f with (H:=H0). rewrite H. rewrite fin2nat_nat2fin. auto.
  Qed.
  
  (* (** `vsum` of (S n) elements, equal to addition of Sum and tail *) *)
  (* Lemma vsumS_tail : forall {n} (v : @vec A (S n)), *)
  (*     vsum v = vsum (fun i => v $ (fin2SuccRange i)) + v $ (nat2finS n). *)
  (* Proof. intros. apply fseqsumS_tail; auto. Qed. *)

  (* (** `vsum` of (S n) elements, equal to addition of head and Sum *) *)
  (* Lemma vsumS_head : forall {n} (v : @vec A (S n)), *)
  (*     vsum v = v $ (nat2finS 0) + vsum (fun i => v $ (fin2SuccRangeSucc i)). *)
  (* Proof. intros. apply fseqsumS_head; auto. Qed. *)

End vfold.

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

  (* ∑ (u;v) = ∑u + ∑v *)
  Lemma vsum_vapp : forall {m n} (u : @vec A m) (v : @vec A n),
      vsum (vapp u v) = vsum u + vsum v.
  Proof.
    intros. apply vsum_plusIdx; intros.
    - erewrite vnth_vapp_L. f_equal. rewrite fin2AddRangeR'_fin2AddRangeR. auto.
    - erewrite vnth_vapp_R. f_equal. rewrite fin2AddRangeAddL'_fin2AddRangeAddL. auto.
      Unshelve. rewrite fin2nat_fin2AddRangeR. apply fin2nat_lt.
      rewrite fin2nat_fin2AddRangeAddL. lia.
  Qed.
  
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
    Lemma vsum_cmul : forall {n} (u v : @vec A n) k,
        (forall i, u $ i = k * v $ i) -> vsum u = k * vsum v.
    Proof. intros. unfold vsum. apply fseqsum_cmul. auto. Qed.
  End ARing.

  (* if equip a `OrderedARing` *)
  Section OrderedARing.
    Context `{HOrderedARing
        : OrderedARing A Aadd Azero Aopp Amul Aone Alt Ale Altb Aleb}.
    (* Check HOrderedARing : Order Alt Ale Altb Aleb. *)
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
      - rewrite nth_ff2f with (H:=fin2nat_lt _). rewrite nat2fin_fin2nat. auto.
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
    
    (** ∑v = 0 -> ∀i,v.i>=0 -> ∀i,v.i=0 *)
    Lemma vsum_eq0_rev : forall {n} (v : @vec A n),
        (forall i, 0 <= v $ i) -> vsum v = 0 -> (forall i, v $ i = 0).
    Proof.
      intros. destruct (Aeqdec (v$i) 0); auto. exfalso.
      pose proof (vsum_ge_any v i H). rewrite H0 in H1.
      specialize (H i).
      pose proof (@le_antisym _ _ _ _ _ HOrderedARing (v i) 0 H1 H). easy.
    Qed.
    
  End OrderedARing.

End vsum.

(** vsum with vinsert and vremove  *)
Section vsum_vinsert_vremove.
  Context `{HAGroup : AGroup}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + - b).
  Infix "-" := Asub : A_scope.
  Notation vsum := (@vsum _ Aadd Azero).
  Notation seqsum := (@seqsum _ Aadd Azero).
  Notation seqsum_plusIdx := (@seqsum_plusIdx _ Aadd Azero).

  (** ∑(insert v i a) = ∑v + a *)
  Lemma vsum_vinsert : forall {n} (v : @vec A n) (a : A) (i : fin (S n)),
      vsum (vinsert v i a) = vsum v + a.
  Proof.
    intros. pose proof (fin2nat_lt i).
    rewrite (vinsert_eq_vinsert' _ (Azero:=Azero)).
    unfold vinsert'. unfold vsum, fseqsum.
    match goal with | |- seqsum ?f _ = _ => remember f as g end.
    replace n with (fin2nat i + (n - fin2nat i))%nat at 3 by lia.
    replace (S n) with (fin2nat i + (S (n - fin2nat i)))%nat at 1 by lia.
    rewrite seqsum_plusIdx. rewrite seqsum_plusIdx. rewrite associative. f_equal.
    - rewrite Heqg. apply seqsum_eq. intros. unfold f2v,v2f,f2ff,ff2f. simpl in *.
      destruct (_??<_),(_??<_); try lia. destruct (_??<_); try lia. auto.
    - rewrite seqsumS_head. monoid. rewrite commutative. f_equal.
      + apply seqsum_eq. intros j H0. rewrite Heqg.
        assert (fin2nat i + S j < S n) by lia. rewrite nth_ff2f with (H:=H1).
        assert (fin2nat i + j < n) by lia. rewrite nth_ff2f with (H:=H2).
        rewrite vnth_f2v. simpl.
        destruct (_??<_); try lia. destruct (_??=_)%nat; try lia.
        assert (pred (fin2nat i + S j) < n) by lia.
        rewrite nth_v2f with (H:=H3). f_equal. apply sig_eq_iff. lia.
      + rewrite Heqg. rewrite nth_ff2f with (H:=H). rewrite vnth_f2v. simpl.
        destruct (_??<_); try lia. destruct (_??=_)%nat; auto. lia.
  Qed.

  (** ∑(remove v i) = ∑v - v.i *)
  Lemma vsum_vremove : forall {n} (v : @vec A (S n)) (i : fin (S n)),
      vsum (vremove v i) = vsum v - v$i.
  Proof.
    intros. pose proof (fin2nat_lt i).
    rewrite (vremove_eq_vremove' (Azero:=Azero)).
    unfold vremove'. unfold vsum, fseqsum.
    match goal with | |- seqsum ?f _ = _ => remember f as g end.
    replace n with (fin2nat i + (n - fin2nat i))%nat at 1 by lia.
    replace (S n) with (fin2nat i + (S (n - fin2nat i)))%nat at 4 by lia.
    rewrite seqsum_plusIdx. rewrite seqsum_plusIdx. rewrite associative. f_equal.
    - rewrite Heqg. apply seqsum_eq. intros. unfold f2v,v2f,f2ff,ff2f. simpl in *.
      destruct (_??<_),(_??<_); try lia. destruct (_??<_); try lia. auto.
    - rewrite seqsumS_head. monoid.
      symmetry. rewrite commutative. rewrite associative.
      replace (- v i + v!fin2nat i) with 0.
      + monoid. apply seqsum_eq. intros j H0. rewrite Heqg.
        assert (fin2nat i + S j < S n) by lia. rewrite nth_ff2f with (H:=H1).
        assert (fin2nat i + j < n) by lia. rewrite nth_ff2f with (H:=H2).
        rewrite vnth_f2v. simpl. destruct (_??<_); try lia.
        assert (S (fin2nat i + j) < S n) by lia. rewrite nth_v2f with (H:=H3).
        f_equal. apply sig_eq_iff. lia.
      + rewrite nth_ff2f with (H:=H). rewrite nat2fin_fin2nat. group.
  Qed.
  
End vsum_vinsert_vremove.

(** Extension for `vsum` *)
Section vsum_ext.
  
  Context `{HAMonoidA : AMonoid}.
  Context `{HAMonoidB : AMonoid B Badd Bzero}.
  Context (cmul : A -> B -> B).
  Infix "*" := cmul.
  
  (** ∑(a*bi) = a*b1+a*b2+a*b3 = a*(b1+b2+b3) = a * ∑(bi) *)
  Section form1.
    Context (cmul_zero_keep : forall a : A, cmul a Bzero = Bzero).
    Context (cmul_badd : forall (a : A) (b1 b2 : B),
                a * (Badd b1 b2) = Badd (a * b1) (a * b2)).
    Lemma vsum_cmul_extK : forall {n} (a : A) (f : @vec B n) (g : @vec B n),
        (forall i, f$i = a * g$i) ->
        @vsum _ Badd Bzero _ f = a * (@vsum _ Badd Bzero _ g).
    Proof. intros. apply fseqsum_cmul_extK; auto. Qed.
  End form1.
  
  (** ∑(ai*b) = a1*b+a2*b+a3*b = (a1+a2+a3)*b = ∑(ai) * b *)
  Section form2.
    Context (cmul_zero_keep : forall b : B, cmul Azero b = Bzero).
    Context (cmul_aadd : forall (a1 a2 : A) (b : B),
                (Aadd a1 a2) * b = Badd (a1 * b) (a2 * b)).
    Lemma vsum_cmul_extA : forall {n} (b : B) (f : @vec B n) (g : @vec A n),
        (forall i, f$i = g$i * b) ->
        @vsum _ Badd Bzero _ f = (@vsum _ Aadd Azero _ g) * b.
    Proof. intros. apply fseqsum_cmul_extA; auto. Qed.
  End form2.
  
End vsum_ext.


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
  Proof. intros. unfold vdot. apply vsum_cmul; intros. cbv. ring. Qed.
  
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
        rewrite nat2fin_fin2nat in H. rewrite vnth_vmap2 in H.
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

Section vdot_extra.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  
  (** <<u,D>, v> = <u, <D,v> *)
  (* For example:
     (u1,u2,u3) [D11,D12] [v1]  记作 u*D*v，
                [D21,D22] [v2]
                [D31,D32]
     (u*D)*v = <u,col(D,1)> v1 + <u,col(D,2)> v2
             = (u1D11+u2D21+u3D31)v1 + (u1D12+u2D22+u3D32)v2
     u*(D*v) = u1 <row(D,1),v> + u2 <row(D,2),v> + u3 <row(D,3),v>
             = u1(D11v1+D12v2)+u2(D21v1+D22v2)+u3(D31v1+D32v2) *)
  
  Lemma vdot_assoc : forall {r c} (u : @vec A c) (D : @vec (@vec A r) c) (v : @vec A r),
      vdot (fun j => vdot u (fun i => D i j)) v = vdot u (fun i => vdot (D i) v).
  Proof.
    intros. unfold vdot. unfold vmap2.
    pose proof (vsum_vsum_exchg c r (fun i j => Amul (Amul (u i) (D i j)) (v j))).
    match goal with
    | H: ?a1 = ?a2 |- ?b1 = ?b2 => replace b1 with a2; [replace b2 with a1|]; auto
    end.
    - f_equal. extensionality i. apply vsum_cmul; intros. ring.
    - f_equal. extensionality i. rewrite commutative. apply vsum_cmul; intros. ring.
  Qed.

End vdot_extra.


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
(** ** Orthogonal vectors 正交的两个向量 *)
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
  Notation vunit := (@vunit _ Aadd Azero Amul Aone).
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

  (** vunit v -> vproj u v = <u, v> \.* v *)
  Lemma vproj_vunit : forall {n} (u v : vec n), vunit v -> vproj u v = <u, v> \.* v.
  Proof. intros. unfold vproj. f_equal. rewrite H. field. apply field_1_neq_0. Qed.

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

  (** vperp u v = u - vproj u v *)
  Lemma vperp_eq_minus_vproj : forall {n} (u v : vec n), vperp u v = u - vproj u v.
  Proof. auto. Qed.

  (** vproj u v = u - vperp u v *)
  Lemma vproj_eq_minus_vperp : forall {n} (u v : vec n), vproj u v = u - vperp u v.
  Proof.
    intros. unfold vperp. unfold vsub. rewrite group_opp_distr.
    rewrite group_opp_opp. move2h (vproj u v). group.
  Qed.

  (** vproj u v = u - vperp u v *)
  Lemma vproj_plus_vperp : forall {n} (u v : vec n), vproj u v + vperp u v = u.
  Proof. intros. unfold vperp. unfold vsub. move2h u. group. Qed.
  
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
