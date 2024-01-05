(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : sequence.
  author    : ZhengPu Shi
  date      : 2022.06
 *)

Require Export Basic.
Require Export NatExt.
Require Export ListExt.
Require Export Hierarchy.
Require RExt.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv.

(* ######################################################################### *)
(** * Sequence by function, f : nat -> A  *)

Open Scope nat_scope.
Open Scope A_scope.


(* ======================================================================= *)
(** ** Properties of sequence *)

(** Top (S n) elements of a sequence satisfy P, iff
    top n elements of the sequencoe satisfy P and the n-th element hold too. *)
Lemma seq_prop_S_iff : forall (P : nat -> Prop) (n : nat),
    (forall i, i < S n -> P i) <-> (forall i, i < n -> P i) /\ P n.
Proof.
  intros. split; intros.
  - split; auto.
  - destruct H. bdestruct (i =? n); subst; auto. apply H; lia.
Qed.


(* ======================================================================= *)
(** ** Equality of sequence *)
Section seqeq.
  Context {A : Type}.
  
  (** Equality of two sequence which have one index *)
  Definition seqeq n (f g : nat -> A) := forall i, i < n -> f i = g i.

  (** seqeq is an equivalence relation *)
  #[export] Instance seqeq_equiv : forall n, Equivalence (seqeq n).
  Proof.
    intros. constructor; intro; intros; hnf in *; intros; auto.
    rewrite H; auto. rewrite H,H0; auto.
  Qed.

  (** seqeq of S has a equivalent form. *)
  Lemma seqeq_S : forall n (f g : nat -> A),
      seqeq (S n) f g <-> (seqeq n f g) /\ (f n = g n).
  Proof.
    intros. unfold seqeq. split; intros. split; auto.
    destruct H. bdestruct (i =? n); subst; auto. apply H. lia.
  Qed.

  (** seqeq is decidable  *)
  Lemma seqeq_dec : forall n f g,
      (forall a b : A, {a = b} + {a <> b}) -> {seqeq n f g} + {~seqeq n f g}.
  Proof.
    intros n f g H. unfold seqeq. induction n.
    - left. easy.
    - destruct IHn as [H1 | H1].
      + destruct (H (f n) (g n)) as [H2 | H2].
        * left. intros. bdestruct (i =? n). subst; auto. apply H1. lia.
        * right. intro H3. rewrite H3 in H2; auto.
      + right. intro H3. destruct H1. auto.
  Qed.
  
End seqeq.


(* ======================================================================= *)
(** ** Equality of sequence with two indexes *)
Section seq2eq.
  Context {A : Type}.

  (** Equality of two sequence which have two indexes *)
  Definition seq2eq r c (f g : nat -> nat -> A) := 
    forall ri ci, ri < r -> ci < c -> f ri ci = g ri ci.
  
  (** seq2eq of Sr has a equivalent form. *)
  Lemma seq2eq_Sr : forall r c (f g : nat -> nat -> A), 
      seq2eq (S r) c f g <-> (seq2eq r c f g) /\ (seqeq c (f r) (g r)).
  Proof.
    intros. unfold seq2eq, seqeq. split; intros. split; auto.
    destruct H. bdestruct (ri =? r); subst; auto. apply H; lia.
  Qed.

  (** seq2eq of Sc has a equivalent form. *)
  Lemma seq2eq_Sc : forall r c (f g : nat -> nat -> A), 
      seq2eq r (S c) f g <-> (seq2eq r c f g) /\ (seqeq r (fun i => f i c) (fun i => g i c)).
  Proof.
    intros. unfold seq2eq, seqeq. split; intros. split; auto.
    destruct H. bdestruct (ci =? c); subst; auto. apply H; lia.
  Qed.

  #[export] Instance seq2eq_equiv : forall r c, Equivalence (seq2eq r c).
  Proof.
    intros. unfold seq2eq. constructor; intro; intros; auto.
    rewrite H; auto. rewrite H,H0; auto.
  Qed.

  (** seq2eq is decidable  *)
  Lemma seq2eq_dec : forall r c f g,
      (forall a b : A, {a = b} + {a <> b}) -> {seq2eq r c f g} + {~seq2eq r c f g}.
  Proof.
    intros r c f g H. unfold seq2eq. revert c. induction r; intros.
    - left. easy.
    - destruct (IHr c) as [H1 | H1].
      + (* give a new proposition *)
        pose proof (seqeq_dec c (f r) (g r) H) as H2. unfold seqeq in H2.
        destruct H2 as [H2 | H2].
        * left. intros. bdestruct (ri =? r); subst; auto. apply H1; lia.
        * right. intro H3. specialize (H3 r). destruct H2. auto.
      + right. intro H2. destruct H1. auto.
  Qed.
  
End seq2eq.


(* ======================================================================= *)
(** ** Sum of a sequence *)
Section seqsum.
  
  (** Let's have an monoid structure *)
  Context `{M : Monoid}.
  Infix "+" := Aadd : A_scope.

  
  (** Sum of a sequence *)
  Fixpoint seqsum (f : nat -> A) (n : nat) : A := 
    match n with
    | O => Azero
    | S n' => seqsum f n' + f n'
    end.
    
  (** Sum of a sequence which every element is zero get zero. *)
  Lemma seqsum_eq0 : forall (f : nat -> A) (n : nat), 
      (forall i, i < n -> f i = Azero) -> seqsum f n = Azero.
  Proof. intros. induction n; simpl; auto. rewrite H,IHn; auto. monoid. Qed.

  (** Two sequences are equal, imply the sum are equal. *)
  Lemma seqsum_eq : forall (f g : nat -> A) (n : nat),
      (forall i, i < n -> f i = g i) -> seqsum f n = seqsum g n.
  Proof. intros. induction n; simpl; auto. rewrite H,IHn; auto. Qed.
  
  
  (** Let's have an abelian monoid structure *)
  Context {AM : AMonoid Aadd Azero}.

  (** Sum a sequence of (S n) elements, equal to addition of Sum and tail *)
  Lemma seqsumS_tail : forall n f, 
      seqsum f (S n) = seqsum f n + f n.
  Proof. reflexivity. Qed.
  
  (** Sum a sequence of (S n) elements, equal to addition of head and Sum *)
  Lemma seqsumS_head : forall n f, 
      seqsum f (S n) = f O + seqsum (fun i => f (S i)) n.
  Proof.
    intros. induction n; simpl in *. amonoid. rewrite IHn. amonoid.
  Qed.

  (** Sum of a sequence given by `l2f l` equal to folding of `l` *)
  Lemma seqsum_l2f : forall (l : list A) n,
      length l = n ->
      seqsum (@l2f _ Azero n l) n = fold_right Aadd Azero l.
  Proof.
    unfold l2f. induction l; intros.
    - simpl in H. subst; simpl. auto.
    - destruct n; simpl in H. lia. rewrite seqsumS_head. rewrite IHl; auto.
  Qed.
  
  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma seqsum_add : forall (f g h : nat -> A) (n : nat),
      (forall i, i < n -> h i = f i + g i) ->
      seqsum h n = seqsum f n + seqsum g n.
  Proof.
    intros. induction n; simpl. monoid.
    rewrite IHn; auto. asemigroup. rewrite H; auto.
  Qed.

  
  (** Let's have a group structure *)
  Context `{G : Group A Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.

  
  (** Opposition of the sum of a sequence. *)
  Lemma seqsum_opp : forall (f g : nat -> A) (n : nat),
      (forall i, i < n -> f i = - g i) ->
      (seqsum f n) = - (seqsum g n).
  Proof.
    intros. induction n; simpl. group. (* not so smart *)
    rewrite group_inv_id; auto.
    rewrite H,IHn; auto. rewrite group_inv_distr. amonoid.
  Qed.

  
  (** Let's have an ring structure *)
  Context `{AR : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : make_ring_theory.
  
  
  (** Scalar multiplication of the sum of a sequence. *)
  Lemma seqsum_cmul : forall k (f g : nat -> A) (n : nat),
       (forall i, i < n -> f i = k * g i) ->
      seqsum f n = k * seqsum g n.
  Proof.
    intros. induction n; simpl. ring. rewrite H, IHn; auto. ring.
  Qed.

  (** Sum a sequence which only one item is nonzero, then got this item. *)
  Lemma seqsum_unique : forall (f : nat -> A) (k : A) (n i : nat), 
      i < n -> f i = k -> (forall j, i <> j -> f j = Azero) -> seqsum f n = k.
  Proof.
    intros f k n. induction n; intros. lia. simpl. bdestruct (i =? n).
    - subst. rewrite seqsum_eq0; try ring. intros. apply H1. lia.
    - replace (seqsum f n) with k. replace (f n) with Azero; try ring.
      rewrite H1; auto. rewrite (IHn i); auto. lia.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] f(i) + Σ[i,0,n] f(m + i). *)
  Lemma seqsum_plusIdx : forall f m n,
      seqsum f (m + n) = seqsum f m + seqsum (fun i => f (m + i)%nat) n. 
  Proof.
    (* induction on `n` is simpler than on `m` *)
    intros. induction n; intros; simpl.
    - rewrite Nat.add_0_r. monoid.
    - replace (m + S n)%nat with (S (m + n))%nat; auto. simpl.
      rewrite IHn. asemigroup.
  Qed.
  
  (** Sum the m+n elements equal to plus of two parts.
      (i < m -> f(i) = g(i)) ->
      (i < n -> f(m+i) = h(i)) ->
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] g(i) + Σ[i,0,n] h(i). *)
  Lemma seqsum_plusIdx_ext : forall f g h m n,
      (forall i, i < m -> f i = g i) ->
      (forall i, i < n -> f (m + i)%nat = h i) ->
      seqsum f (m + n) = seqsum g m + seqsum h n.
  Proof.
    intros. induction n; intros; simpl.
    - rewrite Nat.add_0_r. monoid. apply seqsum_eq. auto.
    - replace (m + S n)%nat with (S (m + n))%nat; auto. simpl.
      rewrite IHn. asemigroup. rewrite H0; auto. intros. auto.
  Qed.

  (** Product two sum equal to sum of products.
      Σ[i,0,m] f(i) * Σ[i,0,n] g(i) = Σ[i,0,m*n] f(i/n)*g(i%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
   *)
  Lemma seqsum_product : forall f g m n,
      n <> O ->
      seqsum f m * seqsum g n = seqsum (fun i => f (i / n) * g (i mod n)) (m * n). 
  Proof.
    intros. induction m; simpl. ring. ring_simplify.
    replace (n + m * n)%nat with (m * n + n)%nat by ring.
    rewrite seqsum_plusIdx. rewrite <- IHm. asemigroup.
    apply seqsum_cmul. intros. f_equal; f_equal.
    apply add_mul_div; auto. apply add_mul_mod; auto.
  Qed.
  
  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] f_ij) = 
      f00 + f01 + ... + f0c + 
      f10 + f11 + ... + f1c + 
      ...
      fr0 + fr1 + ... + frc = 
      ∑[j,0,c](∑[i,0,r] f_ij) *)
  Lemma seqsum_seqsum_exchg : forall f r c,
      seqsum (fun i => seqsum (fun j => f i j) c) r =
        seqsum (fun j => seqsum (fun i => f i j) r) c.
  Proof.
    intros f. induction r.
    - destruct c; simpl; auto. rewrite seqsum_eq0; auto. ring.
    - destruct c; simpl; auto. rewrite seqsum_eq0; auto. ring.
      replace (seqsum (fun i : nat => seqsum (fun j : nat => f i j) c + f i c) r)
        with ((seqsum (fun i : nat => seqsum (fun j : nat => f i j) c) r) +
                (seqsum (fun i : nat => f i c) r)).
      replace (seqsum (fun j : nat => seqsum (fun i : nat => f i j) r + f r j) c)
        with ((seqsum (fun j : nat => seqsum (fun i : nat => f i j) r) c) +
                (seqsum (fun j : nat => f r j) c)).
      rewrite IHr. asemigroup.
      symmetry. apply seqsum_add; auto.
      symmetry. apply seqsum_add; auto.
  Qed.
  
End seqsum.


(* ======================================================================= *)
(** ** Sequence on R type *)
Section Seq_R.

  Import Reals.
  Open Scope R.
  
  Notation seqsum := (@seqsum _ Rplus R0).

  (** If all elements of a sequence are >= 0, then the sum is >= 0 *)
  Lemma seqsum_ge0 : forall (f : nat -> R) n,
      (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= seqsum f n.
  Proof. intros. induction n; simpl. lra. apply Rplus_le_le_0_compat; auto. Qed.

  (** If all elements of a sequence are >= 0, and the sum of top (n+1) elements of
      the sequence is = 0, then the sum of top n elements are 0 *)
  Lemma seqsum_eq0_less : forall (f : nat -> R) (n : nat), 
      (forall i, (i < S n)%nat -> 0 <= f i) ->
      seqsum f (S n) = 0 ->
      seqsum f n = 0.
  Proof.
    intros. rewrite seqsumS_tail in H0.
    assert (0 <= f n); auto.
    assert (0 <= seqsum f n). apply seqsum_ge0; auto. lra.
  Qed.

  (** If all elements of a sequence are >= 0, and the sum of the sequence is = 0,
      then all elements of the sequence are 0. *)
  Lemma seqsum_eq0_imply_seq0 : forall (f : nat -> R) (n : nat), 
      (forall i, (i < n)%nat -> 0 <= f i) -> seqsum f n = 0 -> (forall i, (i < n)%nat -> f i = 0).
  Proof.
    intros f n. induction n. intros H1 H2 i H3; try easy. intros.
    assert (i < n \/ i = n)%nat by nia. destruct H2.
    - apply IHn; auto. apply seqsum_eq0_less; auto.
    - subst.
      assert (0 <= f n); auto.
      assert (0 <= seqsum f n). apply seqsum_ge0; auto.
      rewrite seqsumS_tail in H0. lra.
  Qed.
  
End Seq_R.


(* ======================================================================= *)
(** ** Usage demo *)
Section test.
  Import RExt.

  Example seq1 := fun n => Z2R (Z.of_nat n).

  (* Compute @seqsum _ Rplus R0 seq1 3. *)
  
  Open Scope Z.
  Example seq2 := fun i j => Z.of_nat i + Z.of_nat j.
  Example seq3 := fun i j => Z.of_nat i + Z.of_nat j + 1.

  (* Compute @seqsum _ Z.add (0%Z) (seq2 0) 3. *)
  
End test. 
