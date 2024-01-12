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

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Ale Alt.

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
  (* ∑(f,n) = 0 + f 0 + f 1 + ... + f (n-1) *)
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
  Lemma seqsumS_tail : forall f n, 
      seqsum f (S n) = seqsum f n + f n.
  Proof. reflexivity. Qed.
  
  (** Sum a sequence of (S n) elements, equal to addition of head and Sum *)
  Lemma seqsumS_head : forall f n, 
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
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  
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
(** ** Sum of a sequence with bounds *)
Section seqsumb.
  
  (** Let's have an monoid structure *)
  Context `{M : Monoid}.
  Infix "+" := Aadd : A_scope.
  Notation seqsum := (@seqsum _ Aadd Azero).

  (** Sum of a sequence with lower bounds and length *)
  (* ∑(f,lo,n) = 0 + f lo + f (lo+1) + ... + f (lo+n-1) *)
  Fixpoint seqsumb (f : nat -> A) (lo n : nat) : A := 
    match n with
    | O => Azero
    | S n' => seqsumb f lo n' + f (lo + n')%nat
    end.

  (** Sum of a sequence with bounds equal to sum of a sequence *)
  Lemma seqsumb_eq_seqsum : forall (f : nat -> A) (n : nat),
      seqsumb f 0 n = seqsum f n.
  Proof. intros. induction n; simpl; auto. rewrite IHn. auto. Qed.

  (** Sum of a sequence which every element is zero get zero. *)
  Lemma seqsumb_eq0 : forall (f : nat -> A) (lo n : nat), 
      (forall i, i < n -> f (lo+i)%nat = Azero) -> seqsumb f lo n = Azero.
  Proof.
    intros. induction n; simpl; auto. rewrite H,IHn; auto; try lia. monoid.
  Qed.

  (** Two sequences are equal, imply the sum are equal. *)
  Lemma seqsumb_eq : forall (f g : nat -> A) (lo n : nat),
      (forall i, i < n -> f (lo+i) = g (lo+i))%nat ->
      seqsumb f lo n = seqsumb g lo n.
  Proof. intros. induction n; simpl; auto. rewrite H,IHn; auto. Qed.
  
  
  (** Let's have an abelian monoid structure *)
  Context {AM : AMonoid Aadd Azero}.

  (** Sum a sequence of (S n) elements, equal to addition of Sum and tail *)
  Lemma seqsumbS_tail : forall f lo n,
      seqsumb f lo (S n) = seqsumb f lo n + f (lo + n)%nat.
  Proof. reflexivity. Qed.
  
  (** Sum a sequence of (S n) elements, equal to addition of head and Sum *)
  Lemma seqsumbS_head : forall f lo n, 
      seqsumb f lo (S n) = f lo + seqsumb (fun i => f (S i)) lo n.
  Proof.
    intros. induction n; simpl in *. amonoid. rewrite IHn.
    replace (lo + S n)%nat with (S (lo + n)); auto. amonoid.
  Qed.

  (** Sum of a sequence given by `l2f l` equal to folding of sublist of `l` *)
  Lemma seqsumb_l2f : forall (l : list A) lo n,
      length l = n ->
      seqsumb (@l2f _ Azero n l) lo n = fold_right Aadd Azero (sublist l lo n).
  Proof.
    unfold l2f. induction l; intros.
    - simpl in H. subst; simpl. auto.
    - destruct n; simpl in H. lia. rewrite seqsumbS_head. rewrite IHl; auto.
      rewrite sublist_cons. simpl. destruct lo; simpl; auto.
      rewrite (sublist_Sn Azero).
      bdestruct (length l <=? lo); simpl; auto.
      rewrite nth_overflow; try lia.
      rewrite sublist_overflow; try lia. simpl. monoid.
  Qed.
  
  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma seqsumb_add : forall (f g h : nat -> A) (lo n : nat),
      (forall i, i < n -> h (lo+i)%nat = f (lo+i)%nat + g (lo+i)%nat) ->
      seqsumb h lo n = seqsumb f lo n + seqsumb g lo n.
  Proof.
    intros. induction n; simpl. monoid.
    rewrite IHn; auto. asemigroup. rewrite H; auto.
  Qed.

  
  (** Let's have a group structure *)
  Context `{G : Group A Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.

  
  (** Opposition of the sum of a sequence. *)
  Lemma seqsumb_opp : forall (f g : nat -> A) (lo n : nat),
      (forall i, i < n -> f (lo+i)%nat = - g (lo+i)%nat) ->
      (seqsumb f lo n) = - (seqsumb g lo n).
  Proof.
    intros. induction n; simpl. rewrite group_inv_id; auto.
    rewrite H,IHn; auto. rewrite group_inv_distr. amonoid.
  Qed.

  
  (** Let's have an ring structure *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  
  (** Scalar multiplication of the sum of a sequence. *)
  Lemma seqsumb_cmul : forall k (f g : nat -> A) (lo n : nat),
       (forall i, i < n -> f (lo+i)%nat = k * g (lo+i)%nat) ->
      seqsumb f lo n = k * seqsumb g lo n.
  Proof.
    intros. induction n; simpl. ring. rewrite H, IHn; auto. ring.
  Qed.

  (** Sum a sequence which only one item is nonzero, then got this item. *)
  Lemma seqsumb_unique : forall (f : nat -> A) (k : A) (lo n i : nat), 
      i < n -> f (lo+i)%nat = k ->
      (forall j, j < n -> i <> j -> f (lo+j)%nat = Azero) -> seqsumb f lo n = k.
  Proof.
    intros f k lo n. induction n; intros. lia. simpl. bdestruct (i =? n).
    - subst. rewrite seqsumb_eq0; try ring. intros. apply H1. lia. lia.
    - replace (seqsumb f lo n) with k.
      replace (f (lo + n)%nat) with Azero; try ring.
      rewrite H1; auto. rewrite (IHn i); auto. lia.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      Σ[i,lo,(m+n)] f(i) = Σ[i,lo,m] f(i) + Σ[i,lo+m,n] f(m + i). *)
  Lemma seqsumb_plusSize : forall f lo m n,
      seqsumb f lo (m + n) = seqsumb f lo m + seqsumb f (lo+m) n. 
  Proof.
    (* induction on `n` is simpler than on `m` *)
    intros. induction n; intros; simpl.
    - rewrite Nat.add_0_r. monoid.
    - replace (m + S n)%nat with (S (m + n))%nat; auto. simpl.
      rewrite IHn. asemigroup.
  Qed.

  (* (** Sum the m+n elements equal to plus of two parts. *)
  (*     Σ[i,(lo,(m+n)] f(i) = Σ[i,lo,m] f(i) + Σ[i,lo+m,n] f(m + i). *) *)
  (* Lemma seqsumb_minusIdx : forall f lo m n, *)
  (*     seqsumb f lo (m + n) = seqsumb f lo m + seqsumb f (lo+m) n.  *)
  (* Proof. *)
  (*   (* induction on `n` is simpler than on `m` *) *)
  (*   intros. induction n; intros; simpl. *)
  (*   - rewrite Nat.add_0_r. monoid. *)
  (*   - replace (m + S n)%nat with (S (m + n))%nat; auto. simpl. *)
  (*     rewrite IHn. asemigroup. *)
  (* Qed. *)
  
  (** Sum the m+n elements equal to plus of two parts.
      (i < m -> f(lo+i) = g(lo+i)) ->
      (i < n -> f(lo+m+i) = h(lo+i)) ->
      Σ[i,lo,(m+n)] f(i) = Σ[i,lo,m] g(i) + Σ[i,lo+m,n] h(i). *)
  Lemma seqsumb_plusIdx_ext : forall f g h lo m n,
      (forall i, i < m -> f (lo+i)%nat = g (lo+i)%nat) ->
      (forall i, i < n -> f (lo+m+i)%nat = h (lo+i)%nat) ->
      seqsumb f lo (m + n) = seqsumb g lo m + seqsumb h lo n.
  Proof.
    intros. induction n; intros; simpl.
    - rewrite Nat.add_0_r. monoid. apply seqsumb_eq. auto.
    - replace (m + S n)%nat with (S (m + n))%nat; auto. simpl.
      rewrite IHn. asemigroup. rewrite H0; auto. intros. auto.
  Qed.

  (** Product two sum equal to sum of products.
      Σ[i,lo,m] f(i) * Σ[i,lo,n] g(i) = Σ[i,lo,m*n] f((i-lo)/n)*g((i-lo)%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
   *)
  Lemma seqsumb_product : forall f g lo m n,
      n <> O ->
      seqsumb f lo m * seqsumb g lo n =
        seqsumb (fun i => f ((i-lo) / n)%nat * g ((i-lo) mod n)%nat) lo (m * n). 
  Proof.
    intros. induction m; simpl. ring. ring_simplify. rewrite IHm.
    replace (n + m * n)%nat with (m * n + n)%nat by ring.
    rewrite seqsumb_plusSize. asemigroup.
    Abort.
  
  (** The order of two nested summations can be exchanged.
      ∑[i,lor,r](∑[j,loc,c] f_ij) = 
      ... + f11 + ... + f1c + 
                    ...
      ... + fr1 + ... + frc = 
      ∑[j,loc,c](∑[i,lor,r] f_ij) *)
  Lemma seqsumb_seqsumb_exchg : forall f lor loc r c,
      seqsumb (fun i => seqsumb (fun j => f i j) loc c) lor r =
        seqsumb (fun j => seqsumb (fun i => f i j) lor r) loc c.
  Proof.
    intros f lor loc. induction r.
    - destruct c; simpl; auto. rewrite seqsumb_eq0; auto. ring.
    - destruct c; simpl; auto. rewrite seqsumb_eq0; auto. ring.
      replace (seqsumb (fun i : nat => seqsumb (fun j : nat => f i j) loc c + f i (loc+c)%nat) lor r)
        with ((seqsumb (fun i : nat => seqsumb (fun j : nat => f i j) loc c) lor r) +
                (seqsumb (fun i : nat => f i (loc + c)%nat) lor r)).
      replace (seqsumb (fun j : nat => seqsumb (fun i : nat => f i j) lor r + f (lor+r)%nat j) loc c)
        with ((seqsumb (fun j : nat => seqsumb (fun i : nat => f i j) lor r) loc c) +
                (seqsumb (fun j : nat => f (lor+r)%nat j) loc c)).
      rewrite IHr. asemigroup.
      symmetry. apply seqsumb_add; auto.
      symmetry. apply seqsumb_add; auto.
  Qed.
  
End seqsumb.


(* ======================================================================= *)
(** ** More properties of sequence on special structure *)
Section seqsum_more.

  (** Let's have an monoid structure *)
  Context `{AMonoid A Aadd Azero}.
  Infix "+" := Aadd.
  Notation "0" := Azero.
  Notation seqsum := (@seqsum _ Aadd 0).

  (** Let's have order structure *)
  Context `{AleDec : Dec A Ale}.
  Context `{AltDec : Dec A Alt}.

  Infix "<=" := Ale.
  Context (Ale_refl : forall a : A, a <= a).
  Context (Aadd_le_compat : forall a1 b1 a2 b2 : A,
              a1 <= a2 -> b1 <= b2 -> a1 + b1 <= a2 + b2).
  Context (Aadd_eq_0_reg_l : forall a b : A,
              0 <= a -> 0 <= b -> a + b = 0 -> a = 0).

  (** If all elements of a sequence are >= 0, then the sum is >= 0 *)
  Lemma seqsum_ge0 : forall (f : nat -> A) n, (forall i, i < n -> 0 <= f i) -> 0 <= seqsum f n.
  Proof.
    intros. induction n; simpl.
    - apply Ale_refl.
    - replace 0 with (0 + 0); try apply identityLeft.
      apply Aadd_le_compat; auto.
      rewrite identityLeft. apply IHn; auto.
  Qed.
  
  (** If all elements of a sequence are >= 0, and the sum of top (n+1) elements of
      the sequence is = 0, then the sum of top n elements are 0 *)
  Lemma seqsum_eq0_less : forall (f : nat -> A) (n : nat), 
      (forall i, i < S n -> 0 <= f i) ->
      seqsum f (S n) = 0 ->
      seqsum f n = 0.
  Proof.
    intros. rewrite seqsumS_tail in H1.
    assert (0 <= f n); auto.
    assert (0 <= seqsum f n). apply seqsum_ge0; auto.
    apply Aadd_eq_0_reg_l in H1; auto.
  Qed.

  (** If all elements of a sequence are >= 0, and the sum of the sequence is = 0,
      then all elements of the sequence are 0. *)
  Lemma seqsum_eq0_imply_seq0 : forall (f : nat -> A) (n : nat), 
      (forall i, i < n -> 0 <= f i) -> seqsum f n = 0 -> (forall i, i < n -> f i = 0).
  Proof.
    intros f n. induction n. intros H1 H2 i H3; try easy. intros.
    assert (i < n \/ i = n)%nat by nia. destruct H3.
    - apply IHn; auto. apply seqsum_eq0_less; auto.
    - subst.
      assert (0 <= f n); auto.
      assert (0 <= seqsum f n). apply seqsum_ge0; auto.
      rewrite seqsumS_tail in H1.
      rewrite commutative in H1. apply Aadd_eq_0_reg_l in H1; auto.
  Qed.
  
End seqsum_more.


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