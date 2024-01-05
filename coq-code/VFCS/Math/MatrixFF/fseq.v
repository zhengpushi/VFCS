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
Require Export fin seq.
Require RExt.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv.

(* ######################################################################### *)
(** * Sequence by function, ff : fin n -> A  *)

Open Scope nat_scope.
Open Scope A_scope.

(* Notation fseq A n := (fin n -> A). *)

(* ======================================================================= *)
(** ** Equality of sequence *)
Section fseqeq.
  Context {A} {Azero : A}.

  (* Variable n : nat. *)
  (* Variable ff : fin (S n) -> A. *)
  (* Goal fin n -> A. *)
  (* apply (f2ff (@ff2f _ Azero _ ff)). *)
  (* Definition  *)
  (** seqeq of S has a equivalent form. *)
  (* Variable n : nat. *)
  (* Variable f : fin (S n) -> A. *)
  (* Check fun (i : fin n) => f (fin2fin _ _ i _). *)
  (* Variable i : fin n. *)
  (* Let H1: (fin2nat i < S n). *)
  (*   Search fin2nat. *)
  (*   apply ? *)
  Lemma fseqeq_S : forall n (f g : fin (S n) -> A),
      let f0 : fin n -> A := ff2ff (Azero:=Azero) _ _ f in
      let g0 : fin n -> A := ff2ff (Azero:=Azero) _ _ g in
      f = g <-> (f (nat2finS n) = g (nat2finS n) /\ f0 = g0).
  Proof.
    intros. split; intros. subst. split; auto.
    destruct H. unfold f0,g0 in H0.
    rewrite ffeq_iff_feq. rewrite ffeq_iff_feq in H0. intros.
    bdestruct (i <? n).
    - specialize (H0 i H2).
  Abort.

  (** seqeq is decidable  *)
  Lemma fseqeq_dec : forall {n} (f g : fin n -> A),
      (forall a b : A, {a = b} + {a <> b}) -> {f = g} + {f <> g}.
  Proof.
    intros n f g. induction n.
    - left. extensionality i. destruct fin0_False; auto.
    - intros.
      destruct (IHn (@ff2ff _ Azero _ _ f) (@ff2ff _ Azero _ _ g)); auto.
      apply ff2ff_inj in e; auto. Abort.
  
  (*     ? *)
  (*     easy. *)
  (*   - destruct IHn as [H1 | H1]. *)
  (*     + destruct (H (f n) (g n)) as [H2 | H2]. *)
  (*       * left. intros. bdestruct (i =? n). subst; auto. apply H1. lia. *)
  (*       * right. intro H3. rewrite H3 in H2; auto. *)
  (*     + right. intro H3. destruct H1. auto. *)
  (* Qed. *)
  
End fseqeq.


(* ======================================================================= *)
(** ** Equality of sequence with two indexes *)
Section fseq2eq.
  Context {A} {Azero : A}.

  (** seq2eq of Sr has a equivalent form. *)
  (* Variable r c : nat. *)
  (* Variable f g : fin r -> fin c -> A. *)
  (* Variable i : fin (S r). *)
  (* Variable j : fin c. *)
  (* Goal fin (S r) -> fin c -> A. *)
  (*   Check f i. *)
  (*   Check (fun i j =>  *)
  (* Variable *)
  (* Lemma seq2eq_Sr : forall r c (f g : nat -> nat -> A),  *)
  (*     seq2eq (S r) c f g <-> (seq2eq r c f g) /\ (seqeq c (f r) (g r)). *)
  (* Proof. *)
  (*   intros. unfold seq2eq, seqeq. split; intros. split; auto. *)
  (*   destruct H. bdestruct (ri =? r); subst; auto. apply H; lia. *)
  (* Qed. *)

  (** seq2eq of Sc has a equivalent form. *)
  (* Lemma seq2eq_Sc : forall r c (f g : nat -> nat -> A),  *)
  (*     seq2eq r (S c) f g <-> (seq2eq r c f g) /\ (seqeq r (fun i => f i c) (fun i => g i c)). *)
  (* Proof. *)
  (*   intros. unfold seq2eq, seqeq. split; intros. split; auto. *)
  (*   destruct H. bdestruct (ci =? c); subst; auto. apply H; lia. *)
  (* Qed. *)

  (** seq2eq is decidable  *)
  (* Lemma seq2eq_dec : forall r c f g, *)
  (*     (forall a b : A, {a = b} + {a <> b}) -> {seq2eq r c f g} + {~seq2eq r c f g}. *)
  (* Proof. *)
  (*   intros r c f g H. unfold seq2eq. revert c. induction r; intros. *)
  (*   - left. easy. *)
  (*   - destruct (IHr c) as [H1 | H1]. *)
  (*     + (* give a new proposition *) *)
  (*       pose proof (seqeq_dec c (f r) (g r) H) as H2. unfold seqeq in H2. *)
  (*       destruct H2 as [H2 | H2]. *)
  (*       * left. intros. bdestruct (ri =? r); subst; auto. apply H1; lia. *)
  (*       * right. intro H3. specialize (H3 r). destruct H2. auto. *)
  (*     + right. intro H2. destruct H1. auto. *)
  (* Qed. *)
  
End fseq2eq.


(* ======================================================================= *)
(** ** Sum of a sequence *)
Section fseqsum.
  
  (** Let's have an monoid structure *)
  Context `{M : Monoid}.
  Infix "+" := Aadd : A_scope.

  (** Sum of a sequence *)
  Definition fseqsum {n} (f : fin n -> A) :=
    @seqsum _ Aadd Azero (@ff2f _ Azero _ f) n.
    
  (** Sum of a sequence which every element is zero get zero. *)
  Lemma fseqsum_eq0 : forall {n} (f : fin n -> A),
      (forall i, f i = Azero) -> fseqsum f = Azero.
  Proof.
    intros. unfold fseqsum. apply seqsum_eq0.
    intros. unfold ff2f. destruct (_?<_); auto.
  Qed.

  (** Two sequences are equal, imply the sum are equal. *)
  Lemma fseqsum_eq : forall {n} (f g : fin n -> A),
      (forall i, f i = g i) -> fseqsum f = fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_eq.
    intros. unfold ff2f. destruct (_?<_); auto.
  Qed.

  
  (** Let's have an abelian monoid structure *)
  Context {AM : AMonoid Aadd Azero}.

  (* (** Sum a sequence of (S n) elements, equal to addition of Sum and tail *) *)
  (* Lemma seqsumS_tail : forall n f,  *)
  (*     seqsum f (S n) = seqsum f n + f n. *)
  (* Proof. reflexivity. Qed. *)
  
  (* (** Sum a sequence of (S n) elements, equal to addition of head and Sum *) *)
  (* Lemma seqsumS_head : forall n f,  *)
  (*     seqsum f (S n) = f O + seqsum (fun i => f (S i)) n. *)
  (* Proof. *)
  (*   intros. induction n; simpl in *. amonoid. rewrite IHn. amonoid. *)
  (* Qed. *)

  (* (** Sum of a sequence given by `l2f l` equal to folding of `l` *) *)
  (* Lemma seqsum_l2f : forall (l : list A) n, *)
  (*     length l = n -> *)
  (*     seqsum (@l2f _ Azero n l) n = fold_right Aadd Azero l. *)
  (* Proof. *)
  (*   unfold l2f. induction l; intros. *)
  (*   - simpl in H. subst; simpl. auto. *)
  (*   - destruct n; simpl in H. lia. rewrite seqsumS_head. rewrite IHl; auto. *)
  (* Qed. *)
  
  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma fseqsum_add : forall {n} (f g h : fin n -> A),
      (forall i, h i = f i + g i) -> fseqsum h = fseqsum f + fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_add.
    intros. unfold ff2f. destruct (_?<_); auto. monoid.
  Qed.

  
  (** Let's have a group structure *)
  Context `{G : Group A Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.

  
  (** Opposition of the sum of a sequence. *)
  Lemma fseqsum_opp : forall {n} (f g : fin n -> A),
      (forall i, f i = - g i) -> fseqsum f = - fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_opp.
    intros. unfold ff2f. destruct (_?<_); auto. rewrite group_inv_id; auto.
  Qed.

  
  (** Let's have an ring structure *)
  Context `{AR : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : make_ring_theory.
  
  
  (** Scalar multiplication of the sum of a sequence. *)
  Lemma fseqsum_cmul : forall k {n} (f g : fin n -> A),
      (forall i, f i = k * g i) -> fseqsum f = k * fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_cmul.
    intros. unfold ff2f. destruct (_?<_); auto. ring.
  Qed.

  Lemma fin2nat_iff_nat2fin : forall {n} (i : fin n) j (H: j < n),
      nat2fin j H = i <-> fin2nat i = j.
  Proof.
    intros. unfold nat2fin, fin2nat. destruct i; simpl. split; intros.
    inversion H0; auto. apply fin_eq_iff; auto.
  Qed.

  (** Sum a sequence which only one item is nonzero, then got this item. *)
  Lemma fseqsum_unique : forall {n} (f : fin n -> A) (k : A) i,
      f i = k -> (forall j, i <> j -> f j = Azero) -> fseqsum f = k.
  Proof.
    intros. unfold fseqsum. apply seqsum_unique with (i:=fin2nat i).
    apply fin2nat_lt. rewrite ff2f_fin2nat; auto.
    intros. unfold ff2f. destruct (_?<_); auto. apply H0.
    apply not_eq_sym. rewrite fin2nat_iff_nat2fin. auto.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      (i < m -> f(i) = g(i)) ->
      (i < n -> f(m+i) = h(i)) ->
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] f(i) + Σ[i,0,n] f(m + i). *)

  Lemma fseqsum_plusIdx : forall m n (f:fin (m + n) -> A) (g:fin m -> A) (h:fin n -> A),
      (forall i : fin m, f (fin2ExtendR i) = g i) ->
      (forall i : fin n, f (fin2PlusL i) = h i) ->
      fseqsum f = fseqsum g + fseqsum h.
  Proof.
    intros. unfold fseqsum. apply seqsum_plusIdx_ext.
    - intros. unfold ff2f. destruct (_?<_),(_?<_); try lia.
      rewrite <- H. f_equal. apply fin_eq_iff. rewrite fin2nat_nat2fin_id; auto.
    - intros. unfold ff2f. destruct (_?<_),(_?<_); try lia.
      rewrite <- H0. f_equal. apply fin_eq_iff. rewrite fin2nat_nat2fin_id; auto.
  Qed.

  (** Product two sum equal to sum of products.
      Σ[i,0,m] f(i) * Σ[i,0,n] g(i) = Σ[i,0,m*n] f(i/n)*g(i%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
   *)
  (* Lemma fseqsum_product : forall f g m n, *)
  (*     n <> O -> *)
  (*     seqsum f m * seqsum g n = seqsum (fun i => f (i / n) * g (i mod n)) (m * n).  *)
  (* Proof. *)
  (*   intros. induction m; simpl. ring. ring_simplify. *)
  (*   replace (n + m * n)%nat with (m * n + n)%nat by ring. *)
  (*   rewrite seqsum_plusIdx. rewrite <- IHm. asemigroup. *)
  (*   apply seqsum_cmul. intros. f_equal; f_equal. *)
  (*   apply add_mul_div; auto. apply add_mul_mod; auto. *)
  (* Qed. *)

  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] f_ij) = 
      f00 + f01 + ... + f0c + 
      f10 + f11 + ... + f1c + 
      ...
      fr0 + fr1 + ... + frc = 
      ∑[j,0,c](∑[i,0,r] f_ij) *)
  Lemma fseqsum_fseqsum_exchg : forall r c (f : fin r -> fin c -> A),
      fseqsum (fun i => fseqsum (fun j => f i j)) =
        fseqsum (fun j => fseqsum (fun i => f i j)).
  Proof.
    intros. unfold fseqsum. destruct r,c.
    - simpl. auto.
    - simpl. rewrite seqsum_eq0. unfold ff2f. destruct (_?<_); ring.
      intros. unfold ff2f. destruct (_?<_); auto.
    - simpl. rewrite seqsum_eq0. unfold ff2f. destruct (_?<_); ring.
      intros. unfold ff2f. destruct (_?<_); ring.
    - pose proof (seqsum_seqsum_exchg).
      specialize (H (fun i j => f (nat2finS i) (nat2finS j)) (S r) (S c)).
      match goal with
      | H: ?a1 = ?b1 |- ?a2 = ?b2 => replace a2 with a1;[replace b2 with b1|]; auto
      end.
      + apply seqsum_eq; intros. rewrite nth_ff2f with (H:=H0).
        apply seqsum_eq; intros. rewrite nth_ff2f with (H:=H1).
        f_equal; apply nat2finS_eq; apply fin_eq_iff.
      + apply seqsum_eq; intros. rewrite nth_ff2f with (H:=H0).
        apply seqsum_eq; intros. rewrite nth_ff2f with (H:=H1).
        f_equal; apply nat2finS_eq; apply fin_eq_iff.
  Qed.
  
End fseqsum.


(* ======================================================================= *)
(** ** Sequence on R type *)
Section Seq_R.

  Import Reals.
  Open Scope R.
  
  Notation fseqsum := (@fseqsum _ Rplus R0).

  (* (** If all elements of a sequence are >= 0, then the sum is >= 0 *) *)
  (* Lemma seqsum_ge0 : forall (f : nat -> R) n, *)
  (*     (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= seqsum f n. *)
  (* Proof. intros. induction n; simpl. lra. apply Rplus_le_le_0_compat; auto. Qed. *)

  (* (** If all elements of a sequence are >= 0, and the sum of top (n+1) elements of *)
  (*     the sequence is = 0, then the sum of top n elements are 0 *) *)
  (* Lemma seqsum_eq0_less : forall (f : nat -> R) (n : nat),  *)
  (*     (forall i, (i < S n)%nat -> 0 <= f i) -> *)
  (*     seqsum f (S n) = 0 -> *)
  (*     seqsum f n = 0. *)
  (* Proof. *)
  (*   intros. rewrite seqsumS_tail in H0. *)
  (*   assert (0 <= f n); auto. *)
  (*   assert (0 <= seqsum f n). apply seqsum_ge0; auto. lra. *)
  (* Qed. *)

  (* (** If all elements of a sequence are >= 0, and the sum of the sequence is = 0, *)
  (*     then all elements of the sequence are 0. *) *)
  (* Lemma seqsum_eq0_imply_seq0 : forall (f : nat -> R) (n : nat),  *)
  (*     (forall i, (i < n)%nat -> 0 <= f i) -> seqsum f n = 0 -> (forall i, (i < n)%nat -> f i = 0). *)
  (* Proof. *)
  (*   intros f n. induction n. intros H1 H2 i H3; try easy. intros. *)
  (*   assert (i < n \/ i = n)%nat by nia. destruct H2. *)
  (*   - apply IHn; auto. apply seqsum_eq0_less; auto. *)
  (*   - subst. *)
  (*     assert (0 <= f n); auto. *)
  (*     assert (0 <= seqsum f n). apply seqsum_ge0; auto. *)
  (*     rewrite seqsumS_tail in H0. lra. *)
  (* Qed. *)
  
End Seq_R.


(* ======================================================================= *)
(** ** Usage demo *)
Section test.
  Import RExt.

  Let n := 3%nat.
  Let seq1 : fin n -> R := fun i => Z2R (Z.of_nat (fin2nat i)).
  (* Compute @fseqsum _ Rplus R0 _ seq1. *)
  
  Open Scope Z.
  Let seq2 : fin n -> fin n -> Z :=
        fun i j => Z.of_nat (fin2nat i) + Z.of_nat (fin2nat j) + 1.
  (* Compute @fseqsum _ Z.add 0 _ (seq2 fin0). *)
End test. 
