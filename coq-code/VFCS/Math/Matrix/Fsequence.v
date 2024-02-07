(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : sequence.
  author    : ZhengPu Shi
  date      : 2022.06
 *)

Require Export Basic.
Require Export ListExt.
Require Export Hierarchy.
Require Export NatExt.
Require Export Fin Sequence.
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
  Context {A : Type}.

  (** seqeq is decidable *)
  Lemma fseq_eqdec : forall {n} (f g : fin n -> A),
      (forall a b : A, {a = b} + {a <> b}) -> {f = g} + {f <> g}.
  Proof.
    intros n f g H. induction n.
    - left. extensionality i. exfalso. apply fin0_False; auto.
    - destruct (IHn (ffS2ff f) (ffS2ff g)) as [H1|H1].
      + destruct (H (f (nat2finS n)) (g (nat2finS n))) as [H2|H2].
        * left. extensionality i. destruct (fin2nat i ??< n).
          ** pose proof (equal_f H1) as H3. specialize (H3 (fin2PredRange i l)).
             unfold ffS2ff in H3. rewrite fin2nat_fin2PredRange in H3.
             rewrite nat2finS_fin2nat in H3. auto.
          ** assert (fin2nat i = n). pose proof (fin2nat_lt i). lia.
             replace (@nat2finS n n) with i in H2; auto.
             rewrite <- (nat2fin_fin2nat (S n) i (fin2nat_lt _)).
             rewrite (nat2finS_eq n n (Nat.lt_succ_diag_r _)).
             apply sig_eq_iff; auto.
        * right. intro. destruct H2. subst. auto.
      + right. intro. destruct H1. subst. auto.
  Qed.
  
  #[export] Instance fseq_eqDec : forall {n} (AeqDec: Dec (@eq A)), Dec (@eq (fin n -> A)).
  Proof. intros. constructor. intros. apply fseq_eqdec. apply AeqDec. Qed.

End fseqeq.


(* ======================================================================= *)
(** ** Equality of sequence with two indexes *)
Section fseq2eq.
  Context {A} {Azero : A}.

  (** fseq2eq is decidable  *)
  (* Lemma fseq2eq_dec : forall r c f g, *)
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
  Notation seqsum := (@seqsum _ Aadd Azero).

  (** Sum of a sequence *)
  Definition fseqsum {n} (f : fin n -> A) :=
    (* @seqsum _ Aadd Azero (@ff2f _ Azero _ f) n. *)
    seqsum (@ff2f _ Azero _ f) n.
    
  (** Sum of a sequence which every element is zero get zero. *)
  Lemma fseqsum_eq0 : forall {n} (f : fin n -> A),
      (forall i, f i = Azero) -> fseqsum f = Azero.
  Proof.
    intros. unfold fseqsum. apply seqsum_eq0.
    intros. unfold ff2f. destruct (_??<_); auto.
  Qed.

  (** Two sequences are equal, imply the sum are equal. *)
  Lemma fseqsum_eq : forall {n} (f g : fin n -> A),
      (forall i, f i = g i) -> fseqsum f = fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_eq.
    intros. unfold ff2f. destruct (_??<_); auto.
  Qed.

  (** Convert `fseqsum` to `seqsum` *)
  Lemma fseqsum_to_seqsum : forall {n} (f : fin n -> A) (g : nat -> A),
      (forall i, f i = g (fin2nat i)) -> fseqsum f = seqsum g n.
  Proof.
    intros. unfold fseqsum. apply seqsum_eq; intros.
    specialize (H (nat2fin i H0)). simpl in *.
    unfold ff2f. destruct (_??<_); try lia.
    rewrite <- H. f_equal. apply sig_eq_iff; auto.
  Qed.

  (** Convert `fseqsum` to `seqsum` (succ form) *)
  Lemma fseqsum_to_seqsum_succ : forall {n} (f : fin (S n) -> A),
      fseqsum f = seqsum (fun i => f (nat2finS i)) n + f (nat2finS n).
  Proof.
    intros. unfold fseqsum. simpl. f_equal.
    - apply seqsum_eq; intros. unfold ff2f,nat2finS. destruct (_??<_); auto. lia.
    - unfold ff2f,nat2finS. destruct (_??<_); auto. lia.
  Qed.
  
  
  (** Let's have an abelian monoid structure *)
  Context {AM : AMonoid Aadd Azero}.
  
  (** Sum a sequence of (S n) elements, equal to addition of Sum and tail *)
  Lemma fseqsumS_tail : forall {n} (f : fin (S n) -> A) (g : fin n -> A),
      (forall i, f (fin2SuccRange i) = g i) ->
      fseqsum f = fseqsum g + f (nat2finS n).
  Proof.
    intros. unfold fseqsum. rewrite seqsumS_tail. f_equal.
    - apply seqsum_eq. intros. specialize (H (nat2fin i H0)).
      rewrite nth_ff2f with (H:=H0). rewrite <- H.
      erewrite nth_ff2f. f_equal. rewrite nat2fin_iff_fin2nat.
      rewrite fin2nat_fin2SuccRange. rewrite fin2nat_nat2fin. auto.
      Unshelve. lia.
    - erewrite nth_ff2f. f_equal.
      erewrite nat2finS_eq. apply sig_eq_iff; auto.
      Unshelve. apply Nat.lt_succ_diag_r. apply Nat.lt_succ_diag_r.
  Qed.

  (** Sum a sequence of (S n) elements, equal to addition of head and Sum *)
  Lemma fseqsumS_head : forall {n} (f : fin (S n) -> A) (g : fin n -> A),
      (forall i, f (fin2SuccRangeSucc i) = g i) ->
      fseqsum f = f (nat2finS O) + fseqsum g.
  Proof.
    intros. unfold fseqsum. rewrite seqsumS_head. f_equal.
    apply seqsum_eq. intros.
    rewrite nth_ff2f with (H:=H0). rewrite <- H.
    erewrite nth_ff2f. f_equal. rewrite nat2fin_iff_fin2nat.
    rewrite fin2nat_fin2SuccRangeSucc. rewrite fin2nat_nat2fin. auto.
    Unshelve. lia.
  Qed.

  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma fseqsum_add : forall {n} (f g h : fin n -> A),
      (forall i, h i = f i + g i) -> fseqsum h = fseqsum f + fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_add.
    intros. unfold ff2f. destruct (_??<_); auto. monoid.
  Qed.

  (** Sum a sequence which only one item is nonzero, then got this item. *)
  Lemma fseqsum_unique : forall {n} (f : fin n -> A) (a : A) i,
      f i = a -> (forall j, i <> j -> f j = Azero) -> fseqsum f = a.
  Proof.
    intros. unfold fseqsum. apply seqsum_unique with (i:=fin2nat i).
    apply fin2nat_lt. rewrite ff2f_fin2nat; auto.
    intros. unfold ff2f. destruct (_??<_); auto. apply H0.
    apply not_eq_sym. rewrite nat2fin_iff_fin2nat. auto.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      (i < m -> f(i) = g(i)) ->
      (i < n -> f(m+i) = h(i)) ->
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] f(i) + Σ[i,0,n] f(m + i). *)
  Lemma fseqsum_plusIdx : forall m n (f:fin (m + n) -> A) (g:fin m -> A) (h:fin n -> A),
      (forall i : fin m, f (fin2AddRangeR i) = g i) ->
      (forall i : fin n, f (fin2AddRangeAddL i) = h i) ->
      fseqsum f = fseqsum g + fseqsum h.
  Proof.
    intros. unfold fseqsum. apply seqsum_plusIdx_ext.
    - intros. unfold ff2f. destruct (_??<_), (_??<_); try lia.
      rewrite <- H. f_equal. apply sig_eq_iff. rewrite fin2nat_nat2fin; auto.
    - intros. unfold ff2f. destruct (_??<_), (_??<_); try lia.
      rewrite <- H0. f_equal. apply sig_eq_iff. rewrite fin2nat_nat2fin; auto.
  Qed.

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
    - simpl. rewrite seqsum_eq0. unfold ff2f. destruct (_??<_); monoid.
      intros. unfold ff2f. destruct (_??<_); auto.
    - simpl. rewrite seqsum_eq0. unfold ff2f. destruct (_??<_); monoid.
      intros. unfold ff2f. destruct (_??<_); auto.
    - pose proof (seqsum_seqsum_exchg).
      specialize (H (fun i j => f (nat2finS i) (nat2finS j)) (S r) (S c)).
      match goal with
      | H: ?a1 = ?b1 |- ?a2 = ?b2 => replace a2 with a1;[replace b2 with b1|]; auto
      end.
      + apply seqsum_eq; intros. rewrite nth_ff2f with (H:=H0).
        apply seqsum_eq; intros. rewrite nth_ff2f with (H:=H1).
        f_equal; apply nat2finS_eq; apply sig_eq_iff.
      + apply seqsum_eq; intros. rewrite nth_ff2f with (H:=H0).
        apply seqsum_eq; intros. rewrite nth_ff2f with (H:=H1).
        f_equal; apply nat2finS_eq; apply sig_eq_iff.
  Qed.

  
  (** Let's have a group structure *)
  Context `{G : Group A Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.

  
  (** Opposition of the sum of a sequence. *)
  Lemma fseqsum_opp : forall {n} (f g : fin n -> A),
      (forall i, f i = - g i) -> fseqsum f = - fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_opp.
    intros. unfold ff2f. destruct (_??<_); auto. rewrite group_opp_0; auto.
  Qed.

  
  (** Let's have an ring structure *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  
  (** Scalar multiplication of the sum of a sequence. *)
  Lemma fseqsum_cmul : forall k {n} (f g : fin n -> A),
      (forall i, f i = k * g i) -> fseqsum f = k * fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_cmul.
    intros. unfold ff2f. destruct (_??<_); auto. ring.
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
  
End fseqsum.

(** Extension for `fseqsum` *)
Section fseqsum_ext.
  
  (** Let's have an abelian monoid structure *)
  Context `{AM : AMonoid}.
  Infix "+" := Aadd : A_scope.
  Notation fseqsum := (@fseqsum _ Aadd Azero).

  (** Let's have another type K and an operation scalar multiplication *)
  Context {K : Type}.
  Context (cmul : K -> A -> A).
  Infix "*" := cmul.
  Context (cmul_zero_keep : forall k : K, cmul k Azero = Azero).
  Context (cmul_add_distr : forall (a b : A) (k : K), k * (a + b) = k * a + k * b).

  (** Scalar multiplication of the sum of a sequence with different type. *)
  Lemma fseqsum_cmul_ext : forall {n} (k : K) (f g : fin n -> A),
      (forall i, f i = k * g i) -> fseqsum f = k * fseqsum g.
  Proof.
    intros. unfold fseqsum. apply seqsum_cmul_ext; auto.
    intros. unfold ff2f. destruct (_??<_); auto.
  Qed.
  
End fseqsum_ext.



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
