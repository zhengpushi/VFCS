(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : auxiliary library for sequence.
  author    : ZhengPu Shi
  date      : 2022.06
 *)

Require Export NatExt.
Require Export BasicConfig AlgebraStructure.
Require RExt.

Generalizable Variable A Aeq Aadd Aopp Amul Ainv.


(* ######################################################################### *)
(** * Sequence by function, f : nat -> A  *)

Open Scope nat_scope.
Open Scope A_scope.

Declare Scope seq_scope.
Delimit Scope seq_scope with seq.
Open Scope seq_scope.

Declare Scope seq2_scope.
Delimit Scope seq2_scope with seq2.
Open Scope seq2_scope.

(* ======================================================================= *)
(** ** Equality of sequence *)
Section seqeq.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.

  (** Equality of two sequence which have one index *)
  Definition seqeq n (f g : nat -> A) := forall i, i < n -> f i == g i.

  (** seqeq is an equivalence relation *)
  Section seqeq_equiv.

    Context {n : nat}.
    Infix "==" := (seqeq n) : A_scope.
    
    Lemma seqeq_refl : forall (f : nat -> A), f == f.
    Proof. intros. hnf. easy. Qed.

    Lemma seqeq_sym : forall (f g : nat -> A), f == g -> g == f.
    Proof. intros. hnf in *. intros. rewrite <- H; easy. Qed.

    Lemma seqeq_trans : forall (f g h : nat -> A), f == g -> g == h -> f == h.
    Proof. intros. hnf in *. intros. rewrite H, <- H0; easy. Qed.

    Lemma seqeq_equiv : Equivalence (seqeq n).
    Proof.
      intros. constructor; intro; intros.
      apply seqeq_refl.
      apply seqeq_sym; auto.
      apply seqeq_trans with y; auto.
    Qed.

    Global Existing Instance seqeq_equiv.
  End seqeq_equiv.


  (** seqeq of S has a equivalent form. *)
  Lemma seqeq_S : forall n (f g : nat -> A),
      seqeq (S n) f g <-> (seqeq n f g) /\ (f n == g n).
  Proof.
    split; intros.
    - split; auto. unfold seqeq in *. auto.
    - unfold seqeq in *. intros. destruct H.
      (* Note: Aeq_reflect is come from typeclass of Decidable theory. *)
      destruct (Aeq_reflect i n); subst; auto. apply H. lia.
  Qed.
  
  (** seqeq is decidable  *)
  Global Instance seqeq_dec {Dec_Aeq : Decidable Aeq} : forall n, Decidable (seqeq n).
  Proof.
    induction n; constructor; intros.
    - left. unfold seqeq. easy.
    - unfold seqeq in *.
      destruct (a ==? b), (a n ==? b n).
      + left. intros. destruct (eqb_reflect i n); subst; auto. apply a0. lia.
      + right. intro. destruct n0. apply H. auto.
      + right. intro. destruct n0. intros. auto.
      + right. intro. destruct n0. intros. auto.
  Qed.

  (** *** seqeq is decidable with the help of bool equality *)
  Section seqeq_dec_with_eqb.
    Context {Dec: Decidable Aeq}.

    (** Boolean equality of two sequence *)
    Fixpoint seqeqb n (f g : nat -> A) : bool :=
      match n with
      | O => true
      | 1 => Aeqb (f 0) (g 0)
      | S n' => (seqeqb n' f g) && Aeqb (f n') (g n')
      end.
    
    (** seqeqb of S has a equivalent form. *)
    Lemma seqeqb_S : forall {n} (f g : nat -> A), 
        seqeqb (S n) f g = (seqeqb n f g) && (Aeqb (f n) (g n)).
    Proof.
      intros. destruct n; auto.
    Qed.
    
    (** seqeqb = true <-> seqeq *)
    Lemma seqeqb_true_iff : forall n f g, seqeqb n f g = true <-> seqeq n f g.
    Proof.
      induction n; intros.
      - unfold seqeqb, seqeq. split; intros; auto. lia.
      - rewrite seqeqb_S. rewrite seqeq_S.
        rewrite andb_true_iff.
        rewrite Aeqb_true. rewrite IHn. split; auto.
    Qed.
    
    (** seqeqb = false <-> ~seqeq *)
    Lemma seqeqb_false_iff : forall n f g, seqeqb n f g = false <-> ~(seqeq n f g).
    Proof.
      induction n; intros.
      - unfold seqeqb, seqeq. split; intros; try easy. destruct H. easy.
      - rewrite seqeqb_S. rewrite seqeq_S.
        rewrite andb_false_iff.
        rewrite IHn. rewrite Aeqb_false. split; intros.
        + apply Classical_Prop.or_not_and; auto.
        + apply Classical_Prop.not_and_or in H; auto.
    Qed.
    
    (** seqeq is decidable (with the help of eqb)  *)
    Global Instance seqeq_dec_with_eqb : forall n, Decidable (seqeq n).
    Proof.
      intros. constructor. intros f g. destruct (seqeqb n f g) eqn:E1.
      - left. apply seqeqb_true_iff in E1. auto.
      - right. apply seqeqb_false_iff in E1. auto.
    Qed.

  End seqeq_dec_with_eqb.
  
End seqeq.


(* ======================================================================= *)
(** ** Equality of sequence with two index *)
Section seq2eq.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Notation seqeq := (seqeq (Aeq:=Aeq)).

  (** Equality of two sequence which have two indexes *)
  Definition seq2eq r c (f g : nat -> nat -> A) := 
    forall ri ci, ri < r -> ci < c -> f ri ci == g ri ci.
  
  (** seq2eq of Sr has a equivalent form. *)
  Lemma seq2eq_Sr : forall r c (f g : nat -> nat -> A), 
      seq2eq (S r) c f g <-> (seq2eq r c f g) /\ (seqeq c (f r) (g r)).
  Proof.
    split.
    - intros. split; auto.
      + unfold seq2eq in *. intros. apply H; auto.
      + unfold seq2eq, seqeq in *. intros. auto.
    - unfold seq2eq,seqeq. intros. destruct H.
      destruct (Aeq_reflect ri r); subst; auto. apply H; auto. lia.
  Qed.

  (** seq2eq is a equivalence relation *)
  Lemma seq2eq_refl : forall r c (f : nat -> nat -> A),
      let R := seq2eq r c in R f f.
  Proof. intros. hnf. easy. Qed.

  Lemma seq2eq_sym : forall r c (f g : nat -> nat -> A),
      let R := seq2eq r c in R f g -> R g f.
  Proof. intros. hnf in *. intros. rewrite <- H; easy. Qed.

  Lemma seq2eq_trans : forall r c (f g h : nat -> nat -> A),
      let R := seq2eq r c in R f g -> R g h -> R f h.
  Proof. intros. hnf in *. intros. rewrite H, <- H0; easy. Qed.

  Lemma seq2eq_equiv : forall r c, Equivalence (seq2eq r c).
  Proof.
    intros. constructor; intro; intros.
    apply seq2eq_refl.
    apply seq2eq_sym; auto.
    apply seq2eq_trans with y; auto.
  Qed.

  Global Existing Instance seq2eq_equiv.
  
  (** *** seq2eq is decidable with the help of bool equality *)
  Section seq2eq_dec_with_eqb.
    Context {Dec: Decidable Aeq}.

    (** seq2eq is decidable  *)
    Lemma seq2eq_dec : forall r c, Decidable (seq2eq r c).
    Proof.
      induction r; constructor; intros f g.
      - left. unfold seq2eq. intros. easy.
      - unfold seq2eq in *. specialize (IHr c).
        destruct (f ==? g).
        + (* Tips: need to construct a prop *)
          assert (Decidable (fun f g : nat -> nat -> A =>
                               forall ci, ci < c -> f r ci == g r ci)) as H.
          { constructor. intros. apply seqeq_dec. }
          destruct (f ==? g).
          * left. intros. destruct (Aeq_reflect ri r); subst; auto.
            apply a; try easy. lia.
          * right. intro. destruct n. intros. apply H0; auto.
        + right. intro. destruct n. intros. auto.
    Qed.

    (** Boolean equality of two sequence *)
    Fixpoint seq2eqb r c (f g : nat -> nat -> A) : bool :=
      match r with
      | O => true
      | 1 => seqeqb c (f 0) (g 0)
      | S r' => (seq2eqb r' c f g) && (seqeqb c (f r') (g r')) 
      end.
    
    (** seq2eqb of Sr has a equivalent form. *)
    Lemma seq2eqb_Sr : forall r c (f g : nat -> nat -> A), 
        seq2eqb (S r) c f g = (seq2eqb r c f g) && (seqeqb c (f r) (g r)).
    Proof.
      intros. destruct r; auto.
    Qed.
    
    (** seq2eqb = true <-> seq2eq *)
    Lemma seq2eqb_true_iff : forall r c f g, seq2eqb r c f g = true <-> seq2eq r c f g.
    Proof.
      induction r; intros.
      - unfold seq2eqb, seq2eq. split; intros; auto. lia.
      - rewrite seq2eqb_Sr. rewrite seq2eq_Sr.
        rewrite andb_true_iff. rewrite IHr. rewrite seqeqb_true_iff. reflexivity.
    Qed.
    
    (** seq2eqb = false <-> ~seq2eq *)
    Lemma seq2eqb_false_iff : forall r c f g, seq2eqb r c f g = false <-> ~(seq2eq r c f g).
    Proof.
      induction r; intros.
      - unfold seq2eqb, seq2eq. split; intros; try easy. destruct H. easy.
      - rewrite seq2eqb_Sr. rewrite seq2eq_Sr.
        rewrite andb_false_iff. rewrite IHr. rewrite seqeqb_false_iff. split; intros H.
        + apply Classical_Prop.or_not_and; auto.
        + apply Classical_Prop.not_and_or in H; auto.
    Qed.

    (** seq2eq is decidable (with the help of eqb)  *)
    Lemma seq2eq_dec_with_eqb : forall r c, Decidable (seq2eq r c).
    Proof.
      intros. constructor. intros f g. destruct (seq2eqb r c f g) eqn:E1.
      - left. apply seq2eqb_true_iff in E1. auto.
      - right. apply seq2eqb_false_iff in E1. auto.
    Qed.

  End seq2eq_dec_with_eqb.
  
End seq2eq.


(* ======================================================================= *)
(** ** Sum of a sequence *)
Section Sum.

  (** Let's have a monoid structure *)
  Context `{M : Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.

  (** Sum of a sequence *)
  Fixpoint seqsum (f : nat -> A) (n : nat) : A := 
    match n with
    | O => A0
    | S n' => seqsum f n' + f n'
    end.
  
  (** Sum of a sequence which every element is zero get zero. *)
  Lemma seqsum_seq0 : forall (f : nat -> A) (n : nat), 
      (forall i, i < n -> f i == A0) -> seqsum f n == A0.
  Proof.
    intros f n H. induction n; simpl. easy.
    rewrite H; auto. rewrite IHn; auto. monoid_simp.
  Qed.

  (** Corresponding elements of two sequences are equal, imply the sum are 
      equal. *)
  Lemma seqsum_eq : forall (f g : nat -> A) (n : nat),
      (forall i, i < n -> f i == g i) -> seqsum f n == seqsum g n.
  Proof. 
    intros f g n H. 
    induction n; simpl; auto. easy. rewrite !IHn; auto. rewrite H; auto. easy.
  Qed.
  
  (** Let's have an abelian monoid structure *)
  Context {AM : AMonoid Aadd A0 Aeq}.

  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma seqsum_add : forall (f g : nat -> A) (n : nat),
      seqsum (fun i => f i + g i) n == seqsum f n + seqsum g n.  
  Proof. 
    intros f g n. induction n; simpl. monoid_simp. rewrite IHn.
    rewrite ?associative. f_equiv.
    rewrite <- ?associative. f_equiv. apply commutative.
  Qed.

  (** Let's have a group structure *)
  Context `{G : Group A Aadd A0 Aopp Aeq}.
  Notation "- a" := (Aopp a) : A_scope.

  (** Opposition of the sum of a sequence. *)
  Lemma seqsum_opp : forall (f : nat -> A) (n : nat),
      - (seqsum f n) == seqsum (fun i => - f i) n.
  Proof.
    intros f n. induction n; simpl. apply group_inv_id.
    rewrite <- IHn. rewrite group_inv_distr. apply commutative.
  Qed.

  (** Let's have an ring structure *)
  Context `{R : Ring A Aadd A0 Aopp Amul A1 Aeq}.
  Add Ring ring_inst : (make_ring_theory R).
  
  Infix "*" := Amul : A_scope.

  
  (** Constant left multiply to the sum of a sequence. *)
  Lemma seqsum_cmul_l : forall c (f : nat -> A) (n : nat),
      c * seqsum f n == seqsum (fun i => c * f i) n.  
  Proof.  
    intros c f n. induction n; simpl. ring.
    ring_simplify. rewrite IHn. ring.
  Qed.

  (** Constant right multiply to the sum of a sequence. *)
  Lemma seqsum_cmul_r : forall c (f : nat -> A) (n : nat),
      seqsum f n * c == seqsum (fun i => f i * c) n.  
  Proof.
    intros c f n. induction n; simpl; try ring.
    ring_simplify. rewrite IHn. ring.
  Qed.

  (** Sum a sequence which only one item in nonzero, then got this item. *)
  Lemma seqsum_unique : forall (f : nat -> A) (k : A) (n i : nat), 
      i < n -> f i == k -> (forall j, i <> j -> f j == A0) -> seqsum f n == k.
  Proof.
    (* key idea: induction n, and case {x =? n} *)
    intros f k n. induction n; intros. easy. simpl.
    destruct (Aeq_reflect i n).
    - subst.
      assert (seqsum f n == A0) as H2.
      + apply seqsum_seq0. intros. apply H1. lia.
      + rewrite H2. rewrite H0. ring.
    - assert (f n == A0) as H2.
      + apply H1; auto.
      + rewrite H2. monoid_simp. apply IHn with i; auto. lia.
  Qed.
  
  (** Add the sum and a tail element *)
  Lemma seqsum_extend_r : forall n f, 
      seqsum f n + f n == seqsum f (S n).
  Proof. reflexivity. Qed.
  
  (** Add a head element and the sum *)
  Lemma seqsum_extend_l : forall n f, 
      f O + seqsum (fun i => f (S i)) n == seqsum f (S n).
  Proof.
    intros n f. induction n; simpl. ring.
    ring_simplify. rewrite IHn. simpl. ring.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] f(i) + Σ[i,0,n] f(m + i). *)
  Lemma seqsum_plusIdx : forall m n f,
      seqsum f (m + n) == seqsum f m + seqsum (fun i => f (m + i)%nat) n. 
  Proof.
    intros m n f. induction m.
    - simpl. ring_simplify. easy.
    - simpl. rewrite IHm. rewrite !associative. f_equal.
      remember (fun x => f (m + x)%nat) as g.
      replace (f (m + n)%nat) with (g n).
      replace (f m) with (g 0).
      replace (fun i => f (S (m + i))) with (fun i => g (S i)).
      rewrite seqsum_extend_l.
      rewrite seqsum_extend_r. easy.
      all: rewrite Heqg; auto.
      extensionality i. f_equal. lia.
  Qed.

  (** Product two sum equal to sum of products.
      Σ[i,0,m] f(i) * Σ[i,0,n] g(i) = Σ[i,0,m*n] f(i/n)*g(i%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
   *)
  Lemma seqsum_product : forall m n f g,
      n <> O ->
      seqsum f m * seqsum g n == seqsum (fun i => f (i / n) * g (i mod n)) (m * n). 
  Proof.
    intros. induction m.
    - simpl. ring.
    - simpl. ring_simplify. rewrite IHm; auto.
      remember (fun i : nat => f (i / n) * g (i mod n)) as h.
      rewrite seqsum_cmul_l.
      (* Σ[i,0,n] f(m)*g(i) = Σ[i,0,n] f((m*n+i)/n)*g((m*n+i)%n) *)
      setoid_replace (seqsum (fun i : nat => f m * g i) n)
        with (seqsum (fun i : nat => h (m * n + i)%nat) n).
      rewrite <- seqsum_plusIdx. f_equiv. ring.
      apply seqsum_eq.
      intros. rewrite Heqh.
      (* (m * n + i) / n = m *)
      rewrite Nat.div_add_l; auto.  (* a * b + c) / b = a + c / b *)
      rewrite Nat.div_small; auto.  (* a < b -> a / b = 0 *)
      (* (m * n + i) % n = i *)
      rewrite Nat.add_mod; auto.  (* (a + b) % n = a % n + b % n) % n *)
      rewrite Nat.mod_mul; auto.  (* (a * b) mod b = 0 *)
      repeat rewrite Nat.mod_small; auto. (* a < b -> a % b = 0 *)
      rewrite Nat.add_0_l, Nat.add_0_r. easy.
  Qed.

  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] f_ij) = 
      f00 + f01 + ... + f0c + 
      f10 + f11 + ... + f1c + 
      ...
      fr0 + fr1 + ... + frc = ∑[j,0,c](∑[i,0,r] f_ij) *)
  Lemma seqsum_seqsum_exchg : forall f r c,
      seqsum (fun i => seqsum (fun j => f i j) c) r ==
        seqsum (fun j => seqsum (fun i => f i j) r) c.
  Proof.
    intros f.
    induction r.
    - induction c; simpl in *; try easy. rewrite <- IHc. ring.
    - induction c; simpl in *; auto. specialize (IHr 0). simpl in *. rewrite IHr.
      ring. rewrite <- ?associative. f_equiv.
      rewrite <- IHc. rewrite associative.
      rewrite (commutative (seqsum _ c)). rewrite <- associative. f_equiv.
      setoid_replace (seqsum (fun i : nat => seqsum (fun j : nat => f i j) c + f i c) r) with
        (seqsum (fun i => seqsum (fun j => f i j) (S c)) r); try easy.
      rewrite IHr. simpl. f_equiv. rewrite IHr. easy.
  Qed.
  
End Sum.

Section test.
  Import RExt.

  Example seq1 := fun n => Z2R (Z.of_nat n).
  Notation seqsum := (seqsum (Aadd:=Rplus) (A0:=R0)).

  (* Compute seqsum seq1 3. *)
  (* Eval simpl in seqeqb 5 seq1 seq1. *)
  (* Compute seqeqb 5 seq1 seq1. *)
  
  Open Scope Z.
  Example seq2 := fun i j => Z.of_nat i + Z.of_nat j.
  Example seq3 := fun i j => Z.of_nat i + Z.of_nat j + 1.

  (* Eval simpl in seq2eqb 2 3 seq2 seq3. *)
  (* Compute seq2eqb 2 3 seq2 seq3. *)
  (* Compute seq2eqb 2 3 seq2 seq2. *)
  
End test. 
