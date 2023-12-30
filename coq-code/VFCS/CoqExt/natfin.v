(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : finite set of natural numbers
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. 比较自然数的判定程序
     le_gt_dec     : forall n m : nat, {n <= m} + {n > m}
     lt_eq_lt_dec  : forall n m : nat, {n < m} + {n = m} + {m < n}
 *)

Require Export PropExtensionality.
Require Export Arith Lia.
Require Export ListExt.
Require Import Extraction.

Ltac inv H := inversion H; subst; clear H.

Lemma lt_imply_gt : forall n m : nat, n < m -> m > n.
Proof. intros. lia. Qed.

Lemma gt_imply_lt : forall n m : nat, n > m -> m < n.
Proof. intros. lia. Qed.


(* 方案1: fin 0 : unit, fin (S _) : sig
   特点：
   1. 使用 unit 来处理 fin 0
   2. fin2nat 时，将 fin 0 处理为 0，不使用 option 机制。
   3. nat2fin 
 *)
Module natfin_old.

  (** fin type *)
  Definition fin (n : nat) :=
    match n with
    | O => unit                  (* 当 n = 0 时，用 unit 来表示 *)
    | _ => {i : nat | i < n}
    end.

  (** fin to nat *)
  Definition fin2nat {n} (f : fin n) : nat.
    destruct n.
    - exact 0.                  (* 当 n = 0 时，返回 0 *)
    - exact (proj1_sig f).
  Defined.

  (** nat to fin *)
  Definition nat2fin {n} (i : nat) : fin n.
    destruct n.
    - exact tt.                 (* 当 n = 0 时，返回 tt *)
    - destruct (le_lt_dec n i).
      + refine (exist _ 0 _). apply Nat.lt_0_succ. (* 当 i >= n 时，返回 {0|0<n} *)
      + refine (exist _ i _). auto.                (* 否则，返回正确的 {i|i<n} *)
  Defined.

End natfin_old.

(* 方案2: fin : sig
   特点：
   1. fin 0 集合中没有元素
   2. fin2nat 不需要特殊处理
   3. nat2fin 使用option
 *)
Module Export natfin.

  (** Definition of fin type *)
  Definition fin (n : nat) := {i | i < n}.

  (** Make a value of `fin (S n)`: {0 | 0 < S n}  *)
  Definition finS_0 {n} : fin (S n) := exist _ 0 (Nat.lt_0_succ _).
  
  (** Convert from fin to nat *)
  Definition fin2nat {n} (f : fin n) := proj1_sig f.

  Lemma fin_eq_iff : forall {n} (f1 f2 : fin n), f1 = f2 <-> fin2nat f1 = fin2nat f2.
  Proof.
    intros. destruct f1,f2; simpl; split; intros.
    - inversion H. auto.
    - subst. f_equal. apply proof_irrelevance.
  Qed.

  Lemma fin_neq_iff : forall {n} (f1 f2 : fin n), f1 <> f2 <-> fin2nat f1 <> fin2nat f2.
  Proof. intros. rewrite fin_eq_iff. split; auto. Qed.

  (** Convert from nat to fin *)
  Definition nat2fin {n} (i : nat) : option (fin n).
    destruct (le_gt_dec n i).
    - exact None.
    - refine (Some (exist _ i _)). auto.
  Defined.

  Lemma nat2fin_None : forall n i, i >= n -> @nat2fin n i = None.
  Proof. intros. unfold nat2fin. destruct le_gt_dec; auto. lia. Qed.

  Lemma nat2fin_fin2nat : forall n (f : fin n), nat2fin (fin2nat f) = Some f.
  Proof.
    intros. unfold nat2fin,fin2nat. destruct f. simpl.
    destruct (le_gt_dec n x). lia.
    f_equal. f_equal. apply proof_irrelevance.
  Qed.
  
  Lemma fin2nat_nat2fin : forall n i, i < n -> exists f, @nat2fin n i = Some f /\ fin2nat f = i.
  Proof.
    intros. unfold nat2fin, fin2nat. destruct le_gt_dec. lia.
    exists (exist _ i g). auto.
  Qed.
  
  (** Convert from nat to fin (S n). If `i >= S n` then {0} *)
  Definition nat2finS {n} (i : nat) : fin (S n).
    destruct (le_gt_dec (S n) i). (* {S n <= i} + {S n > i} *)
    - refine finS_0.
    - refine (exist _ i g).
  Defined.
  
  Lemma nat2finS_eq_nat2fin_Some : forall n i f,
      @nat2fin (S n) i = Some f -> @nat2finS n i = f.
  Proof.
    intros. unfold nat2fin, nat2finS in *. destruct (le_gt_dec (S n) i). easy.
    inversion H. f_equal.
  Qed.

  Lemma nat2finS_eq_nat2fin_None : forall n i,
      @nat2fin (S n) i = None -> @nat2finS n i = finS_0.
  Proof.
    intros. unfold nat2fin, nat2finS in *. destruct (le_gt_dec (S n) i); auto. easy.
  Qed.

  (** Convert from fin to fin *)
  Definition fin2fin {n m} (f : fin n) : option (fin m).
    destruct f as [i p].
    destruct (le_gt_dec m i).     (* {m<=i} + {m>i} *)
    - exact None.
    - refine (Some (exist _ i _)). auto.
  Defined.

  Lemma fin2fin_Some : forall n m (f : fin n),
      n <= m -> @fin2fin n m f = nat2fin (fin2nat f).
  Proof. intros. unfold fin2fin, nat2fin, fin2nat. destruct f. simpl. auto. Qed.

  (** Get sequence of fin *)
  Module finSeq_old.
    
    Fixpoint finSeqAux (n i : nat) {H : i < n} : list (fin n).
      destruct i. apply [exist _ 0 H].
      assert (i < n). apply (Nat.lt_succ_l i n H).
      apply (finSeqAux n i H0 ++ [exist _ (S i) H]).
    Defined.

    Lemma finSeqAux_length_Sn : forall n i {H1:i < n} {H2:i < S n},
        length (@finSeqAux (S n) i H2) = length (@finSeqAux n i H1).
    Proof.
      intros n i. revert n. induction i; intros; simpl; auto.
      rewrite !app_length; simpl. f_equal. apply IHi.
    Qed.

    Definition finSeq (n : nat) : list (fin n).
      destruct n. apply [].
      apply (@finSeqAux (S n) n). apply Nat.lt_succ_diag_r.
    Defined.

    Lemma finSeq_length : forall n, length (finSeq n) = n.
    Proof.
      induction n; simpl; auto.
      unfold finSeq in *. destruct n; simpl in *; auto.
      rewrite app_length; simpl. rewrite Nat.add_1_r. f_equal.
      erewrite finSeqAux_length_Sn. apply IHn.
    Qed.

    Lemma finSeq_nth : forall n i (H:i<n) (f0:fin n), nth i (finSeq n) f0 = exist _ i H.
    Proof.
      intros. unfold finSeq. destruct n; simpl; auto. lia.
    Admitted.

    Lemma finSeq_eq_seq : forall n, map fin2nat (finSeq n) = seq 0 n.
    Proof.
      intros. rewrite (list_eq_iff_nth 0 n).
      - intros. rewrite (@nth_map (fin n) nat _ _ n i (exist _ i H) 0); auto.
        + rewrite (finSeq_nth n i H); simpl. rewrite seq_nth; auto.
        + apply finSeq_length.
      - rewrite map_length. apply finSeq_length.
      - apply seq_length.
    Qed.
    
  End finSeq_old.

  Definition finSeq (n : nat) : list (fin n) :=
    match n with
    | O => []
    | _ => map nat2finS (seq 0 n)
    end.

  Lemma finSeq_length : forall n, length (finSeq n) = n.
  Proof. destruct n; auto. cbn. rewrite map_length. rewrite seq_length. auto. Qed.
  
  Lemma finSeq_nth : forall n i (H:i<n) (f0:fin n), nth i (finSeq n) f0 = exist _ i H.
  Proof.
    intros. unfold finSeq. destruct n; simpl; auto. lia. destruct i.
    - unfold nat2finS. destruct le_gt_dec. lia. f_equal. apply proof_irrelevance.
    - rewrite (nth_map (seq 1 n) nat2finS n i 0 f0).
      + rewrite seq_nth; try lia. simpl. unfold nat2finS.
        destruct le_gt_dec. lia. f_equal. apply proof_irrelevance.
      + apply seq_length.
      + lia.
  Qed.

  Lemma finSeq_eq_seq : forall n, map fin2nat (finSeq n) = seq 0 n.
  Proof.
    intros. rewrite (list_eq_iff_nth 0 n).
    - intros. rewrite (@nth_map (fin n) nat _ _ n i (exist _ i H) 0); auto.
      + rewrite (finSeq_nth n i H); simpl. rewrite seq_nth; auto.
      + apply finSeq_length.
    - rewrite map_length. apply finSeq_length.
    - apply seq_length.
  Qed.
  
End natfin.


(* ===================================================================== *)
(** ** Convert between list and finite-set-index-function *)
Section ff2l_l2ff.
  Context {A} {Azero : A}.

  Definition l2ff (n : nat) (l : list A) : fin n -> A :=
    fun f => nth (fin2nat f) l Azero.

  Definition ff2l {n} (ff : fin n -> A) : list A := map ff (finSeq n).

  Lemma ff2l_length : forall n f, length (@ff2l n f) = n.
  Proof.
    intros. unfold ff2l. rewrite map_length. apply finSeq_length.
  Qed.

  (** (ff2l f)[i] = f i *)
  Lemma nth_ff2l {n} f a i (H: i < n) : nth i (@ff2l n f) a = f (exist _ i H).
  Proof.
    intros. unfold ff2l.
    unfold finSeq. destruct n. lia. simpl. destruct i.
    - f_equal. unfold nat2finS. simpl. f_equal. apply proof_irrelevance.
    - rewrite (nth_map _ _ n i finS_0); try lia;
        [| rewrite map_length; apply seq_length].
      rewrite (nth_map _ _ n i 0); try lia;[| apply seq_length].
      f_equal. rewrite seq_nth; [|lia]. unfold nat2finS. destruct le_gt_dec. lia.
      f_equal. apply proof_irrelevance.
  Qed.

  Lemma ff2l_l2ff_id : forall l {n}, length l = n -> @ff2l n (@l2ff n l) = l.
  Proof.
    intros. rewrite (list_eq_iff_nth Azero n); auto.
    - intros. rewrite (nth_ff2l _ _ _ H0); auto.
    - apply ff2l_length.
  Qed.

  Lemma fin0_False : fin 0 -> False.
  Proof. intros. inversion H. lia. Qed.

  Lemma l2ff_ff2l_id : forall {n} f, @l2ff n (@ff2l n f) = f.
  Proof.
    intros. unfold l2ff,ff2l.
    apply functional_extensionality. intros.
    unfold finSeq. destruct n. destruct (fin0_False x).
    erewrite nth_map. erewrite nth_map. simpl.
    destruct (fin2nat x). simpl.
    ?
  Admitted.

End ff2l_l2ff.

Section test.
  (** [1;2;3] *)
  Let f := fun (f:fin 3) => fin2nat f + 1.
  Compute (ff2l f).
  Compute (l2ff 3 (ff2l f)).
End test.  
