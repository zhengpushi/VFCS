(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for sequence on R.
  author    : ZhengPu Shi
  date      : 2022.06
 *)

Require Export Sequence.
Require Export Fsequence.
Require Export RExt.

(* ======================================================================= *)
(** ** More properties of sequence on R type *)
Section seq_R.
  Import RExt.
  Open Scope R_scope.

  Notation Sum := (@seqsum _ Rplus R0).
  
  (** *** 算术-几何平均值不等式，简称 “算几不等式” *)
  (* 设 x1,x2,...,xn 为 n 个正实数，
     记算术平均数是 An = (∑xi)/n，
     记几何平均数是 Gn = n√(∏xi)，
     则 An >= Gn
     等号成立，当且仅当 x1 = x2 = ... = xn。
     
     展开后的形式

     a1+a2+...+an    n ______________
     ------------ >=  / a1*a2*...*an
          n
   *)

  (** 平均数不等式，或称平均值不等式、均值不等式。是算几不等式的推广 *)
  (* https://zh.wikipedia.org/wiki/平均数不等式 *)

  (* 在2维和3维的具体形式 *)
  Lemma Rineq2 : forall a b : R,
      0 <= a -> 0 <= b ->
      (a + b) / 2 >= sqrt(a * b).
  Abort.
  
  Lemma Rineq3 : forall a b c : R,
      0 <= a -> 0 <= b -> 0 <= c ->
      (a + b + c) / 3 >= sqrt(a * b).
  Abort.
  
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
  
End seq_R.

