(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : auxiliary library for nat.
  author    : ZhengPu Shi
  date      : 2021.05
 *)

Require Import Basic.
Require Import Bool.
Require Export Init.Nat.
Require Export Arith.
Require Export PeanoNat.
Require Export Nat.
Require Export Lia.
Require Export Hierarchy.  


(* ######################################################################### *)
(** * Mathematical Structure *)

(** *** well-defined *)
Hint Resolve
  Nat.add_wd Nat.mul_wd  (* nat *)
  : wd.

#[export] Instance nat_eq_Dec : Dec (@eq nat).
Proof. constructor. apply Nat.eq_dec. Defined.

#[export] Instance nat_le_Dec : Dec le.
Proof. constructor. intros. destruct (le_lt_dec a b); auto. right. lia. Defined.

#[export] Instance nat_lt_Dec : Dec lt.
Proof. constructor. intros. destruct (lt_dec a b); auto. Defined.

(* n <= n *)
Lemma nat_le_refl : forall n : nat, n <= n.
Proof. intros. lia. Qed.

Section test.
  Goal forall a b : nat, {a = b} + {a <> b}.
  Proof. intros. apply Aeqdec. Abort.
End test.


(* ######################################################################### *)
(** * More properties for nat *)

(** a natural number must be odd or even *)
Lemma nat_split : forall (n : nat), exists (x : nat),
    n = 2 * x \/ n = 2 * x + 1.
Proof.
  induction n.
  - exists 0. auto.
  - destruct IHn. destruct H.
    + exists x. right. subst. lia.
    + exists (x+1). left. subst. lia.
Qed.

(** Two step induction principle for natural number *)
Theorem nat_ind2 : forall (P : nat -> Prop),
    (P 0) -> (P 1) -> (forall n, P n -> P (S (S n))) -> (forall n, P n).
Proof.
  intros. destruct (nat_split n). destruct H2; subst; induction x; auto.
  - replace (2 * S x) with (S (S (2 * x))); [apply H1; auto | lia].
  - replace (2 * S x + 1) with (S (S (2 * x + 1))); [apply H1; auto | lia].
Qed.

(** Connect induction principle between nat and list *)
Lemma ind_nat_list {A} : forall (P : list A -> Prop) ,
    (forall n l, length l = n -> P l) -> (forall l, P l).
Proof.
  intros. apply (H (length l)). auto.
Qed.


(* ######################################################################### *)
(** * Loop shift *)
Section loop_shift.

  (** Left loop shift *)
  Definition nat_lshl (n : nat) (i : nat) (k : nat) : nat :=
    Nat.modulo (i + k) n.

  (** Right loop shift *)
  Definition nat_lshr (n : nat) (i : nat) (k : nat) : nat :=
    Nat.modulo (i + (n - (Nat.modulo k n))) n.

  (* Compute List.map (fun i => nat_lshl 5 i 1) (List.seq 0 10). *)
  (* Compute List.map (fun i => nat_lshr 5 i 1) (List.seq 0 10). *)
  
  (** Let S is a set of natural numbers modulo n, i.e. its elements are [0,1,...,(n-1)],
    and n is equivalent to 0.
    Then right loop shift S by k got T.
    We claim that: forall i < n, (T[i] = (S[i] + k)%n /\ (S[i] = (T[i] + ?)%n) *)
  (* Theorem nat_lshl_spec0 : forall n i k, nat_lshl n i k = Nat. *)

End loop_shift.

(* ######################################################################### *)
(** * Extension for nat from (Verified Quantum Computing). *)

(* https://www.cs.umd.edu/~rrand/vqc/index.html *)

(*******************************)
(* Automation *)
(*******************************)

Lemma double_mult : forall (n : nat), (n + n = 2 * n).
Proof.
  intros. lia.
Qed.

Lemma pow_two_succ_l : forall x, 2^x * 2 = 2 ^ (x + 1).
Proof.
  intros. rewrite Nat.mul_comm. rewrite <- Nat.pow_succ_r'. rewrite Nat.add_1_r. auto.
Qed.

Lemma pow_two_succ_r : forall x, 2 * 2^x = 2 ^ (x + 1).
Proof.
  intros. rewrite <- Nat.pow_succ_r'. rewrite Nat.add_1_r. auto.
Qed.

Lemma double_pow : forall (n : nat), 2^n + 2^n = 2^(n+1). 
Proof.
  intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity.
Qed.

Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> a^m = b^n.
Proof.
  intuition.
Qed.

Ltac unify_pows_two :=
  repeat match goal with
    (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
    | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat 
        by reflexivity
    | [ |- context[ (0 + ?a)%nat]]            => rewrite Nat.add_0_l 
    | [ |- context[ (?a + 0)%nat]]            => rewrite Nat.add_0_r 
    | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
    | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
    | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
    | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
    | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
    | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
    | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite Nat.add_assoc 
    | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
    end.

(** Restoring Matrix dimensions *)
Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => match type of A with
                | nat => idtac
                end
  end.

(* ######################################################################### *)
(** * Useful bdestruct tactic with the help of reflection *)

(** There havn't GT and GE in standard library. *)

Notation  "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a) (at level 70) : nat_scope.

(* 证明自然数不等式 *)
Ltac solve_nat_ineq :=
  match goal with
  (* H: _ = true *)
  | H:(?a <? ?b) = true |- ?a < ?b => apply Nat.ltb_lt; apply H
  | H:(?a <? ?b) = true |- ?b > ?a => apply Nat.ltb_lt; apply H
  | H:(?a <? ?b) = false |- ?a >= ?b => apply Nat.ltb_ge; apply H
  | H:(?a <? ?b) = false |- ?b <= ?a => apply Nat.ltb_ge; apply H
  | H:(?a <=? ?b) = false |- ?b < ?a => apply Nat.leb_gt; apply H
  end.


(** Proposition and boolean are reflected. *)

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

(** These theorems are automatic used. *)
Global Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

(** This tactic makes quick, easy-to-read work of our running example. *)
Example reflect_example2: forall a, (if a <? 5 then a else 2) < 6.
Proof.
  intros. bdestruct (a <? 5);  (* instead of: [destruct (ltb_reflect a 5)]. *)
  lia.
Qed.


(* ######################################################################### *)
(** * Lost or deprecated lemmas *)

(** Coq.Arith.Lt.lt_S_n is deprecated since Coq 8.16.
    1. although coqc suggest us to use Nat.succ_lt_mono,
       but that is a  a bidirectional version, not exactly same as lt_S_n.
    2. from Coq 8.16, there is a same lemma Arith_prebase.lt_S_n,
       but it not exist in Coq 8.13,8.14.
*)
Definition lt_S_n: forall n m : nat, S n < S m -> n < m.
Proof.
  intros. apply Nat.succ_lt_mono. auto.
Qed.

(* 0 < x < S n -> pred x < n *)
Lemma pred_lt : forall x n : nat, 0 < x < S n -> pred x < n.
Proof.
  intros. destruct H. destruct x. easy.
  rewrite Nat.pred_succ. apply Nat.succ_lt_mono; auto.
Qed.


(* ######################################################################### *)
(** * Properties for div and mod *)

(* Check Nat.div_add.    (* (a + b * c) / c = a / c + b *) *)
(* Check Nat.div_add_l.  (* a * b + c) / b = a + c / b *) *)
(* Check Nat.div_small.  (* a < b -> a / b = 0 *) *)
(* Check Nat.add_mod.    (* (a + b) % n = (a % n + b % n) % n *) *)
(* Check Nat.mod_add.    (* (a + b * c) mod c = a mod c *) *)
(* Check Nat.mod_mul.    (* (a * b) % b = 0 *) *)
(* Check Nat.mod_small.  (* a < b -> a % b = 0 *) *)


(* i < n -> (m * n + i) / n = m *)
Lemma add_mul_div : forall m n i, n <> 0 -> i < n -> (m * n + i) / n = m.
Proof.
  intros. rewrite Nat.div_add_l; auto. rewrite Nat.div_small; auto.
Qed.
 
(* i < n -> (m * n + i) % n = i *)
Lemma add_mul_mod : forall m n i, n <> 0 -> i < n -> (m * n + i) mod n = i.
Proof.
  intros. rewrite Nat.add_mod; auto. rewrite Nat.mod_mul; auto.
  repeat rewrite Nat.mod_small; auto.
Qed.
