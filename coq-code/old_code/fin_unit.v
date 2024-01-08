(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : finite set of natural numbers
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. 比较自然数的判定程序
     已有的程序
     le_gt_dec     : forall n m : nat, {n <= m} + {n > m}
     lt_eq_lt_dec  : forall n m : nat, {n < m} + {n = m} + {m < n}
     新增的程序
     lt_ge_dec     : forall n m : nat, {n < m} + {n >= m}

  2. fin 的几种实现方案
     (1). 使用 unit 来表示 fin 0
        定义：
        Definition fin (n : nat) :=
        match n with O => unit | _ => {i : nat | i < n} end.
        特点：
        1. fin2nat 中，将 fin 0 处理为 0
           注意，由于这个特殊处理，往往需要处理 n = 0 和 n > 0 这两类问题。
           实际使用时，部分引理需要 0 < n 时成立。
           同时，部分引理需要 i < n 时成立。
        2. nat2fin 不需要使用option
        3. 由于fin是依赖类型，抽取出的Ocaml代码含有 Obj.magic
     (2). fin 0 集合中没有元素
        定义：
        Definition fin (n : nat) := {i | i < n}.
        特点：
        1. fin2nat 不需要特殊处理
        2. nat2fin 使用option
           由于 option 的存在，使得表达式较为复杂。
        3. sig类型本质上不是依赖类型，抽取的Ocaml代码是正常的。
     (3). 多使用一个下标
        定义：
        Definition fin (n : nat) := {i | i <= n}
        特点：
        1. fin 0 有一个元素，fin 1 有两个元素，fin n 有 S n 个元素。
           所以该集合永远不为空。
           同时，fin2nat, nat2fin 也成为了全函数，并且代码抽取也是正常的。
        3. 已知的一些问题
           由于fin用于访问vec，所以 vec 0 也修改为含有1个元素的向量。
           所以，vec n 含有 S n 个元素。
           这就导致 vec 3 实际上是 4 个元素，很奇怪。
        4. 一个思路是，只修改 fin，而不修改 vec, seq 等模块。
           fin 0 = {0}       丢弃 {0}
           fin 1 = {0,1}     丢弃 {1}
           fin 2 = {0,1,2}   丢弃 {2}
           在与 vec 交互时，人为的丢弃最大的那个值。
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

Lemma lt_ge_dec : forall x y : nat, {x < y} + {x >= y}.
Proof. intros. destruct (le_gt_dec y x); auto. Defined.

Infix "?<" := (lt_ge_dec) (at level 30).


#[export] Hint Rewrite
  map_length
  seq_length
  : fin.


(** ** Type of fin *)

Notation "[ | n ]" := (exist _ n _) (format "[ | n ]").

(** Definition of fin type *)
Definition fin (n : nat) :=
  match n with
  | O => unit
  | S n0 => {i | i < n}
  end.

(* `fin 0` is unique  *)
Lemma fin_0_unique : forall i : fin 0, i = tt.
Proof. intros. destruct i. auto. Qed.

(* Two `fin 0` is equal  *)
Lemma fin_0_eq : forall i j : fin 0, i = j.
Proof. intros. destruct i,j. auto. Qed.

(* Two `fin (S n)` is equal, iff value is equal *)
Lemma fin_S_eq : forall {n} x1 x2 (H1 : x1 < S n) (H2 : x2 < S n),
    exist (fun i => i < S n) x1 H1 = exist _ x2 H2 <-> x1 = x2.
Proof.
  intros. split; intros.
  - inversion H. auto.
  - subst. f_equal. apply proof_irrelevance.
Qed.

(* Two `fin (S n)` is not equal, iff, value is not equal  *)
Lemma fin_S_neq : forall {n} x1 x2 (H1 : x1 < S n) (H2 : x2 < S n),
    exist (fun i => i < S n) x1 H1 <> exist _ x2 H2 <-> x1 <> x2.
Proof. intros. rewrite fin_S_eq. easy. Qed.

(* (* Two `fin (S n)` of same value is equal *) *)
(* Lemma fin_S_eq_refl : forall {n} x (H1 H2 : x < S n), *)
(*     exist (fun i => i < S n) x H1 = exist _ x H2. *)
(* Proof. intros. rewrite fin_S_eq. auto. Qed. *)

(** Equality of `fin` is decidable *)
Definition finEqdec : forall {n} (i j : fin n), {i = j} + {i <> j}.
Proof.
  intros. destruct n. destruct i,j; auto. destruct i as [i], j as [j].
  destruct (Nat.eq_dec i j).
  - subst. left. apply fin_S_eq; auto.
  - right. apply fin_S_neq; auto.
Defined.

(** A default entry of `fin` *)
Definition fin0 {n : nat} : fin n :=
  match n with
  | O => tt
  | S n0 => exist _ 0 (Nat.lt_0_succ _)
  end.


(** ** [fin] to [nat] *)

(** Convert from [fin] to [nat] *)
Definition fin2nat {n} : fin n -> nat :=
  match n with
  | O => fun _ => 0                                (* if n=0, then 0  *)
  | S n0 => fun (f : fin (S n0)) => proj1_sig f    (* if n>0, then proj1(f) *)
  end.

Lemma fin_eq_iff : forall {n} (f1 f2 : fin n), f1 = f2 <-> fin2nat f1 = fin2nat f2.
Proof.
  intros. destruct n.
  - simpl. split; intros; auto. apply fin_0_eq.
  - destruct f1,f2; simpl; split; intros.
    + apply fin_S_eq in H; auto.
    + apply fin_S_eq; auto.
Qed.

Lemma fin_neq_iff : forall {n} (f1 f2 : fin n), f1 <> f2 <-> fin2nat f1 <> fin2nat f2.
Proof. intros. rewrite fin_eq_iff. split; auto. Qed.

Lemma fin2nat_lt_Sn : forall {n} (f : fin (S n)), fin2nat f < S n.
Proof. intros. simpl. destruct f; simpl. auto. Qed.

Lemma fin2nat_lt_n_gt0 : forall {n} (f : fin n), 0 < n -> fin2nat f < n.
Proof. intros. destruct n. lia. apply fin2nat_lt_Sn. Qed.

Lemma fin2nat_fin0 : forall {n}, @fin2nat n fin0 = 0.
Proof. intros. destruct n; auto. Qed.


(** ** [nat] to [fin n] *)

(** Convert from [nat] to [fin] *)
Definition nat2fin {n} (i : nat) : fin n.
  destruct n. apply tt.                     (* if n=0, tt : fin 0  *)
  destruct (i ?< S n).
  - refine [|i]. auto.                      (* if i< n, {i | i < S n} *)
  - refine [|0]. apply Nat.lt_0_succ.       (* if i>=n, {0 | 0 < S n} *)
Defined.

Lemma nat2fin_fin2nat_id : forall n (f : fin n), nat2fin (fin2nat f) = f.
Proof.
  destruct n. intros. apply fin_0_eq.
  intros. destruct f. simpl fin2nat. unfold nat2fin. destruct (lt_ge_dec).
  apply fin_S_eq; auto. lia. 
Qed.

Lemma fin2nat_nat2fin_id : forall n i, i < n -> fin2nat (@nat2fin n i) = i.
Proof.
  intros. unfold nat2fin, fin2nat. destruct n. lia.
  destruct lt_ge_dec; simpl; auto. lia.
Qed.

Lemma nat2fin_overflow : forall {n} i, i >= n -> @nat2fin n i = fin0.
Proof.
  intros. unfold nat2fin. destruct n. apply fin_0_eq.
  destruct (i ?< S n). lia. cbn. apply fin_S_eq; auto.
Qed.

Lemma fin2nat_nat2fin_overflow : forall n i, i >= n -> fin2nat (@nat2fin n i) = 0.
Proof.
  intros. destruct (i ?< n). lia. rewrite nat2fin_overflow; auto.
  apply fin2nat_fin0.
Qed.


(** ** [fin n] to [fin m] *)

(** Convert from [fin n] to [fin m] *)
Definition fin2fin {n m} (f : fin n) : fin m := nat2fin (fin2nat f).


(** ** Conversion between nat-Function (f) and Fin-Function (ff) *)
Section ff2f_f2ff.
  Context {A} {Azero : A}.

  (** `ff` to `f` *)
  Definition ff2f {n} (ff : fin n -> A) : nat -> A := fun i => ff (nat2fin i).
  
  (** `f` to `ff` *)
  Definition f2ff {n} (f : nat -> A) : fin n -> A := fun i => f (fin2nat i).

  (* Note: Equality of two nat-function is defined on top n elements *)
  Lemma ff2f_f2ff_id : forall {n} (f : nat -> A) i, i < n -> @ff2f n (f2ff f) i = f i.
  Proof. intros. unfold f2ff,ff2f. rewrite fin2nat_nat2fin_id; auto. Qed.

  Lemma f2ff_ff2f_id : forall {n} (ff : fin n -> A), f2ff (ff2f ff) = ff.
  Proof.
    intros. unfold f2ff,ff2f. apply functional_extensionality; intros.
    rewrite nat2fin_fin2nat_id; auto.
  Qed.
  
End ff2f_f2ff.


(** ** Sequence of fin *)

Definition finseq (n : nat) : list (fin n) := map nat2fin (seq 0 n).

Lemma finseq_length : forall n, length (finseq n) = n.
Proof. destruct n; simpl; auto. autorewrite with fin; auto. Qed.

#[export] Hint Rewrite
  finseq_length
  : fin.

Lemma nth_finseq : forall (n : nat) i, nth i (finseq n) fin0 = nat2fin i.
Proof.
  intros. unfold finseq.
  bdestruct (i >=? n).
  - simpl. rewrite nat2fin_overflow; auto.
    rewrite nth_overflow; auto. autorewrite with fin; auto.
  - rewrite nth_map with (n:=n)(Azero:=0); autorewrite with fin; auto; try lia.
    rewrite seq_nth; try lia. auto.
Qed.

Lemma map_fin2nat_finseq : forall n, map fin2nat (finseq n) = seq 0 n.
Proof.
  intros.
  rewrite (list_eq_iff_nth 0 n); autorewrite with fin; auto.
  intros. rewrite seq_nth; auto.
  rewrite nth_map with (n:=n)(Azero:=fin0); autorewrite with fin; auto.
  rewrite nth_finseq. rewrite fin2nat_nat2fin_id; auto.
Qed.

Lemma nth_map_finseq : forall {A} (n : nat) (f : fin n -> A) i (H: i < n) (a : A),
    nth i (map f (finseq n)) a = f (nat2fin i).
Proof.
  intros. rewrite nth_map with (n:=n)(Azero:=fin0); autorewrite with fin; auto.
  rewrite nth_finseq; autorewrite with fin; auto. 
Qed.

(** (ff2f ff)[i] equal to ff[i] *)
Lemma nth_ff2f : forall {A} {n} (ff : fin n -> A) i, ff2f ff i = ff (nat2fin i).
Proof. intros. unfold ff2f. auto. Qed.


(** ** Sum of a Fin-indexing-Fun (FF) *)
Section ffsum.
  Context `{M : Monoid}.
  
  (* Definition ffsum {n} (ff : fin n -> A) : A := *)
  (*   seqsum (ff2f ff) n. *)

End ffsum.


(** ** Convert between list and Fin-indexing-fun (ff) *)

(** [list] to `ff` *)
Section l2ff_ff2l.
  Context {A} {Azero : A}.
  
  Definition l2ff (n : nat) (l : list A) : fin n -> A :=
    fun i => nth (fin2nat i) l Azero.

  Lemma nth_l2ff : forall {n} (l : list A) (i : fin n),
      (l2ff n l) i = nth (fin2nat i) l Azero.
  Proof. intros. unfold l2ff. auto. Qed.

  
  (** `ff` to [list] *)
  Definition ff2l {n} (ff : fin n -> A) : list A := map ff (finseq n).

  Lemma ff2l_length : forall {n} (ff : fin n -> A), length (ff2l ff) = n.
  Proof. intros. unfold ff2l; autorewrite with fin; auto. Qed.

  Hint Rewrite @ff2l_length : fin.

  (** (ff2l f)[i] = f i *)
  Lemma nth_ff2l : forall {n} (ff: fin n -> A) i (H: i < n),
      nth i (ff2l ff) Azero = ff (nat2fin i).
  Proof. intros. unfold ff2l. rewrite nth_map_finseq; auto. Qed.

  Lemma ff2l_l2ff_id : forall l {n}, length l = n -> ff2l (l2ff n l) = l.
  Proof.
    intros. rewrite (list_eq_iff_nth Azero n); autorewrite with fin; auto.
    intros. rewrite nth_ff2l; auto. unfold l2ff. rewrite fin2nat_nat2fin_id; auto.
  Qed.

  Lemma l2ff_ff2l_id : forall {n} f, 0 < n -> l2ff n (ff2l f) = f.
  Proof.
    intros. unfold l2ff,ff2l.
    apply functional_extensionality. intros.
    rewrite nth_map_finseq. rewrite nat2fin_fin2nat_id; auto.
    apply fin2nat_lt_n_gt0; auto.
  Qed.
End l2ff_ff2l.

#[export] Hint Rewrite @ff2l_length : fin.


Section test.
  (* [1;2;3] *)
  Let f := fun (f:fin 3) => fin2nat f + 1.
  (* Compute (ff2l f). *)
  (* Compute (l2ff 0 []). *)
  (* Compute (l2ff 3 [1;2;3]). *)
  
  Goal @l2ff _ 0 3 [1;2;3] = f.
  Proof.
    unfold l2ff. unfold f.
    apply functional_extensionality. intros.
    simpl.
    destruct x; simpl; auto.
    destruct x; simpl; auto.
    destruct x; simpl; auto.
    destruct x; simpl; auto. lia.
  Qed.
End test.  
