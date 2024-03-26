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
     le_gt_dec     : forall m n : nat, {m <= n} + {m > n}
     lt_eq_lt_dec  : forall m n : nat, {m < n} + {m = n} + {n < m}
     新增的程序
     lt_ge_dec     : forall m n : nat, {m < n} + {m >= n}

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
           由于很多很自然成立的引理需要额外的前提约束，非常不直观。
           最根本原因是 fin2nat和nat2fin不是一一映射。
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
        4. 多数引理不需要额外的前提就能成立。
           比如 vnth 不会越界。
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
Require Export NatExt.
Require Import Extraction.

(* #[export] Hint Rewrite *)
(*   map_length *)
(*   seq_length *)
(*   : fin. *)


(** ** Type of fin *)

Declare Scope fin_scope.
Delimit Scope fin_scope with fin.

Open Scope nat_scope.
Open Scope fin_scope.

(* Notation "[ | i ]" := (exist _ i _) (format "[ | i ]"). *)

(** Definition of fin type *)
(* Notation fin n := {i | i < n}. *)
(* Definition fin (n : nat) := {i | i < n}. *)
(* 借鉴ordinal，使用 Inductive 可避免因过于多态的 sig 类型而带来的不必要的复杂性 *)
Inductive fin (n : nat) := Fin (i : nat) (E : i < n).
(* 借鉴了 ordinal 的记号 *)
Notation "''I_' n" := (fin n)
                        (at level 8, n at level 2, format "''I_' n").
Arguments Fin {n}.

Lemma fin_n_gt0 :forall {n} (i : fin n), 0 < n.
Proof.
  intros. destruct i as [i E]. destruct n. lia. lia.
Qed.

Lemma fin0_False : fin 0 -> False.
Proof. intros. inversion H. lia. Qed.

Lemma fin_eq_iff : forall {n} i j Ei Ej, i = j <-> @Fin n i Ei = @Fin n j Ej.
Proof.
  intros. split; intros.
  - subst. f_equal. apply proof_irrelevance.
  - inversion H. auto.
Qed.


(** ** [fin] to [nat] *)

(** Convert from [fin] to [nat] *)
Definition fin2nat {n} (f : fin n) := let '(Fin i _) := f in i.
(* Coercion fin2nat : fin >-> nat. *)

Lemma fin2nat_inj : forall {n} (i1 i2 : fin n), fin2nat i1 = fin2nat i2 -> i1 = i2.
Proof. intros. destruct i1,i2; simpl in H. apply fin_eq_iff; auto. Qed.

Lemma fin2nat_inj_not : forall {n} (i1 i2 : fin n), fin2nat i1 <> fin2nat i2 -> i1 <> i2.
Proof. intros. intro. destruct H. subst; auto. Qed.

Lemma fin2nat_lt : forall {n} (i : fin n), fin2nat i < n.
Proof. intros. destruct i; simpl. auto. Qed.

Lemma fin2nat_lt_Sn : forall {n} (i : fin n), fin2nat i < S n.
Proof. intros. pose proof (fin2nat_lt i). auto. Qed.

Lemma fin_fin2nat : forall {n} (i : fin n) (E : fin2nat i < n), Fin (fin2nat i) E = i.
Proof. intros. destruct i; simpl. apply fin_eq_iff; auto. Qed.


(** ** comparison procedure of [fin] *)
Notation "i ??= j" := (fin2nat i ??= fin2nat j) : fin_scope.
Notation "i ??> j" := (fin2nat i ??> fin2nat j) : fin_scope.
Notation "i ??>= j" := (fin2nat i ??>= fin2nat j) : fin_scope.
Notation "i ??< j" := (fin2nat i ??< fin2nat j) : fin_scope.
Notation "i ??<= j" := (fin2nat i ??<= fin2nat j) : fin_scope.


(** ** [fin0] *)

(** A default entry of `fin` *)
Definition fin0 {n : nat} : fin (S n) := Fin 0 (Nat.lt_0_succ _).

(** i <> fin0 -> 0 < fin2nat i *)
Lemma fin2nat_gt0_if_neq0 : forall {n} (i : fin (S n)), i <> fin0 -> 0 < fin2nat i.
Proof.
  intros. unfold fin2nat,fin0 in *. destruct i.
  assert (i <> 0). intro. destruct H. apply fin_eq_iff. auto. lia.
Qed.

(** 0 < fin2nat i -> i <> fin0 *)
Lemma fin2nat_gt0_imply_neq0 : forall {n} (i : fin (S n)), 0 < fin2nat i -> i <> fin0.
Proof.
  intros. unfold fin2nat,fin0 in *. destruct i.
  intro. apply fin_eq_iff in H0. lia.
Qed.


(** ** [fin1] *)

(** fin 1 is unique *)
Lemma fin1_uniq : forall (i : fin 1), i = fin0.
Proof. intros. destruct i. apply fin_eq_iff. lia. Qed.


(** ** [nat] to [fin (S n)] *)

(** Convert from nat to fin (S n). If `i >= S n` then {0} *)
Definition nat2finS {n} (i : nat) : fin (S n).
  destruct (i ??< S n)%nat as [E|E].
  - apply (Fin i E).
  - apply fin0.
Defined.

Notation "# i" := (nat2finS i) (at level 1, format "# i").

Lemma nat2finS_eq : forall n i (E : i < S n), nat2finS i = Fin i E.
Proof.
  intros. unfold nat2finS. destruct (_??<_)%nat; try lia. apply fin_eq_iff; auto.
Qed.

Lemma nat2finS_fin2nat : forall n i, nat2finS (@fin2nat (S n) i) = i.
Proof.
  intros. destruct i; simpl. rewrite nat2finS_eq with (E:=E); auto.
Qed.

Lemma fin2nat_nat2finS : forall n i, i < (S n) -> fin2nat (@nat2finS n i) = i.
Proof.
  intros. rewrite nat2finS_eq with (E:=H); auto.
Qed.

(** {i<n} <> nat2finS n -> fin2nat i < n *)
Lemma nat2finS_neq_imply_lt : forall {n} (i : fin (S n)), i <> nat2finS n -> fin2nat i < n.
Proof.
  intros. pose proof (fin2nat_lt i).
  assert (fin2nat i <> n); try lia.
  intro. destruct H. destruct i; simpl in *. subst.
  rewrite nat2finS_eq with (E:=H0); auto. apply fin_eq_iff; auto.
Qed.


(** ** [nat] to [fin n] *)

(** Convert from [nat] to [fin] *)
Definition nat2fin {n} (i : nat) (E : i < n) : fin n := Fin i E.

Lemma nat2fin_fin2nat : forall n (f : fin n) (E: fin2nat f < n),
    nat2fin (fin2nat f) E = f.
Proof. intros. unfold nat2fin,fin2nat. destruct f. apply fin_eq_iff; auto. Qed.

Lemma fin2nat_nat2fin : forall n i (E: i < n), (fin2nat (nat2fin i E)) = i.
Proof. intros. auto. Qed.

Lemma fin2nat_imply_nat2fin : forall {n} (i : fin n) j (H: j < n),
    fin2nat i = j -> nat2fin j H = i.
Proof.
  intros. unfold nat2fin, fin2nat in *. destruct i. apply fin_eq_iff; auto.
Qed.

Lemma nat2fin_imply_fin2nat : forall {n} (i : fin n) j (E: j < n),
    nat2fin j E = i -> fin2nat i = j.
Proof.
  intros. unfold nat2fin, fin2nat in *. destruct i. apply fin_eq_iff in H; auto.
Qed.

Lemma nat2fin_iff_fin2nat : forall {n} (i : fin n) j (E: j < n),
    nat2fin j E = i <-> fin2nat i = j.
Proof.
  intros; split; intros. apply nat2fin_imply_fin2nat in H; auto.
  apply fin2nat_imply_nat2fin; auto.
Qed.



(** ** Tactic for fin *)

(* 自动化简在上下文和目标中与fin有关的判定过程 *)
Ltac fin :=
  repeat
    (intros;
     let E := fresh "E" in
     match goal with
     (* 若上下文中有 i : fin n, H : n = 0，则转化为 i : fin 0 *)
     | [i : fin ?n, H: ?n = 0 |- _]     => subst
     (* 若上下文中有 fin 0，则立即得证 *)
     | i : fin 0 |- _                   => exfalso; apply (fin0_False i)
     (* 若上下为中是 i : fin n，目标是 fin2nat i < n，则立即得证 *)
     | [i : fin ?n |- fin2nat ?i < ?n]  => apply fin2nat_lt
     (* 若目标是 Fin i Ei = Fin j Ej，转换为 i = j *)
     | |- Fin ?i ?Ei = Fin ?j ?Ej       => apply fin_eq_iff; auto
     (* 若目标是 nat2fin i Ei = Fin j Ej，转换为 i = j *)
     | |- nat2fin ?i ?Ei = Fin ?j ?Ej   => apply fin_eq_iff; auto
     (* 若目标是 Fin j Ej = nat2fin i Ei，转换为 i = j *)
     | |- Fin ?j ?Ej = nat2fin ?i ?Ei   => apply fin_eq_iff; auto
     (* 若目标是 nat2fin i Ei = nat2fin j Ej，转换为 i = j *)
     | |- nat2fin ?i ?Ei = nat2fin ?j ?Ej   => apply fin_eq_iff; auto
     (* 若目标是 f i = f j，转换为 i = j *)
     | |- ?f ?i = ?f ?j => f_equal
     (* 若目标是 H1, H2 : P, H1 = H2，则使用证明无关性 *)
     | [H1 : ?P, H2: ?P |- ?H1 = ?H2]     =>
         match type of P with | Prop => apply proof_irrelevance end
     (* 若上下文中有 fin2nat i = fin2nat j，则推导出 i = j *)
     | H : fin2nat ?i = fin2nat ?j |- _ => apply fin2nat_inj in H
     (* 若上下文中有 fin2nat i <> fin2nat j，则推导出 i <> j *)
     | H : fin2nat ?i <> fin2nat ?j |- _ => apply fin2nat_inj_not in H
     (* 若上下文或目标有 fin2nat #i，或者 nat2finS (fin2nat i)，则化简 *)
     | [H : context [(fin2nat #?i)] |- _]   => rewrite fin2nat_nat2finS in H
     | [ |- context [(fin2nat #?i)]]        => rewrite fin2nat_nat2finS
     | [H : context [(nat2finS (fin2nat ?i))] |- _] => rewrite nat2finS_fin2nat in H
     | [ |- context [(nat2finS (fin2nat ?i))]]    => rewrite nat2finS_fin2nat
     (* 若要证 (i : fin n) |- fin2nat i < n，可立即得证 *)
     | [i : fin ?n |- fin2nat ?i < ?n]            => apply fin2nat_lt
     (* 若上下文中是 ??=, ??<, ??<= ，则进行分解 *)
     | [ H : context [(?i ??= ?j)%nat] |- _]  => destruct (i ??= j)%nat as [E|E]
     | [ |- context [(?i ??= ?j)%nat]]        => destruct (i ??= j)%nat as [E|E]
     | [ H : context [(?i ??< ?j)%nat] |- _]  => destruct (i ??< j)%nat as [E|E]
     | [ |- context [(?i ??< ?j)%nat]]        => destruct (i ??< j)%nat as [E|E]
     | [ H : context [(?i ??<= ?j)%nat] |- _] => destruct (i ??<= j)%nat as [E|E]
     | [ |- context [(?i ??<= ?j)%nat]]       => destruct (i ??<= j)%nat as [E|E]
     (* 若上下文中有 fin n 类型的等式 i = j，则重写 *)
     | H : ?i = ?j |- _ => match type of i with | fin ?n => try rewrite H in * end
     end;
     (* simpl; *)
     auto; try reflexivity; try easy; try lia; try ring
    ).


(** ** Cast between two [fin] type with actual equal range *)

(** Cast from [fin n] type to [fin m] type if [n = m] *)
Definition cast_fin : forall n m, n = m -> 'I_n = 'I_m.
Proof. intros. subst. auto. Qed.


(** ** [fin m] to [fin n] *)

(** Convert from [fin m] to [fin n] *)
Definition fin2fin m n (f : fin m) (E : fin2nat f < n) : fin n :=
  nat2fin (fin2nat f) E.

Lemma fin2nat_fin2fin : forall m n (i : fin m) (E : fin2nat i < n),
    fin2nat (fin2fin m n i E) = fin2nat i.
Proof. intros. unfold fin2fin,fin2nat,nat2fin. auto. Qed.

Lemma fin2fin_fin2fin :
  forall m n (i : fin m) (E1 : fin2nat i < n) (E2 : fin2nat (fin2fin m n i E1) < m),
    fin2fin n m (fin2fin m n i E1) E2 = i.
Proof.
  intros. unfold fin2fin,fin2nat,nat2fin. destruct i. apply fin_eq_iff; auto.
Qed.

(** {i<n} + {k<n} -> (i+k<n) ? {i+k<n} : {0<n} *)
Definition fin2SameRangeAdd {n : nat} (i k:fin n) : fin (n).
  destruct (fin2nat i + fin2nat k ??< n)%nat as [E|E].
  - refine (nat2fin (fin2nat i + fin2nat k) E).
  - refine (nat2fin 0 _). destruct (n ??= 0)%nat.
    + subst; fin.
    + apply neq_0_lt_stt; auto.
Defined.

Lemma fin2nat_fin2SameRangeAdd : forall {n} (i k : fin n),
    fin2nat (fin2SameRangeAdd i k) =
      if (fin2nat i + fin2nat k ??< n)%nat then (fin2nat i + fin2nat k) else 0.
Proof. intros. unfold fin2SameRangeAdd. fin. Qed.

(** {i<n} - {k<n} -> {i-k<n} *)
Definition fin2SameRangeSub {n : nat} (i k:fin n) : fin (n).
  refine (nat2fin (fin2nat i - fin2nat k) _).
  pose proof (fin2nat_lt i). apply Nat.le_lt_trans with (fin2nat i).
  apply Nat.le_sub_l. auto.
Defined.

Lemma fin2nat_fin2SameRangeSub : forall {n} (i k : fin n),
    fin2nat (fin2SameRangeSub i k) = fin2nat i - fin2nat k.
Proof. intros. unfold fin2SameRangeSub. simpl. auto. Qed.

(** {i<n} -> (S i<n) ? {S i<n} : {i<n} *)
Definition fin2SameRangeSucc {n : nat} (i:fin n) : fin (n).
  destruct (S (fin2nat i) ??< n)%nat as [H|H].
  - refine (nat2fin (S (fin2nat i)) H).
  - apply i.
Defined.

Lemma fin2nat_fin2SameRangeSucc : forall {n} (i : fin n),
    fin2nat (fin2SameRangeSucc i) =
      if (S (fin2nat i) ??< n)%nat then S (fin2nat i) else fin2nat i.
Proof. intros. unfold fin2SameRangeSucc. fin. Qed.

(** {i<n} -> (0 < i) ? {pred i<n} : {i<n} *)
Definition fin2SameRangePred {n : nat} (i:fin n) : fin n.
  destruct (0 ??< fin2nat i)%nat.
  - refine (nat2fin (pred (fin2nat i)) _). apply Nat.lt_lt_pred. apply fin2nat_lt.
  - apply i.
Defined.

Lemma fin2nat_fin2SameRangePred : forall {n} (i : fin n),
    fin2nat (fin2SameRangePred i) =
      if (0 ??< fin2nat i)%nat then pred (fin2nat i) else fin2nat i.
Proof. intros. unfold fin2SameRangePred. fin. Qed.

(** Loop shift left : {i<n} << {k<n}. Eg: 0 1 2 =1=> 1 2 0  *)
Definition fin2SameRangeLSL {n : nat} (i k:fin n) : fin (n).
  destruct (n ??= 0)%nat.
  - subst; fin.
  - refine (nat2fin ((n + fin2nat i + fin2nat k) mod n) _).
    apply Nat.mod_upper_bound. auto.
Defined.

Lemma fin2nat_fin2SameRangeLSL : forall {n} (i k : fin n),
    fin2nat (fin2SameRangeLSL i k) = (n + fin2nat i + fin2nat k) mod n.
Proof. intros. unfold fin2SameRangeLSL. fin. Qed.

(** Loop shift right : {i<n} <-> {k<n}. Eg: 0 1 2 =1=> 2 0 1  *)
Definition fin2SameRangeLSR {n : nat} (i k:fin n) : fin (n).
  destruct (n ??= 0)%nat.
  - subst; fin.
  - refine (nat2fin ((n + fin2nat i - fin2nat k) mod n) _).
    apply Nat.mod_upper_bound. auto.
Defined.

Lemma fin2nat_fin2SameRangeLSR : forall {n} (i k : fin n),
    fin2nat (fin2SameRangeLSR i k) = (n + fin2nat i - fin2nat k) mod n.
Proof. intros. unfold fin2SameRangeLSR. fin. Qed.


(** {i < n} -> {n - i < n}  *)
Definition fin2SameRangeRemain {n} (i : fin n) (E : 0 < fin2nat i) : fin n.
  destruct (n ??= 0)%nat.
  - subst; fin.
  - refine (nat2fin (n - fin2nat i) _).
    apply nat_sub_lt; auto. apply neq_0_lt_stt; auto.
Defined.

Lemma fin2nat_fin2SameRangeRemain : forall {n} (i : fin n) (E : 0 < fin2nat i),
    fin2nat (fin2SameRangeRemain i E) = n - fin2nat i.
Proof. intros. unfold fin2SameRangeRemain. fin. Qed.


(** {i<n} -> {i<S n} *)
Definition fin2SuccRange {n} (i:fin n) : fin (S n).
  refine (nat2finS (fin2nat i)).
Defined.

Lemma fin2nat_fin2SuccRange : forall {n} (i:fin n),
    fin2nat (@fin2SuccRange n i) = fin2nat i.
Proof.
  intros. unfold fin2SuccRange. apply fin2nat_nat2finS.
  pose proof (fin2nat_lt i). lia.
Qed.

Lemma fin2SuccRange_nat2fin : forall {n} (i:nat) (E : i < n) (E0 : i < S n),
  fin2SuccRange (nat2fin i E) = nat2fin i E0.
Proof.
  intros. unfold fin2SuccRange, nat2finS. simpl. fin.
Qed.


(** {i<S n} -> {i<n} *)
Definition fin2PredRange {n} (i:fin (S n)) (H:fin2nat i < n) : fin n :=
  nat2fin (fin2nat i) H.

Lemma fin2nat_fin2PredRange : forall {n} (i:fin (S n)) (E : fin2nat i < n),
    fin2nat (@fin2PredRange n i E) = fin2nat i.
Proof. intros. unfold fin2PredRange. simpl. auto. Qed.

Lemma fin2SuccRange_fin2PredRange : forall {n} (i:fin (S n)) (E : fin2nat i < n),
    fin2SuccRange (fin2PredRange i E) = i.
Proof.
  intros. destruct i. unfold fin2SuccRange,fin2PredRange,nat2finS; simpl. fin.
Qed.

Lemma fin2PredRange_fin2SuccRange : forall {n} (i:fin n) (E: fin2nat (fin2SuccRange i) < n),
    fin2PredRange (fin2SuccRange i) E = i.
Proof.
  intros. destruct i as [i Hi].
  unfold fin2SuccRange,fin2PredRange,nat2finS in *; simpl in *. fin.
Qed.


(** {i < n} -> {i < m + n} *)
Definition fin2AddRangeL {m n} (i : fin n) : fin (m + n).
  refine (nat2fin (fin2nat i) _).
  apply Nat.lt_lt_add_l. fin.
Defined.

Lemma fin2nat_fin2AddRangeL : forall {m n} (i : fin n),
    fin2nat (@fin2AddRangeL m n i) = fin2nat i.
Proof. intros. auto. Qed.

(* {i < m + n} -> {i < m} *)
Definition fin2AddRangeL' {m n} (i : fin (m + n)) (E : fin2nat i < n) : fin n :=
  nat2fin (fin2nat i) E.

Lemma fin2nat_fin2AddRangeL' : forall {m n} (i:fin (m + n)) (E : fin2nat i < n),
    fin2nat (fin2AddRangeL' i E) = fin2nat i.
Proof. intros. auto. Qed.

Lemma fin2AddRangeL_fin2AddRangeL' : forall {m n} (i:fin (m+n)) (E : fin2nat i < n),
    fin2AddRangeL (fin2AddRangeL' i E) = i.
Proof.
  intros. unfold fin2AddRangeL, fin2AddRangeL'. simpl.
  destruct i as [i Hi]. apply fin_eq_iff; auto.
Qed.

(** {i < m} -> {i < m + n} *)
Definition fin2AddRangeR {m n} (i : fin m) : fin (m + n).
  refine (nat2fin (fin2nat i) _).
  apply Nat.lt_lt_add_r. apply fin2nat_lt.
Defined.

Lemma fin2nat_fin2AddRangeR : forall {m n} (i : fin m),
    fin2nat (@fin2AddRangeR m n i) = fin2nat i.
Proof. intros. auto. Qed.

(** {i < m + n} -> {i < m} *)
Definition fin2AddRangeR' {m n} (i : fin (m + n)) (E : fin2nat i < m) : fin m :=
  nat2fin (fin2nat i) E.

Lemma fin2nat_fin2AddRangeR' : forall {m n} (i:fin (m+n)) (E : fin2nat i < m),
    fin2nat (fin2AddRangeR' i E) = fin2nat i.
Proof. intros. auto. Qed.

Lemma fin2AddRangeR_fin2AddRangeR' : forall {m n} (i:fin (m+n)) (E : fin2nat i < m),
    fin2AddRangeR (fin2AddRangeR' i E) = i.
Proof.
  intros. unfold fin2AddRangeR, fin2AddRangeR'. simpl.
  destruct i as [i Hi]. apply fin_eq_iff; auto.
Qed.

Lemma fin2AddRangeR'_fin2AddRangeR : forall {m n} (i : fin m) (E : fin2nat i < m),
    @fin2AddRangeR' m n (fin2AddRangeR i) E = i.
Proof.
  intros. unfold fin2AddRangeR, fin2AddRangeR'. simpl.
  rewrite nat2fin_fin2nat. auto.
Qed.

(** {i < n} -> {m + i < m + n} *)
Definition fin2AddRangeAddL {m n} (i : fin n) : fin (m + n).
  refine (nat2fin (m + fin2nat i) _).
  apply Nat.add_lt_mono_l. apply fin2nat_lt.
Defined.

Lemma fin2nat_fin2AddRangeAddL : forall {m n} (i : fin n),
    fin2nat (@fin2AddRangeAddL m n i) = m + fin2nat i.
Proof. intros. auto. Qed.

(** {m + i < m + n} -> {i < n} *)
Definition fin2AddRangeAddL' {m n} (i : fin (m + n)) (E : m <= fin2nat i) : fin n.
  refine (nat2fin (fin2nat i - m) _).
  pose proof (fin2nat_lt i). apply le_ltAdd_imply_subLt_L; auto.
Defined.

Lemma fin2nat_fin2AddRangeAddL' : forall {m n} (i:fin (m + n)) (E : m <= fin2nat i),
    fin2nat (@fin2AddRangeAddL' m n i E) = fin2nat i - m.
Proof. intros. auto. Qed.

Lemma fin2AddRangeAddL_fin2AddRangeAddL' :
  forall {m n} (i : fin (m + n)) (E : m <= fin2nat i),
    fin2AddRangeAddL (fin2AddRangeAddL' i E) = i.
Proof.
  intros. unfold fin2AddRangeAddL, fin2AddRangeAddL'. simpl.
  destruct i as [i Hi]. simpl in *. apply fin_eq_iff; auto. lia.
Qed.

Lemma fin2AddRangeAddL'_fin2AddRangeAddL :
  forall {m n} (i : fin n) (E : m <= fin2nat (fin2AddRangeAddL i)),
    @fin2AddRangeAddL' m n (fin2AddRangeAddL i) E = i.
Proof.
  intros. unfold fin2AddRangeAddL, fin2AddRangeAddL'. simpl.
  destruct i as [i Ei]. simpl in *. apply fin_eq_iff; auto. lia.
Qed.
  
(** {i < m} -> {i + n < m + n} *)
Definition fin2AddRangeAddR {m n} (i : fin m) : fin (m + n).
  refine (nat2fin (fin2nat i + n) _).
  apply Nat.add_lt_mono_r. apply fin2nat_lt.
Defined.

Lemma fin2nat_fin2AddRangeAddR : forall {m n} (i : fin m),
    fin2nat (@fin2AddRangeAddR m n i) = fin2nat i + n.
Proof. intros. auto. Qed.
  
(** {i + n < m + n} -> {i < m} *)
Definition fin2AddRangeAddR' {m n} (i:fin (m + n)) (E : n <= fin2nat i) : fin m.
  refine (nat2fin (fin2nat i - n) _).
  pose proof (fin2nat_lt i). apply le_ltAdd_imply_subLt_R; auto.
Defined.

Lemma fin2nat_fin2AddRangeAddR' : forall {m n} (i : fin (m + n)) (E : n <= fin2nat i),
    fin2nat (@fin2AddRangeAddR' m n i E) = fin2nat i - n.
Proof. intros. auto. Qed.

Lemma fin2AddRangeAddR_fin2AddRangeAddR' :
  forall {m n} (i : fin (m + n)) (E : n <= fin2nat i),
    fin2AddRangeAddR (@fin2AddRangeAddR' m n i E) = i.
Proof.
  intros. unfold fin2AddRangeAddR, fin2AddRangeAddR'. simpl.
  destruct i as [i Hi]. simpl in *. apply fin_eq_iff; auto. lia.
Qed.

Lemma fin2AddRangeAddR'_fin2AddRangeAddR :
  forall {m n} (i : fin m) (E : n <= fin2nat (fin2AddRangeAddR i)),
    @fin2AddRangeAddR' m n (fin2AddRangeAddR i) E = i.
Proof.
  intros. unfold fin2AddRangeAddR, fin2AddRangeAddR'. simpl.
  destruct i as [i Hi]. simpl in *. apply fin_eq_iff; auto. lia.
Qed.

(** {S i < S n} -> {i < n} *)
Definition fin2PredRangePred {n} (i:fin (S n)) (E : 0 < fin2nat i) : fin n.
  refine (nat2fin (pred (fin2nat i)) _).
  destruct i; simpl in *. apply pred_lt; auto.
Defined.

Lemma fin2nat_fin2PredRangePred : forall {n} (i:fin (S n)) (E : 0 < fin2nat i),
    fin2nat (fin2PredRangePred i E) = pred (fin2nat i).
Proof. intros. unfold fin2PredRangePred. apply fin2nat_nat2fin. Qed.

(* {i < n} -> {S i < S n} *)
Definition fin2SuccRangeSucc {n} (i:fin n) : fin (S n).
  refine (nat2fin (S (fin2nat i)) _).
  rewrite <- Nat.succ_lt_mono. apply fin2nat_lt.
Defined.

Lemma fin2nat_fin2SuccRangeSucc : forall {n} (i:fin n),
    fin2nat (fin2SuccRangeSucc i) = S (fin2nat i).
Proof. intros. unfold fin2SuccRangeSucc. simpl. auto. Qed.

Lemma fin2SuccRangeSucc_fin2PredRangePred : forall {n} (i:fin (S n)) (E : 0 < fin2nat i),
    fin2SuccRangeSucc (fin2PredRangePred i E) = i.
Proof.
  intros. destruct i. cbv. cbv in E. destruct i; try lia. apply fin_eq_iff; auto.
Qed.

Lemma fin2PredRangePred_fin2SuccRangeSucc :
  forall {n} (i : fin n) (E : 0 < fin2nat (fin2SuccRangeSucc i)),
    fin2PredRangePred (fin2SuccRangeSucc i) E = i.
Proof.
  intros. destruct i as [i Hi]. cbv. apply fin_eq_iff; auto.
Qed.

Lemma fin2nat_fin2SuccRangeSucc_gt0 : forall {n} (i : fin n),
    0 < fin2nat (fin2SuccRangeSucc i).
Proof. intros. unfold fin2SuccRangeSucc. simpl. lia. Qed.


(** ** Properties of Fin-index-Fun (ff) *)
Section ff.
  Context {A} {Azero : A}.

  Lemma ffeq_iff_nth : forall {n} (ff1 ff2 : fin n -> A),
      ff1 = ff2 <-> forall i, ff1 i = ff2 i.
  Proof.
    intros. split; intros; subst; auto. extensionality i. auto.
  Qed.

  Lemma ffeq_iff_nth_nat : forall {n} (ff1 ff2 : fin n -> A),
      ff1 = ff2 <-> forall i (E : i < n), ff1 (nat2fin i E) = ff2 (nat2fin i E).
  Proof.
    intros. split; intros; subst; auto. extensionality i.
    specialize (H (fin2nat i) (fin2nat_lt _)).
    rewrite nat2fin_fin2nat in H. auto.
  Qed.

End ff.


(** ** Conversion between nat-index-Fun (f) and Fin-index-Fun (ff) *)
Section ff2f_f2ff.
  Context {A} {Azero : A}.

  (** `ff` to `f` *)
  Definition ff2f {n} (ff : fin n -> A) : nat -> A.
    intros i. destruct (i ??< n)%nat as [E|E].
    - apply (ff (nat2fin i E)).
    - apply Azero.
  Defined.

  Lemma nth_ff2f : forall {n} (ff : fin n -> A) i (E : i < n),
      (ff2f ff) i = ff (nat2fin i E).
  Proof. intros. unfold ff2f. fin. Qed.
  
  (** ff [|i] = ff2f ff i *)
  Lemma nth_ff_eq_nth_f : forall {n} (ff : fin n -> A) (i : nat) (E : i < n),
      ff (Fin i E) = ff2f ff i.
  Proof. intros. rewrite nth_ff2f with (E:=E). f_equal. Qed.


  (* (ff2f f)[fin2nat i] = f[i] *)
  Lemma ff2f_fin2nat : forall {n} (f : fin n -> A) (i : fin n),
      ff2f f (fin2nat i) = f i.
  Proof.
    intros. unfold ff2f. unfold fin2nat. destruct i; simpl. fin.
  Qed.


  (** `f` to `ff` *)
  Definition f2ff {n} (f : nat -> A) : fin n -> A := fun fi => f (fin2nat fi).
  
  Lemma nth_f2ff : forall {n} (f : nat -> A) (i : fin n),
      (@f2ff n f) i = f (fin2nat i).
  Proof. intros. unfold f2ff. auto. Qed.

  (* Note that, equality of two nat-indexing-fun is defined on top n elements *)
  Lemma ff2f_f2ff : forall {n} (f : nat -> A) i, i < n -> @ff2f n (f2ff f) i = f i.
  Proof.
    intros. unfold f2ff,ff2f. fin.
  Qed.

  Lemma f2ff_ff2f : forall {n} (ff : fin n -> A), f2ff (ff2f ff) = ff.
  Proof.
    intros. unfold f2ff,ff2f. extensionality i. fin.
    rewrite nat2fin_fin2nat; auto. pose proof (fin2nat_lt i). lia.
  Qed.

  (** `ff` to `ff` *)
  Definition ff2ff m n (ff : fin m -> A) : fin n -> A := f2ff (ff2f ff).
  
  Lemma nth_ff2ff : forall {m n} (ff : fin m -> A) (i : fin n) (E : fin2nat i < m),
      (ff2ff m n ff) i = ff (fin2fin _ _ i E).
  Proof.
    intros. unfold ff2ff, f2ff, ff2f, fin2fin, fin2nat, nat2fin.
    destruct i; simpl in *. fin.
  Qed.

  Lemma ff2ff_inj : forall {m n} (ff1 ff2 : fin m -> A),
      m <= n -> @ff2ff m n ff1 = @ff2ff m n ff2 -> ff1 = ff2.
  Proof.
    intros. rewrite ffeq_iff_nth in H0. rewrite ffeq_iff_nth. intros.
    assert (fin2nat i < n). { pose proof (fin2nat_lt i). lia. }
    specialize (H0 (fin2fin _ _ i H1)).
    erewrite !nth_ff2ff in H0. rewrite !fin2fin_fin2fin in H0. auto.
    Unshelve.
    - rewrite fin2nat_fin2fin. apply fin2nat_lt.
    - rewrite fin2nat_fin2fin. apply fin2nat_lt.
  Qed.

  (* `ff` of (S n) to `ff` of n *)
  Definition ffS2ff {n} (ff : fin (S n) -> A) : fin n -> A :=
    fun i => ff (nat2finS (fin2nat i)).

End ff2f_f2ff.

Infix "!" := (ff2f) : fin_scope.


(** Convert `nth of ff` to `nth of nat-fun` *)
Ltac ff2f Azero :=
  repeat
    match goal with
    | [ H : context[?ff (Fin ?i ?Hi)] |- _ ] =>
        rewrite (@nth_ff_eq_nth_f _ Azero _ ff i) in H
    | [ |- context [ ?ff (Fin ?i ?Hi) ]] =>
        rewrite (@nth_ff_eq_nth_f _ Azero _ ff i)
    end.

Section test.

  Notation "ff $ i" := (ff (nat2finS i)).
  (* This example shows how to convert `ff` to `f` *)
  Example ex_ff2f : forall (ff: fin 10 -> nat),
      ff$0 + ff$1 + ff$2 = ff$2 + ff$0 + ff$1.
  Proof. intros. cbn. ff2f 0. lia. Qed.
  
End test.


(** ** Sequence of fin *)
Section finseq.

  Definition finseq (n : nat) : list (fin n) :=
    match n with
    | O => []
    | _ => map nat2finS (seq 0 n)
    end.

  Lemma finseq_length : forall n, length (finseq n) = n.
  Proof. destruct n; simpl; auto. rewrite map_length, seq_length. auto. Qed.
    
  Lemma finseq_eq_seq : forall n, map fin2nat (finseq n) = seq 0 n.
  Proof.
    destruct n; simpl; auto. f_equal.
    rewrite map_map. apply map_id_In. intros. rewrite fin2nat_nat2finS; auto.
    apply in_seq in H. lia.
  Qed.

  Lemma nth_finseq : forall (n : nat) i (E : i < n) i0,
      nth i (finseq n) i0 = Fin i E.
  Proof.
    intros. destruct n. lia. simpl. destruct i; simpl.
    - apply nat2finS_eq.
    - rewrite nth_map_seq; try lia.
      replace (i + 1) with (S i) by lia. apply nat2finS_eq.
  Qed.

  Lemma nth_map_finseq : forall {A} (n : nat) (f : fin n -> A) i (E : i < n) (a : A),
      nth i (map f (finseq n)) a = f (Fin i E).
  Proof.
    intros. rewrite nth_map with (n:=n)(Azero:=Fin i E); auto.
    rewrite nth_finseq with (E:=E). auto.
    rewrite finseq_length; auto.
  Qed.

  (* {i<n} ∈ (finseq n) *)
  Lemma In_finseq : forall {n} (i : fin n), In i (finseq n).
  Proof.
    intros. unfold finseq. destruct n. exfalso. apply fin0_False; auto.
    apply in_map_iff. exists (fin2nat i). split.
    - apply nat2finS_fin2nat.
    - apply in_seq. pose proof (fin2nat_lt i). lia.
  Qed.
  
End finseq.


(** ** Sequence of fin with bounds *)
Section finseqb.

  (* A list of `fin (S n)` which its value is from `lo` to `lo + cnt -1` *)
  Definition finseqb (n : nat) (lo cnt : nat) : list (fin (S n)) :=
    map nat2finS (seq lo cnt).

  Lemma finseqb_length : forall n lo cnt, length (finseqb n lo cnt) = cnt.
  Proof. intros. unfold finseqb. rewrite map_length, seq_length. auto. Qed.

  Lemma finseqb_eq_seq : forall n lo cnt,
      lo + cnt <= S n -> map fin2nat (finseqb n lo cnt) = seq lo cnt.
  Proof.
    intros. unfold finseqb. rewrite map_map. apply map_id_In. intros.
    rewrite fin2nat_nat2finS; auto. apply in_seq in H0. lia.
  Qed.

  (* Lemma nth_finseqb : forall (n lo cnt : nat) i (H: i < n), *)
  (*     nth i (finseqb n lo cnt) fin0 = (Fin i H : fin n). *)
  (* Proof. *)
  (*   intros. destruct n. lia. simpl. destruct i; simpl. *)
  (*   - apply nat2finS_eq. *)
  (*   - rewrite nth_map_seq; try lia. *)
  (*     replace (i + 1) with (S i) by lia. apply nat2finS_eq. *)
  (* Qed. *)

  (* Lemma nth_map_finseqb : forall {A} (n : nat) (f : fin n -> A) i (H: i < n) (a : A), *)
  (*     nth i (map f (finseqb n)) a = f (Fin i H). *)
  (* Proof. *)
  (*   intros. rewrite nth_map with (n:=n)(Azero:=Fin i H:fin n); auto. *)
  (*   rewrite nth_finseqb with (H:=H). auto. *)
  (*   rewrite finseqb_length; auto. *)
  (* Qed. *)

  (* (* {i<n} ∈ (finseqb n) *) *)
  (* Lemma In_finseqb : forall {n} (i : fin n), In i (finseqb n). *)
  (* Proof. *)
  (*   intros. unfold finseqb. destruct n. exfalso. apply fin0_False; auto. *)
  (*   apply in_map_iff. exists (fin2nat i). split. *)
  (*   - apply nat2finS_fin2nat. *)
  (*   - apply in_seq. pose proof (fin2nat_lt i). lia. *)
  (* Qed. *)
  
End finseqb.


(** ** Sum of a Fin-indexing-Fun (FF) *)
Section ffsum.
  Context `{M : Monoid}.

  Definition ffsum {n} (ff : fin n -> A) : A :=
    fold_right Aadd Azero (map ff (finseq n)).

End ffsum.


(** ** Convert between list and Fin-indexing-fun (ff) *)
Section ff2l_l2ff.
  Context {A} {Azero : A}.
  
  (** [list] to `ff` *)
  Definition l2ff (n : nat) (l : list A) : fin n -> A :=
    fun f => nth (fin2nat f) l Azero.

  Lemma nth_l2ff : forall {n} (l : list A) i, (l2ff n l) i = nth (fin2nat i) l Azero.
  Proof. intros. unfold l2ff. auto. Qed.
  
  Lemma l2ff_inj : forall {n} (l1 l2 : list A),
      length l1 = n -> length l2 = n ->
      l2ff n l1 = l2ff n l2 -> l1 = l2.
  Proof.
    intros. unfold l2ff in H1.
    rewrite ffeq_iff_nth_nat in H1.
    rewrite (list_eq_iff_nth Azero n); auto.
  Qed.


  (** `ff` to [list] *)
  Definition ff2l {n} (ff : fin n -> A) : list A := map ff (finseq n).

  Lemma ff2l_length : forall n f, length (@ff2l n f) = n.
  Proof.
    intros. unfold ff2l.
    rewrite map_length, finseq_length; auto.
  Qed.

  (** (ff2l f)[i] = f i *)
  Lemma nth_ff2l {n} f a i (E : i < n) : nth i (@ff2l n f) a = f (Fin i E).
  Proof.
    intros. unfold ff2l. erewrite nth_map_finseq; auto.
  Qed.

  Lemma ff2l_inj : forall {n} (f g : fin n -> A), ff2l f = ff2l g -> f = g.
  Proof.
    intros. apply ffeq_iff_nth_nat; intros.
    unfold ff2l in H. rewrite map_ext_in_iff in H. apply H. apply In_finseq.
  Qed.

  Lemma ff2l_l2ff : forall l {n}, length l = n -> @ff2l n (@l2ff n l) = l.
  Proof.
    intros. rewrite (list_eq_iff_nth Azero n); auto.
    - intros. rewrite (nth_ff2l _ _ _ H0); auto.
    - apply ff2l_length.
  Qed.

  Lemma l2ff_ff2l : forall {n} f, @l2ff n (@ff2l n f) = f.
  Proof.
    intros. unfold l2ff,ff2l.
    apply functional_extensionality. intros.
    rewrite nth_map_finseq with (E:=fin2nat_lt _). f_equal.
    destruct x. simpl. f_equal. apply proof_irrelevance.
  Qed.

  Lemma l2ff_surj : forall {n} (ff : fin n -> A), (exists l, l2ff n l = ff).
  Proof.
    intros. unfold l2ff. exists (ff2l ff). apply ffeq_iff_nth; intros.
    rewrite nth_ff2l with (E:=fin2nat_lt _). f_equal. apply fin_fin2nat.
  Qed.

  Lemma ff2l_surj : forall {n} (l : list A),
      length l = n -> exists f : fin n -> A, ff2l f = l.
  Proof. intros. exists (l2ff n l). apply ff2l_l2ff; auto. Qed.
  
End ff2l_l2ff.

Section test.
  (* [1;2;3] *)
  Let f := fun (f:fin 3) => fin2nat f + 1.
  (* Compute (ff2l f). *)
  (* Compute (l2ff 3 [1;2;3]). *)
  
  Goal @l2ff _ 0 3 [1;2;3] = f.
  Proof.
    apply functional_extensionality. intros.
    unfold l2ff. simpl. unfold f. simpl.
    destruct x; simpl; auto.
    repeat (destruct i; simpl; auto; try lia).
  Qed.
  
End test.  
