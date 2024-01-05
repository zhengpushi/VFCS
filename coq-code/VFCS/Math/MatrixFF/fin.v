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
Require Export NatExt.
Require Export ListExt.
Require Import Extraction.

Ltac inv H := inversion H; subst; clear H.

Lemma lt_imply_gt : forall n m : nat, n < m -> m > n.
Proof. intros. lia. Qed.

Lemma gt_imply_lt : forall n m : nat, n > m -> m < n.
Proof. intros. lia. Qed.

Lemma lt_ge_dec : forall x y : nat, {x < y} + {x >= y}.
Proof. intros. destruct (le_gt_dec y x); auto. Defined.

Infix "??<" := (lt_ge_dec) (at level 70).
Infix "??=" := (Nat.eq_dec) (at level 70).


#[export] Hint Rewrite
  map_length
  seq_length
  : fin.


(** ** Type of fin *)

Notation "[ | i ]" := (exist _ i _) (format "[ | i ]").

(** Definition of fin type *)
Definition fin (n : nat) := {i | i < n}.

Lemma fin_eq_iff : forall {n} x1 x2 (H1 : x1 < n) (H2 : x2 < n),
    (exist _ x1 H1 : fin n) = (exist _ x2 H2 : fin n) <-> x1 = x2.
Proof.
  intros. split; intros.
  - inversion H. auto.
  - subst. f_equal. apply proof_irrelevance.
Qed.

 (* [|proj1_sig i] = i *)
Lemma fin_proj1_eq : forall {n} (i : fin n) (H : proj1_sig i < n),
    exist _ (proj1_sig i) H = i.
Proof. intros. destruct i; simpl. apply fin_eq_iff; auto. Qed.

(* proj1_sig ([|i]) = i *)
Lemma proj1_fin_eq : forall {n} i (H : i < n), proj1_sig (exist _ i H : fin n) = i.
Proof. intros. simpl. auto. Qed.

(** Equality of `fin` is decidable *)
Definition finEqdec : forall {n} (i j : fin n), {i = j} + {i <> j}.
Proof.
  intros. destruct i as [i Hi], j as [j Hj]. destruct (i??=j).
  - subst. left. f_equal. apply proof_irrelevance.
  - right. intro. inversion H. easy.
Defined.


(** A default entry of `fin` *)
Definition fin0 {n : nat} : fin (S n) := exist _ 0 (Nat.lt_0_succ _).

Lemma fin0_False : fin 0 -> False.
Proof. intros. inversion H. lia. Qed.


(** ** [fin] to [nat] *)

(** Convert from [fin] to [nat] *)
Definition fin2nat {n} (f : fin n) := proj1_sig f.

Lemma fin2nat_inj : forall {n} (f1 f2 : fin n), fin2nat f1 = fin2nat f2 -> f1 = f2.
Proof. intros. destruct f1,f2; simpl in H. apply fin_eq_iff; auto. Qed.

Lemma fin2nat_lt : forall {n} (f : fin n), fin2nat f < n.
Proof. intros. destruct f; simpl. auto. Qed.

Lemma fin2nat_lt_Sn : forall {n} (f : fin n), fin2nat f < S n.
Proof. intros. pose proof (fin2nat_lt f). auto. Qed.

Lemma fin_fin2nat : forall {n} (i : fin n) (H : fin2nat i < n),
    exist _ (fin2nat i) H = i.
Proof. intros. destruct i; simpl. apply fin_eq_iff; auto. Qed.

(* i <> fin0 -> 0 < fin2nat i *)
Lemma fin2nat_gt0_iff_neq0 : forall {n} (i : fin (S n)), 0 < fin2nat i <-> i <> fin0.
Proof.
  intros. unfold fin2nat,fin0 in *. destruct i. simpl in *.
  rewrite fin_eq_iff. lia.
Qed.


(** ** [nat] to [fin (S n)] *)

(** Convert from nat to fin (S n). If `i >= S n` then {0} *)
Definition nat2finS {n} (i : nat) : fin (S n).
  destruct (i ??< S n).
  - refine (exist _ i l).
  - refine fin0.
Defined.

Lemma nat2finS_eq : forall n i (H : i < S n), nat2finS i = exist _ i H.
Proof.
  intros. unfold nat2finS. destruct (_??<_); auto.
  apply fin_eq_iff; auto. lia.
Qed.

Lemma nat2finS_fin2nat_id : forall n i, nat2finS (@fin2nat (S n) i) = i.
Proof.
  intros. unfold fin2nat, nat2finS. destruct i; simpl.
  destruct (_??<_). apply fin_eq_iff; auto. lia.
Qed.

Lemma fin2nat_nat2finS_id : forall n i, i < (S n) -> fin2nat (@nat2finS n i) = i.
Proof.
  intros. unfold fin2nat, nat2finS. destruct (_??<_); simpl; auto. lia.
Qed.

(** ** [nat] to [fin n] (option version) *)

(** Convert from [nat] to [fin] *)
Definition nat2finOpt {n} (i : nat) : option (fin n).
  destruct (i ??< n).
  - refine (Some (exist _ i _)). auto.
  - exact None.
Defined.

Lemma nat2finOpt_overflow : forall n i, i >= n -> @nat2finOpt n i = None.
Proof.
  intros. unfold nat2finOpt. destruct (_??<_); auto. lia.
Qed.

Lemma nat2finOpt_Some n i (H: i < n) : @nat2finOpt n i = Some (exist _ i H).
Proof.
  intros. unfold nat2finOpt. destruct (_??<_); auto.
  f_equal. apply fin_eq_iff; auto. lia.
Qed.

Lemma nat2finOpt_None_imply_nat2finOptS : forall n i,
    @nat2finOpt (S n) i = None -> @nat2finS n i = fin0.
Proof.
  intros. unfold nat2finOpt, nat2finS in *. destruct (_??<_); auto. easy.
Qed.

Lemma nat2finOpt_Some_imply_nat2finOptS : forall n i f,
    @nat2finOpt (S n) i = Some f -> @nat2finS n i = f.
Proof.
  intros. unfold nat2finOpt, nat2finS in *. destruct (_??<_); auto.
  inversion H; auto. easy.
Qed.

Lemma nat2finOpt_fin2nat_id : forall n (f : fin n), nat2finOpt (fin2nat f) = Some f.
Proof.
  intros. unfold nat2finOpt,fin2nat. destruct f; simpl. destruct (_??<_); auto.
  f_equal; apply fin_eq_iff; auto. lia.
Qed.

Lemma fin2nat_nat2finOpt_id : forall n i,
    i < n -> exists f, @nat2finOpt n i = Some f /\ fin2nat f = i.
Proof.
  intros. unfold nat2finOpt, fin2nat. destruct (_??<_).
  exists (exist _ i l). split; auto. lia.
Qed.


(** ** [nat] to [fin n] (condition version) *)

(** Convert from [nat] to [fin] *)
Definition nat2fin {n} (i : nat) (H : i < n) : fin n := exist _ i H.

Lemma nat2finOpt_eq_nat2fin : forall {n} i (H : i < n),
    nat2finOpt i = Some (nat2fin i H).
Proof.
  intros. unfold nat2fin, nat2finOpt. destruct (_??<_); auto.
  f_equal; apply fin_eq_iff; auto. lia.
Qed.

Lemma nat2fin_fin2nat_id : forall n (f : fin n) (H: fin2nat f < n),
    nat2fin (fin2nat f) H = f.
Proof.
  intros. unfold nat2fin,fin2nat. apply fin_proj1_eq.
Qed.

Lemma fin2nat_nat2fin_id : forall n i (H: i < n), (fin2nat (nat2fin i H)) = i.
Proof.
  intros. unfold nat2fin, fin2nat. apply proj1_fin_eq.
Qed.


(** ** [fin n] to [fin m] *)

(** Convert from [fin n] to [fin m] (option version) *)
Definition fin2finOpt n m (f : fin n) : option (fin m).
  destruct f as [i p].
  destruct (i ??< m).
  - refine (Some (exist _ i _)). auto.
  - exact None.
Defined.

Lemma fin2finOpt_Some : forall n m (f : fin n),
    n <= m -> @fin2finOpt n m f = nat2finOpt (fin2nat f).
Proof.
  intros. unfold fin2finOpt, nat2finOpt, fin2nat. destruct f; simpl.
  destruct (_??<_); auto.
Qed.

(** Convert from [fin n] to [fin m] *)
Definition fin2fin n m (f : fin n) (H : fin2nat f < m) : fin m :=
  nat2fin (fin2nat f) H.

Lemma fin2nat_fin2fin : forall n m (i : fin n) (H : fin2nat i < m),
    fin2nat (fin2fin n m i H) = fin2nat i.
Proof. intros. unfold fin2fin,fin2nat,nat2fin. auto. Qed.

Lemma fin2fin_fin2fin :
  forall n m (i : fin n) (H1 : fin2nat i < m) (H2 : fin2nat (fin2fin n m i H1) < n),
    fin2fin m n (fin2fin n m i H1) H2 = i.
Proof.
  intros. unfold fin2fin,fin2nat,nat2fin. simpl. apply fin_proj1_eq.
Qed.

(* {i<m} -> {i<n+m} *)
Definition fin2ExtendL {m n} (i:fin m) : fin (n+m).
  refine (nat2fin (fin2nat i) _).
  apply Nat.lt_lt_add_l. apply fin2nat_lt.
Defined.

Lemma fin2ExtendL_spec : forall {m n} (i:fin m),
    fin2nat (@fin2ExtendL m n i) = fin2nat i.
Proof. intros. unfold fin2ExtendL. rewrite fin2nat_nat2fin_id. auto. Qed.

(* {i<m} -> {i<m+n} *)
Definition fin2ExtendR {m n} (i:fin m) : fin (m+n).
  refine (nat2fin (fin2nat i) _).
  apply Nat.lt_lt_add_r. apply fin2nat_lt.
Defined.

Lemma fin2ExtendR_spec : forall {m n} (i:fin m),
    fin2nat (@fin2ExtendR m n i) = fin2nat i.
Proof. intros. unfold fin2ExtendR. rewrite fin2nat_nat2fin_id. auto. Qed.

(* {i<m} -> {i<S m} *)
Definition fin2ExtendSucc {m} (i:fin m) : fin (S m).
  refine (nat2finS (fin2nat i)).
Defined.

Lemma fin2ExtendSucc_spec : forall {m} (i:fin m),
    fin2nat (@fin2ExtendSucc m i) = fin2nat i.
Proof.
  intros. unfold fin2ExtendSucc. apply fin2nat_nat2finS_id.
  pose proof (fin2nat_lt i). lia.
Qed.

(* {i<S m} -> {i<m} *)
Definition fin2ExtendPred {m} (i:fin (S m)) (H:fin2nat i < m) : fin m :=
  nat2fin (fin2nat i) H.

Lemma fin2ExtendPred_spec : forall {m} (i:fin (S m)) (H:fin2nat i < m),
    fin2nat (@fin2ExtendPred m i H) = fin2nat i.
Proof. intros. unfold fin2ExtendPred. apply fin2nat_nat2fin_id. Qed.

(* {i<m} -> {n+i<n+m} *)
Definition fin2PlusL {m n} (i:fin m) : fin (n+m).
  refine (nat2fin (n + fin2nat i)%nat _).
  apply (Plus.plus_lt_compat_l_stt). apply fin2nat_lt.
Defined.

Lemma fin2PlusL_spec : forall {m n} (i:fin m),
    fin2nat (@fin2PlusL m n i) = n + fin2nat i.
Proof. intros. unfold fin2PlusL. apply fin2nat_nat2fin_id. Qed.
  
(* {i<m} -> {i+n<m+n} *)
Definition fin2PlusR {m n} (i:fin m) : fin (m+n).
  refine (nat2fin (fin2nat i + n)%nat _).
  apply (Plus.plus_lt_compat_r_stt). apply fin2nat_lt.
Defined.

Lemma fin2PlusR_spec : forall {m n} (i:fin m),
    fin2nat (@fin2PlusR m n i) = fin2nat i + n.
Proof. intros. unfold fin2PlusR. apply fin2nat_nat2fin_id. Qed.
  
(* {S i<S m} -> {i<m} *)
Definition fin2Pred {m} (i:fin (S m)) (H:0 < fin2nat i) : fin m.
  refine (nat2fin (pred (fin2nat i)) _).
  destruct i; simpl in *. apply pred_lt; auto.
Defined.

Lemma fin2Pred_spec : forall {m} (i:fin (S m)) (H:0 < fin2nat i),
    fin2nat (fin2Pred i H) = pred (fin2nat i).
Proof. intros. unfold fin2Pred. apply fin2nat_nat2fin_id. Qed.


(** ** Properties of Fin-index-Fun (ff) *)
Section ff.
  Context {A} {Azero : A}.

  Lemma ffeq_iff_nth : forall {n} (ff1 ff2 : fin n -> A),
      ff1 = ff2 <-> forall i, ff1 i = ff2 i.
  Proof.
    intros. split; intros; subst; auto. extensionality i. auto.
  Qed.

  Lemma ffeq_iff_nth_nat : forall {n} (ff1 ff2 : fin n -> A),
      ff1 = ff2 <-> forall i (H: i < n), ff1 (nat2fin i H) = ff2 (nat2fin i H).
  Proof.
    intros. split; intros; subst; auto. extensionality i.
    specialize (H (fin2nat i) (fin2nat_lt _)).
    rewrite nat2fin_fin2nat_id in H. auto.
  Qed.

End ff.

(** ** Conversion between nat-index-Fun (f) and Fin-index-Fun (ff) *)
Section ff2f_f2ff.
  Context {A} {Azero : A}.

  (** `ff` to `f` *)
  Definition ff2f {n} (ff : fin n -> A) : nat -> A :=
    fun i => match (i ??< n) with
           | left H => ff (nat2fin i H)
           | _ => Azero
           end.

  Lemma nth_ff2f : forall {n} (ff : fin n -> A) i (H : i < n),
      (ff2f ff) i = ff (nat2fin i H).
  Proof.
    intros. unfold ff2f. unfold nat2fin. destruct (_??<_).
    f_equal. apply fin_eq_iff; auto. lia.
  Qed.

  (* (ff2f f)[fin2nat i] = f[i] *)
  Lemma ff2f_fin2nat : forall {n} (f : fin n -> A) (i : fin n),
      ff2f f (fin2nat i) = f i.
  Proof.
    intros. unfold ff2f. unfold fin2nat. destruct i; simpl. destruct (_??<_).
    f_equal. apply fin_eq_iff; auto. lia.
  Qed.

  (** `f` to `ff` *)
  Definition f2ff {n} (f : nat -> A) : fin n -> A := fun fi => f (fin2nat fi).
  
  Lemma nth_f2ff : forall {n} (f : nat -> A) (i : fin n),
      (@f2ff n f) i = f (fin2nat i).
  Proof. intros. unfold f2ff. auto. Qed.

  (* Note that, equality of two nat-indexing-fun is defined on top n elements *)
  Lemma ff2f_f2ff_id : forall {n} (f : nat -> A) i, i < n -> @ff2f n (f2ff f) i = f i.
  Proof.
    intros. unfold f2ff,ff2f. destruct (_??<_); auto. lia.
  Qed.

  Lemma f2ff_ff2f_id : forall {n} (ff : fin n -> A), f2ff (ff2f ff) = ff.
  Proof.
    intros. unfold f2ff,ff2f. extensionality i. destruct (_??<_).
    rewrite nat2fin_fin2nat_id; auto. pose proof (fin2nat_lt i). lia.
  Qed.

  (** `ff` to `ff` *)
  Definition ff2ff n m (ff : fin n -> A) : fin m -> A := f2ff (ff2f ff).
  
  Lemma nth_ff2ff : forall {n m} (ff : fin n -> A) (i : fin m) (H : fin2nat i < n),
      (ff2ff n m ff) i = ff (fin2fin _ _ i H).
  Proof.
    intros. unfold ff2ff, f2ff, ff2f, fin2fin, fin2nat, nat2fin, nat2finOpt.
    destruct i; simpl in *. destruct (_??<_).
    f_equal. apply fin_eq_iff; auto. lia.
  Qed.

  Lemma ff2ff_inj : forall {n m} (ff1 ff2 : fin n -> A),
      n <= m -> @ff2ff n m ff1 = @ff2ff n m ff2 -> ff1 = ff2.
  Proof.
    intros. rewrite ffeq_iff_nth in H0. rewrite ffeq_iff_nth. intros.
    assert (fin2nat i < m). { pose proof (fin2nat_lt i). lia. }
    specialize (H0 (fin2fin _ _ i H1)).
    erewrite !nth_ff2ff in H0. rewrite !fin2fin_fin2fin in H0. auto.
    Unshelve.
    - rewrite fin2nat_fin2fin. apply fin2nat_lt.
    - rewrite fin2nat_fin2fin. apply fin2nat_lt.
  Qed.

End ff2f_f2ff.


(** ** Sequence of fin *)
Section finseq.

  Definition finseq (n : nat) : list (fin n) :=
    match n with
    | O => []
    | _ => map nat2finS (seq 0 n)
    end.

  Lemma finseq_length : forall n, length (finseq n) = n.
  Proof.
    destruct n; simpl; auto. autorewrite with fin; auto.
  Qed.
    
  Lemma finseq_eq_seq : forall n, map fin2nat (finseq n) = seq 0 n.
  Proof.
    destruct n; simpl; auto. f_equal.
    rewrite map_map. apply map_id_In. intros.
    rewrite fin2nat_nat2finS_id; auto. apply in_seq in H. lia.
  Qed.

  Lemma nth_finseq : forall (n : nat) i (H: i < n) i0,
      nth i (finseq n) i0 = (exist _ i H : fin n).
  Proof.
    intros. destruct n. lia. simpl. destruct i; simpl.
    - apply nat2finS_eq.
    - rewrite nth_map_seq; try lia.
      replace (i + 1) with (S i) by lia. apply nat2finS_eq.
  Qed.

  Lemma nth_map_finseq : forall {A} (n : nat) (f : fin n -> A) i (H: i < n) (a : A),
      nth i (map f (finseq n)) a = f (exist _ i H).
  Proof.
    intros. rewrite nth_map with (n:=n)(Azero:=exist _ i H:fin n); auto.
    rewrite nth_finseq with (H:=H). auto.
    rewrite finseq_length; auto.
  Qed.

  (* {i<n} ∈ (finseq n) *)
  Lemma In_finseq : forall {n} (i : fin n), In i (finseq n).
  Proof.
    intros. unfold finseq. destruct n. exfalso. apply fin0_False; auto.
    apply in_map_iff. exists (fin2nat i). split.
    - apply nat2finS_fin2nat_id.
    - apply in_seq. pose proof (fin2nat_lt i). lia.
  Qed.
  
End finseq.


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
  Lemma nth_ff2l {n} f a i (H: i < n) : nth i (@ff2l n f) a = f (exist _ i H).
  Proof.
    intros. unfold ff2l. erewrite nth_map_finseq; auto.
  Qed.

  Lemma ff2l_inj : forall {n} (f g : fin n -> A), ff2l f = ff2l g -> f = g.
  Proof.
    intros. apply ffeq_iff_nth_nat; intros.
    unfold ff2l in H. rewrite map_ext_in_iff in H. apply H. apply In_finseq.
  Qed.

  Lemma ff2l_l2ff_id : forall l {n}, length l = n -> @ff2l n (@l2ff n l) = l.
  Proof.
    intros. rewrite (list_eq_iff_nth Azero n); auto.
    - intros. rewrite (nth_ff2l _ _ _ H0); auto.
    - apply ff2l_length.
  Qed.

  Lemma l2ff_ff2l_id : forall {n} f, @l2ff n (@ff2l n f) = f.
  Proof.
    intros. unfold l2ff,ff2l.
    apply functional_extensionality. intros.
    rewrite nth_map_finseq with (H:=fin2nat_lt _). f_equal.
    destruct x. simpl. f_equal. apply proof_irrelevance.
  Qed.

  Lemma l2ff_surj : forall {n} (ff : fin n -> A), (exists l, l2ff n l = ff).
  Proof.
    intros. unfold l2ff. exists (ff2l ff). apply ffeq_iff_nth; intros.
    rewrite nth_ff2l with (H:=fin2nat_lt _). f_equal. apply fin_fin2nat.
  Qed.

  Lemma ff2l_surj : forall {n} (l : list A),
      length l = n -> exists f : fin n -> A, ff2l f = l.
  Proof. intros. exists (l2ff n l). apply ff2l_l2ff_id; auto. Qed.
  
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
    destruct x; simpl; auto.
    destruct x; simpl; auto.
    destruct x; simpl; auto. lia.
  Qed.
End test.  
