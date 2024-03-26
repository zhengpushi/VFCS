(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Gauss elimination of matrix
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
 *)

Require Import NatExt.
Require Import Hierarchy.
Require Import Matrix.
Require Import MyExtrOCamlR.
Require Import Utils.           (* LDict *)
Require QcExt RExt.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * 补充性质 *)


(* ======================================================================= *)
(** ** 未分类的 *)

(* ab = (a, b) -> a = fst ab *)
Lemma pair_eq_imply_fst : forall {A B} {ab} {a : A} {b : B}, ab = (a, b) -> a = fst ab.
Proof. intros. subst. auto. Qed.

(* ab = (a, b) -> b = snd ab *)
Lemma pair_eq_imply_snd : forall {A B} {ab} {a : A} {b : B}, ab = (a, b) -> b = snd ab.
Proof. intros. subst. auto. Qed.


(* ############################################################################ *)
(** * Gauss elimination. *)
Section GaussElim.
  Context `{HField : Field} `{HAeqDec : Dec _ (@eq A)}.
  Add Field field_inst : (make_field_theory HField).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun a b => a * / b) : A_scope.
  Notation Aeqb := (@Acmpb _ (@eq A) _).
  
  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.
  Notation matRowSwap := (@matRowSwap _ 0 1 _).
  Notation matRowScale := (@matRowScale _ 0 1 _).
  Notation matRowAdd := (@matRowAdd _ Aadd 0 1 _).
  Notation mrowSwap := (@mrowSwap A).
  Notation mrowScale := (@mrowScale _ Amul).
  Notation mrowAdd := (@mrowAdd _ Aadd Amul).
  Notation mrow := (@mrow _ Azero).


  (* ======================================================================= *)
  (** ** 行变换的抽象表示 *)
  
  (* 为避免逆矩阵计算时的大量计算，使用抽象表示，可提高计算效率 *)
  Inductive RowOp {n} :=
  | ROnop
  | ROswap (i j : fin (S n))
  | ROscale (i : fin (S n)) (c : A)
  | ROadd (i j : fin (S n)) (c : A).

  (** 行变换列表转换为矩阵 *)
  Definition rowOps2mat {n} (l : list (@RowOp n)) : smat (S n) :=
    fold_right (fun op M =>
                 match op with
                 | ROnop => M
                 | ROswap i j => mrowSwap i j M
                 | ROscale i c => mrowScale i c M
                 | ROadd i j c => mrowAdd i j c M
                 end) mat1 l.

  (** mrowSwap i j (M * N) = mrowSwap i j M * N *)
  Lemma mrowSwap_mmul : forall {n} (M N : smat n) (i j : fin n),
      mrowSwap i j (M * N) = mrowSwap i j M * N.
  Proof. intros. rewrite !mrowSwap_eq. rewrite mmul_assoc; auto. Qed.

  (** mrowScale i c (M * N) = mrowScale i c M * N *)
  Lemma mrowScale_mmul : forall {n} (M N : smat n) (i : fin n) (c : A),
      mrowScale i c (M * N) = mrowScale i c M * N.
  Proof. intros. rewrite !mrowScale_eq. rewrite mmul_assoc; auto. Qed.

  (** mrowAdd i j c (M * N) = mrowScale i j c M * N *)
  Lemma mrowAdd_mmul : forall {n} (M N : smat n) (i j : fin n) (c : A),
      mrowAdd i j c (M * N) = mrowAdd i j c M * N.
  Proof. intros. rewrite !mrowAdd_eq. rewrite mmul_assoc; auto. Qed.

  (** rowOps2mat (l1 ++ l2) = rowOps2mat l1 * rowOps2mat l2 *)
   Lemma rowOps2mat_app : forall {n} (l1 l2 : list (@RowOp n)),
      rowOps2mat (l1 ++ l2) = rowOps2mat l1 * rowOps2mat l2.
  Proof.
    intros n. induction l1; intros; simpl.
    - rewrite mmul_1_l; auto.
    - destruct a; auto.
      + rewrite IHl1. rewrite mrowSwap_mmul; auto.
      + rewrite IHl1. rewrite mrowScale_mmul; auto.
      + rewrite IHl1. rewrite mrowAdd_mmul; auto.
  Qed.


  (* ======================================================================= *)
  (** ** 矩阵形状的谓词 *)

  (** 方阵 M 的前 x 列的左下角(不含对角线)是 0。当 x = n 时，整个矩阵左下角是 0 *)
  Definition mLeftLowerZeros {n} (M : smat n) (x : nat) : Prop :=
    forall (i j : fin n), fin2nat j < x -> fin2nat j < fin2nat i -> M i j = 0.

  Lemma mLeftLowerZeros_less : forall {n} (M : smat (S n)) (x : nat),
      mLeftLowerZeros M (S x) -> mLeftLowerZeros M x.
  Proof. intros. hnf in *; intros. rewrite H; auto. Qed.
  
  Lemma mLeftLowerZeros_S : forall {n} (M : smat (S n)) (x : nat),
      (forall (i : fin (S n)), x < fin2nat i -> M i #x = 0) ->
      mLeftLowerZeros M x -> mLeftLowerZeros M (S x).
  Proof.
    intros. hnf in *; intros. destruct (x ??= fin2nat j)%nat.
    - assert (j = #x). rewrite e. rewrite nat2finS_fin2nat; auto.
      rewrite H3. rewrite H; auto. lia.
    - rewrite H0; auto. lia.
  Qed.

  
  (** 方阵 M 是下三角矩阵（即，左下角都是0）  *)
  Definition mLowerTriangle {n} (M : smat n) : Prop :=
    mLeftLowerZeros M n.
  
  Lemma mat1_mLeftLowerZeros : forall {n}, mLeftLowerZeros (@mat1 n) n.
  Proof.
    intros. hnf. intros. rewrite mnth_mat1_diff; auto.
    assert (fin2nat i <> fin2nat j); try lia. fin.
  Qed.
  
  Lemma mat1_mLowerTriangle : forall {n}, mLowerTriangle (@mat1 n).
  Proof. intros. unfold mLowerTriangle. apply mat1_mLeftLowerZeros. Qed.

  
  (** 方阵 M 的前 x 行/列的对角线都是 1。当 x=n 时，整个矩阵的对角线是 1 *)
  Definition mDiagonalOne {n} (M : smat n) (x : nat) : Prop :=
    forall (i : fin n), fin2nat i < x -> M i i = 1.
  
  Lemma mat1_mDiagonalOne : forall {n}, mDiagonalOne (@mat1 n) n.
  Proof. intros. hnf; intros. rewrite mnth_mat1_same; auto. Qed.

  
  (** 方阵 M 的对角线都是 1 *)
  Definition mDiagonalOnes {n} (M : smat n) : Prop := mDiagonalOne M n.
  
  Lemma mat1_mDiagonalOnes : forall {n}, mDiagonalOnes (@mat1 n).
  Proof. intros. unfold mDiagonalOnes. apply mat1_mDiagonalOne. Qed.

  
  (** 归一化的下三角矩阵：对角线全1，左下角全0 *)
  Definition mNormedLowerTriangle {n} (M : smat n) := 
    mLowerTriangle M /\ mDiagonalOnes M.

  (* 归一化上三角矩阵，任意下面的行的倍数加到上面，仍然是归一化上三角矩阵 *)
  Lemma mrowAdd_keep_NormedLowerTriangle : forall {n} (M : smat (S n)) (i j : fin (S n)),
      mNormedLowerTriangle M ->
      fin2nat i < fin2nat j ->
      mNormedLowerTriangle (mrowAdd i j (- (M i j))%A M).
  Proof.
    intros. unfold mNormedLowerTriangle in *. destruct H. split; hnf in *; intros.
    - unfold mrowAdd; fin. subst.
      rewrite !(H _ j0); auto. ring.
      pose proof (fin2nat_lt j). lia.
    - unfold mrowAdd; fin. subst.
      rewrite H1; auto. rewrite (H _ i); auto. ring.
  Qed.
  
  
  (** 方阵 M 的后 x 列的右上角（不含对角线）全是 0。
      当 x = n 时，整个矩阵右上角是 0 *)
  Definition mRightUpperZeros {n} (M : smat n) (x : nat) : Prop :=
    forall (i j : fin n), n - x <= fin2nat j -> fin2nat i < fin2nat j -> M i j = 0.
  
  Lemma mat1_mRightUpperZeros : forall {n}, mRightUpperZeros (@mat1 n) n.
  Proof.
    intros. hnf. intros. rewrite mnth_mat1_diff; auto.
    assert (fin2nat i <> fin2nat j); try lia. fin.
  Qed.
  

  (* ======================================================================= *)
  (** ** 某列的第一个非零元的行号 *)

  (** 第 j 列的后 x 个元素中的第 1 个非零元的行号。
      eg: 当 x 是`维数` 时，则从第 0 行开始往下查找。 *)
  Fixpoint firstNonzero {n} (M : smat (S n)) (x : nat) (j : fin (S n))
    : option (fin (S n)) :=
    match x with
    | O => None
    | S x' =>
        (* x的递归顺序：   x,    x-1, ... ,    1, (0)
           S n-x的顺序：Sn-x, Sn-x+1, ... , Sn-1, (Sn) *)
        if Aeqdec (M #(S n - x) j) 0
        then firstNonzero M x' j
        else Some #(S n - x)
    end.

  Lemma firstNonzero_imply_nonzero :
    forall (x : nat) {n} (M : smat (S n)) (i j : fin (S n)),
      firstNonzero M x j = Some i -> M i j <> 0.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct (Aeqdec (M #(n - x) j) 0).
      + apply IHx in H; auto.
      + inv H. auto.
  Qed.
  
  (* 非零元行号 r < S n *)
  Lemma firstNonzero_max : forall (x : nat) {n} (M : smat (S n)) (j r : fin (S n)),
      firstNonzero M x j = Some r -> fin2nat r < S n.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct Aeqdec as [E|E].
      + apply IHx in H. auto.
      + inversion H. rewrite fin2nat_nat2finS; lia.
  Qed.
  
  (* 非零元行号 r >= S n - x *)
  Lemma firstNonzero_min: forall (x : nat) {n} (M : smat (S n)) (j r : fin (S n)),
      firstNonzero M x j = Some r -> fin2nat r >= S n - x.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct Aeqdec as [E|E].
      + apply IHx in H. lia.
      + inversion H. rewrite fin2nat_nat2finS; lia.
  Qed.
  
(* End GaussElim. *)
(* Section test. *)
(*   Let M : smat nat 3 := l2m 0 [[1;0;0];[0;1;0];[0;0;1]]. *)
(*   Notation firstNonzero := (@firstNonzero nat 0). *)
(*   Compute firstNonzero M 3 #0. *)
(*   Compute firstNonzero M 3 #1. *)
(*   Compute firstNonzero M 3 #2. *)
(*   Compute firstNonzero M 2 #0. *)
(*   Compute firstNonzero M 2 #1. *)
(*   Compute firstNonzero M 2 #2. *)
(*   Compute firstNonzero M 1 #0. *)
(*   Compute firstNonzero M 1 #1. *)
(*   Compute firstNonzero M 1 #2. *)
(*   Compute firstNonzero M 0 #0. *)
(*   Compute firstNonzero M 0 #1. *)
(*   Compute firstNonzero M 0 #2. *)
(* End test. *)


  (* ******************************************************************* *)
  (** ** 向下消元 *)
  
  (* 将矩阵M的第j列的后 x 行元素变为 0。当 j=#0时，x=n *)
  Fixpoint elimDown {n} (M : smat (S n)) (x : nat) (j : fin (S n))
    : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        (* 递归时 x 从大到小，而 fx 是从小到大 *)
        let fx : fin (S n) := #(S n - x) in
        let x : A := M $ fx $ j in
        (* 如果 M[S n-x,j] <> 0，则 j 行的 -M[S n-x,j] 倍加到 S n-x 行。要求 M[j,j]=1 *)
        if Aeqdec x 0
        then elimDown M x' j
        else
          let (op1, M1) := (ROadd fx j (-x)%A, mrowAdd fx j (-x)%A M) in
          let (l2, M2) := elimDown M1 x' j in
          (l2 ++ [op1], M2)
    end.

  (** 对 M 向下消元得到 (l, M')，则 [l] * M = M' *)
  Lemma elimDown_imply_eq :
    forall (x : nat) {n} (M M' : smat (S n)) (j : fin (S n)) (l : list RowOp),
      elimDown M x j = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #(n - x) j) 0) as [E|E].
      + apply IHx in H; auto.
      + destruct elimDown as [l2 M2] eqn: T2.
        apply IHx in T2. inversion H. rewrite <- H2, <- T2.
        rewrite rowOps2mat_app. simpl.
        rewrite !mmul_assoc. f_equal.
        rewrite <- mrowAdd_mmul. rewrite mmul_1_l. auto.
  Qed.

  (* 若M[y,y]=1，则对第y列的 后 x 行向下消元后，前S n - x行的所有元素保持不变 *)
  Lemma elimDown_former_row_keep :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : fin (S n)),
      elimDown M x y = (l, M') ->
      M y y = 1 ->
      x < S n - fin2nat y ->
      (forall i j : fin (S n), fin2nat i < S n - x -> M' i j = M i j).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct Aeqdec as [E|E].
      + apply IHx with (i:=i)(j:=j) in H; auto; try lia.
      + destruct elimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5. apply IHx with (i:=i)(j:=j) in T2; try lia.
        * rewrite T2. unfold mrowAdd; fin.
        * unfold mrowAdd; fin.
  Qed.
  
  (* 若M[y,y]=1，则对第y列的 后 x 行向下消元后，第 y 列的后x行的所有元素变成 0 *)
  Lemma elimDown_latter_row_0:
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : fin (S n)),
      elimDown M x y = (l, M') ->
      M y y = 1 ->
      x < S n - fin2nat y ->
      (forall i : fin (S n), S n - x <= fin2nat i -> M' i y = 0).
  Proof.
    induction x; intros.
    - pose proof (fin2nat_lt i). lia.
    - simpl in H.
      destruct (Aeqdec (M #(n - x) y) 0) as [E|E].
      + destruct (fin2nat i ??= n - x)%nat as [E1|E1].
        * apply elimDown_former_row_keep with (i:=i)(j:=y) in H; auto; try lia.
          subst. rewrite H. rewrite <- E1 in E. rewrite nat2finS_fin2nat in E; auto.
        * apply IHx with (i:=i) in H; auto; try lia.
      + destruct elimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5.
        replace (S n - S x) with (n - x) in H2 by lia.
        destruct (fin2nat i ??= n - x)%nat as [E1|E1].
        * apply elimDown_former_row_keep with (i:=i)(j:=y) in T2; auto; try lia.
          ** rewrite T2. unfold mrowAdd; fin. rewrite H0. rewrite <- E0. fin.
          ** unfold mrowAdd; fin.
        * apply IHx with (i:=i) in T2; auto; try lia. unfold mrowAdd; fin.
  Qed.

  (* 若 M 的前 y 列左下方都是0，则对后 x 行向下消元后，M' 的前 y 列左下方都是0 *)
  Lemma elimDown_keep_lowerLeftZeros:
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : fin (S n)),
      elimDown M x y = (l, M') ->
      mLeftLowerZeros M (fin2nat y) ->
      x < S n - fin2nat y ->
      M y y = 1 ->
      mLeftLowerZeros M' (fin2nat y).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #(n - x) y) 0) as [E|E].
      + apply IHx in H; auto; try lia.
      + destruct elimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5.
        hnf; intros.
        destruct (x ??< S n - fin2nat y)%nat as [E1|E1].
        * apply IHx in T2; auto; try lia; clear IHx.
          ** hnf; intros. unfold mrowAdd; fin.
             rewrite !(H0 _ j0); auto. ring.
          ** unfold mrowAdd; fin.
        * apply elimDown_former_row_keep with (i:=i)(j:=j) in T2; auto; try lia.
  Qed.

  (** 若 M 前 x 列左下是0，则对 M 的后 S n - S x 列消元后的 M' 的前 S x 列左下是 0 *)
  Lemma elimDown_kepp_LeftLowerZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      elimDown M (S n - S x) #x = (l, M') ->
      x < S n ->
      M #x #x = 1 ->
      mLeftLowerZeros M x ->
      mLeftLowerZeros M' (S x).
  Proof.
    intros. hnf; intros.
    (* 两种情况：在 x 列，在 x 列左侧 *)
    destruct (fin2nat j ??= x)%nat as [E|E].
    - apply elimDown_latter_row_0 with (i:=i) in H; auto; subst; fin.
    - apply elimDown_keep_lowerLeftZeros in H; auto; fin.
      rewrite H; auto.
      pose proof (fin2nat_lt j). lia.
  Qed.

(* End GaussElim. *)
(* Section test. *)
(*   Import QcExt. *)
(*   Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult _). *)
  
(*   (* 化阶梯形测试 *) *)
(*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;2;3];[4;5;6];[7;8;9]]%Q). *)
(*   Compute m2l (snd (elimDown M 2 #0)). *)
(* End test. *)


  (* ******************************************************************* *)
  (** ** 化为行阶梯形 *)

  (*            (x=3)        (x=4)
     * * * *    * * * *     1 * * *
     * * * *    * 1 * *     0 1 * *
     * * * * => * 0 1 *     0 0 1 *
     * * * *    * 0 0 1     0 0 0 1
     -----------------------------------
     递归时i    3 2 1 (0)   4 3 2 1 (0)
     递归时n-i  1 2 3       0 1 2 3
   *)
  (* 将矩阵M的后 x 行化为标准上三角形。
     参数 x 最大为维数，递归时 x 递减，而 (维数-x) 递增。*)
  Fixpoint rowEchelon {n} (M : smat (S n)) (x : nat)
    : option (list RowOp * smat (S n)) :=
    match x with
    | O => Some ([], M)
    | S x' =>
        let j : fin (S n) := #(S n - x) in
        (* 找出主元 *)
        match firstNonzero M x j with
        | None => None (* 没有非零元，则该矩阵不可逆 *)
        | Some i =>
            (* 使主元行在当前行 *)
            let (op1, M1) :=
              (if i ??= j       (* 若当前行就是主元行，则不需要交换 *)
               then (ROnop, M)
               else (ROswap j i, mrowSwap j i M)) in
            (* 使主元是 1 *)
            let (op2, M2) :=
              (let c : A := M1 $ j $ j in
               (ROscale j (/c), mrowScale j (/c) M1)) in
            (* 使主元以下都是 0 *)
            let (l3, M3) := elimDown M2 x' j in
            (* 递归 *)
            match rowEchelon M3 x' with
            | None => None
            | Some (l4, M4) => Some (l4 ++ l3 ++ [op2; op1], M4)
            end
        end
    end.

  (** 对 M 行变换得到 (l, M')，则 [l] * M = M' *)
  Lemma rowEchelon_imply_eq : forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M x = Some (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros.
    - simpl in H. inversion H. simpl. apply mmul_1_l.
    - unfold rowEchelon in H; fold (@rowEchelon (n)) in H. (* Tips: simpl会展开太多 *)
      destruct firstNonzero as [i|] eqn: Hi; try easy.
      replace (S n - S x) with (n - x) in * by lia.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + (* i 就是当前行，不需要换行 *)
        destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4. inversion H. rewrite <- H2, <- T4.
        apply elimDown_imply_eq in T3. rewrite <- T3.
        rewrite !rowOps2mat_app. simpl. rewrite !mmul_assoc. f_equal. f_equal.
        rewrite <- mrowScale_mmul. rewrite mmul_1_l. auto.
      + (* i 不是当前行，需要换行 *)
        destruct elimDown as [l3 M3] eqn:T3.
        destruct (rowEchelon M3 x) as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4. inversion H. rewrite <- H2, <- T4.
        apply elimDown_imply_eq in T3. rewrite <- T3.
        rewrite !rowOps2mat_app. simpl. rewrite !mmul_assoc. f_equal. f_equal.
        rewrite <- mrowScale_mmul. rewrite <- mrowSwap_mmul. rewrite mmul_1_l. auto.
  Qed.

  (** M 的前 S n - x 列左下角是0，且将 M 的后 x 行变换上三角得到 (l, M')，
      则 M' 的所有列的左下角是 0 *)
  Lemma rowEchelon_LeftLowerZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M x = Some (l, M') ->
      x <= S n ->
      mLeftLowerZeros M (S n - x) ->
      mLeftLowerZeros M' (S n).
  Proof.
    induction x; intros.
    - simpl in *. inv H. auto.
    - unfold rowEchelon in H; fold (@rowEchelon n) in H.
      replace (S n - S x) with (n - x) in * by lia.
      destruct firstNonzero as [i|] eqn : Hi; try easy.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        inv H. apply IHx in T4; auto; try lia; clear IHx.
        replace x with (S n - (S (n - x))) in T3 at 4 by lia.
        apply elimDown_kepp_LeftLowerZeros in T3; try lia.
        * replace (S (n - x)) with (S n - x) in T3 by lia; auto.
        * unfold mrowScale; fin.
          (* 确保元素非零时才能消去除法逆元 *)
          rewrite field_mulInvL; auto.
          apply firstNonzero_imply_nonzero in Hi. auto.
        * hnf; intros. unfold mrowScale; fin. rewrite (H1 _ j); fin.
      + destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        inv H. apply IHx in T4; auto; try lia; clear IHx.
        replace x with (S n - (S (n - x))) in T3 at 6 by lia.
        apply elimDown_kepp_LeftLowerZeros in T3; try lia.
        * replace (S (n - x)) with (S n - x) in T3 by lia; auto.
        * unfold mrowScale; fin.
          (* 确保元素非零时才能消去除法逆元 *)
          rewrite field_mulInvL; auto.
          unfold mrowSwap; fin. apply firstNonzero_imply_nonzero in Hi. auto.
        * hnf; intros. unfold mrowScale, mrowSwap; fin.
          ** rewrite (H1 _ j); fin. ring. lia. apply firstNonzero_min in Hi. lia.
          ** rewrite (H1 _ j); fin.
  Qed.

  (** 化行阶梯矩阵得到了下三角矩阵 *)
  Lemma rowEchelon_LowerTriangle : forall {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M') -> mLowerTriangle M'.
  Proof.
    intros. apply rowEchelon_LeftLowerZeros in H; auto.
    hnf; intros. lia.
  Qed.
  
  (** M 的前 S n - x 个对角线元素是1，且将 M 的后 x 行变换上三角得到 (l, M')，
      则 M' 的所有对角线都是1 *)
  Lemma rowEchelon_DiagonalOne :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M x = Some (l, M') ->
      mDiagonalOne M (S n - x) ->
      x <= S n ->
      mDiagonalOne M' (S n).
  Proof.
    induction x; intros.
    - simpl in *. inv H. auto.
    - (* simpl in H. *) (* too much! *)
      unfold rowEchelon in H; fold (@rowEchelon n) in H.
      destruct firstNonzero as [i|] eqn: Hi; try easy.
      replace (S n - S x) with (n - x) in * by lia.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4; clear IHx; try lia.
        * inversion H; clear H. rewrite <- H4. auto.
        * hnf; intros.
          apply elimDown_former_row_keep with (i:=i0)(j:=i0) in T3; fin.
          ** rewrite T3. unfold mrowScale; fin.
             *** rewrite <- E0. fin. rewrite field_mulInvL; auto.
                 rewrite <- E0 in *. fin.
                 apply firstNonzero_imply_nonzero in Hi; auto.
             *** rewrite H0; auto. lia.
          ** unfold mrowScale; fin.
             rewrite field_mulInvL; auto.
             apply firstNonzero_imply_nonzero in Hi. auto.
      + destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4; clear IHx; try lia.
        * inversion H; clear H. rewrite <- H4. auto.
        * hnf; intros.
          apply elimDown_former_row_keep with (i:=i0)(j:=i0) in T3; fin.
          ** rewrite T3. unfold mrowScale, mrowSwap; fin.
             *** rewrite <- E0. fin. rewrite field_mulInvL; auto.
                 apply firstNonzero_imply_nonzero in Hi.
                 rewrite <- E0 in *. fin.
             *** subst.
                 pose proof (firstNonzero_max _ _ _ _ Hi).
                 pose proof (firstNonzero_min _ _ _ _ Hi). lia.
             *** assert (fin2nat i0 < n - x)%nat. lia.
                 rewrite H0; auto.
          ** unfold mrowScale, mrowSwap; fin.
             rewrite field_mulInvL; auto.
             apply firstNonzero_imply_nonzero in Hi. auto.
  Qed.
  
  (** 化行阶梯矩阵得到的矩阵的对角线都是 1 *)
  Lemma rowEchelon_DiagonalOnes : forall {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M') -> mDiagonalOnes M'.
  Proof.
    intros. unfold mDiagonalOnes. apply rowEchelon_DiagonalOne in H; auto.
    hnf; lia.
  Qed.

  (** 化行阶梯矩阵得到的矩阵是规范的的下三角矩阵 *)
  Lemma rowEchelon_NormedLowerTriangle : forall {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M') -> mNormedLowerTriangle M'.
  Proof.
    intros. hnf. split.
    apply rowEchelon_LowerTriangle in H; auto.
    apply rowEchelon_DiagonalOnes in H; auto.
  Qed.

  (** 化行阶梯形满足乘法不变式，并且结果矩阵是规范的下三角矩阵 *)
  Theorem rowEchelon_spec :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M') ->
      (rowOps2mat l * M = M') /\ mNormedLowerTriangle M'.
  Proof.
    intros. split.
    apply rowEchelon_imply_eq in H; auto.
    apply rowEchelon_NormedLowerTriangle in H; auto.
  Qed.


(* End GaussElim. *)
(* Section test. *)

(*   Import QcExt. *)
(*   Notation firstNonzero := (firstNonzero (Azero:=0)). *)
(*   Notation rowEchelon := (@rowEchelon _ Qcplus 0 Qcopp Qcmult Qcinv _). *)
(*   Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult _). *)
(*   Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1 _). *)
(*   Notation mmul := (@mmul _ Qcplus 0 Qcmult). *)
(*   Infix "*" := mmul : mat_scope. *)

(*   (* 行阶梯形 *) *)
(* (*      [  0 -2  1]     [0    1/3  0]   [1 0 -2/3] *) *)
(* (*      [  3  0 -2]  => [-1/2   0  0] * [0 1 -1/2] *) *)
(* (*      [ -2  3  0]     [9      4  6]   [0 0    1] *) *)
(*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[0;-2;1];[3;0;-2];[-2;3;0]]%Q). *)
(*   Let M1 : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;0;-2/3];[0;1;-1/2];[0;0;1]]%Q). *)
(*   Let E1 : smat Qc 3 := l2m 0 (Q2Qc_dlist [[0;1/3;0];[-1/2;0;0];[9;4;6]]%Q). *)
  
(*   Goal match rowEchelon M 3 with *)
(*        | Some (l1',M1') => m2l (rowOps2mat l1') = m2l E1 *)
(*                           /\ m2l M1' = m2l M1 *)
(*        | _ => False *)
(*        end. *)
(*   Proof. *)
(*     Time cbv; split; list_eq; f_equal; apply proof_irrelevance. *)
(*   Qed. *)

(*   (* 验证 E1 将 M 变换到了 M1 *) *)
(*   Goal (E1 * M)%M = M1. *)
(*   Proof. apply m2l_inj. cbv. list_eq; f_equal. Qed. *)

(* End test. *)

  (* ******************************************************************* *)
  (** ** 向上消元 *)
  
  (* 将矩阵M的第 j 列的前 x 行元素变为 0。当 j=#(S n)时，x=S n *)
  Fixpoint elimUp {n} (M : smat (S n)) (x : nat) (j : fin (S n))
    : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        let fx : fin (S n) := #x' in
        let a : A := (M $ fx $ j) in
        (* 如果 M[x',j] <> 0，则 j 行的 -M[x',j] 倍加到 x' 行。要求 M[j,j]=1 *)
        if Aeqdec a 0
        then elimUp M x' j
        else
          let (op1, M1) := (ROadd fx j (-a)%A, mrowAdd fx j (-a)%A M) in
          let (l2, M2) := elimUp M1 x' j in
          (l2 ++ [op1], M2)
    end.

  (** 对 M 向上消元得到 (l, M')，则 [l] * M = M' *)
  Lemma elimUp_imply_eq :
    forall (x : nat) {n} (M M' : smat (S n)) (j : fin (S n)) (l : list RowOp),
      elimUp M x j = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H; auto.
      + destruct elimUp as [l2 M2] eqn:T2.
        apply IHx in T2. inv H.
        rewrite rowOps2mat_app. simpl.
        rewrite !mmul_assoc. f_equal.
        rewrite <- mrowAdd_mmul. rewrite mmul_1_l. auto.
  Qed.

  (** 对 M 向上消元保持下三角矩阵 *)
  Lemma elimUp_keep_NormedLowerTriangle :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (j : fin (S n)),
      elimUp M x j = (l, M') ->
      x <= fin2nat j ->     (* 前 x 行，行号不超过 j *)
      mNormedLowerTriangle M -> mNormedLowerTriangle M'.
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H; auto; try lia.
      + destruct elimUp as [l2 M2] eqn: T2. inv H.
        apply IHx in T2; auto; try lia.
        apply mrowAdd_keep_NormedLowerTriangle; auto. fin.
        pose proof (fin2nat_lt j). lia.
  Qed.

  (* 上消元时，x 行及以下的行保持不变 *)
  Lemma elimUp_keep_lower_rows :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : fin (S n)),
      elimUp M x y = (l, M') ->
      x <= fin2nat y ->     (* 前 x 行，行号不超过 y *)
      (forall i j : fin (S n), x <= fin2nat i -> M' i j = M i j).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #x y) 0) as [E|E].
      + apply IHx with (i:=i)(j:=j) in H; auto; try lia.
      + destruct elimUp as [l2 M2] eqn: T2. inv H.
        apply IHx with (i:=i)(j:=j) in T2; auto; try lia.
        rewrite T2. unfold mrowAdd; fin.
        pose proof (fin2nat_lt y). lia.
  Qed.
  
  (* 上消元后该列上方元素为 0 *)
  Lemma elimUp_upper_rows_to_0 :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : fin (S n)),
      elimUp M x y = (l, M') ->
      mNormedLowerTriangle M ->
      x <= fin2nat y ->     (* 前 x 行，行号不超过 y *)
      (forall i : fin (S n), fin2nat i < x -> M' i y = 0).
  Proof.
    induction x; intros; try lia.
    simpl in H. hnf in H0. destruct H0 as [H00 H01].
    destruct (Aeqdec (M #x y) 0) as [E|E].
    - (* i 在当前列 x，或者 i 小于 x *)
      destruct (x ??= fin2nat i)%nat as [E1|E1].
      + apply elimUp_keep_lower_rows with (i:=i)(j:=y) in H; try lia.
        rewrite H. subst. fin.
      + apply IHx with (i:=i) in H; auto; try lia. split; auto.
    - destruct elimUp as [l2 M2] eqn: T2. inv H.
      (* i 在当前列 x，或者 i 小于 x *)
      destruct (x ??= fin2nat i)%nat as [E1|E1].
      + rewrite E1 in *.
        apply elimUp_keep_lower_rows with (i:=i)(j:=y) in T2; try lia. rewrite T2.
        unfold mrowAdd; fin. rewrite H01; auto; try lia; fin.
      + apply IHx with (i:=i) in T2; auto; try lia.
        apply mrowAdd_keep_NormedLowerTriangle; auto. split; auto.
        fin. pose proof (fin2nat_lt y). lia.
  Qed.

  (** 若 M 的后 L 列的右上角都是 0，则上消元后，M' 的后 L 列的右上角都是 0 *)
  Lemma elimUp_keep_upperRightZeros :
    forall (x L : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : fin (S n)),
      elimUp M x y = (l, M') ->
      x <= fin2nat y ->
      L < S n - fin2nat y ->
      mNormedLowerTriangle M ->
      mRightUpperZeros M L ->
      mRightUpperZeros M' L.
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    simpl in H.
    destruct (Aeqdec (M #x y) 0) as [E|E].
    - hnf; intros.
      apply IHx with (L:=L) in H; auto; try lia.
    - destruct elimUp as [l2 M2] eqn: T2. inv H.
      hnf; intros.
      apply IHx with (L:=L) in T2; auto; try lia.
      + apply mrowAdd_keep_NormedLowerTriangle; auto. fin.
      + hnf; intros. unfold mrowAdd; fin.
        rewrite !(H3 _ j0); try lia. ring.
  Qed.
  
  (** 若 M 的后 (S n - S y) 列的右上角都是 0，则上消元后，S n - y 列的右上角都是 0 *)
  Lemma elimUp_keep_upperRightZeros_S:
    forall {n} (M M' : smat (S n)) (l : list RowOp) (y : nat),
      elimUp M y #y = (l, M') ->
      y < S n ->
      mNormedLowerTriangle M ->
      mRightUpperZeros M (S n - S y) ->
      mRightUpperZeros M' (S n - y).
  Proof.
    intros. hnf; intros.
    replace (S n - (S n - y)) with y in H3 by lia.
    destruct (fin2nat j ??= y)%nat as [E|E].
    - subst. apply elimUp_upper_rows_to_0 with (i:=i) in H; auto; fin.
    - apply elimUp_keep_upperRightZeros with (L:=S n - S y) in H; auto; fin.
      rewrite H; auto. lia.
  Qed.
  
(* End GaussElim. *)
(* Section test. *)

(*   Import QcExt. *)
(*   Notation elimUp := (@elimUp _ Qcplus 0 Qcopp Qcmult _). *)
  
(*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;2;3];[4;5;6];[7;8;1]]%Q). *)
(*   Compute m2l (snd (elimUp M 2 #2)). *)
(* End test. *)
  

  (* ******************************************************************* *)
  (** ** 最简行阶梯形矩阵 *)

  (* 将矩阵 M 的前 x 行(列)化为行最简阶梯形。当 x 为 S n 时表示整个矩阵 *)
  Fixpoint minRowEchelon {n} (M : smat (S n)) (x : nat) : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        let fx : fin (S n) := #x' in
        let (l1, M1) := elimUp M x' fx in
        let (l2, M2) := minRowEchelon M1 x' in
        (l2 ++ l1, M2)
    end.

  (** 对 M 最简行变换得到 (l, M')，则 [l] * M = M' *)
  Lemma minRowEchelon_imply_eq : forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M x = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - destruct elimUp as [l1 M1] eqn : T1.
      destruct minRowEchelon as [l2 M2] eqn : T2.
      apply IHx in T2. inv H.
      apply elimUp_imply_eq in T1. rewrite <- T1.
      rewrite rowOps2mat_app. apply mmul_assoc.
  Qed.

  (* minRowEchelon 保持上三角 *)
  Lemma minRowEchelon_keep_NormedLowerTriangle :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M x = (l, M') ->
      x <= S n ->
      mNormedLowerTriangle M ->
      mNormedLowerTriangle M'.
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    destruct elimUp as [l1 M1] eqn : T1.
    destruct minRowEchelon as [l2 M2] eqn : T2. inv H.
    apply IHx in T2; auto; try lia.
    apply elimUp_keep_NormedLowerTriangle in T1; auto. fin.
  Qed.
  
  (** 若 M 的 后 S n - x 列的右上角都是0，则对 M 最简行变换得到的 M' 的右上角都是0 *)
  Lemma minRowEchelon_RightUpperZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M x = (l, M') ->
      x <= S n ->
      mNormedLowerTriangle M ->
      mRightUpperZeros M (S n - x) ->
      mRightUpperZeros M' (S n).
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    destruct elimUp as [l1 M1] eqn : T1.
    destruct minRowEchelon as [l2 M2] eqn : T2. inv H.
    apply IHx in T2; auto; try lia.
    - apply elimUp_keep_NormedLowerTriangle in T1; auto. fin.
    - apply elimUp_keep_upperRightZeros_S in T1; auto.
  Qed.
  
  (** 对 M 最简行变换得到 (l, M')，则 M' 是单位阵 *)
  Lemma minRowEchelon_imply_mat1 : forall {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M (S n) = (l, M') ->
      mNormedLowerTriangle M -> M' = mat1.
  Proof.
    intros. apply meq_iff_mnth; intros. 
    (* 分别处理：左下角、对角线、右上角 *)
    destruct (j ??< i).
    - (* 左下角 *)
      rewrite mat1_mLeftLowerZeros; auto; fin.
      apply minRowEchelon_keep_NormedLowerTriangle in H; auto.
      hnf in H. destruct H. rewrite H; auto; fin.
    - destruct (j ??= i).
      + (* 对角线 *)
        apply minRowEchelon_keep_NormedLowerTriangle in H; auto. fin.
        rewrite mat1_mDiagonalOne; fin.
        hnf in H. destruct H. rewrite H1; auto; fin.
      + (* 右上角 *)
        assert (fin2nat i < fin2nat j) by lia.
        rewrite mat1_mRightUpperZeros; auto; fin.
        apply minRowEchelon_RightUpperZeros in H; auto; fin.
        * rewrite H; auto; try lia.
        * hnf; intros. pose proof (fin2nat_lt j0). lia.
  Qed.
  
  (* End GaussElim. *)
(* Section test. *)
(*   Import QcExt. *)
(*   Notation minRowEchelon := (@minRowEchelon _ Qcplus 0 Qcopp Qcmult _). *)
(*   Notation elimUp := (@elimUp _ Qcplus 0 Qcopp Qcmult _). *)
(*   Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1). *)
(*   Notation mmul := (@mmul _ Qcplus 0 Qcmult). *)
(*   Infix "*" := mmul : mat_scope. *)
(*   Notation mat1 := (@mat1 _ 0 1). *)
  
(*   (* 简化行阶梯形 *) *)
(* (*      [1 0 -2/3]     [1  0  2/3]   [1 0 0] *) *)
(* (*      [0 1 -1/2]  => [0  1  1/2] * [0 1 0] *) *)
(* (*      [0 0    1]     [0  0    1]   [0 0 1] *) *)
(*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;0;-2/3];[0;1;-1/2];[0;0;1]]%Q). *)
(*   Let l1 := fst (minRowEchelon M 3). *)
(*   Let M1 := snd (minRowEchelon M 3). *)

(*   Goal (rowOps2mat l1 * M)%M = M1. *)
(*   Proof. apply m2l_inj. cbv. list_eq. Qed. *)
(* End test. *)
  
  (* ******************************************************************* *)
  (** ** 计算逆矩阵 *)

  (** 计算逆矩阵(option版本) *)
  Definition minvGEo {n} : smat n -> option (smat n) :=
    match n with
    | O => fun _ => None           (* 0级矩阵不可逆 *)
    | S n' =>
        fun (M : smat (S n')) =>
          match rowEchelon M (S n') with
          | None => None
          | Some (l1, M1) =>
              let (l2, M2) := minRowEchelon M1 (S n') in
              Some (rowOps2mat (l2 ++ l1))
          end
    end.

  (** minvGEo 的结果左乘原矩阵等于单位阵 *)
  Theorem minvGEo_spec : forall {n} (M M' : smat n),
      minvGEo M = Some M' -> M' * M = mat1.
  Proof.
    intros. unfold minvGEo in H. destruct n; try easy.
    destruct rowEchelon as [[l1 M1]|] eqn:T1; try easy.
    destruct minRowEchelon as [l2 M2] eqn:T2. inv H.
    pose proof (rowEchelon_imply_eq _ _ _ _ T1).
    pose proof (minRowEchelon_imply_eq _ _ _ _ T2).
    rewrite rowOps2mat_app. rewrite mmul_assoc. rewrite H, H0.
    apply minRowEchelon_imply_mat1 in T2; auto.
    apply rowEchelon_NormedLowerTriangle in T1; auto.
  Qed.
  
  (* 计算逆矩阵(默认值是mat1的版本) *)
  Definition minvGE {n} : smat n -> smat n :=
     match n with
    | O => fun M => M              (* 0级矩阵，返回自身 *)
    | S n' =>
        fun (M : smat (S n')) =>
          match rowEchelon M n with
          | None => M            (* 不可逆矩阵，返回自身 *)
          | Some (l1, M1) =>
              let (l2, M2) := minRowEchelon M1 n in
              rowOps2mat (l2 ++ l1)
          end
    end.

  (* minvGEo 算出的结果与 minvGE 的结果相等 *)
  Theorem minvGE_spec : forall {n} (M M' : smat (S n)),
      minvGEo M = Some M' -> minvGE M = M'.
  Proof.
    intros. unfold minvGEo, minvGE in *.
    destruct rowEchelon as [[l1 M1]|] eqn:T1; try easy.
    destruct minRowEchelon as [l2] eqn:T2.
    inv H. auto.
  Qed.
  

  (* ******************************************************************* *)
  (** ** 可逆的矩阵 *)

  (** The matrix `N` is the left inverse of matrix `M` *)
  Definition minverseL {n} (M N : smat n) : Prop := N * M = mat1.

  (** The matrix `M` has a left inverse under matrix multiplication *)
  Definition minvertibleL {n} (M : smat n) : Prop := exists N, minverseL M N.
  
  (* 左逆是唯一的 *)
  Lemma minverseL_unique : forall {n} (M N1 N2 : smat n),
      minverseL M N1 -> minverseL M N2 -> N1 = N2.
  Proof.
    intros. hnf in *.
    Abort.

  (** Left cancellation law of matrix multiplication *)
  Lemma mmul_cancel_l : forall {r c} (M : smat r) (N1 N2 : mat r c) ,
      minvertibleL M -> M * N1 = M * N2 -> N1 = N2.
  Proof.
    intros. hnf in H. destruct H as [N H].
    assert (N * M * N1 = N * M * N2). rewrite !mmul_assoc, H0; auto.
    rewrite H in H1. rewrite !mmul_1_l in H1. auto.
  Qed.

  (** The matrix `N` is the right inverse of matrix `M` *)
  Definition minverseR {n} (M N : smat n) : Prop := M * N = mat1.

  (** The matrix `M` has a right inverse under matrix multiplication *)
  Definition minvertibleR {n} (M : smat n) : Prop := exists N, minverseR M N.

  (** Right cancellation law of matrix multiplication *)
  Lemma mmul_cancel_r : forall {r c} (M : smat c) (N1 N2 : mat r c) ,
      minvertibleR M -> N1 * M = N2 * M -> N1 = N2.
  Proof.
    intros. hnf in H. destruct H as [N H].
    assert (N1 * M * N = N2 * M * N). rewrite H0; auto.
    rewrite !mmul_assoc, H in H1. rewrite !mmul_1_r in H1. auto.
  Qed.

  (** The matrix `M` is invertible *)
  Definition minvertible {n} (M : smat n) : Prop := exists N, minverseL M N /\ minverseR M N.

  (** mat1 is invertible *)
  Lemma mat1_invertible : forall {n}, minvertible (@mat1 n).
  Proof. intros. hnf. exists mat1. split; hnf; rewrite mmul_1_l; auto. Qed.

  (** 两个可逆矩阵相乘仍可逆 *)
  Lemma mmul_invertible: forall {n} (M N : smat n), 
      minvertible M -> minvertible N -> minvertible (M * N).
  Proof.
    intros. hnf in *. destruct H as [M' [HL HR]], H0 as [N' [HL1 HR1]]; hnf in *.
    exists (N' * M'). split; hnf.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc M' M). rewrite HL, mmul_1_l; auto.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc N N'). rewrite HR1, mmul_1_l; auto.
  Qed.
  
  (** The matrix `M` is singular (i.e., not invertible) *)
  Definition msingular {n} (M : smat n) : Prop := ~(minvertible M).

    
  (* ******************************************************************* *)
  (** ** minvGE (高斯消元求逆矩阵) 的性质 *)

  (* 如果 minvGEo 算出了结果，则 M 是可逆的 *)
  Lemma minvGEo_Some_invertible : forall {n} (M M' : smat n),
      minvGEo M = Some M' -> minvertibleL M.
  Proof. intros. apply minvGEo_spec in H. hnf. exists M'; auto. Qed.

  (* 如果 minvGEo 算出了结果，则 M' 是 M 的左逆 *)
  Lemma minvGEo_Some_inverseL : forall {n} (M M' : smat n),
      minvGEo M = Some M' -> minverseL M M'.
  Proof. intros. apply minvGEo_spec in H. hnf. auto. Qed.

  (* (* 如果 minvGEo 算不出结果，则 M 不可逆 *) *)
  (* Lemma minvGEo_None_singular : forall {n} (M M' : smat n), *)
  (*     minvGEo M = None -> msingular M. *)
  (* Proof. intros. apply minvGEo_spec in H. hnf. exists M'; auto. Qed. *)
  
  
(* 抽取代码测试 *)
(* End GaussElim. *)

(* Definition mmul_R := @mmul _ Rplus R0 Rmult. *)
(* Definition minvGE_R := @minvGE _ Rplus R0 Ropp Rmult R1 Rinv R_eq_Dec. *)
(* Require Import ExtrOcamlBasic ExtrOcamlNatInt. *)
(* Require Import MyExtrOCamlR. *)

(* (** two float numbers are comparison decidable *) *)
(* Extract Constant total_order_T => "fun r1 r2 -> *)
(*   let c = Float.compare r1 r2 in *)
(*   if c < 0 then Some true *)
(*   else (if c = 0 then None else Some false)". *)

(* Extract Constant Req_dec_T => "fun r1 r2 -> *)
(*   let c = Float.compare r1 r2 in *)
(*   if c = 0 then true *)
(*   else false". *)

(* (* Recursive Extraction minvGE_R. *) *)
(* Extraction "ocaml_test/matrix.ml" minvGE_R m2l l2m mmul_R. *)
  
  (* 在Coq中直接计算逆矩阵的测试 *)
End GaussElim.
Section test.
  Import QcExt.
  Notation mat1 := (@mat1 _ 0 1).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Infix "*" := mmul : mat_scope.
  Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult).
  Notation rowEchelon := (@rowEchelon _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation minvGE := (@minvGE _ Qcplus 0 Qcopp Qcmult 1 Qcinv _).

  (* 输入和输出都是 list 的逆矩阵求解 *)
  Definition minvGE_Qclist (n : nat) (l : list (list Q)) : list (list Q) :=
    Qc2Q_dlist (m2l (@minvGE n (l2m 0 (Q2Qc_dlist l)))).

  Open Scope Q_scope.
  
  (* [ 1  2]     [ 3  2]
     [-1 -3] <-> [-1 -1] *)
  Compute minvGE_Qclist 2 [[1;2];[-1;-3]].
  
  (* [1 3 1]     [-1 -1  2]
     [2 1 1] <-> [ 0 -1  1]
     [2 2 1]     [ 2  4 -5] *)
  Compute minvGE_Qclist 3 [[1;3;1];[2;1;1];[2;2;1]].

  (* [  0 -2  1]     [6 3 4]
     [  3  0 -2] <-> [4 2 3]
     [ -2  3  0]     [9 4 6] *)
  Compute minvGE_Qclist 3 [[0;-2;1];[3;0;-2];[-2;3;0]].

  (* 一个8阶矩阵，手动构造的 *)
  Compute minvGE_Qclist 8
    [[1;2;3;4;5;6;7;8];
     [2;4;5;6;7;8;9;1];
     [3;5;7;6;8;4;2;1];
     [4;5;7;6;9;8;3;2];
     [5;4;3;7;9;6;8;1];
     [6;5;3;4;7;8;9;2];
     [7;8;6;5;9;2;1;3];
     [8;9;6;3;4;5;2;1]].
  (* 在 matlab 中，输入以下指令计算逆矩阵
     M = [1 2 3 4 5 6 7 8; ...
          2 4 5 6 7 8 9 1; ...
          3 5 7 6 8 4 2 1; ...
          4 5 7 6 9 8 3 2; ...
          5 4 3 7 9 6 8 1; ...
          6 5 3 4 7 8 9 2; ...
          7 8 6 5 9 2 1 3; ...
          8 9 6 3 4 5 2 1]
     M' = inv(M)
     使用如下指令切换分数格式，以便与Coq中的结果对比
     format rat
     format short
     看起来与Coq的结果不同。比如 M'(0,2)，在Coq中是41846/50943, matlab中是23/28 
     可能的原因是，matlab以浮点数计算，再将不精确的结果转换为分数也无法弥补差异。
     相反，Coq的精确结果或许有潜在的好处，暂未知。*)

  (* 可证明这两个值不相同 *)
  Goal ~(Qmake 41846 50943 == Qmake 23 28).
  Proof. intro. cbv in H. easy. Qed.

  (* 再测试一个带有小数的复杂矩阵 *)
  (* 使用matlab来生成随机矩阵：
     format short
     M = rand(8,8)
     或者等价于以下结果
     M = [0.8001  0.5797  0.0760  0.9448  0.3897  0.0598  0.7317  0.1835; ...
  0.4314  0.5499  0.2399  0.4909  0.2417  0.2348  0.6477  0.3685; ...
  0.9106  0.1450  0.1233  0.4893  0.4039  0.3532  0.4509  0.6256; ...
  0.1818  0.8530  0.1839  0.3377  0.0965  0.8212  0.5470  0.7802; ...
  0.2638  0.6221  0.2400  0.9001  0.1320  0.0154  0.2963  0.0811; ...
  0.1455  0.3510  0.4173  0.3692  0.9421  0.0430  0.7447  0.9294; ...
  0.1361  0.5132  0.0497  0.1112  0.9561  0.1690  0.1890  0.7757; ...
  0.8693  0.4018  0.9027  0.7803  0.5752  0.6491  0.6868  0.4868]
     然后计算逆矩阵
     M' = inv(M)
 *)

  (* 计算逆矩阵耗时18s，验证“M*M'=mat1”，耗时约1分钟 *)
  (*
  Time Compute minvGE_Qclist 8
    [[0.8001;0.5797;0.0760;0.9448;0.3897;0.0598;0.7317;0.1835];
     [0.4314;0.5499;0.2399;0.4909;0.2417;0.2348;0.6477;0.3685];
     [0.9106;0.1450;0.1233;0.4893;0.4039;0.3532;0.4509;0.6256];
     [0.1818;0.8530;0.1839;0.3377;0.0965;0.8212;0.5470;0.7802];
     [0.2638;0.6221;0.2400;0.9001;0.1320;0.0154;0.2963;0.0811];
     [0.1455;0.3510;0.4173;0.3692;0.9421;0.0430;0.7447;0.9294];
     [0.1361;0.5132;0.0497;0.1112;0.9561;0.1690;0.1890;0.7757];
     [0.8693;0.4018;0.9027;0.7803;0.5752;0.6491;0.6868;0.4868]].
   *)
  
  Open Scope Qc_scope.

  (* 测试：将第j列的第x行以下全部化为0 *)
  Section ex1.
    (*
      来自《线性代数》同济，第5版，P60, B1->B2
      将 B1 第1列的第1行以下全部化为0，得到B2。

      B1 = 
       [[1;  1; -2;  1];
        [2; -1; -1;  1];
        [2; -3;  1; -1];
        [3;  6; -9;  7]]

      B2 = 
       [[1;  1; -2;  1];
        [0; -3;  3; -1];
        [0; -5;  5; -3];
        [0;  3; -3;  4]]
     *)
    Let n : nat := 4.
    Let M1 : smat Qc n :=
        l2m 0
          (Q2Qc_dlist
             [[1;  1; -2;  1];
              [2; -1; -1;  1];
              [2; -3;  1; -1];
              [3;  6; -9;  7]]%Q).
    Let M2 : smat Qc n :=
        l2m 0
          (Q2Qc_dlist
             [[1;  1; -2;  1];
              [0; -3;  3; -1];
              [0; -5;  5; -3];
              [0;  3; -3;  4]]%Q).
    Goal snd (elimDown M1 3 #0) = M2.
    Proof. apply m2l_inj. cbv. auto. Qed.
  End ex1.
End test.

(* Recursive Extraction echelon minEchelon. *)
