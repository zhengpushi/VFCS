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
(** ** 找出序列后一段中第1个为真的项 *)

(* 找出序列 P 中末尾 i 个元素 P(n-i), P(n-i+1), ..., P(n-1) 中的第1个为真的序号 *)
Fixpoint seqFirst (n i : nat) (P : nat -> bool) : option nat :=
  match i with
  | O => None
  | S i' =>
      (* 递归顺序：  i,   i-1, ... ,   1, (0)
         实际顺序：n-i, n-i+1, ... , n-1, (n) *)
      if P (n - i)
      then Some (n - i)
      else seqFirst n i' P
  end.

(* (* 若返回 None，则都不满足 *) *)
(* Lemma seqFirst_spec_None : forall {n i : nat} (P : nat -> bool) j, *)
(*     seqFirst n i P = None -> j < n -> P j = false. *)
(* Proof. *)
(*   intros n i. revert n. induction i; intros; simpl in *. 2:{  easy. *)
(*   destruct (P (n - S i)) eqn:E1. *)
(*   - inversion H; auto. *)
(*   - apply IHi in H; auto. *)
(* Qed. *)

(* (* 若返回 Some r，则第 r 个满足 *) *)
(* Lemma seqFirst_spec1 : forall {n i : nat} (P : nat -> bool) r, *)
(*     seqFirst n i P = Some r -> P r = true. *)
(* Proof. *)
(*   intros n i. revert n. induction i; intros; simpl in *. easy. *)
(*   destruct (P (n - S i)) eqn:E1. *)
(*   - inversion H; auto. *)
(*   - apply IHi in H; auto. *)
(* Qed. *)


(* Lemma seqFirst_spec2 : forall {n i : nat} (P : nat -> bool) r, *)
(*     seqFirst n i P = Some r -> (forall j, j < r -> P j = false). *)
(* Proof. *)
(*   intros n i. revert n. induction i; intros; simpl in *. easy. *)
(*   destruct (P (n - S i)) eqn:E1. *)
(*   - inversion H. split; auto. lia. *)
(*   - apply IHi in H; auto. lia. *)
(* Qed. *)

Lemma seqFirst_min : forall {n i : nat} (P : nat -> bool) r,
    seqFirst n i P = Some r -> n - i <= r.
Proof.
  intros n i. revert n. induction i; intros; simpl in *. easy.
  destruct (P (n - S i)).
  - inversion H. lia.
  - apply IHi in H; auto. lia.
Qed.

Lemma seqFirst_max : forall {n i : nat} (P : nat -> bool) r,
    0 < n -> seqFirst n i P = Some r -> r < n.
Proof.
  intros n i. revert n. induction i; intros; simpl in *. easy.
  destruct (P (n - S i)).
  - inversion H0. lia.
  - apply IHi in H0; auto.
Qed.


(* ############################################################################ *)
(** * Gauss elimination. *)
Section GaussElim.
  Context `{Field} `{Dec _ (@eq A)}.

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

  (* 为避免逆矩阵计算时的大量计算，使用抽象表示，可提高计算效率 *)
  Inductive RowOp {n} :=
  | ROnop
  | ROswap (i j : fin (S n))
  | ROscale (i : fin (S n)) (c : A)
  | ROadd (i j : fin (S n)) (c : A).

  Definition rowOps2mat {n} (l : list (@RowOp n)) : smat (S n) :=
    fold_right (fun op M =>
                 match op with
                 | ROnop => M
                 | ROswap i j => mrowSwap i j M
                 | ROscale i c => mrowScale i c M
                 | ROadd i j c => mrowAdd i j c M
                 end) mat1 l.

  (* ======================================================================= *)
  (** ** 某列的第一个非零元的行号 *)

  (** 第 j 列的从第 n-i 行开始往下的第 1 个非零元的行号 *)

  Definition firstNonzero {n} (M : smat (S n)) (i j : fin (S n))
    : option (fin (S n)) :=
    match seqFirst (S n) (S (fin2nat i))
            (fun i0 => if Aeqdec (M #i0 j) 0
                     then false else true) with
    | Some r => Some #r
    | _ => None
    end.

(* End GaussElim. *)
(* Section test. *)
(*   Let M : smat nat 3 := l2m 0 [[1;0;0];[0;1;0];[0;0;1]]. *)
(*   Notation firstNonzero := (@firstNonzero nat 0). *)
(*   Compute firstNonzero M #2 #0. *)
(*   Compute firstNonzero M #2 #1. *)
(*   Compute firstNonzero M #2 #2. *)
(*   Compute firstNonzero M #1 #0. *)
(*   Compute firstNonzero M #1 #1. *)
(*   Compute firstNonzero M #1 #2. *)
(*   Compute firstNonzero M #0 #0. *)
(*   Compute firstNonzero M #0 #1. *)
(*   Compute firstNonzero M #0 #2. *)
(* End test. *)
  
  (* (* 非零元行号最大不超过 n *) *)
  (* Lemma firstNonzero_max: forall {n} (M : smat (S n)) (i j r : fin (S n)), *)
  (*     firstNonzero M i j = Some r -> fin2nat r < S n. *)
  (* Proof. *)
  (*   intros. unfold firstNonzero in H1. destruct seqFirst as [r'|] eqn: Hr; try easy. *)
  (*   apply seqFirst_max in Hr; auto; try lia. inversion H1. *)
  (*   rewrite fin2nat_nat2finS; auto. *)
  (* Qed. *)
  
  (* (* 非零元行号最小值是 n - i *) *)
  (* Lemma firstNonzero_min: forall {n} (M : smat (S n)) (i j r : fin (S n)), *)
  (*     firstNonzero M i j = Some r -> S n - fin2nat i <= fin2nat r. *)
  (* Proof. *)
  (*   intros. unfold firstNonzero in H1. destruct seqFirst as [r'|] eqn: Hr; try easy. *)
  (*   inversion H1. *)
  (*   pose proof (seqFirst_max _ r' (Nat.lt_0_succ _) Hr). *)
  (*   pose proof (seqFirst_min _ r' Hr). *)
  (*   pose proof (fin2nat_lt (@nat2finS n r')). *)
  (*   rewrite fin2nat_nat2finS; auto. lia. *)
  (* Qed. *)


  (* ******************************************************************* *)
  (** ** 向下消元 *)
  
  (* 对矩阵M第j列的从(维数-i)的行开始向下消元，返回(变换阵,变换结果)，i初始为(维数-1) *)
  Fixpoint elimDown {n} (M : smat (S n)) (i : nat) (j : fin (S n))
    : list RowOp * smat (S n) :=
    match i with
    | O => ([], M)
    | S i' =>
        (* 递归时 i 从大到小，而 fi 是从小到大 *)
        let fi : fin (S n) := #(S n - i) in
        (* 是0则直接递归，不是0则消元后递归 *)
        let x : A := M $ fi $ j in
        if Aeqdec x 0
        then elimDown M i' j
        else
          (let M1 := mrowAdd fi j (-x)%A M in
           let (l', M2) := elimDown M1 i' j in
           (l' ++ [ROadd fi j (-x)%A], M2))
    end.
  
(* End GaussElim. *)
(* Section test. *)
(*   Import QcExt. *)
(*   Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult 1 _). *)
  
(*   (* 化阶梯形测试 *) *)
(* (*     [[  0; -2;  1];     [[  1;  0;  -2/3]; *) *)
(* (*      [  3;  0; -2];  =>  [  0;  1;  -1/2]; *) *)
(* (*      [ -2;  3;  0]]      [  0;  0;   1/6]] *) *)
(*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;2;3];[4;5;6];[7;8;9]]%Q). *)
(*   Compute m2l (snd (elimDown M 2 #0)). *)
(* End test. *)


  (* ******************************************************************* *)
  (** ** 化为行阶梯形 *)
  
  (* 将矩阵M化为行阶梯形，参数 i 初始为维数，递归时 i 递减，而 (维数-i) 递增。*)
  Fixpoint rowEchelon {n} (M : smat (S n)) (i : nat)
    : option (list RowOp * smat (S n)) :=
    match i with
    | O => Some ([], M)
    | S i' =>
        let fi : fin (S n) := #(S n - i) in
        (* 找出主元 *)
        match firstNonzero M #(i - 1) fi with
        | None => None (* 没有非零元，则该矩阵不可逆 *)
        | Some r =>
            (* 使主元行在当前行 *)
            let (op1, M1) :=
              (if r ??= fi
               then (ROnop, M)
               else (ROswap fi r, mrowSwap fi r M)) in
            (* 使主元是 1 *)
            let (op2, M2) :=
              (let c : A := M1 $ fi $ fi in
               if Aeqdec c 0
               then (ROnop, M1)
               else (ROscale fi (/c), mrowScale fi (/c) M1)) in
            (* 使主元以下都是 0 *)
            let (l3, M3) := elimDown M2 i' fi in
            (* 递归 *)
            match rowEchelon M3 i' with
            | None => None
            | Some (l4, M4) => Some (l4 ++ l3 ++ [op2; op1], M4)
            end
        end
    end.
  
(* End GaussElim. *)
(* Section test. *)

(*   Import QcExt. *)
(*   Notation firstNonzero := (firstNonzero (Azero:=0)). *)
(*   Notation rowEchelon := (@rowEchelon _ Qcplus 0 Qcopp Qcmult 1 Qcinv _). *)
(*   Notation rowEchelon2 := (@rowEchelon2 _ Qcplus 0 Qcopp Qcmult Qcinv _). *)
(*   Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult 1 _). *)
(*   Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1 _). *)
(*   Notation mmul := (@mmul _ Qcplus 0 Qcmult). *)
(*   Infix "*" := mmul : mat_scope. *)

  (* 行阶梯形
     [  0 -2  1]     [0    1/3  0]   [1 0 -2/3]
     [  3  0 -2]  => [-1/2   0  0] * [0 1 -1/2]
     [ -2  3  0]     [9      4  6]   [0 0    1] *)
(*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[0;-2;1];[3;0;-2];[-2;3;0]]%Q). *)
(*   Let M1 : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;0;-2/3];[0;1;-1/2];[0;0;1]]%Q). *)
(*   Let E1 : smat Qc 3 := l2m 0 (Q2Qc_dlist [[0;1/3;0];[-1/2;0;0];[9;4;6]]%Q). *)

(*   (* 使用抽象表示速度会比较快 *) *)
(*   Goal match rowEchelon2 M 3 with *)
(*        | Some (l1',M1') => m2l (rowOps2mat l1') = m2l E1 *)
(*                           /\ m2l M1' = m2l M1 *)
(*        | _ => True *)
(*        end. *)
(*   Proof. *)
(*     Time cbv; split; list_eq; f_equal; apply proof_irrelevance. *)
(*   Qed. *)

(*   (* 具体矩阵表示速度较慢 *) *)
(*   Goal match rowEchelon M 3 with *)
(*        | Some (E1',M1') => m2l E1' = m2l E1 *)
(*                           (* /\ m2l M1' = m2l M1 *) *)
(*        | _ => True *)
(*        end. *)
(*   Proof. *)
(*     (* Time cbv. *) *)
(*   Abort. *)

(*   (* 验证 E1 将 M 变换到了 M1 *) *)
(*   Goal (E1 * M)%M = M1. *)
(*   Proof. apply m2l_inj. cbv. list_eq; f_equal. Qed. *)

(* End test. *)

  (* ******************************************************************* *)
  (** ** 向上消元 *)
  
  (* 对矩阵M第j列的从i行开始向上消元，返回(变换阵,变换结果)，i初始为(维数-1) *)
  Fixpoint elimUp {n} (M : smat (S n)) (i : nat) (j : fin (S n))
    : list RowOp * smat (S n) :=
    match i with
    | O => ([], M)
    | S i' =>
        (* 如果 M[i',j] <> 0，则 j 行的 -M[i',j] 倍加到 i' 行 *)
        let fi : fin (S n) := #i' in
        let x : A := (M $ fi $ j) in
        if Aeqdec x 0
        then elimUp M i' j
        else
          let (op1, M1) := (ROadd fi j (-x)%A, mrowAdd fi j (-x)%A M) in
          let (l2, M2) := elimUp M1 i' j in
          (l2 ++ [op1], M2)
    end.
  
(* End GaussElim. *)
(* Section test. *)

(*   Import QcExt. *)
(*   Notation elimUp := (@elimUp _ Qcplus 0 Qcopp Qcmult 1 _). *)
  
(*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;2;3];[4;5;6];[7;8;1]]%Q). *)
(*   Compute m2l (snd (elimUp M 2 #2)). *)
(* End test. *)
  

  (* ******************************************************************* *)
  (** ** 最简行阶梯形矩阵 *)

  (* 将矩阵M化为行最简阶梯形，参数 i 初始为维数 *)
  Fixpoint minRowEchelon {n} (M : smat (S n)) (i : nat) : list RowOp * smat (S n) :=
    match i with
    | O => ([], M)
    | S i' =>
        let fi : fin (S n) := #i' in
        let (l1, M1) := elimUp M i' fi in
        let (l2, M2) := minRowEchelon M1 i' in
        (l2 ++ l1, M2)
    end.
  
(* End GaussElim. *)
(* Section test. *)
(*   Import QcExt. *)
(*   Notation minRowEchelon := (@minRowEchelon _ Qcplus 0 Qcopp Qcmult 1 _). *)
(*   Notation minRowEchelon2 := (@minRowEchelon _ Qcplus 0 Qcopp Qcmult _). *)
(*   Notation elimUp := (@elimUp _ Qcplus 0 Qcopp Qcmult 1 _). *)
(*   Notation mmul := (@mmul _ Qcplus 0 Qcmult). *)
(*   Infix "*" := mmul : mat_scope. *)
(*   Notation mat1 := (@mat1 _ 0 1). *)
  
(*   (* 简化行阶梯形 *)
(*      [1 0 -2/3]     [1  0  2/3]   [1 0 0] *)
(*      [0 1 -1/2]  => [0  1  1/2] * [0 1 0] *)
(*      [0 0    1]     [0  0    1]   [0 0 1] *) *)
(*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;0;-2/3];[0;1;-1/2];[0;0;1]]%Q). *)
(*   Let E1 := fst (minRowEchelon M 3). *)
(*   Let M1 := snd (minRowEchelon M 3). *)

(*   Goal (E1 * M)%M = M1. *)
(*   Proof. apply m2l_inj. cbv. list_eq. Qed. *)
(* End test. *)
  
  (* ******************************************************************* *)
  (** ** 计算逆矩阵 *)

  (* 计算逆矩阵(option版本) *)
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

(* 抽取代码测试 *)
End GaussElim.

Definition minvGE_R := @minvGE _ Rplus R0 Ropp Rmult R1 Rinv R_eq_Dec.
Require Import ExtrOcamlBasic ExtrOcamlNatInt.
Require Import MyExtrOCamlR.

(** two float numbers are comparison decidable *)
Extract Constant total_order_T => "fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c < 0 then Some true
  else (if c = 0 then None else Some false)".

Extract Constant Req_dec_T => "fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c = 0 then true
  else false".

Recursive Extraction minvGE_R.
  Extraction "ocaml_test/matrix.ml" minvGE_R m2l l2m.
  
?
(* Print sumbool. *)
Check total_order_T.
Check Req_dec_T.

Check minvGE.
 
End A.
Sect

  (* 在Coq中直接计算逆矩阵的测试 *)
End GaussElim.
Section test.
  Import QcExt.
  Notation mat1 := (@mat1 _ 0 1).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Infix "*" := mmul : mat_scope.
  Notation minvGE := (@minvGE _ Qcplus 0 Qcopp Qcmult 1 Qcinv _).

  (* 输入和输出都是 list 的逆矩阵求解 *)
  Definition minvGE_Qclist (n : nat) (l : list (list Q)) : list (list Q) :=
    Qc2Q_dlist (m2l (@minvGE n (l2m 0 (Q2Qc_dlist l)))).

  Open Scope Q_scope.
  
  (* [ 1  2]     [ 3  2]
     [-1 -3] <-> [-1 -1] *)
  (* Compute minvGE_Qclist 2 [[1;2];[-1;-3]]. *)
  
  (* [1 3 1]     [-1 -1  2]
     [2 1 1] <-> [ 0 -1  1]
     [2 2 1]     [ 2  4 -5] *)
  (* Compute minvGE_Qclist 3 [[1;3;1];[2;1;1];[2;2;1]]. *)

  (* [  0 -2  1]     [6 3 4]
     [  3  0 -2] <-> [4 2 3]
     [ -2  3  0]     [9 4 6] *)
  (* Compute minvGE_Qclist 3 [[0;-2;1];[3;0;-2];[-2;3;0]]. *)

  (* 一个8阶矩阵，手动构造的 *)
  (* Compute minvGE_Qclist 8 *)
  (*   [[1;2;3;4;5;6;7;8]; *)
  (*    [2;4;5;6;7;8;9;1]; *)
  (*    [3;5;7;6;8;4;2;1]; *)
  (*    [4;5;7;6;9;8;3;2]; *)
  (*    [5;4;3;7;9;6;8;1]; *)
  (*    [6;5;3;4;7;8;9;2]; *)
  (*    [7;8;6;5;9;2;1;3]; *)
  (*    [8;9;6;3;4;5;2;1]]. *)
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
  (* Compute minvGE_Qclist 8 *)
  (*   [[0.8001;0.5797;0.0760;0.9448;0.3897;0.0598;0.7317;0.1835]; *)
  (*    [0.4314;0.5499;0.2399;0.4909;0.2417;0.2348;0.6477;0.3685]; *)
  (*    [0.9106;0.1450;0.1233;0.4893;0.4039;0.3532;0.4509;0.6256]; *)
  (*    [0.1818;0.8530;0.1839;0.3377;0.0965;0.8212;0.5470;0.7802]; *)
  (*    [0.2638;0.6221;0.2400;0.9001;0.1320;0.0154;0.2963;0.0811]; *)
  (*    [0.1455;0.3510;0.4173;0.3692;0.9421;0.0430;0.7447;0.9294]; *)
  (*    [0.1361;0.5132;0.0497;0.1112;0.9561;0.1690;0.1890;0.7757]; *)
  (*    [0.8693;0.4018;0.9027;0.7803;0.5752;0.6491;0.6868;0.4868]]. *)
End test.

(*

?
.  (* 第j列的第i行以下元素都是0 *)
  (* Definition belowElemsAllZero {r c} (M : mat r c) (i : fin r) (j : fin c) : bool := *)
  (*   @vsum _ andb true _ *)
  (*     (fun k => *)
  (*        if fin2nat k ??<= fin2nat i *)
  (*        then true *)
  (*        else Aeqb (M $ k $ j) Azero). *)
  (* forallb (fun k => Aeqb (M $ k $ j) Azero) (seq (S i) (r - (S i))). *)
  
  (* 第j列的第i行以下所有元素进行消元 *)
  Definition elim0Below {r c} (p : list RowOp * mat (S r) (S c))
    (i : fin (S r)) (j : fin (S c)) : list RowOp * mat (S r) (S c) :=
    let fix F (fuel : nat) (p : list RowOp * mat (S r) (S c)) (k : fin (S r))
      : list RowOp * mat (S r) (S c) :=
      match fuel with
      | O => p
      | S fuel' =>
          let coef : A := (- (snd p) $ k $ j / (snd p) $ i $ j)%A in
          (* 若元素为0，则不需要变换 *)
          if Aeqb coef Azero
          then F fuel' p (fin2SameRangeSucc k)
          else F fuel' (RTadd i k coef :: fst p, mrowAdd (snd p) i k coef)
                 (fin2SameRangeSucc k)
      end in
    F r p (fin2SameRangeSucc i).

  (* 第i行的第j列右侧所有元素进行消元 *)
  Definition elim0Right {r c} (p : list RowOp * mat (S r) (S c))
                        (pivots : @vec (option (fin (S r))) (S c))
                        (i : fin (S r)) (j : fin (S c))
    : list RowOp * mat (S r) (S c) :=
    let fix F (fuel : nat) (p : list RowOp * mat (S r) (S c)) (k : fin (S c))
      : list RowOp * mat (S r) (S c) :=
      match fuel with
      | O => p
      | S fuel' =>
          let ele : A := (snd p) $ i $ k in
          (* 若元素为0，则不需要变换 *)
          if Aeqb ele Azero
          then F fuel' p (fin2SameRangeSucc k)
          else
            (* 找到当前列的主元：若没找到则结束循环，找到后做消元 *)
            match pivots $ k with
            | None => p
            | Some i' => 
                let coef := - ele in
                F fuel' 
                  (RTadd i' i coef :: fst p, mrowAdd (snd p) i' i coef)
                  (fin2SameRangeSucc k)
            end
      end in
    F c p (fin2SameRangeSucc j).
  

  (** 序列中的指标严格递增. 即：从头到尾遍历序列中的元素时，
      (1) 若元素是None，则其余元素都必须是 None
      (2) 否则当前元素是Some i的形式，然后下一个元素必须是两种情形之一，
          要么是 None，要么是 Some j的形式（其中，i < j）。*)
  Fixpoint idxStrictInc (s : nat -> option nat) (n : nat) (olast : option nat) : bool :=
    (* 此处的算法是倒序遍历的，即：从尾到头遍历序列中的元素，
       并使用辅助变量 olast 表示上次的元素值（初始时为 None)。
       * 当olast是None，继续
       * 当olast是Some j，当前是None，则出错
       * 当olast是Some j, 当前是Some i，则必须 i < j，并接着检查剩下的元素。*)
    match n with
    | S n' =>
        match olast, s n' with
        | None, _ => idxStrictInc s n' (s n')
        | Some i, None => false
        | Some i, Some j => (j <? i) && (idxStrictInc s n' (s n'))
        end
    | O => true
    end.

  Section test.
    Let s (i : nat) : option nat :=
          match i with
          | 0 => Some 0
          | 3 => Some 3
          | _ => None
          end.
    (* Compute idxStrictInc s 3 None. *)
    (* Compute idxStrictInc s 5 None. *)
  End test.
  
  Definition vidxStrictInc {n s : nat} (v : @vec (option (fin n)) s) : bool :=
    let oi2i (oi : option (fin n)) : option nat :=
      match oi with Some i => Some (fin2nat i) | _ => None end in
    idxStrictInc (v2f None (vmap oi2i v)) s None.
  
  (** 是否为(行)阶梯形矩阵 *)
  Definition MatEchelon {r c} (M : mat r c) : bool :=
    vidxStrictInc (vmap (vfirst (fun x => negb (Aeqb x Azero))) M).
  
  (** 转换为阶梯形矩阵
      步骤：
      1. 如果输入的矩阵是0行或0列，则直接返回输入的矩阵。
      2. 矩阵元素索引(i,j)从(0,0)开始递增遍历，当无法递增时则结束。
      a. 找出第j列的从第i行开始的第一个非零元，
      b. 若没有非零元，则使用(i, S j)递归
      c. 否则在(i',j)处找到了非零元。
      d. 若i和i'不相等，则交换i,i'两行。
      e. 接着，把第j列的第i'行以下的所有元素进行消元
      f. 然后递归(S i, S j)
 *)
  Definition echelon {r c} : mat r c -> list (@RowOp r) * mat r c :=
    match r, c with
    | O, _ => fun m => ([], m)
    | _, O => fun m => ([], m)
    | S r, S c =>
        fun m =>
          let fix F (fuel:nat) (p : list RowOp * mat (S r) (S c))
                (i : fin (S r)) (j : fin (S c)) {struct fuel}
            : list RowOp * mat (S r) (S c) :=
            match fuel with
            | O => p
            | S fuel' =>
                (* 如果行列到达边界则结束 *)
                if (fin2nat i >=? r) || (fin2nat j >=? c)
                then p
                else
                  (* 找到第j列的第i行开始的第一个非零元 *)
                  match vfirstNonZeroFrom (fun i => (snd p) $ i $ j) i with
                  | None =>
                      (* 若该列没有非零元，则查找下一列 *)
                      F fuel' p i (fin2SameRangeSucc j)
                  | Some i' =>
                      (* 若 i <> i'，则交换 *)
                      let p1 : list RowOp * mat (S r) (S c) :=
                        if i ??= i'
                        then p
                        else (ROswap i i' :: (fst p),
                               mrowSwap (snd p) i i') in
                      (* 第j列的第i行以下所有元素进行消元 *)
                      let p2 : list RowOp * mat (S r) (S c) :=
                        elim0Below p1 i j in
                      (* 进入下一行下一列 *)
                      F fuel' p2 (fin2SameRangeSucc i) (fin2SameRangeSucc j)
                  end
            end
          in
          F (r + c) ([], m) fin0 fin0
    end.

  (* 简化行阶梯形矩阵，也称“行最简阶梯形矩阵”：
     1. 它是阶梯形矩阵
     2. 每个非零行的主元都是1
     3. 每个主元所在的列的其余元素都是0
   *)
  (* Definition MatMinEchelon {r c} (M : mat r c) : bool. *)
  
  (* 将阶梯形矩阵转换为行最简阶梯形矩阵
     流程：
      1. 如果输入的矩阵M(r,c)是0行或0列，则直接返回输入的矩阵。
      2. 矩阵行号i从r开始递减遍历，当无法递减时则结束。
      a. 找出第i行的第1个非零元，
      b. 若没有非零元，则使用pred i递归
      c. 否则在(i,j)找到了非零元。
      d. 若(i,j)处不是1，则使用 mrowScale 变换为1
      e. 把第i行的第j列右侧的所有元素进行消元
      消元时的做法：数组pivots记录了每列的主元编号，初始为None，随着递归而逐步填充。
      f. 用(pred i)递归
   *)
  Definition minEchelon {r c} : mat r c -> list (@RowOp r) * mat r c :=
    match r, c with
    | O, _ => fun m => ([], m)
    | _, O => fun m => ([], m)
    | S r, S c =>
        fun m =>
          let fix F (fuel : nat) (p : list RowOp * mat (S r) (S c))
                (pivots : @vec (option (fin (S r))) (S c))
                (i : fin (S r)) {struct fuel}
            : list (@RowOp (S r)) * mat (S r) (S c) :=
            match fuel with
            | O => p
            | S fuel' =>
                (* 找出第i行第1个非零元 *)
                match vpivot (m $ i) with
                | None =>
                    (* 若本行全部为零，则向上一行 *)
                    if Nat.eqb (fin2nat i) 0 then p else
                      F fuel' p pivots (fin2SameRangePred i)
                | Some j =>
                    let pivots' := vset pivots j (Some i) in
                    let pivot : A := m $ i $ j in
                    (* 若主元不是1，则先变换为1 *)
                    let p1 : list RowOp * mat (S r) (S c) :=
                      match Aeqb pivot Aone with
                      | true => p 
                      | _ =>
                          let coef : A := Aone / pivot in
                          (ROscale i coef :: fst p, mrowScale (snd p) i coef)
                      end in
                    (* 对第i行的第j列右侧消元 *)
                    let p2 : list RowOp * mat (S r) (S c) :=
                      elim0Right p1 pivots i j in
                    if Nat.eqb (fin2nat i) 0 then p2 else 
                      F fuel' p2 pivots' (fin2SameRangePred i)
                end
            end in
          F (S r) ([], m) (vzero None) #r
    end.
  
End GaussElim.

Section test.
  Import QcExt.
  Notation mat1 := (@mat1 Qc 0 1).
  Notation MatEchelon := (MatEchelon (Azero:=0)).
  Notation elim0Below := (@elim0Below _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation elim0Right := (@elim0Right _ Qcplus 0 Qcopp Qcmult).

  Notation echelon := (@echelon _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation minEchelon := (@minEchelon _ Qcplus 0 Qcopp Qcmult 1 Qcinv).

  (* 临时测试 *)
  Section ex0.
    Let M1 : mat Qc 3 3 := l2m 0 (Q2Qc_dlist [[1;2;3];[2;1;0];[3;4;6]]%Q).
    (* Compute MatEchelon M1. *)
    (* Compute fst (echelon M1). *)
    (* Compute m2l (snd (echelon M1)). *)
    (* Compute m2l (snd (minEchelon (snd (echelon M1)))). *)

    (* 逆矩阵的例子
   [a b]      1/(ad-bc) [d -b]
   [c d] <->            [-c a]

   [ 1  2]     [ 3  2]
   [-1 -3] <-> [-1 -1]
     *)
    Let M2 : mat Qc 2 2 := l2m 0 (Q2Qc_dlist [[1;2];[-1;-3]]%Q).
    (* Compute m2l (snd (echelon M2)). *)
    (* Compute m2l (snd (minEchelon (snd (echelon M1)))). *)
  End ex0.

  (* 测试：将第j列的第i行以下全部化为0 *)
  Section ex1.
    (*
      来自《线性代数》同济，第5版，P60, B1->B2
      将 B1 第1列的第1行以下全部化为0，得到B2。

      B1 = 
       [[1;  1; -2;  1;  4];
        [2; -1; -1;  1;  2];
        [2; -3;  1; -1;  2];
        [3;  6; -9;  7;  9]]

      B2 = 
       [[1;  1; -2;  1;  4];
        [0; -3;  3; -1; -6];
        [0; -5;  5; -3; -6];
        [0;  3; -3;  4; -3]]
     *)
    Let r : nat := 4. Let c : nat := 5.
    Let i : nat := 0. Let j : nat := 0.
    Let M1 : mat Qc r c :=
        l2m 0
          (Q2Qc_dlist
             [[1;  1; -2;  1;  4];
              [2; -1; -1;  1;  2];
              [2; -3;  1; -1;  2];
              [3;  6; -9;  7;  9]]%Q).
    Let M2 : mat Qc r c :=
        l2m 0
          (Q2Qc_dlist
             [[1;  1; -2;  1;  4];
              [0; -3;  3; -1; -6];
              [0; -5;  5; -3; -6];
              [0;  3; -3;  4; -3]]%Q).
    Goal snd (elim0Below ([], M1) (nat2finS 0) (nat2finS 0)) = M2.
    Proof. apply m2l_inj. auto. Qed.
  End ex1.
  
  (* 高斯消元测试 *)
  Section ex2.
    (*
      来自《线性代数》同济，第5版，P64，例1
      [[  2; -1; -1];
       [  1;  1; -2];
       [  4; -6;  2]]

      [[  2;  -1;   -1];
       [  0; 3/2; -3/2];
       [  4;   0;    0]]
    
     *)
    Let r : nat := 3. Let c : nat := 3.
    Let M1 : mat Qc r c :=
        l2m 0
          (Q2Qc_dlist
             [[  2; -1; -1];
              [  1;  1; -2];
              [  4; -6;  2]]%Q).
    Let M2 : mat Qc r c :=
        l2m 0
          (Q2Qc_dlist
             [[  2;  -1;   -1];
              [  0; 3/2; -3/2];
              [  0;   0;    0]]%Q).
    Goal m2l (snd (echelon M1)) = m2l M2.
    Proof. cbv. auto. Qed.

    Let M3 : mat _ r c :=
        l2m 0
          (Q2Qc_dlist
             [[  1;  0; -1];
              [  0;  1; -1];
              [  0;  0;  0]]%Q).
    Goal m2l (snd (minEchelon M2)) = m2l M3.
    Proof. cbv. list_eq; f_equal; apply UIP. Qed.
  End ex2.

  (* 高斯消元测试 *)
  Section ex3.
    (*
      来自《线性代数》同济，第5版，P64，例2
      [[  0; -2;  1];
       [  3;  0; -2];
       [ -2;  3;  0]]

      [[  3;  0;  -2];
       [  0; -2;   1];
       [  0;  0; 1/6]]
     *)
    Let r : nat := 3. Let c : nat := 3.
    Let M1 : mat _ r c :=
        l2m 0
          (Q2Qc_dlist
             [[  0; -2;  1];
              [  3;  0; -2];
              [ -2;  3;  0]]%Q).
    Let M2 : mat _ r c :=
        l2m 0
          (Q2Qc_dlist
             [[  3;  0;  -2];
              [  0; -2;   1];
              [  0;  0; 1/6]]%Q).
    Goal m2l (snd (echelon M1)) = m2l M2.
    Proof. cbv. auto. Qed.

    Let M3 : mat _ r c :=
        l2m 0
          (Q2Qc_dlist
             [[  1;  0; 0];
              [  0;  1; 0];
              [  0;  0; 1]]%Q).
    Goal m2l (snd (minEchelon M2)) = m2l M3.
    Proof. cbv. list_eq; f_equal; apply UIP. Qed.
  End ex3.

  (* 高斯消元测试 *)
  Section ex4.
    Goal echelon (@mat1 1) = ([], mat1).
    Proof. cbv. auto. Qed.
    
    Goal echelon (@mat1 2) = ([], mat1).
    Proof. cbv. auto. Qed.
    
    Goal echelon (@mat1 3) = ([], mat1).
    Proof. cbv. auto. Qed.

    Example M : mat Qc 5 5 :=
      l2m 0
        (Q2Qc_dlist
           [[0.1622; 0.4505; 0.1067; 0.4314; 0.853; 0.4173; 0.7803; 0.2348; 0.547; 0.9294];
            [0.7943; 0.0838; 0.9619; 0.9106; 0.6221; 0.0497; 0.3897; 0.3532; 0.2963; 0.7757];
            [0.3112; 0.229; 0.0046; 0.1818; 0.351; 0.9027; 0.2417; 0.8212; 0.7447; 0.4868];
            [0.5285; 0.9133; 0.7749; 0.2638; 0.5132; 0.9448; 0.4039; 0.0154; 0.189; 0.4359];
            [0.1656; 0.1524; 0.8173; 0.1455; 0.4018; 0.4909; 0.0965; 0.043; 0.6868; 0.4468];
            [0.602; 0.8258; 0.8687; 0.1361; 0.076; 0.4893; 0.132; 0.169; 0.1835; 0.3063];
            [0.263; 0.5383; 0.0844; 0.8693; 0.2399; 0.3377; 0.9421; 0.6491; 0.3685; 0.5085];
            [0.6541; 0.9961; 0.3998; 0.5797; 0.1233; 0.9001; 0.9561; 0.7317; 0.6256; 0.5108];
            [0.6892; 0.0782; 0.2599; 0.5499; 0.1839; 0.3692; 0.5752; 0.6477; 0.7802; 0.8176];
            [0.7482; 0.4427; 0.8001; 0.145; 0.24; 0.1112; 0.0598; 0.4509; 0.0811; 0.7948];
            [0.7482; 0.4427; 0.8001; 0.145; 0.24; 0.1112; 0.0598; 0.4509; 0.0811; 0.7948]]%Q).
    (* time: 0.8s *)
    (* time: 4.8s *)
    (* time: 0.128s *)
    (* Time Compute (m2l (snd (echelon(M)))). *)

    (* time: 0.36s *)
    (* time: 0.276s *)
    (* Time Compute (m2l (snd (minEchelon(snd (echelon(M)))))). *)
  End ex4.

  (* 这个例子说明了“阶梯形矩阵的台阶并非一样长”，需要特别考虑 *)
  Section ex5.
    Let r : nat := 3. Let c : nat := 4.
    Let M1 : mat Qc r c :=
        l2m 0
          (Q2Qc_dlist
             [[1;1;1;1];
              [0;0;1;1];
              [0;0;0;1]]%Q).
    Goal m2l (snd (echelon (M1))) = m2l M1.
    Proof. cbv. auto. Qed.
  End ex5.
  
End test.

(* Recursive Extraction echelon minEchelon. *)
*)
