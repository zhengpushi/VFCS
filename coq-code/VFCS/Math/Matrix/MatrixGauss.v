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


(* ======================================================================= *)
(** ** 初等行变换 *)

(** 初等行变换的操作 *)
Inductive RowOp {A} {r:nat} :=
| RowOp_Swap (i j : fin r)          (* 交换 i, j 两行，记作 <i,j> *)
| RowOp_K (i : fin r) (k : A)       (* 用非零数 k 乘以第 i 行，记作 k * i *)
| RowOp_KAdd (i j : fin r) (k : A)  (* 第 i 行的 k 倍加到第 j 行，记作 j + k * i *)
.

(* ======================================================================= *)
(** ** Gauss elimination. *)
Section GaussElim.
  Context `{Field} `{Dec _ (@eq A)}.

  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mrowSwap := (@mrowSwap A).
  Notation mrowK := (@mrowK _ Amul).
  Notation mrowKAdd := (@mrowKAdd _ Aadd Amul).
  Notation mrow := (@mrow _ Azero).
  Notation Aeqb := (@Acmpb _ (@eq A) _).
  Notation vfirstNonZeroFrom := (@vfirstNonZeroFrom _ _ Azero).
  Notation vfirstNonZero := (@vfirstNonZero _ _ Azero).
  Notation RowOp := (@RowOp A).

  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun a b => a * / b) : A_scope.
  Infix "*" := mmul : mat_scope.

  (* 行变换操作转为矩阵 *)
  Definition rowOp2mat {r:nat} (ro : RowOp) : smat r :=
    match ro with
    | RowOp_Swap i j => mrowSwap mat1 i j
    | RowOp_K i k => mrowK mat1 i k
    | RowOp_KAdd i j k => mrowKAdd mat1 i j k
    end.
  
  (* 行变换操作的列表转为单个矩阵。
     eg: [op1;op2;op3] => m(op1)*m(op2)*m(op3)*mat1  *)
  Definition rowOpList2mat {r:nat} (ops : list RowOp) : smat r :=
    fold_right (fun op M => (rowOp2mat op) * M) mat1 ops.

  (* 第j列的第i行以下元素都是0 *)
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
          else F fuel' (RowOp_KAdd i k coef :: fst p, mrowKAdd (snd p) i k coef)
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
                  (RowOp_KAdd i' i coef :: fst p, mrowKAdd (snd p) i' i coef)
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
    vidxStrictInc (vmap (vfirstIdx (fun x => negb (Aeqb x Azero))) M).
  
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
                        else (RowOp_Swap i i' :: (fst p),
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
      d. 若(i,j)处不是1，则使用 mrowK 变换为1
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
                match vfirstNonZero (m $ i) with
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
                          (RowOp_K i coef :: fst p, mrowK (snd p) i coef)
                      end in
                    (* 对第i行的第j列右侧消元 *)
                    let p2 : list RowOp * mat (S r) (S c) :=
                      elim0Right p1 pivots i j in
                    if Nat.eqb (fin2nat i) 0 then p2 else 
                      F fuel' p2 pivots' (fin2SameRangePred i)
                end
            end in
          F (S r) ([], m) (vzero None) (nat2finS r)
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
