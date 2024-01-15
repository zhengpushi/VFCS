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
(** ** 基于列表的自然数字典 *)
Section LDictNat.
  Definition LDict := LDict nat nat.
  Definition ldictEmpty : LDict := ldictEmpty _ _.
  Definition ldictAdd x d : LDict := ldictAdd _ _ Nat.eqb x d.
  Definition ldictFind k d : option nat := ldictFind _ _ Nat.eqb k d.

  (* 对于字典，以任何顺序加入都不影响查询结果 *)
  Let ex1 : LDict :=
        ldictAdd (0,0)
          (ldictAdd (1,2)
             (ldictAdd (2,3)
                ldictEmpty)).
  Let ex2 : LDict := ldictAdd (2,3) (ldictAdd (1,2) (ldictAdd (0,0) ldictEmpty)).

  Goal forall k, ldictFind k ex1 = ldictFind k ex2.
  Proof.
    destruct k; cbn; auto.
    destruct k; cbn; auto.
  Qed.
End LDictNat.


(* ======================================================================= *)
(** ** Gauss elimination. *)
Section GaussElim.
  Context `{Field} `{Dec _ (@eq A)}.

  (** 初等行变换的操作 *)
  Inductive RowOp {A} {r:nat} :=
  | RowOp_Swap (i j : fin r)          (* 交换 i, j 两行，记作 <i,j> *)
  | RowOp_K (i : fin r) (k : A)       (* 用非零数 k 乘以第 i 行，记作 k * i *)
  | RowOp_KAdd (i j : fin r) (k : A)  (* 第 i 行的 k 倍加到第 j 行，记作 j + k * i *)
  .

  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun a b => a * / b) : A_scope.
  
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mrowSwap := (@mrowSwap A).
  Notation mrowK := (@mrowK _ Amul).
  Notation mrowKAdd := (@mrowKAdd _ Aadd Amul).
  Notation mrow := (@mrow _ Azero).
  Notation Aeqb := (@Acmpb _ (@eq A) _).
  Notation listFirstNonZero := (@listFirstNonZero A Azero Aeqb).

  (* 行变换操作转为矩阵 *)
  Definition rowOp2mat {n:nat} (ro : RowOp) : @smat A n :=
    match ro with
    | RowOp_Swap i j => mrowSwap mat1 i j
    | RowOp_K i k => mrowK mat1 i k
    | RowOp_KAdd i j k => mrowKAdd mat1 i j k
    end.
  
  (* 行变换操作的列表转为单个矩阵。
     eg: [op1;op2;op3] => m(op1)*m(op2)*m(op3)*mat1  *)
  Definition rowOpList2mat {n:nat} (ops : list (@RowOp A n)) : @smat A n :=
    fold_right (fun op M => mmul (rowOp2mat op) M) mat1 ops.

  (* 第j列的第i行以下元素都是0 *)
  Let belowElemsAllZero {r c} (M : @mat A r c) (i : fin r) (j : fin c) : bool :=
    @vsum _ andb true _
      (fun k =>
         if (fin2nat k) ??<= (fin2nat i)
         then true
         else Aeqb (M $ k $ j) Azero).
  (* forallb (fun k => Aeqb (M $ k $ j) Azero) (seq (S i) (r - (S i))). *)

  (* 第j列的第i行开始往下，第1个不为0的行号 *)
  Definition firstNonZeroRowIdx {r c} (M : mat A r c) (i : fin r) (j : fin c)
    : option (fin r) :=
    let fix F (fuel:nat) (i0 : fin r) : option (fin r) :=
      match fuel with
      | O => None
      | S fuel' =>
          if negb (Aeqb (M $ i0 $ j) Azero)
          then Some i0
          else F fuel' (fin2SameRangeSucc i0)
      end in
    F r i.

  (** * nat版本的实现，供参考 *)
  (*
  (* 高斯消元法：计算阶梯形矩阵 *)
  Definition rowEchelon {r c} (m : mat r c) : (list RowOp * mat r c) :=
    let fix F (fuel:nat) (params : list RowOp * mat r c) (i j : nat) {struct fuel}
      : list RowOp * mat r c :=
      match fuel with
      | O => params
      | S fuel' =>
          if (i >=? r) || (j >=? c)
          then params
          else 
            match firstNonZeroRowIdx (snd params) i j with
            | None => F fuel' params i (S j)
            | Some i' =>
                (* 若 i <> i'，则交换 *)
                let params1 : list RowOp * mat r c :=
                  if i =? i'
                  then params
                  else (RowOp_Swap i i' :: (fst params),
                         mrowSwap (snd params) i i') in
                (* 第j列的第i行以下所有行做 KAdd 变换 *)
                let params2 : list RowOp * mat r c :=
                  fold_left (fun (p:list RowOp*mat r c) (k:nat) =>
                               let coef : A := (- (snd p) $ k $ j / (snd p) $ i $ j)%A in
                               (* 若元素为0，则不需要变换 *)
                               if (Aeqb coef Azero)
                               then p
                               else (RowOp_KAdd i k coef :: fst p,
                                      mrowKAdd (snd p) i k coef))
                    (seq (S i) (r - S i)) params1 in
                (* 递归 *)
                F fuel' params2 (S i) (S j)
            end
      end
    in
    F r ([], m) 0 0.

  (* 高斯消元法：从阶梯形矩阵计算行最简阶梯形矩阵 *)
  Definition minRowEchelon {r c} (m : mat r c) : (list (@RowOp A) * mat r c) :=
    let fix F (params : list RowOp * mat r c) (pivots : LDict) (i : nat) {struct i}
      : list RowOp * mat r c :=
      match i with
      | O => params
      | S i =>
          let oNonZeroColId : option nat := listFirstNonZero (mrow m i) in
          match oNonZeroColId with
          | None => F params pivots i
          | Some j =>
              let pivotsNew : LDict := ldictAdd (j,i) pivots in
              let pivot : A := m $ i $ j in
              (* 若主元不是i，则做一次 rowK 变换 *)
              let params1 : list RowOp * mat r c :=
                match Aeqb pivot Aone with
                | true => params 
                | _ =>
                    let coef1 : A := Aone / pivot in
                    (RowOp_K i coef1 :: fst params, mrowK (snd params) i coef1)
                end in
              (* 第i行的第j列右侧准备消元 *)
              let params2 : list RowOp * mat r c :=
                fold_left (
                    fun (p:list RowOp*mat r c) (j':nat) =>
                      let ele : A := (snd p) $ i $ j' in
                      match Aeqb ele Azero with
                      | true => p
                      | _ =>
                          let oExistPivot : option nat := ldictFind j' pivots in
                          match oExistPivot with
                          | None => p
                          | Some i' =>
                              let coef2 := - ele in
                              (RowOp_KAdd i' i coef2 :: fst p,
                                mrowKAdd (snd p) i' i coef2)
                          end
                      end)
                  (seq (S j) (c - S j)) params1 in
              F params2 pivotsNew i
          end
      end in
    F ([], m) ldictEmpty r.
   *)
  
  (* 高斯消元法：计算阶梯形矩阵 *)
(*  Definition rowEchelon {r c} (m : mat A r c) : (list RowOp * mat A r c) :=
    let fix F (fuel:nat) (params : list RowOp * mat A r c)
          (i : fin r)(j : fin c) {struct fuel} : list RowOp * mat A r c :=
      match fuel with
      | O => params
      | S fuel' =>
          if (fin2nat i >=? r) || (fin2nat j >=? c)
          then params
          else 
            match firstNonZeroRowIdx (snd params) i j with
            | None => F fuel' params i (fin2SameRangeSucc j)
            | Some i' =>
                (* 若 i <> i'，则交换 *)
                let params1 : list RowOp * mat A r c :=
                  if finEqdec i i'
                  then params
                  else (RowOp_Swap i i' :: (fst params),
                         mrowSwap (snd params) i i') in
                (* 第j列的第i行以下所有行做 KAdd 变换 *)
                let params2 : list RowOp * mat A r c :=
                  fold_left (fun (p:list RowOp*mat A r c) (k : fin r) =>
                               let coef : A := (- (snd p) $ k $ j / (snd p) $ i $ j)%A in
                               (* 若元素为0，则不需要变换 *)
                               if (Aeqb coef Azero)
                               then p
                               else (RowOp_KAdd i k coef :: fst p,
                                      mrowKAdd (snd p) i k coef))
                    (* (seq (S (fin2nat i)) *)
                    (*    (r - S (fin2nat i))) *)
                            _

                    params1 in
                (* 递归 *)
                F fuel' params2 (fin2SameRangeSucc i) (fin2SameRangeSucc j)
            end
      end
    in
    F r ([], m) fin0 fin0.
 *)
  Parameter rowEchelon :
    forall (Aadd:A->A->A)(Azero:A)(Aopp:A->A)
      (Amul:A->A->A)(Ainv:A->A)
      (H:Dec (@eq A))
      {r c} (M : mat A r c), (list (@RowOp A r) * mat A r c).
  
  (* 高斯消元法：从阶梯形矩阵计算行最简阶梯形矩阵 *)
  Parameter minRowEchelon :
    forall (Aadd:A->A->A)(Azero:A)(Aopp:A->A)
      (Amul:A->A->A)(Aone:A)(Ainv:A->A)
      (H:Dec (@eq A))
      {r c} (M : mat A r c), (list (@RowOp A r) * mat A r c).

End GaussElim.


Section test.
  Import QcExt.
  Notation mat1 := (@mat1 Qc 0 1).
  Notation mrowKAdd := (mrowKAdd (Aadd:=Qcplus) (Amul:=Qcmult)).
  Notation firstNonZeroRowIdx := (firstNonZeroRowIdx (Azero:=0)).
  Notation rowEchelon :=
    (@rowEchelon _ Qcplus 0 Qcopp Qcmult Qcinv Qc_eq_Dec).
  Notation minRowEchelon :=
    (@minRowEchelon _ Qcplus 0 Qcopp Qcmult 1 Qcinv Qc_eq_Dec).

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
    (* Goal m2l (fold_left *)
    (*             (fun (m:mat _ r c) (k:nat) => *)
    (*                let coef : Qc := (- m $ k $ j / m $ i $ j) in *)
    (*                if (Aeqb coef 0) *)
    (*                then m *)
    (*                else mrowKAdd m i k coef) *)
    (*             (seq (S i) (r-S i)) M1) = m2l M2. *)
    (* Proof. cbv. auto. Qed. *)
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
    Goal m2l (snd (rowEchelon M1)) = m2l M2.
    (* Proof. cbv. auto. Qed. *)
    Abort.

    Let M3 : mat _ r c :=
        l2m 0
          (Q2Qc_dlist
             [[  1;  0; -1];
              [  0;  1; -1];
              [  0;  0;  0]]%Q).
    Goal m2l (snd (minRowEchelon M2)) = m2l M3.
      (* Proof. cbv. lma; f_equal; apply UIP. Qed. *)
    Abort.
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
    Goal m2l (snd (rowEchelon M1)) = m2l M2.
    (* Proof. cbv. auto. Qed. *)
    Abort.

    Let M3 : mat _ r c :=
        l2m 0
          (Q2Qc_dlist
             [[  1;  0; 0];
              [  0;  1; 0];
              [  0;  0; 1]]%Q).
    Goal m2l (snd (minRowEchelon M2)) = m2l M3.
      (* Proof. cbv. lma; f_equal; apply UIP. Qed. *)
    Abort.
    
  End ex3.

  (* 高斯消元测试 *)
(*
  Section ex4.
    Goal rowEchelon (@mat1 1) = ([], mat1).
    Proof. cbv. auto. Qed.
    
    Goal rowEchelon (@mat1 2) = ([], mat1).
    Proof. cbv. auto. Qed.
    
    Goal rowEchelon (@mat1 3) = ([], mat1).
    Proof. cbv. auto. Qed.

    Example M : mat 10 10 :=
          l2m 0 _ _
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
    (* Time Compute (m2l (snd (rowEchelon(M)))). *)

    (* time: 0.36s *)
    Time Compute (m2l (snd (minRowEchelon(snd (rowEchelon(M)))))).
  End ex4.

  (* 这个例子说明了“阶梯形矩阵的台阶并非一样长”，需要特别考虑 *)
  Section ex5.
    Let r : nat := 3. Let c : nat := 4.
    Let M1 : mat r c :=
        l2m 0 _ _
          (Q2Qc_dlist
             [[1;1;1;1];
              [0;0;1;1];
              [0;0;0;1]]%Q).
    Goal m2l (snd (rowEchelon (M1))) = m2l M1.
    Proof. cbv. auto. Qed.
  End ex5.
  *)
End test.

(* Recursive Extraction rowEchelon minRowEchelon. *)
