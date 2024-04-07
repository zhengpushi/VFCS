(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix Determinant
  author    : ZhengPu Shi
  date      : 2022.06

  motivation :
  1. 数域K上n个方程的n元线性方程组有唯一解 <==> n阶行列式(n级矩阵的行列式)非零。
  2. 行列式在几何、分析等数学分支中也有重要应用。

  remark    :
  1. compute permutation of a list, such as 
     perm [a;b;c] => [[a;b;c]; [a;c;b]; [b;a;c]; [b;c;a]; [c;a;b]; [c;b;a]]
     perm [1;2;3] => [[1;2;3]; [1;3;2]; [2;1;3]; [2;3;1]; [3;1;2]; [3;2;1]]
  2. 行列式问题

     行列式的定义：它是一个单项式的求和，每个单项式是矩阵中不同行不同列元素的乘积，并
     冠以逆序数。

     二级矩阵
        A = [[a11;a12]; [a21;a22]]
        det(A) = a11*a22 + -(a12*a21)
               = a11*det[[a22]] + (-a12)*det[[a21]]  按第1行展开
               = (-a21)*det[[a12]] + a22*det[[a11]]  按第2行展开
               = a11*det[[a22]] + (-a21)*det[[a12]]  按第1列展开
               = (-a12)*det[[a21]] + a22*det[[a11]]  按第2列展开
     三级矩阵
        A = [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]]，
        det(A) = a11*a22*a33 + -a11*a23*a32 + ...
               = a11*det[[a22;a23];[a32;a33]])
                 + (-a12)*det[[a21;a23];[a31;a33]]
                 + a13*det[[a21;a22];[a31;a32]]    按第1行展开
               = 其他含开方式类似

     这里展示了两种方法：原始的凑下标的方式，递归的按某行某列展开的方法。
     数学上已经证明这两种方法的等价性。在Coq中也可以验证一次。
                 
     上述分析发现，我们需要如下的算法：
     1. 逆序数：给定一个自然数列表，
     2. 行列式原始算法：如何取出不同行不同列下标的所有组合。
     3. 子矩阵：去掉一行一列后剩下的矩阵。这是构造按某行某列展开算法的基础。

 *)

Require Import Extraction.
Require Import NatExt.
Require Import Matrix.
Require Import Perm.
Require ZArith Reals.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * n-order of determinant *)


(* ======================================================================= *)
(** ** Original definition of determinant *)
Section mdet.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.

  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ 0 1).

  (** n阶行列式的完全展开式 (在任意矩阵模型上可用，只依赖 mnth 函数) *)
  Definition mdet {n} : smat n -> A :=
    match n with
    | O => fun _ => 1        (* the determinant of a empty matrix is 1 *)
    | S n' =>
        fun (M : smat (S n')) =>
          (* 列号 0,1,..,(n-1) 的全排列 *)
          (* let colIds := perm (Azero:=0)%nat (seq 0 n)%nat in *)
          let colIds := perm (seq 0 n)%nat in
          (* 一个单项式 *)
          let item (l:list nat) : A :=
            fold_left Amul (map (fun i => M.[#i].[#(nth i l 0)%nat]) (seq 0 n)) 1 in
          (* 是否为偶排列 *)
          let isOdd (l:list nat) : bool := odd (ronum l (Altb:=Nat.ltb)) in
          (* 加总所有带符号的单项式 *)
          let items : list A :=
            map (fun l => if isOdd l then Aopp (item l) else item l) colIds in
          fold_left Aadd items 0
    end.

  (* |M\T| = |M| *)
  Lemma mdet_mtrans : forall {n} (M : smat n), mdet (M\T) = mdet M.
  Proof.
  Admitted.

  (* |M*N| = |M| * |N| *)
  Lemma mdet_mmul : forall {n} (M N : smat n),
      mdet (M * N) = (mdet M * mdet N)%A.
  Proof.
  Admitted.

  (* |mat1| = 1 *)
  Lemma mdet_mat1 : forall {n}, mdet (@mat1 n) = 1.
  Proof.
  Admitted.

End mdet.


(* ======================================================================= *)
(** ** Determinant on concrete dimensions *)
Section mdet_concrete.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.

  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).

  (** Determinant of a matrix of dimension-1 *)
  Definition mdet1 (M : smat A 1) := M.11.

  (** mdet1 M = |M| *)
  Lemma mdet1_eq_mdet : forall M, mdet1 M = mdet M.
  Proof. intros. cbv. ring. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet1_neq0_iff : forall (M : smat A 1),
      mdet M <> 0 <-> M.11 <> 0.
  Proof. intros. rewrite <- mdet1_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-2 *)
  Definition mdet2 (M : smat A 2) := (M.11*M.22 - M.12*M.21)%A.

  (** mdet2 M = |M| *)
  Lemma mdet2_eq_mdet : forall M, mdet2 M = mdet M.
  Proof. intros. unfold mdet2. cbn. ring. Qed.

  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet2_neq0_iff : forall (M : smat A 2),
      mdet M <> 0 <-> (M.11*M.22 - M.12*M.21)%A <> 0.
  Proof. intros. rewrite <- mdet2_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-3 *)
  Definition mdet3 (M : smat A 3) :=
    (M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
       M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
       M.13 * M.21 * M.32 - M.13 * M.22 * M.31)%A.

  (** mdet3 M = mdet M *)
  Lemma mdet3_eq_mdet : forall M, mdet3 M = mdet M.
  Proof. intros. unfold mdet3; cbn; ring. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet3_neq0_iff : forall (M : smat A 3),
      mdet M <> 0 <->
        (M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
           M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
           M.13 * M.21 * M.32 - M.13 * M.22 * M.31)%A <> 0.
  Proof. intros. rewrite <- mdet3_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-4 *)
  Definition mdet4 (M : smat A 4) :=
    (M.11*M.22*M.33*M.44 - M.11*M.22*M.34*M.43 -
       M.11*M.23*M.32*M.44 + M.11*M.23*M.34*M.42 +
       M.11*M.24*M.32*M.43 - M.11*M.24*M.33*M.42 -
       M.12*M.21*M.33*M.44 + M.12*M.21*M.34*M.43 +
       M.12*M.23*M.31*M.44 - M.12*M.23*M.34*M.41 -
       M.12*M.24*M.31*M.43 + M.12*M.24*M.33*M.41 +
       M.13*M.21*M.32*M.44 - M.13*M.21*M.34*M.42 -
       M.13*M.22*M.31*M.44 + M.13*M.22*M.34*M.41 +
       M.13*M.24*M.31*M.42 - M.13*M.24*M.32*M.41 -
       M.14*M.21*M.32*M.43 + M.14*M.21*M.33*M.42 +
       M.14*M.22*M.31*M.43 - M.14*M.22*M.33*M.41 -
       M.14*M.23*M.31*M.42 + M.14*M.23*M.32*M.41)%A.

  (** mdet4 M = mdet M *)
  Lemma mdet4_eq_mdet : forall M, mdet4 M = mdet M.
  Proof. intros. unfold mdet4; cbn; ring. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet4_neq0_iff : forall (M : smat A 4),
      mdet M <> 0 <->
        (M.11*M.22*M.33*M.44 - M.11*M.22*M.34*M.43 -
           M.11*M.23*M.32*M.44 + M.11*M.23*M.34*M.42 +
           M.11*M.24*M.32*M.43 - M.11*M.24*M.33*M.42 -
           M.12*M.21*M.33*M.44 + M.12*M.21*M.34*M.43 +
           M.12*M.23*M.31*M.44 - M.12*M.23*M.34*M.41 -
           M.12*M.24*M.31*M.43 + M.12*M.24*M.33*M.41 +
           M.13*M.21*M.32*M.44 - M.13*M.21*M.34*M.42 -
           M.13*M.22*M.31*M.44 + M.13*M.22*M.34*M.41 +
           M.13*M.24*M.31*M.42 - M.13*M.24*M.32*M.41 -
           M.14*M.21*M.32*M.43 + M.14*M.21*M.33*M.42 +
           M.14*M.22*M.31*M.43 - M.14*M.22*M.33*M.41 -
           M.14*M.23*M.31*M.42 + M.14*M.23*M.32*M.41)%A <> 0.
  Proof. intros. rewrite <- mdet4_eq_mdet. easy. Qed.
End mdet_concrete.


(* ======================================================================= *)
(** ** Test of determinant *)

(** *** Test of determinant on `Z` type *)
Section testZ.
  Import ZArith.
  Open Scope Z_scope.
  Let mdet {n} (M : @smat Z n) : Z := @mdet _ Z.add 0 Z.opp Z.mul 1 n M.

  (* 《高等代数》邱维声 第三版 习题2.2 *)
  Let ex_1_5 : mat Z 5 5 :=
        l2m 0 [[0;0;0;1;0];[0;0;2;0;0];[0;3;8;0;0];[4;9;0;7;0];[6;0;0;0;5]].
  Goal mdet ex_1_5 = 120. cbv. auto. Qed.

  Let ex_2_1 : mat Z 3 3 := l2m 0 [[1;4;2];[3;5;1];[2;1;6]].
  Goal mdet ex_2_1 = -49. cbv. auto. Qed.
End testZ.

(** *** Test of determinant on `R` type *)
Section testR.
  Import Reals.
  Open Scope R_scope.
  Notation "0" := R0.
  Notation "1" := R1.
  Let mdet {n} (M : @smat R n) : R := @mdet _ Rplus 0 Ropp Rmult 1 n M.

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.

  (* Eval cbv in mdet (mkmat_1_1 a11). *)
  (* = 0 + 1 * a11 *)
  (* Eval cbv in mdet (mkmat_2_2 a11 a12 a21 a22). *)
  (* = 0 + 1 * a11 * a22 + - (1 * a12 * a21) *)
  (* Eval cbv in mdet (mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33). *)
  (* = 0 + 1 * a11 * a22 * a33 
         + - (1 * a11 * a23 * a32) 
         + - (1 * a12 * a21 * a33) 
         + 1 * a12 * a23 * a31 
         + 1 * a13 * a21 * a32 
         + - (1 * a13 * a22 * a31)
   *)

  (* 《高等代数》邱维声 第三版 习题2.2 *)
  Let ex_2_3 : mat R 3 3 := l2m 0 [[a11;a12;a13];[0;a22;a23];[0;0;a33]].
  Goal mdet ex_2_3 = a11 * a22 * a33. cbv. lra. Qed.

  (* 2.2.2节，例题3 *)
  Example eg_2_2_2_3 : forall a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 c1 c2 d1 d2 e1 e2 : R,
      mdet (@l2m _ 0 5 5
              [[a1;a2;a3;a4;a5];
               [b1;b2;b3;b4;b5];
               [ 0; 0; 0;c1;c2];
               [ 0; 0; 0;d1;d2];
               [ 0; 0; 0;e1;e2]]) = 0.
  Proof. intros. cbv. lra. Qed.

  (* 2.2.2节，例题4 *)
  Example eg_2_2_2_4 : forall x:R,
      mdet (@l2m _ 0 4 4
              [[7*x;x;1;2*x];
               [1;x;5;-1];
               [4;3;x;1];
               [2;-1;1;x]]) = 7*x^4 - 5*x^3 - 99*x^2 + 38*x + 11.
  Proof. intros. cbv. lra. Qed.
  
End testR.


(* ======================================================================= *)
(** ** Determinant by expanding on one row or one column *)
Section mdetEx.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.

  Notation vsum := (@vsum _ Aadd 0).
  
  Notation smat n := (smat A n).
  Notation mat0 := (@mat0 _ 0).
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).

  (** Get the sub square matrix by remove i-th row and j-th column. *)
  Definition msubmat {n} (M : smat (S n)) (i0 j0 : fin (S n)) : smat n :=
    fun i j =>
      let i1 := if (fin2nat i ??< fin2nat i0)%nat
                then fin2SuccRange i
                else fin2SuccRangeSucc i in
      let j1 := if (fin2nat j ??< fin2nat j0)%nat
                then fin2SuccRange j
                else fin2SuccRangeSucc j in
      M.[i1].[j1].

  (** 按第一行展开的行列式 *)
  Fixpoint mdetEx {n} : smat n -> A :=
    match n with
    | O => fun _ => 1
    | S n' =>
        fun M => 
          vsum (fun j =>
                  let a := if Nat.even (fin2nat j)
                           then (M.[fin0].[j])
                           else (-(M.[fin0].[j]))%A in
                  let d := mdetEx (msubmat M fin0 j) in
                  a * d)
    end.

  Lemma mdetEx_eq_mdet_1 : forall (M : smat 1), mdetEx M = mdet M.
  Proof. intros. cbv; rewrite <- !(nth_m2f 0). ring. Qed.

  Lemma mdetEx_eq_mdet_2 : forall (M : smat 2), mdetEx M = mdet M.
  Proof. intros. cbv; rewrite <- !(nth_m2f 0). ring. Qed.

  Lemma mdetEx_eq_mdet_3 : forall (M : smat 3), mdetEx M = mdet M.
  Proof. intros. cbv; rewrite <- !(nth_m2f 0). ring. Qed.

  Lemma mdetEx_eq_mdet_4 : forall (M : smat 4), mdetEx M = mdet M.
  (* Proof. intros. cbv; rewrite <- !(nth_m2f 0); ring. Qed. *)
  (* TO SPEED UP THE COMPILATION *)
  Admitted.
  
  Theorem mdetEx_eq_mdet : forall {n} (M : smat n), mdetEx M = mdet M.
  Proof.
    intros.
    unfold mdet. unfold mdetEx.
  Admitted.

End mdetEx.


(* ======================================================================= *)
(** ** Test for `mdetEx` *)
Section test.
  Context `{HARing : ARing}.

  (* Notation msubmat := (msubmat (Azero:=Azero)). *)
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.

  Let M1 : smat A 3 := l2m Azero [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  (* Compute m2l (msubmat M1 #0 #0). *)
  (* Compute m2l (msubmat M1 #1 #0). *)
End test.


(* ############################################################################ *)
(** * Inverse Matrix by Adjoint Matrix *)

Section minvAM.
  Context `{HField : Field} `{HAeqDec : Dec _ (@eq A)}.
  Add Field field_thy_inst : (make_field_theory HField).
  
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * /b).
  Infix "/" := Adiv : A_scope.

  Notation smat n := (smat A n).
  Notation mat1 := (@mat1 _ 0 1).
  Notation mcmul := (@mcmul _ Amul).
  Infix "\.*" := mcmul : mat_scope.
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation mdetEx := (@mdetEx _ Aadd 0 Aopp Amul 1).
  Notation mdet1 := (@mdet1 A).
  Notation mdet2 := (@mdet2 _ Aadd Aopp Amul).
  Notation mdet3 := (@mdet3 _ Aadd Aopp Amul).
  Notation mdet4 := (@mdet4 _ Aadd Aopp Amul).

    
  (* ======================================================================= *)
  (** ** sign of algebraic remainder *)

  (** The sign of algebraic remainder of A[i,j], i.e., (-1)^(i+j) *)
  Definition madjSign {n} (i j : fin n) : A := 
    if Nat.even (fin2nat i + fin2nat j) then 1 else -(1).

  (** madjSign i j = madjSign j i *)
  Lemma madjSign_comm : forall {n} (i j : fin n), madjSign i j = madjSign j i.
  Proof. intros. unfold madjSign. rewrite Nat.add_comm. auto. Qed.


  (* ======================================================================= *)
  (** ** Cofactor matrix *)

  (** Cofactor matrix, cof(A)[i,j] = algebraic remainder of A[i,j] *)
  Definition mcofactor {n} : smat n -> smat n := 
    match n with
    | O => fun M => M 
    | S n' =>
        fun (M : smat (S n')) =>
        fun (i:fin (S n')) (j:fin (S n')) =>
          (madjSign i j * mdetEx (msubmat M i j))%A
    end.

  
  (* ======================================================================= *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix, adj(A)[i,j] = algebraic remainder of A[j,i] *)
  Definition madj {n} : smat n -> smat n := 
    match n with
    | O => fun M => M 
    | S n' =>
        fun (M : smat (S n')) =>
        fun (i:fin (S n')) (j:fin (S n')) =>
          (madjSign i j * mdetEx (msubmat M j i))%A
    end.

  (** (madj M).ij = (-1)^(i+j) * det(submat M i j) *)
  Lemma mnth_madj : forall {n} (M : smat (S n)) i j,
      (madj M) i j = (madjSign i j * mdetEx (msubmat M j i))%A.
  Proof. intros. auto. Qed.
  
  (** (madj M) $ i $ j = (mcofactor M) $ j $ i. *)
  Lemma mnth_madj_eq_mnth_mcofactor_swap : forall {n} (M : smat n) i j,
      (madj M).[i].[j] = (mcofactor M).[j].[i].
  Proof.
    intros. destruct n.
    - exfalso. apply fin0_False; auto.
    - simpl. f_equal. apply madjSign_comm.
  Qed.

  (** (madj M)\T = mcofactor M *)
  Lemma mtrans_madj : forall {n} (M : smat n), (madj M)\T = mcofactor M.
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_mtrans.
    apply mnth_madj_eq_mnth_mcofactor_swap.
  Qed.

  (** (mcofactor M)\T = madj M *)
  Lemma mtrans_mcofactor : forall {n} (M : smat n), (mcofactor M)\T = madj M.
  Proof. intros. rewrite <- mtrans_madj, mtrans_mtrans. auto. Qed.

  
  (* ======================================================================= *)
  (** ** Cramer rule *)

  (** Cramer rule, which can solving the equation with the form of A*x=b.
      Note, the result is valid only when |A| is not zero *)
  Definition cramerRule {n} (A0 : smat n) (b : @vec A n) : @vec A n :=
    let D := mdetEx A0 in
    fun i => mdetEx (msetc A0 b i) / D.


  (* ======================================================================= *)
  (** ** Invertible matrix by determinant *)
  
  (* Note:
     1. we use `AM` to denote `Adjoint Matrix method`
     2. we use `mdetEx` in definitions instead of `mdet`, for fast computation 
     3. we use `mdet` in properties instead of `mdetEx`, for consistency *)

  (** A matrix `M` is invertible, if its determinant is not zero. *)
  Definition minvertibleAM {n} (M : smat n) : bool :=
    if Aeqdec (mdetEx M) 0 then false else true.

  (* `minvertibleAM M` is true, iff the determinant of `M` is not zero *)
  Lemma minvertibleAM_true_iff_mdet_neq0 : forall {n} (M : smat n),
      minvertibleAM M = true <-> mdet M <> 0.
  Proof.
    intros. unfold minvertibleAM. rewrite mdetEx_eq_mdet.
    destruct Aeqdec; try easy.
  Qed.

  (* `minvertibleAM M` is false, iff the determinant of `M` is zero *)
  Lemma minvertibleAM_false_iff_mdet_eq0 : forall {n} (M : smat n),
      minvertibleAM M = false <-> mdet M = 0.
  Proof.
    intros. unfold minvertibleAM. rewrite mdetEx_eq_mdet.
    destruct Aeqdec; try easy.
  Qed.

  (* Identity matrix is invertibleAM *)
  Lemma mat1_invertibleAM_true : forall {n}, minvertibleAM (@mat1 n) = true.
  Proof.
    intros. unfold minvertibleAM. rewrite mdetEx_eq_mdet.
    rewrite mdet_mat1. destruct Aeqdec; auto. apply field_1_neq_0 in e; auto.
  Qed.

  
  (* ======================================================================= *)
  (** ** Inverse matrix by adjoint matrix (option version) *)

  (** Inverse matrix by adjoint matrix (option version) *)
  Definition minvAMo {n} (M : smat n) : option (smat n) :=
    if minvertibleAM M
    then Some ((1 / mdetEx M) \.* (madj M))
    else None.

  (** If `minvAMo M` return `Some M'`, then `M'` is left inverse of `M` *)
  Theorem minvAMo_imply_eq : forall {n} (M M' : smat n),
      minvAMo M = Some M' -> M' * M = mat1.
  Proof.
  Admitted.

  (** `minvAMo` return `Some`, iff, `minvertibleAM` return true *)
  Lemma minvAMo_Some_iff_invertibleAM_true : forall {n} (M : smat n),
      (exists M', minvAMo M = Some M') <-> minvertibleAM M = true.
  Proof.
    intros. unfold minvAMo, minvertibleAM in *. split; intros.
    - destruct H as [M' H]. destruct Aeqdec; try easy.
    - destruct Aeqdec; try easy.
      exists ((1 / mdetEx M) \.* (madj M)). auto.
  Qed.

  (** `minvAMo` return `None`, iff, `minvertibleAM` return false *)
  Lemma minvAMo_None_iff_invertibleAM_false : forall {n} (M : smat n),
      minvAMo M = None <-> minvertibleAM M = false.
  Proof.
    intros. unfold minvAMo, minvertibleAM in *. split; intros.
    - destruct Aeqdec; try easy.
    - destruct Aeqdec; try easy.
  Qed.
  
  
  (* ======================================================================= *)
  (** ** Inverse matrix by adjoint matrix (need to check inversibility) *)
  
  (** Inverse matrix by adjoint matrix (need to check inversibility) *)
  Definition minvAM {n} (M : smat n) := (1 / mdetEx M) \.* (madj M).
  Notation "M \-1" := (minvAM M) : mat_scope.

  (** If `minvAMo M` return `Some M'`, then `minvAM M` equal to `M'` *)
  Lemma minvAMo_Some_imply_minvAM : forall {n} (M M' : smat n),
      minvAMo M = Some M' -> minvAM M = M'.
  Proof.
    intros. unfold minvAMo, minvAM in *.
    destruct minvertibleAM eqn:E; try easy.
    inv H. auto.
  Qed.

  (** If the matrix `M` is invertible, then `minvAM M` is `minvAMo M` *)
  Lemma minvAM_imply_minvAMo_Some : forall {n} (M : smat n),
      minvertibleAM M -> minvAMo M = Some (minvAM M).
  Proof.
    intros. unfold minvAMo, minvAM in *.
    rewrite H. auto.
  Qed.
  
  (** mcofactor M = (det M) .* (M\-1\T) *)
  Lemma mcofactor_eq : forall (M : smat 3),
      mdet M <> 0 -> mcofactor M = mdet M \.* (M\-1\T).
  Proof.
    intros. unfold minvAM. rewrite mdetEx_eq_mdet.
    rewrite mtrans_mcmul. rewrite mcmul_assoc.
      rewrite identityLeft at 1. rewrite field_mulInvR; auto.
      rewrite mcmul_1_l. rewrite mtrans_madj. auto.
  Qed.

  (** M * M\-1 = mat1 *)
  Lemma mmul_minvAM_r : forall {n} (M : smat n), mdet M <> 0 -> M * M\-1 = mat1.
  Proof.
  Admitted.

  (** M\-1 * M = mat1 *)
  Lemma mmul_minvAM_l : forall {n} (M : smat n), mdet M <> 0 -> M\-1 * M = mat1.
  Proof.
  Admitted.

  (** M * N = mat1 -> |M| <> 0 *)
  Lemma mmul_eq1_imply_mdet_neq0_l : forall {n} (M N : smat n),
      M * N = mat1 -> mdet M <> 0.
  Proof.
    intros.
    assert (mdet (M * N) = 1). rewrite H. apply mdet_mat1.
    rewrite mdet_mmul in H0.
    intro. rewrite H1 in H0. rewrite ring_mul_0_l in H0. apply field_1_neq_0; auto.
  Qed.
    
  (** M * N = mat1 -> |N| <> 0 *)
  Lemma mmul_eq1_imply_mdet_neq0_r : forall {n} (M N : smat n),
      M * N = mat1 -> mdet N <> 0.
  Proof.
    intros.
    assert (mdet (M * N) = 1). rewrite H. apply mdet_mat1.
    rewrite mdet_mmul in H0.
    intro. rewrite H1 in H0. rewrite ring_mul_0_r in H0. apply field_1_neq_0; auto.
  Qed.
  
  (* From `M * N = mat1`, the `minvertibleAM M` return true *)
  Lemma mmul_eq1_imply_invertibleAM_true_l : forall {n} (M N : smat n),
    M * N = mat1 -> minvertibleAM M = true.
  Proof.
    intros. apply mmul_eq1_imply_mdet_neq0_l in H.
    apply minvertibleAM_true_iff_mdet_neq0; auto.
  Qed.

  (* From `M * N = mat1`, the `minvertibleAM N` return true *)
  Lemma mmul_eq1_imply_invertibleAM_true_r : forall {n} (M N : smat n),
    M * N = mat1 -> minvertibleAM N = true.
  Proof.
    intros. apply mmul_eq1_imply_mdet_neq0_r in H.
    apply minvertibleAM_true_iff_mdet_neq0; auto.
  Qed.

  (** M * N = mat1 -> M \-1 = N *)
  Lemma mmul_eq1_imply_minvAM_l : forall {n} (M N : smat n), M * N = mat1 -> M\-1 = N.
  Proof.
  Admitted.

  (** M * N = mat1 -> N \-1 = M *)
  Lemma mmul_eq1_imply_minvAM_r : forall {n} (M N : smat n), M * N = mat1 -> N\-1 = M.
  Proof.
  Admitted.

  (** minvertibleAM M = true -> M \-1 = N -> M * N = mat1 *)
  Lemma mmul_eq1_if_minvAM_l : forall {n} (M N : smat n),
      minvertibleAM M = true -> M \-1 = N -> M * N = mat1.
  Proof.
  Admitted.

  (** minvertibleAM N = true -> N \-1 = M -> M * N = mat1 *)
  Lemma mmul_eq1_if_minvAM_r : forall {n} (M N : smat n),
      minvertibleAM N = true -> N \-1 = M -> M * N = mat1.
  Proof.
  Admitted.

  (** mat1 \-1 = mat1 *)
  Lemma minvAM_mat1 : forall {n}, minvAM (@mat1 n) = mat1.
  Proof.
    unfold minvAM. induction n.
    - 
  Admitted.

  
  (* ======================================================================= *)
  (** ** Formula for inversion of a symbol matrix of 1~4 order. *)
  Section SymbolicMatrix.
    Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : A.
    Let m1 := @mkmat_1_1 _ Azero a11.
    Let m2 := @mkmat_2_2 _ Azero a11 a12 a21 a22.
    Let m3 := @mkmat_3_3 _ Azero a11 a12 a13 a21 a22 a23 a31 a32 a33.
    Let m4 := @mkmat_4_4 _ Azero a11 a12 a13 a14 a21 a22 a23 a24
                a31 a32 a33 a34 a41 a42 a43 a44.

    (* Compute (m2l (minvAM m1)). *)
    (* Compute (m2l (minvAM m2)). *)
    (* Compute (m2l (minvAM m3)). *)
    (* Compute (m2l (minvAM m4)). *)
    (* Although this is correct, but the expression is too long. *)
    (* We want to simplify it with RAST *)
  End SymbolicMatrix.

  (* 将 a <> 0 |- b <> 0 转换为 b = 0 |- a = 0 *)
  Ltac solve_neq0_neq0 :=
    let H1 := fresh "H1" in
    match goal with
    | H: ?e1 <> Azero |- ?e2 <> Azero =>
        intros H1; destruct H
    end.

  (* 将 a = 0 |- b = 0 转换为 a = b，并尝试证明 *)
  Ltac solve_eq0_eq0 :=
    match goal with
    | H: ?a = Azero |- ?b = Azero =>
        symmetry; rewrite <- H at 1; try ring
    end.
  
  
  (** *** Inverse matrix of of concrete dimension *)
  Section concrete.
    
    Definition minvAM1 (M : smat 1) : smat 1 := l2m 0 [[1/M.11]].

    (** |M| <> 0 -> minv1 M = inv M *)
    Lemma minvAM1_eq_minvAM : forall M, mdet M <> Azero -> minvAM1 M = minvAM M.
    Proof.
      intros. cbn in H; rewrite <- !(nth_m2f_nat2finS 0) in H; auto.
      apply m2l_inj; cbv; rewrite <- !(nth_m2f 0); list_eq.
      field; solve_neq0_neq0; solve_eq0_eq0.
    Qed.

    Definition minvAM2 (M : smat 2) : smat 2 :=
      let d := mdet2 M in
      l2m 0 [[M.22/d; -M.12/d]; [-M.21/d; M.11/d]].

    (** |M| <> 0 -> minv2 M = inv M *)
    Lemma minvAM2_eq_minvAM : forall M, mdet M <> Azero -> minvAM2 M = minvAM M.
    (* TO SPEED UP THE COMPILATION *)
    Admitted.
    (* Proof. *)
    (*   intros. cbn in H; rewrite <- !(nth_m2f_nat2finS 0) in H; auto. *)
    (*   apply m2l_inj; cbv; rewrite <- !(nth_m2f 0); list_eq. *)
    (*   all: field; solve_neq0_neq0; solve_eq0_eq0. *)
    (* Qed. *)
    
    (* Note, this formula come from matlab, needn't manual work *)
    Definition minvAM3 (M : smat 3) : smat 3 :=
      let d := mdet3 M in
      (l2m 0
         [[(M.22*M.33-M.23*M.32)/d; -(M.12*M.33-M.13*M.32)/d; (M.12*M.23-M.13*M.22)/d];
          [-(M.21*M.33-M.23*M.31)/d; (M.11*M.33-M.13*M.31)/d; -(M.11*M.23-M.13*M.21)/d];
          [(M.21*M.32-M.22*M.31)/d; -(M.11*M.32-M.12*M.31)/d; (M.11*M.22-M.12*M.21)/d]])%A.

    (** |M| <> 0 -> minv3 M = inv M *)
    Lemma minvAM3_eq_minvAM : forall M, mdet M <> Azero -> minvAM3 M = minvAM M.
    (* TO SPEED UP THE COMPILATION *)
    Admitted.
    (* Proof. *)
    (*   intros. cbn in H; rewrite <- !(nth_m2f_nat2finS 0) in H; auto. *)
    (*   apply m2l_inj; cbv; rewrite <- !(nth_m2f 0); list_eq. *)
    (*   all: field; solve_neq0_neq0; solve_eq0_eq0. *)
    (* Qed. *)

    Definition minvAM4 (M : smat 4) : smat 4 :=
      let d := mdet4 M in
      l2m 0
        [[(M.22*M.33*M.44 - M.22*M.34*M.43 - M.23*M.32*M.44 + M.23*M.34*M.42 +
             M.24*M.32*M.43 - M.24*M.33*M.42)/d;
          -(M.12*M.33*M.44 - M.12*M.34*M.43 - M.13*M.32*M.44 + M.13*M.34*M.42 +
              M.14*M.32*M.43 - M.14*M.33*M.42)/d;
          (M.12*M.23*M.44 - M.12*M.24*M.43 - M.13*M.22*M.44 + M.13*M.24*M.42 +
             M.14*M.22*M.43 - M.14*M.23*M.42)/d;
          -(M.12*M.23*M.34 - M.12*M.24*M.33 - M.13*M.22*M.34 + M.13*M.24*M.32 +
              M.14*M.22*M.33 - M.14*M.23*M.32)/d];

         [-(M.21*M.33*M.44 - M.21*M.34*M.43 - M.23*M.31*M.44 + M.23*M.34*M.41 +
              M.24*M.31*M.43 - M.24*M.33*M.41)/d;
          (M.11*M.33*M.44 - M.11*M.34*M.43 - M.13*M.31*M.44 + M.13*M.34*M.41 +
             M.14*M.31*M.43 - M.14*M.33*M.41)/d;
          -(M.11*M.23*M.44 - M.11*M.24*M.43 - M.13*M.21*M.44 + M.13*M.24*M.41 +
              M.14*M.21*M.43 - M.14*M.23*M.41)/d;
          (M.11*M.23*M.34 - M.11*M.24*M.33 - M.13*M.21*M.34 + M.13*M.24*M.31 +
             M.14*M.21*M.33 - M.14*M.23*M.31)/d];

         [(M.21*M.32*M.44 - M.21*M.34*M.42 - M.22*M.31*M.44 + M.22*M.34*M.41
           + M.24*M.31*M.42 - M.24*M.32*M.41)/d;
          -(M.11*M.32*M.44 - M.11*M.34*M.42 - M.12*M.31*M.44 + M.12*M.34*M.41 +
              M.14*M.31*M.42 - M.14*M.32*M.41)/d;
          (M.11*M.22*M.44 - M.11*M.24*M.42 - M.12*M.21*M.44 + M.12*M.24*M.41 +
             M.14*M.21*M.42 - M.14*M.22*M.41)/d;
          -(M.11*M.22*M.34 - M.11*M.24*M.32 - M.12*M.21*M.34 + M.12*M.24*M.31 +
              M.14*M.21*M.32 - M.14*M.22*M.31)/d];

         [-(M.21*M.32*M.43 - M.21*M.33*M.42 - M.22*M.31*M.43 + M.22*M.33*M.41 +
              M.23*M.31*M.42 - M.23*M.32*M.41)/d;
          (M.11*M.32*M.43 - M.11*M.33*M.42 - M.12*M.31*M.43 + M.12*M.33*M.41 +
             M.13*M.31*M.42 - M.13*M.32*M.41)/d;
          -(M.11*M.22*M.43 - M.11*M.23*M.42 - M.12*M.21*M.43 + M.12*M.23*M.41 +
              M.13*M.21*M.42 - M.13*M.22*M.41)/d;
          (M.11*M.22*M.33 - M.11*M.23*M.32 - M.12*M.21*M.33 + M.12*M.23*M.31 +
             M.13*M.21*M.32 - M.13*M.22*M.31)/d]]%A.
    
    (** |M| <> 0 -> minv4 M = inv M *)
    Lemma minvAM4_eq_minvAM : forall M, mdet M <> Azero -> minvAM4 M = minvAM M.
    (* TO SPEED UP THE COMPILATION *)
    Admitted.
    (* Proof. *)
    (*   intros. cbn in H; rewrite <- !(nth_m2f_nat2finS 0) in H; auto. *)
    (*   apply m2l_inj; cbv; rewrite <- !(nth_m2f 0); list_eq. *)
    (*   all: field; solve_neq0_neq0; solve_eq0_eq0. *)
    (* Qed. *)
    
  End concrete.


  (* ******************************************************************* *)
  (** ** Inverse matrix with lists for input and output *)
  
  (** Check matrix invertibility with lists as input *)
  Definition minvertibleAM_list (n : nat) (dl : dlist A) : bool :=
    @minvertibleAM n (l2m 0 dl).

  (** Inverse matrix with lists for input and output *)
  Definition minvAM_list (n : nat) (dl : dlist A) : dlist A :=
    m2l (@minvAM n (l2m 0 dl)).

  (** `minvertibleAM_list` is equal to `minvertibleAM`, by definition *)
  Lemma minvertibleAM_list_spec : forall (n : nat) (dl : dlist A),
      minvertibleAM_list n dl = @minvertibleAM n (l2m 0 dl).
  Proof. intros. auto. Qed.

  (** If the matrix `M` created by [dl] is invertible, then the matrix `M'` 
      created by [minvAM_list dl] is the left inverse of `M` *)
  Theorem minvAM_list_spec : forall (n : nat) (dl : dlist A),
      let M : smat n := l2m 0 dl in
      let M' : smat n := l2m 0 (minvAM_list n dl) in
      minvertibleAM_list n dl = true ->
      M' * M = mat1.
  Proof.
    intros. unfold minvertibleAM_list in H. unfold minvAM_list in M'.
    unfold M', M. rewrite l2m_m2l. apply mmul_minvAM_l; auto.
    apply minvertibleAM_true_iff_mdet_neq0 in H. auto.
  Qed.  
  
End minvAM.



(* ############################################################################ *)
(** * Test *)

(* ******************************************************************* *)
(** ** Test inverse matrix on Q *)
Section test_Q.
  Import QExt.
  
  Notation mmul := (@mmul _ Qplus 0 Qmult).
  Infix "*" := mmul : mat_scope.
  
  Notation minvertibleAM_list := (@minvertibleAM_list _ Qplus 0 Qopp Qmult 1).
  Notation minvAM_list := (@minvAM_list _ Qplus 0 Qopp Qmult 1 Qinv).

  (** Example 1: a `2x2` matrix *)
  Section ex1.
    
    (* [ 1  2]     [ 3  2]
       [-1 -3] <-> [-1 -1] *)
    Let d1 := [[1;2];[-1;-3]].
    Let d2 := [[3;2];[-1;-1]].

    (* we can get the result immediately *)
    (* Compute minvertibleAM_list 2 d1. *)
    (* Compute minvAM_list 2 d1. *)
    (* Compute minvAM_list 2 d2. *)
    
    (* [d1] is invertible *)
    Goal minvertibleAM_list 2 d1 = true.
    Proof. simpl. auto. Qed.
    
    (* inverse of [d1] is [d2] *)
    Goal minvAM_list 2 [[1;2];[-1;-3]] = d2.
    Proof. cbv. auto. Qed.
  End ex1.

  (** Example 2: a `3x3` matrix *)
  Section ex2.
    
    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)
    Let d1 := [[1;3;1];[2;1;1];[2;2;1]].
    Let d2 := [[-1;-1;2];[0;-1;1];[2;4;-5]].
    
    (* Compute minvertibleAM_list 3 d1. *)
    (* Compute minvAM_list 3 d1. *)
    (* Compute minvAM_list 3 d2. *)
    
    Goal dlistSetoidEq Qeq (minvAM_list 3 d1) d2.
    Proof. Local Opaque Qeq. cbv. repeat constructor. Qed.
  End ex2.

(* In summary, for computing inverse matrices with Q type in Coq:
   1. compared to GE method, minvertibleAM needn't Ainv, i.e., the element only need 
      to be a ring structure is enough to determine if the matrix is invertible.
   2. need not `AeqDec (@eq A)` relation.
   3. the Q type also abtained a relative simple output format, compared to GE 
      method. *)
End test_Q.


(* ******************************************************************* *)
(** ** Test inverse matrix on Qc *)
Section test_Qc.
  Import QcExt.

  Notation minvertibleAM_list := (@minvertibleAM_list _ Qcplus 0 Qcopp Qcmult 1).
  Notation minvAM_list := (@minvAM_list _ Qcplus 0 Qcopp Qcmult 1 Qcinv).

  (** Example 2: a `3x3` matrix *)
  Section ex2.

    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)
    Let d1 := Q2Qc_dlist [[1;3;1];[2;1;1];[2;2;1]]%Q.
    Let d2 := Q2Qc_dlist [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q.
    (* Note, we need the `Q2Qc` function to typing term of `Qc` type *)
    
    (* Compute minvertibleAM_list 3 d1. *)
    (* Compute minvAM_list 3 d1. *)
    (* Compute minvAM_list 3 d2. *)
    
    (* Note, the `canon` part is unnecessary for users. 
       But we can remove the proof part easily *)
    (* Compute Qc2Q_dlist (minvAM_list 3 d1). *)

    (* An advantage is that we can use Leibniz equal *)
    Goal minvAM_list 3 d1 = d2.
    Proof. cbv. list_eq; f_equal; apply proof_irrelevance. Qed.
  End ex2.
  
  (* In summary, for computing inverse matrices with Qc type in Coq:
     1. Complex input format which need Q2Qc function, and complex output format 
        which contain unnecessary proof, but these difficulties can be overcome easily.
     2. Built-in Leibniz equal is supported. *)
End test_Qc.


(* ******************************************************************* *)
(** ** inverse matrix on Q type (enhanced version) *)
Section minvAM_Qlist.

  (* What is "enhanced" meannig?
     1. The format of input and ouput is Q type
     2. The inner computation process use Qc type *)
  
  Import QcExt.
  
  (* `minvAM_list` on `Qc` type *)
  Notation minvertibleAM_list := (@minvertibleAM_list _ Qcplus 0 Qcopp Qcmult 1).
  Notation minvAM_list := (@minvAM_list _ Qcplus 0 Qcopp Qcmult 1 Qcinv).

  Import QExt.
  
  (** Check matrix invertibility with rational number lists *)
  Definition minvertibleAM_Qlist (n : nat) (dl : dlist Q) : bool :=
    minvertibleAM_list n (Q2Qc_dlist dl).
  
  (** Inverse matrix with rational number lists *)
  Definition minvAM_Qlist (n : nat) (dl : dlist Q) : dlist Q :=
    Qc2Q_dlist (minvAM_list n (Q2Qc_dlist dl)).
  
  (** Example 2: a `3x3` matrix *)
  Section ex2.

    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)
    Let d1 := [[1;3;1];[2;1;1];[2;2;1]].
    Let d2 := [[-1;-1;2];[0;-1;1];[2;4;-5]].
    
    (* Compute minvertibleAM_Qlist 3 d1. *)
    (* Compute minvAM_Qlist 3 d1. *)
    (* Compute minvAM_Qlist 3 d2. *)
    (* Note, we get a friendly experience for typing and printing *)

    (* An advantage is that we can use Leibniz equal *)
    Goal minvAM_Qlist 3 d1 = d2.
    Proof. cbv. auto. Qed.
  End ex2.

  (* Example 3: a `8x8` matrix *)
  Section ex3.
    (* A manually given random `8x8` matrix *)
    Goal minvAM_Qlist 6
      [[1;2;3;4;5;6;7;8];
       [2;4;5;6;7;8;9;1];
       [3;5;7;6;8;4;2;1];
       [4;5;7;6;9;8;3;2];
       [5;4;3;7;9;6;8;1];
       [6;5;3;4;7;8;9;2];
       [7;8;6;5;9;2;1;3];
       [8;9;6;3;4;5;2;1]] = [].
    Proof.
      (* cbv. *)
      (* too slow, more than 1 minute. Tips, use a small dimension!! *)
    Abort.
    (* Note that many elements are in the fraction format of rational numbers.
       This is reasonable, as fractions typically do not possess a finite decimal 
       representation. *)
    
    (* In MATLAB, we can use these commands to compute inverse matrix:
     >> M = [1 2 3 4 5 6 7 8; ...
             2 4 5 6 7 8 9 1; ...
             3 5 7 6 8 4 2 1; ...
             4 5 7 6 9 8 3 2; ...
             5 4 3 7 9 6 8 1; ...
             6 5 3 4 7 8 9 2; ...
             7 8 6 5 9 2 1 3; ...
             8 9 6 3 4 5 2 1]
     >> M' = inv(M)
     Note, we can use following command to switch the format of rational numbers
     >> format rat
     >> format short
     The result looks different with Coq. For example, 
         M'(0,2)=41846/50943 in Coq,
         M'(0,2)=23/28 in MATLAB, 
     and these two values are not equal. *)

    Goal ~(Qmake 41846 50943 == Qmake 23 28).
    Proof. intro. cbv in H. easy. Qed.

    (* The possible reason is that MATLAB performs calculations using floating-point 
       numbers, and converting the inaccurate results into fractions cannot compensate
       for the difference.
       On the contrary, Coq uses completely precise results.
       While the exact benefits are unclear, this precision could be beneficial. *)
  End ex3.

  (* Example 4 : a `8x8` matrix with decimal numbers *)
  Section ex4.
  (* In MATLAB, use these commands for comparison experiment:
     >> format short
     >> M = rand(8,8)
     Or, manually use these numbers:
     >> M = [0.8001  0.5797  0.0760  0.9448  0.3897  0.0598  0.7317  0.1835; ...
             0.4314  0.5499  0.2399  0.4909  0.2417  0.2348  0.6477  0.3685; ...
             0.9106  0.1450  0.1233  0.4893  0.4039  0.3532  0.4509  0.6256; ...
             0.1818  0.8530  0.1839  0.3377  0.0965  0.8212  0.5470  0.7802; ...
             0.2638  0.6221  0.2400  0.9001  0.1320  0.0154  0.2963  0.0811; ...
             0.1455  0.3510  0.4173  0.3692  0.9421  0.0430  0.7447  0.9294; ...
             0.1361  0.5132  0.0497  0.1112  0.9561  0.1690  0.1890  0.7757; ...
             0.8693  0.4018  0.9027  0.7803  0.5752  0.6491  0.6868  0.4868]
     Compute the inverse matrix
     >> M' = inv(M)
   *)
    Let d1 := 
          [[0.8001;0.5797;0.0760;0.9448;0.3897;0.0598;0.7317;0.1835];
           [0.4314;0.5499;0.2399;0.4909;0.2417;0.2348;0.6477;0.3685];
           [0.9106;0.1450;0.1233;0.4893;0.4039;0.3532;0.4509;0.6256];
           [0.1818;0.8530;0.1839;0.3377;0.0965;0.8212;0.5470;0.7802];
           [0.2638;0.6221;0.2400;0.9001;0.1320;0.0154;0.2963;0.0811];
           [0.1455;0.3510;0.4173;0.3692;0.9421;0.0430;0.7447;0.9294];
           [0.1361;0.5132;0.0497;0.1112;0.9561;0.1690;0.1890;0.7757];
           [0.8693;0.4018;0.9027;0.7803;0.5752;0.6491;0.6868;0.4868]].

    (* Time Compute minvertibleAM_Qlist 8 d1. (* 45s *) *)
    (* Time Compute minvAM_Qlist 8 d1.        (* too slow *) *)
  End ex4.
  
  (* In summary, for computing inverse matrices with Q (with the help of Qc):
     1. simple input format, and relatively simple output format.
     2. accuately result compared to MATLAB, but fractions are not intuitive.
     3. Leibniz equal is supported.
   *)
End minvAM_Qlist.

