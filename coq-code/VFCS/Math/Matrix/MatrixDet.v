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
  2. what is a matrix with zero rows and zero columns?
     * 在 python 的 NumPy 库中，
       ```
       import numpy as np
       matrix = np.zeros((0,0))
       ```
     * 一个实际的问题
       用矩阵A表示学生各科的成绩，行数是学生数量，列数是科目数，
       A(i,j)表示第i个学生第j科目的成绩。
       那么，初始时，就是一个 0x0 的矩阵。
     * 还有种说法是，不存在行数为0或列数为0的矩阵。
  3. 行列式问题

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

Require Import NatExt.
Require Import Matrix.
Require Import Extraction.
Require ZArith Reals.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * Preparation works *)


(* ======================================================================= *)
(** ** Permutation of a list *)
Section perm.
  Context {A : Type} {Azero : A} {Altb : A -> A -> bool}.

  (** Get k-th element and remaining elements from a list *)
  Fixpoint pick (l : list A) (k : nat) : A * list A :=
    match k with
    | 0 => (hd Azero l, tl l)
    | S k' =>
        match l with
        | [] => (Azero, [])
        | x :: l' =>
            let (a,l0) := pick l' k' in
            (a, [x] ++ l0)
        end
    end.

  (** Get permutation of a list from its top n elements *)
  Fixpoint perm_aux (n : nat) (l : list A) : list (list A) :=
    match n with
    | 0 => [[]]
    | S n' =>
        let d1 := map (fun i => pick l i) (seq 0 n) in
        let d2 :=
          map (fun k : A * list A =>
                 let (x, lx) := k in
                 let d3 := perm_aux n' lx in
                 map (fun l1 => [x] ++ l1) d3) d1 in
        concat d2
    end.

  (** Get permutation of a list *)
  Definition perm (l : list A) : list (list A) := perm_aux (length l) l.

  Lemma length_perm_cons : forall l a,
      length (perm (a :: l)) = length (a :: l) * length (perm l).
  Proof.
    intros. unfold perm. induction l.
    - simpl. auto.
    - simpl in *.
  Admitted.

  (** Length of permutation *)
  Definition Pn (l : list A) := length (perm l).

  (** Pn of cons. 
      Example: Pn [a;b;c;d] = 4 * Pn [a;b;c] *)
  Lemma Pn_cons : forall (a : A) (l : list A), Pn (a :: l) = (length (a :: l)) * (Pn l).
  Proof.
    intros a l. revert a. induction l; auto. intros. simpl.
    unfold Pn in *. simpl.
    rewrite length_perm_cons. rewrite IHl.
    simpl. lia.
  Qed.

  (** Length of permutation equal to the factorial of the length *)
  Lemma Pn_eq : forall l, Pn l = fact (length l).
  Proof.
    induction l; simpl; auto.
    rewrite Pn_cons. rewrite IHl. simpl. auto.
  Qed.

End perm.


Section test.
  Context {A} (Azero:A) (a b c : A).
  Let pick := @pick A Azero.
  
  (* 从列表 l 中取出：某个元素，以及剩下的列表 *)
  Let l := [a;b;c].
  (* Compute pick l 0.     (* = (a, [b; c]) *) *)
  (* Compute pick l 1.     (* = (b, [a; c]) *) *)
  (* Compute pick l 2.     (* = (c, [a; b]) *) *)
  (* Compute pick l 3.     (* = (Azero, [a; b; c]) *) *)

  (* 计算列表的全排列 *)
  (* Compute perm [a]. *)
  (* = [[a]] *)
  (* Compute perm [a;b]. *)
  (* = [[a; b]; [b; a]] *)
  (* Compute perm [a;b;c]. *)
  (* = [[a; b; c]; [a; c; b]; [b; a; c]; [b; c; a]; [c; a; b]; [c; b; a]] *)

  (* 正整数列表的全排列，这是计算行列式的其中一步 *)
  (* Compute perm [1;2;3]. *)
  (* = [[1; 2; 3]; [1; 3; 2]; [2; 1; 3]; [2; 3; 1]; [3; 1; 2]; [3; 2; 1]] *)
End test.


(* ======================================================================= *)
(** ** reverse-order-number (RON) of a list, 逆序数 *)
Section ronum.
  Context {A} {Altb : A -> A -> bool}.
  Infix "<?" := Altb.

  (* The RON of one element respect to a list *)
  Definition ronum1 (a : A) (l : list A) : nat :=
    fold_left (fun (n : nat) (b : A) => n + (if b <? a then 1 else 0)) l 0.

  (* The RON of a list *)
  Fixpoint ronum (l : list A) : nat :=
    match l with
    | [] => 0
    | x :: l' => ronum1 x l' + ronum l'
    end.
End ronum.

Section test.
  Let ronum1 := @ronum1 nat Nat.leb.
  Let ronum := @ronum nat Nat.leb.
  (* Compute ronum1 3 [1;2;4]. (* = 2 *) *)
  (* Compute ronum [2;1;4;3]. (* = 2 *) *)
  (* Compute ronum [2;3;4;1]. (* = 3 *) *)
End test.

(* ======================================================================= *)
(** ** Parity of a permutation, 排列的奇偶性 *)
Section parity.
  Context {A} {Altb : A -> A -> bool}.

  (** The RON of a permutation is odd *)
  Definition oddPerm (l : list A) : bool := odd (ronum (Altb:=Altb) l).

End parity.


(* ======================================================================= *)
(** ** Exchange of a permutation 排列的对换 *)
Section permExchg.
  Context {A} {Altb : A -> A -> bool} (Azero : A).

  Notation ronum := (ronum (Altb:=Altb)).
  Notation oddPerm := (oddPerm (Altb:=Altb)).

  (* 对换第 i0,i1 的元素 *)
  Definition permExchg (l : list A) (i0 i1 : nat) : list A :=
    lswap Azero l i0 i1.

  (** 对换相邻位置改变排列的奇偶性 *)
  Theorem permExchg_parity : forall (l : list A) (n i0 i1 : nat),
      length l = n -> i0 < n -> i1 < n -> i0 <> i1 ->
      oddPerm (permExchg l i0 i1) <> oddPerm l.
  Proof.
    intros. unfold oddPerm. unfold permExchg.
    revert l i0 i1 H H0 H1 H2. induction n; intros. lia.
    destruct l; simpl in *. lia.
    (* 教科书上的证明很巧妙，难以形式化的描述出来。
       书上把 l 分解为
       [...] i [...] j [...]
       这种形式，然后分情形讨论
     *)
    Admitted.
  
End permExchg.


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
  
  (** n+1阶行列式的完全展开式 (在任意矩阵模型上可用，只依赖 mnth 函数) *)
  Definition mdet {n} : smat n -> A :=
    match n with
    | O => fun _ => 0
    | S n' =>
        fun (M : smat (S n')) =>
          (* 列号 0,1,..,(n-1) 的全排列 *)
          let colIds := perm (Azero:=0)%nat (seq 0 n)%nat in
          (* 一个单项式 *)
          let item (l:list nat) : A :=
            fold_left Amul (map (fun i => M $ #i $ #(nth i l 0)%nat) (seq 0 n)) 1 in
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
  Lemma mdet_mmul : forall {n} (M N : smat n), mdet (M * N) = (mdet M * mdet N)%A.
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
      let i1 := if fin2nat i <? fin2nat i0
                then fin2SuccRange i
                else fin2SuccRangeSucc i in
      let j1 := if fin2nat j <? fin2nat j0
                then fin2SuccRange j
                else fin2SuccRangeSucc j in
      M $ i1 $ j1.

  (** 按第一行展开的行列式 *)
  Fixpoint mdetEx {n} : smat (S n) -> A :=
    match n with
    | O => fun M => M.11
    | S n' =>
        fun M => 
          vsum (fun j =>
                  let a := if Nat.even (fin2nat j)
                           then (M $ fin0 $ j)
                           else (-(M $ fin0 $ j))%A in
                  let d := mdetEx (msubmat M fin0 j) in
                  a * d)
    end.

  Lemma mdetEx_eq_mdet_1 : forall (M : smat 1), mdetEx M = mdet M.
  Proof. intros. cbn. ring. Qed.

  Lemma mdetEx_eq_mdet_2 : forall (M : smat 2), mdetEx M = mdet M.
  Proof. intros. cbv; rewrite !(mnth_eq_nth_m2f 0 M). ring. Qed.

  Lemma mdetEx_eq_mdet_3 : forall (M : smat 3), mdetEx M = mdet M.
  Proof. intros. cbv; rewrite !(mnth_eq_nth_m2f 0 M). ring. Qed.

  Lemma mdetEx_eq_mdet_4 : forall (M : smat 4), mdetEx M = mdet M.
  Proof.
    (* intros. cbv; rewrite !(mnth_eq_nth_m2f 0 M). ring. *)
    (* Qed. *)
  Admitted.
  
  Theorem mdetEx_eq_mdet : forall {n} (M : smat (S n)), mdetEx M = mdet M.
  Proof.
    intros.
    unfold mdet. unfold mdetEx.
    Abort.

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
          (madjSign i j * mdet (msubmat M i j))%A
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
          (madjSign i j * mdet (msubmat M j i))%A
    end.

  (** (madj M).ij = (-1)^(i+j) * det(submat M i j) *)
  Lemma mnth_madj : forall {n} (M : smat (S n)) i j,
      (madj M) i j = (madjSign i j * mdet (msubmat M j i))%A.
  Proof. intros. auto. Qed.
  
  (** (madj M) $ i $ j = (mcofactor M) $ j $ i. *)
  Lemma mnth_madj_eq_mnth_mcofactor_swap : forall {n} (M : smat n) i j,
      (madj M) $ i $ j = (mcofactor M) $ j $ i.
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
    let D := mdet A0 in
    fun i => mdet (msetc A0 b i) / D.


  (* ======================================================================= *)
  (** ** Invertible matrix by determinant *)

  (** A matrix `M` is invertible, if its determinant is not zero.
      Note that, we use `AM` to denote `Adjoint Matrix method` *)
  Definition minvertibleAM {n} (M : smat n) : bool :=
    if Aeqdec (mdet M) 0 then false else true.

  (* `minvertibleAM M` is true, iff the determinant of `M` is not zero *)
  Lemma minvertibleAM_true_iff_mdet_neq0 : forall {n} (M : smat n),
      minvertibleAM M = true <-> mdet M <> 0.
  Proof. intros. unfold minvertibleAM. destruct Aeqdec; try easy. Qed.

  (* `minvertibleAM M` is false, iff the determinant of `M` is zero *)
  Lemma minvertibleAM_false_iff_mdet_eq0 : forall {n} (M : smat n),
      minvertibleAM M = false <-> mdet M = 0.
  Proof. intros. unfold minvertibleAM. destruct Aeqdec; try easy. Qed.

  (* Identity matrix is invertibleAM *)
  Lemma mat1_invertibleAM_true : forall {n}, minvertibleAM (@mat1 n) = true.
  Proof.
    intros. unfold minvertibleAM.
    rewrite mdet_mat1. destruct Aeqdec; auto. apply field_1_neq_0 in e; auto.
  Qed.

  
  (* ======================================================================= *)
  (** ** Inverse matrix by adjoint matrix (option version) *)

  (** Inverse matrix by adjoint matrix (option version) *)
  Definition minvAMo {n} (M : smat n) : option (smat n) :=
    if minvertibleAM M
    then Some ((1 / mdet M) \.* (madj M))
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
      exists ((1 / mdet M) \.* (madj M)). auto.
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
  Definition minvAM {n} (M : smat n) := (1 / mdet M) \.* (madj M).
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
    intros. unfold minvAM.
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

  (* 将 a <> 0 |- b <> 0 转换为 b = 0 |- a = 0，并尝试自动证明 *)
  Ltac solve_neq0_neq0 :=
    match goal with
    | H: ?e1 <> Azero |- ?e2 <> Azero =>
        let H1 := fresh "H1" in
        intros H1; destruct H;
        (* 尝试自动证明 *)
        cbn; ring_simplify; auto
    end.

  (* 将 a = 0 |- b = 0 转换为 a = b，并尝试证明 *)
  Ltac solve_eq0_eq0 :=
    match goal with
    | H: ?a = Azero |- ?b = Azero =>
        symmetry; rewrite <- H at 1;
        (* 尝试自动证明 *)
        try ring
    end.
  
  (** *** Inverse matrix of of concrete dimension *)
  Section concrete.
    
    Definition minvAM1 (M : smat 1) : smat 1 := l2m 0 [[1/M.11]].

    (** |M| <> 0 -> minv1 M = inv M *)
    Lemma minvAM1_eq_minvAM : forall M, mdet M <> Azero -> minvAM1 M = minvAM M.
    Proof.
    (*   intros.  *)
    (*   ring_simplify. *)
    (*   rewrite (meq_iff_nth_m2f Azero); intros. cbv. *)
    (*   destruct i,j; auto. field. solve_neq0_neq0. *)
      (* Qed. *)
    Admitted.

    (*
    Definition minvAM2 (M : smat 2) : smat 2 :=
      let d := mdet2 M in
      l2m 0 [[M.22/d; -M.12/d]; [-M.21/d; M.11/d]].

    (** |M| <> 0 -> minv2 M = inv M *)
    Lemma AM_minv2_eq_inv : forall M, mdet M <> Azero -> minv2AM M = minvAM M.
    (* Proof. *)
    (*   intros. rewrite (meq_iff_nth_m2f Azero); intros. *)
    (*   repeat (try destruct i; try destruct j; try lia); cbv; *)
    (*     rewrite !(mnth_eq_nth_m2f Azero M) in *; try field. *)
    (*   all: try solve_neq0_neq0; rewrite !(mnth_eq_nth_m2f Azero M) in *. *)
    (* Qed. *)
    Admitted.
    
    (* Note, this formula come from matlab, needn't manual work *)
    Definition minv3AM (M : smat 3) : smat 3 :=
      let d := mdet3 M in
      (l2m
         [[(M.22*M.33-M.23*M.32)/d; -(M.12*M.33-M.13*M.32)/d; (M.12*M.23-M.13*M.22)/d];
          [-(M.21*M.33-M.23*M.31)/d; (M.11*M.33-M.13*M.31)/d; -(M.11*M.23-M.13*M.21)/d];
          [(M.21*M.32-M.22*M.31)/d; -(M.11*M.32-M.12*M.31)/d; (M.11*M.22-M.12*M.21)/d]])%A.

    (** |M| <> 0 -> minv3 M = inv M *)
    Lemma AM_minv3_eq_inv : forall M, mdet M <> Azero -> minv3AM M = minvAM M.
    Proof.
      (* NEED 3 Seconds, JUST TURN OFF TO SPEED UP *)
      (*
      intros. rewrite (meq_iff_nth_m2f Azero); intros.
      repeat (try destruct i; try destruct j; try lia); cbv;
        rewrite !(mnth_eq_nth_m2f Azero M) in *; try field.
      all: try solve_neq0_neq0; rewrite !(mnth_eq_nth_m2f Azero M) in *.
      all: try solve_eq0_eq0.
    Qed.
       *)
      Admitted.

    Definition minv4AM (M : smat 4) : smat 4 :=
      let d := mdet4 M in
      l2m
        [[(M.22*M.33*M.44 - M.22*M.34*M.43 - M.23*M.32*M.44 + M.23*M.34*M.42 + M.24*M.32*M.43 - M.24*M.33*M.42)/d;
          -(M.12*M.33*M.44 - M.12*M.34*M.43 - M.13*M.32*M.44 + M.13*M.34*M.42 + M.14*M.32*M.43 - M.14*M.33*M.42)/d;
          (M.12*M.23*M.44 - M.12*M.24*M.43 - M.13*M.22*M.44 + M.13*M.24*M.42 + M.14*M.22*M.43 - M.14*M.23*M.42)/d;
          -(M.12*M.23*M.34 - M.12*M.24*M.33 - M.13*M.22*M.34 + M.13*M.24*M.32 + M.14*M.22*M.33 - M.14*M.23*M.32)/d];
         [-(M.21*M.33*M.44 - M.21*M.34*M.43 - M.23*M.31*M.44 + M.23*M.34*M.41 + M.24*M.31*M.43 - M.24*M.33*M.41)/d;
          (M.11*M.33*M.44 - M.11*M.34*M.43 - M.13*M.31*M.44 + M.13*M.34*M.41 + M.14*M.31*M.43 - M.14*M.33*M.41)/d;
          -(M.11*M.23*M.44 - M.11*M.24*M.43 - M.13*M.21*M.44 + M.13*M.24*M.41 + M.14*M.21*M.43 - M.14*M.23*M.41)/d;
          (M.11*M.23*M.34 - M.11*M.24*M.33 - M.13*M.21*M.34 + M.13*M.24*M.31 + M.14*M.21*M.33 - M.14*M.23*M.31)/d];
         [(M.21*M.32*M.44 - M.21*M.34*M.42 - M.22*M.31*M.44 + M.22*M.34*M.41 + M.24*M.31*M.42 - M.24*M.32*M.41)/d;
          -(M.11*M.32*M.44 - M.11*M.34*M.42 - M.12*M.31*M.44 + M.12*M.34*M.41 + M.14*M.31*M.42 - M.14*M.32*M.41)/d;
          (M.11*M.22*M.44 - M.11*M.24*M.42 - M.12*M.21*M.44 + M.12*M.24*M.41 + M.14*M.21*M.42 - M.14*M.22*M.41)/d;
          -(M.11*M.22*M.34 - M.11*M.24*M.32 - M.12*M.21*M.34 + M.12*M.24*M.31 + M.14*M.21*M.32 - M.14*M.22*M.31)/d];
         [-(M.21*M.32*M.43 - M.21*M.33*M.42 - M.22*M.31*M.43 + M.22*M.33*M.41 + M.23*M.31*M.42 - M.23*M.32*M.41)/d;
          (M.11*M.32*M.43 - M.11*M.33*M.42 - M.12*M.31*M.43 + M.12*M.33*M.41 + M.13*M.31*M.42 - M.13*M.32*M.41)/d;
          -(M.11*M.22*M.43 - M.11*M.23*M.42 - M.12*M.21*M.43 + M.12*M.23*M.41 + M.13*M.21*M.42 - M.13*M.22*M.41)/d;
          (M.11*M.22*M.33 - M.11*M.23*M.32 - M.12*M.21*M.33 + M.12*M.23*M.31 + M.13*M.21*M.32 - M.13*M.22*M.31)/d]]%A.
    
    (** |M| <> 0 -> minv4 M = inv M *)
    Lemma AM_minv4_eq_inv : forall M, mdet M <> Azero -> minv4AM M = minvAM M.
    Proof.
      (* NEED 30 Seconds, JUST TURN OFF TO SPEED UP *)
      (*
        intros. rewrite (meq_iff_nth_m2f Azero); intros.
      repeat (try destruct i; try destruct j; try lia); cbv;
        rewrite !(mnth_eq_nth_m2f Azero M) in *; try field.
      all: try solve_neq0_neq0; rewrite !(mnth_eq_nth_m2f Azero M) in *.
      all: try solve_eq0_eq0.
       *)
    Admitted.

     *)
    
  End concrete.
  
End minvAM.
