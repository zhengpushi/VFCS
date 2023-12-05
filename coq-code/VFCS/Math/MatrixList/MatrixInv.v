(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with function (Safe version)
  author    : ZhengPu Shi
  date      : 2021.12

  remark    :
  1. This is the safe version of NatFun implementation, that means,
     we modified the definition of matrix type to improve the type safety.
  2. The old definition of matrix type is:
  
        Definition mat {T} (r c : nat) := nat -> nat -> A.

     while new definition of matrix type is:

        Record mat {T} (r c : nat) := mk_mat { matf : nat -> nat -> T }.
 *)


Require Import NatExt.
Require Import MatrixList.ElementType.
Require Import MatrixList.Matrix.
Require Import MatrixList.MatrixDet.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ======================================================================= *)
(** ** Matrix Inversion with gauss elimination. *)
Module GaussElim (E : RingElementType).
  Import E.
  Definition mat r c := @mat A r c.
  Definition mnth {r c} (m : mat r c) := mnth Azero m.
  Notation "M $ i $ j " := (mnth M i j) : mat_scope.
  
  
  (* 对线性方程组的增广矩阵作初等变换，对应于矩阵的初等行变换 *)
  Inductive MatElemRowOpers :=
  | MERO_add (i j : nat) (k : A)  (* 把第 i 行的 k 倍加到第 j 行，记作 j + k * i *)
  | MERO_swap (i j : nat)         (* 交换 i, j 两行，记作 <i,j> *)
  | MERO_mul (i : nat) (k : A)    (* 用非零数 k 乘以第 i 行，记作 k * i *)
  .

  (* 行阶梯形矩阵 *)

  (* 简化行阶梯形矩阵 *)

  (* Gauss Jordan 算法：
     1. 将矩阵A化简为行阶梯形
     (1). 从第i行j列开始向下查找(初始时，i=0,j=0)，看是否全为0：
          若是，则进入第i行(j+1)列；若不是，则找到第一个不为0的i'行
     (2). 交换 i' 和 i 行，<i,i'>
     (3). 对第i行做行变换：(1/A[i,j]) * i，使得A[i,j]变为1
     (4). 将第i行以下的每一行 i'' 做行变换：i'' + (- A[i'',j]) * i，
          使得第j列的第i行以下全为0。
     (5). i++, j++，进入 (1)
     2. 化简为h简化行阶梯性
     (1). 倒序进行
   *)
  (* Variable r c : nat. *)
  (* Variable m : mat r c. *)
  (* Variable i j : nat. *)

  (* 第j列的第i行以下元素都是0 *)
  Let belowElemsAllZero {r c} (m : mat r c) (i j : nat) : bool :=
        forallb (fun k => Aeqb (m $ k $ j) Azero) (seq (S i) (r - (S i))).

  (* 第j列的第i行开始往下，第1个不为0的行号 *)
  Definition firstNonZeroRowIdx {r c} (m : mat r c) (i j : nat) : option nat :=
    let fix F (fuel:nat) (i0 : nat) : option nat :=
      match fuel with
      | O => None
      | S fuel' =>
          if Aeqb (m$i0$j) Azero then Some i0 else F fuel' (S i0)
      end in
    F r i.

  Definition rowEchelonForm {r c} (m : mat r c) : (list MatElemRowOpers * mat r c) :=
    

End GaussElim.

Section MatInv.

  (** fold a sequence to a value *)
  Fixpoint reduce {T} (n: nat) (f: T -> nat -> T) (zero: T) : T :=
    match n with
    | O => zero
    | S n' => f (reduce n' f zero) n'
    end.
  
  (* The process of "reduce 5 f 0" *)
  (* f (reduce 4 f 0) 4 *)
  (* f (f (reduce 3 f 0) 3) 4 *)
  (* f (f (f (reduce 2 f 0) 2) 3) 4 *)
  (* f (f (f (f (reduce 1 f 0) 1) 2) 3) 4 *)
  (* f (f (f (f (f (reduce 0 f 0) 1) 2) 3) 4 *)
  (* f (f (f (f (f 0 1) 2) 3) 4 *)
  (* Compute reduce 5 Nat.add 0. *)

  (* Understand the "reduce" function *)
  Section test.
    (*   R a f 3 *)
    (* = f (R a f 2) 2 *)
    (* = f (f (R a f 1) 1) 2 *)
    (* = f (f (f (R a f 0) 0) 1) 2 *)
    (* = f (f (f a 0) 1) 2 *)
    (* that is: (a0 + f0) + f1 + ... *)
    Let Fixpoint reduce' {T} (a0:T) (f: T -> nat -> T) (n:nat) : T :=
      match n with
      | O => a0
      | S n' => f (reduce' a0 f n') n'
      end.

    Import Reals.
    Let f1 : nat -> R := fun i => INR i.
    (* Compute reduce' R0 (fun r0 i => Rplus r0 (f1 i)) 5. *)
    (* Compute reduce' 0 Nat.add 5. *)

  End test.


  (** 任给两个序列f g，个数n，以及关系R，生成所有这些点对点对上的关系 *)
  Definition pointwise_n {T} (n: nat) (R: relation T) : relation (nat -> T) :=
    fun (f g : nat -> T) => forall (i: nat), i < n -> R (f i) (g i).

  (** 对于序列m1 m2, 若前 S n 个点对上都有关系R，则前 n 个点对上也有关系R。*)
  Lemma pointwise_n_decr {A}:
    forall (n : nat) (m1 m2 : nat -> A) (R : relation A),
      pointwise_n (S n) R m1 m2 -> pointwise_n n R m1 m2.
  Proof. unfold pointwise_n. intuition. Qed.

  
  Context `{F : Field}.
  Infix "+" := Tadd.
  Infix "*" := Tmul.
  Infix "*" := (mmul (T0:=T0)(Tadd:=Tadd)(Tmul:=Tmul)) : mat_scope.

  (* sum f(0) f(1) ... f(k-1) *)
  Notation sum k f := (reduce k (fun acc x => (acc + f x)%T) T0).

  (** (m1 * m2)[i,j] = m1.row[i] dot m2.col[j] *)
  Parameter Mtimes_help : forall {m n p} (m1: @mat T m n) (m2: @mat T n p),
    forall i j,
      i < m -> j < p ->
      mnth T0 (m1 * m2)%M i j =
        sum n (fun k => ((mnth T0 m1 i k) * (mnth T0 m2 k j))%T).

  (** (f m1 m2)[i,j] = f m1[i,j] m2[i,j] *)
  Parameter Melement_op_help :
    forall {m n} (m1: @mat T m n) (m2: @mat T m n) (op: T -> T -> T),
    forall i j,
      i < m -> j < n ->
      mnth T0 (mmap2 op m1 m2) i j = op (mnth T0 m1 i j) (mnth T0 m2 i j).

End MatInv.


Module coordinate_transform_test.

  Import Reals.
  Open Scope R.
  
  (* ref:
  https://en.wikipedia.org/wiki/Matrix_(mathematics)#Basic_operations
   *)

  Infix "*" := Rmult.
  Infix "+" := Rplus.
  Infix "+" := (madd (Tadd:=Rplus)) : mat_scope.
  Infix "*" := (mmul (Tadd:=Rplus) (Tmul:=Rmult) (T0:=R0)) : mat_scope.
  Infix "c*" := (mcmul (Tmul:=Rmult)) : mat_scope.
  Notation "m \T" := (mtrans m) : mat_scope.

  Open Scope mat_scope.

  Definition m1 := l2m 0 2 3 [[1;3;1];[1;0;0]].
  Definition m2 := l2m 0 2 3 [[0;0;5];[7;5;0]].
  Definition m3 := l2m 0 2 3 [[1;3;6];[8;5;0]].
  Example madd_m1_m2_eq_m3 : m1 + m2 = m3.
  Proof. apply meq_iff. cbn. repeat f_equal; ring. Qed.

  Definition m4 := l2m 0 2 3 [[1; 8;-3];[4;-2; 5]].
  Definition m5 := l2m 0 2 3 [[2;16;-6];[8;-4;10]].
  Example mscale_2_m4_eq_m5 : 2 c* m4 = m5.
  Proof. apply meq_iff. cbn. repeat f_equal; ring. Qed.
  
  Definition m6 := l2m 0 2 3 [[1;2;3];[0;-6;7]].
  Definition m7 := l2m 0 3 2 [[1;0];[2;-6];[3;7]].
  Example mtrans_m6_eq_m7 : m6\T = m7.
  Proof. apply meq_iff. cbn. auto. Qed.
  
  Variable θ ψ φ : R.
  Definition Rx (α : R) : mat 3 3 :=
    mk_mat_3_3
      1         0           0
      0         (cos α)     (sin α)
      0         (-sin α)%R    (cos α).

  Definition Ry (β : R) : mat 3 3 :=
    mk_mat_3_3
      (cos β)   0           (-sin β)%R
      0         1           0
      (sin β)   0           (cos β).

  Definition Rz (γ : R) : mat 3 3 :=
    mk_mat_3_3 
      (cos γ)   (sin γ)   0
      (-sin γ)  (cos γ)   0
      0         0         1.

  Definition R_b_e_direct : mat 3 3 :=
    (mk_mat_3_3
       (cos θ * cos ψ)
       (cos ψ * sin θ * sin φ - sin ψ * cos φ)
       (cos ψ * sin θ * cos φ + sin φ * sin ψ)
       
       (cos θ * sin ψ)
       (sin ψ * sin θ * sin φ + cos ψ * cos φ)
       (sin ψ * sin θ * cos φ - cos ψ * sin φ)
       
       (-sin θ)
       (sin φ * cos θ)
       (cos φ * cos θ))%R.
  
  Opaque cos sin.

  Lemma Rx_Ry_Rz_eq_Rbe : (Rz ψ)\T * (Ry θ)\T * (Rx φ)\T = R_b_e_direct.
  Proof. apply meq_iff. cbn. repeat (f_equal; try ring). Qed.
  
End coordinate_transform_test.


(* ==================================== *)
(** ** Determinant of a matrix *)

Section mdet.
  Context `{R : Ring}.
  (* Add Ring ring_inst : make_ring_theory. *)
  
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Asub := (fun x y => Tadd x (Topp y)).
  Infix "-" := Asub : T_scope.
  Infix "*" := Tmul : T_scope.

  Infix "*" := (mmul (Tadd:=Tadd)(T0:=T0)(Tmul:=Tmul)) : mat_scope.

  (** *** Determinant of a square matrix (original definition) *)
  Section def.

  (* 行列式的定义：它是一个单项式的求和，每个单项式是矩阵中不同行不同列元素的乘积，并
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

    ？
    (* ? *)
    Variable a b c : T.
    Compute perm 0 (seq 0 3).
    (* Let dl := perm 0 (seq 0 3). *)
    (* Let l := [1;2;3]. *)
    (* Compute nth 1 l 0. *)
    (* Compute map (fun i => (i, nth i l 0)) (seq 0 3). *)
    (* Compute map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)

  End def.
  (* Let dl1 := map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)
  (* Variable a00 a01 a02 a10 a11 a12 a20 a21 a22 : T. *)
  (* Definition m : smat 3 := mat_3_3 a00 a01 a02 a10 a11 a12 a20 a21 a22. *)
  (* Compute map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)

  (* (** all items in a determinant *) *)
  (* Let dl2 := map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)
  (* Compute dl2. *)

  (* Definition n := 3. *)
  (* Compute perm 0 (seq 0 n). (* *)
   (*  = [[0; 1; 2]; [0; 2; 1]; [1; 0; 2]; [1; 2; 0]; [2; 0; 1]; [2; 1; 0]] *)
   (*  : list (list nat) *) *)

  (* Definition item_of_det {n : nat} (m : smat n) (l : list nat) : T := *)
  (*   fold_left Tmul (map (fun i => m!i!(nth i l 0)) l) T1. *)

  (* (** Definition of determinant *) *)
  (* Definition det_def {n : nat} (m : smat n) : T := *)
  (*   fold_left Tadd (map (fun l => item_of_det m l) (perm 0 (seq 0 n))) T0. *)

  (* Compute det_orig m. *)
  
  (* Compute fold_left Tmul [a00;a01;a02]. *)
  (* Compute fold_left Tadd. *)
  

  (** Get the sub square matrix which remove r-th row and c-th column
        from a square matrix. *)
  Definition msubmat {n} (m : smat (S n)) (r c : nat) : smat n :=
    f2m
      (fun i j =>
         let i' := (if i <? r then i else S i) in
         let j' := (if j <? c then j else S j) in
         m $ i' $ j').

  Global Instance submat_mor (n : nat) :
    Proper (meq (Teq:=Teq) => eq => eq => meq (Teq:=Teq)) (@msubmat n).
  Proof. simp_proper. lma. all: apply H; auto; lia. Qed.
  

  (** Try to prove a proposition such as:
      "~(exp1 = 0) -> ~(exp2 = 0)" *)
  Ltac reverse_neq0_neq0 :=
    match goal with
    | H: ~(?e1 = T0)%T |- ~(?e2 = T0)%T =>
        let H1 := fresh "H1" in
        intro H1; destruct H; ring_simplify; ring_simplify in H1;
        try rewrite H1; try easy
    end.

  (** Determinant of a square matrix, by expanding the first row *)
  Fixpoint mdet {n} : smat n -> T :=
    match n with
    | 0 => fun _ => T1
    | S n' =>
        fun m =>
          fold_left Tadd
            (map (fun i =>
                    let a := if Nat.even i then (m$0$i) else (-(m$0$i))%T in
                    let d := mdet (msubmat m 0 i) in
                    (a * d)%T) (seq 0 n)) T0
    end.

  Global Instance mdet_mor (n : nat) : Proper (meq (Teq:=Teq) => Teq) (@mdet n).
  Proof.
    simp_proper. induction n; intros; try easy. simpl.
    apply fold_left_aeq_mor.
    - apply map_seq_eq. intros. f_equiv.
      + destruct (Nat.even i). apply H; lia. f_equiv. apply H; lia.
      + apply IHn. rewrite H. easy.
    - f_equiv. f_equiv.
      + apply m2f_mor; auto; lia.
      + apply IHn. rewrite H. easy.
  Qed.

  (** *** Properties of determinant *)
  Section props.

    Lemma mdet_1 : forall {n}, (@mdet n (mat1 T0 T1) = T1)%T.
    Proof.
    Admitted.

    Lemma mdet_mtrans : forall {n} (m : smat n), (mdet (m\T) = mdet m)%T.
    Proof.
    Admitted.

    Lemma mdet_mmul : forall {n} (m p : smat n), (mdet (m * p)%M = mdet m * mdet p)%T.
    Proof.
    Admitted.

  End props.

  
  (** *** Determinant on concrete dimensions *)
  Section mdet_concrete.

    (** Determinant of a matrix of dimension-1 *)
    Definition mdet1 (m : smat 1) := m.11.

    (** mdet1 m = mdet m *)
    Lemma mdet1_eq_mdet : forall m, (mdet1 m = mdet m)%T.
    Proof. intros. mat2fun. ring. Qed.
    
    (** mdet m <> 0 <-> mdet_exp <> 0 *)
    Lemma mdet1_neq0_iff : forall (m : smat 1),
        (mdet m != T0) <-> (m.11 != T0).
    Proof. intros. split; intros; mat2fun; reverse_neq0_neq0. Qed.

    (** Determinant of a matrix of dimension-2 *)
    Definition mdet2 (m : smat 2) := (m.11*m.22 - m.12*m.21)%T.

    (** mdet2 m = mdet m *)
    Lemma mdet2_eq_mdet : forall m, (mdet2 m = mdet m)%T.
    Proof. intros. mat2fun. cbv. ring. Qed.

    (** mdet m <> 0 <-> mdet_exp <> 0 *)
    Lemma mdet2_neq0_iff : forall (m : smat 2),
        mdet m != T0 <->  (m.11*m.22 - m.12*m.21 != T0)%T.
    Proof. intros. split; intros; mat2fun; reverse_neq0_neq0. Qed.

    (** Determinant of a matrix of dimension-3 *)
    Definition mdet3 (m : smat 3) :=
      (m.11 * m.22 * m.33 - m.11 * m.23 * m.32 - 
         m.12 * m.21 * m.33 + m.12 * m.23 * m.31 + 
         m.13 * m.21 * m.32 - m.13 * m.22 * m.31)%T.

    (** mdet3 m = mdet m *)
    Lemma mdet3_eq_mdet : forall m, (mdet3 m = mdet m)%T.
    Proof. intros. mat2fun. cbv. ring. Qed.
    
    (** mdet m <> 0 <-> mdet_exp <> 0 *)
    Lemma mdet3_neq0_iff : forall (m : smat 3),
        mdet m != T0 <->
          (m.11 * m.22 * m.33 - m.11 * m.23 * m.32 - 
             m.12 * m.21 * m.33 + m.12 * m.23 * m.31 + 
             m.13 * m.21 * m.32 - m.13 * m.22 * m.31 != T0)%T.
    Proof. intros. split; intros; mat2fun; reverse_neq0_neq0. Qed.

    (** Determinant of a matrix of dimension-4 *)
    Definition mdet4 (m : smat 4) :=
      (m.11*m.22*m.33*m.44 - m.11*m.22*m.34*m.43 - m.11*m.23*m.32*m.44 + m.11*m.23*m.34*m.42 +
         m.11*m.24*m.32*m.43 - m.11*m.24*m.33*m.42 - m.12*m.21*m.33*m.44 + m.12*m.21*m.34*m.43 +
         m.12*m.23*m.31*m.44 - m.12*m.23*m.34*m.41 - m.12*m.24*m.31*m.43 + m.12*m.24*m.33*m.41 +
         m.13*m.21*m.32*m.44 - m.13*m.21*m.34*m.42 - m.13*m.22*m.31*m.44 + m.13*m.22*m.34*m.41 +
         m.13*m.24*m.31*m.42 - m.13*m.24*m.32*m.41 - m.14*m.21*m.32*m.43 + m.14*m.21*m.33*m.42 +
         m.14*m.22*m.31*m.43 - m.14*m.22*m.33*m.41 - m.14*m.23*m.31*m.42 + m.14*m.23*m.32*m.41)%T.

    (** mdet4 m = mdet m *)
    Lemma mdet4_eq_mdet : forall m, (mdet4 m = mdet m)%T.
    Proof. intros. mat2fun. cbv. ring. Qed.
    
  End mdet_concrete.

End mdet.
  

(* ==================================== *)
(** ** Inverse matrix with the help of determinant and adjoint matrix. *)
Section matrix_inversion.
  Context `{R:Ring}.
  Add Ring ring_thy_inst : (make_ring_theory R).

  Infix "=" := Teq : T_scope.
  Infix "!=" := (fun a b => ~(a = b)) : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Asub := (fun x y => Tadd x (Topp y)).
  Infix "-" := Asub : T_scope.
  Infix "*" := Tmul : T_scope.

  Infix "*" := (@mmul T Tadd T0 Tmul _ _ _) : mat_scope.
  Infix "c*" := (@mcmul T Tmul _ _) : mat_scope.
  Infix "=" := (meq (Teq:=Teq)) : mat_scope.
  (* Notation "m ! i ! j " := (mnth T0 m i j) : mat_scope. *)
  Notation mat1 := (mat1 T0 T1).
  Notation l2m := (@l2m T T0 _ _).
  Notation smat n := (smat T n).
  Notation mdet := (mdet (Tadd:=Tadd)(T0:=T0)(Topp:=Topp)(Tmul:=Tmul)(T1:=T1)).
  Notation mdet2 := (mdet2 (Tadd:=Tadd)(Topp:=Topp)(Tmul:=Tmul)).
  Notation mdet3 := (mdet3 (Tadd:=Tadd)(Topp:=Topp)(Tmul:=Tmul)).
  Notation mdet4 := (mdet4 (Tadd:=Tadd)(Topp:=Topp)(Tmul:=Tmul)).

  (** Try to prove a proposition such as:
      "~(exp1 = 0) -> ~(exp2 = 0)" *)
  Ltac reverse_neq0_neq0 :=
    match goal with
    | H: ~(?e1 = T0)%T |- ~(?e2 = T0)%T =>
        let H1 := fresh "H1" in
        intro H1; destruct H; ring_simplify; ring_simplify in H1;
        try rewrite H1; try easy
    end.

  (** T square matrix is invertible, if its determinant is nonzero *)
  Definition minvertible {n} (m : smat n) : Prop :=
    exists m' : smat n, (m * m' = mat1) \/ (m' * m = mat1).

  (** invertible mat1 *)
  Lemma minvertible_1 : forall n : nat, @minvertible n mat1.
  Proof.
  Admitted.

  (** T square matrix is invertible, if its determinant is nonzero *)
  Lemma minvertible_iff_mdet_n0 : forall {n} (m : smat n),
      minvertible m <-> mdet m <> T0.
  Proof.
  Admitted.

  (** invertible m -> invertible (m\T) *)
  Lemma minvertible_trans : forall n (m : smat n),
      minvertible m -> minvertible (m\T).
  Proof.
  Admitted.

  (** invertible m -> invertible p -> invertible (m * p) *)
  Lemma minvertible_mul : forall n (m p : smat n),
      minvertible m -> minvertible p -> minvertible (m * p).
  Proof.
  Admitted.

  
  (** *** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  (** That is: adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  Section adj.

    Definition madj {n} : smat n -> smat n := 
      match n with
      | O => fun m => m 
      | S n' =>
          fun m =>
            f2m (fun i j =>
                   let s := if Nat.even (i + j) then T1 else (-T1)%T in
                   let d := mdet (msubmat m j i) in 
                   (s * d)%T)
      end.

    Global Instance madj_mor (n:nat) :
      Proper (meq (Teq:=Teq) => meq (Teq:=Teq)) (@madj n).
    Proof.
      simp_proper. intros. destruct n; auto. simpl.
      unfold meq; intros; simpl. f_equiv. rewrite H. easy.
    Qed.

  End adj.

  (** *** We need a field structure *)
  Context `{F:Field T Tadd T0 Topp Tmul T1 Tinv Teq}.
  Add Field field_thy_inst : (make_field_theory F).

  Notation "/ a" := (Tinv a) : T_scope.
  Notation Tdiv := (fun x y => Tmul x (Tinv y)).
  Infix "/" := Tdiv : T_scope.

  (** *** Cramer rule *)
  Section cramer_rule.
    
    (** Exchange one column of a square matrix *)
    Definition mchgcol {n} (m : smat n) (k : nat) (v : mat n 1) : smat n :=
      f2m (fun i j => if (Nat.eqb j k) then (v$i$0)%nat else m$i$j).
    
    (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid only when D is not zero *)
    Definition cramerRule {n} (A : smat n) (b : mat n 1) : mat n 1 :=
      let D := mdet T in
      f2m (fun i j => let Di := mdet (mchgcol T i b) in (Di / D)).
    
  End cramer_rule.

  
  (** *** Matrix Inversion *)
  Section inv.

    Definition minv {n} (m : smat n) := (T1 / mdet m) c* (madj m).
    Notation "m ⁻¹" := (minv m) : mat_scope.

    Global Instance minv_mor (n : nat) :
      Proper (meq (Teq:=Teq) => meq (Teq:=Teq)) (@minv n).
    Proof. simp_proper. intros. unfold minv. rewrite H. easy. Qed.
    
    (** m * p = mat1 -> m ⁻¹ = p *)
    Lemma mmul_eq1_iff_minv_l : forall {n} (m p : smat n),
        m * p = mat1 <-> minv m = p.
    Proof.
    Admitted.

    (** m * p = mat1 <-> p ⁻¹ = m *)
    Lemma mmul_eq1_iff_minv_r : forall {n} (m p : smat n),
        m * p = mat1 <-> minv p = m.
    Proof.
    Admitted.

    (** invertible m -> invertible (m⁻¹) *)
    Lemma minvertible_inv : forall {n} (m : smat n), minvertible m -> minvertible (m⁻¹).
    Proof.
    Admitted.

    (** m * m⁻¹ = mat1 *)
    Lemma mmul_minv_r : forall {n} (m : smat n), m * m⁻¹ = mat1.
    Proof.
    Admitted.

    (** m⁻¹ * m = mat1 *)
    Lemma mmul_minv_l : forall {n} (m : smat n), (minv m) * m = mat1.
    Proof.
    Admitted.

    (** mat1 ⁻¹ = mat1 *)
    Lemma minv_1 : forall {n}, @minv n mat1 = mat1.
    Proof.
    Admitted.

    (** m ⁻¹ ⁻¹ = m *)
    Lemma minv_minv : forall {n} (m : smat n), minvertible m -> m ⁻¹ ⁻¹ = m.
    Proof.
    Admitted.

    (** (m * m') ⁻¹ = m' ⁻¹ * m ⁻¹ *)
    Lemma minv_mmul : forall {n} (m m' : smat n),
        minvertible m -> minvertible m' -> (m * m')⁻¹ = m' ⁻¹ * m ⁻¹.
    Proof.
    Admitted.

    (** (m\T) ⁻¹ = (m ⁻¹)\T *)
    Lemma minv_mtrans : forall {n} (m : smat n), minvertible m -> (m\T) ⁻¹ = (m ⁻¹)\T.
    Proof.
    Admitted.

    (** mdet (m⁻¹) = 1 / (mdet m) *)
    Lemma mdet_minv : forall {n} (m : smat n), (mdet (m ⁻¹) = T1 / (mdet m))%T.
    Admitted.
    
  End inv.

  
  (** *** Direct compute inversion of a symbol matrix of 1/2/3rd order. *)
  Section FindFormula.
    Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : T.
    Let m1 := mk_mat_1_1 (T0:=T0) a11.
    Let m2 := mk_mat_2_2 (T0:=T0) a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 (T0:=T0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
    Let m4 := mk_mat_4_4 (T0:=T0)
                a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44.

    (* Compute (m2l (minv m1)). *)
    (* Compute (m2l (minv m2)). *)
    (* Compute (m2l (minv m3)). *)
    (* Compute (m2l (minv m4)). *)
    (* Although this is correct, but the expression is too long. *)
    (* We want to simplify it with RAST *)
    
  End FindFormula.

  
  (** *** Inversion matrix of common finite dimension *)
  Section concrete.
    Definition minv1 (m : smat 1) : smat 1 := l2m [[T1/m.11]].

    (** mdet m <> 0 -> minv1 m = inv m *)
    Lemma minv1_eq_inv : forall m, mdet m != T0 -> minv1 m = minv m.
    Proof. lma. reverse_neq0_neq0. Qed.

    (** minv1 m * m = mat1 *)
    Lemma minv1_correct_l : forall (m : smat 1),
        mdet m != T0 -> (minv1 m) * m = mat1.
    Proof. lma. reverse_neq0_neq0. Qed.

    (** m * minv1 m = mat1 *)
    Lemma minv1_correct_r : forall (m : smat 1),
        mdet m != T0 -> m * (minv1 m) = mat1.
    Proof. lma. reverse_neq0_neq0. Qed.

    (* ==================================== *)
    (** ** Inversion matrix of dimension-2 *)
    Definition minv2 (m : smat 2) : smat 2 :=
      let d := mdet2 m in
      (l2m [[m.22/d; -m.12/d]; [-m.21/d; m.11/d]])%T.

    (** mdet m <> 0 -> minv2 m = inv m *)
    Lemma minv2_eq_inv : forall m, mdet m != T0 -> minv2 m = minv m.
    Proof. lma; reverse_neq0_neq0. Qed.
    
    (** minv2 m * m = mat1 *)
    Lemma minv2_correct_l : forall (m : smat 2),
        mdet m != T0 -> (minv2 m) * m = mat1.
    Proof. lma; reverse_neq0_neq0. Qed.
    
    (** m * minv2 m = mat1 *)
    Lemma minv2_correct_r : forall (m : smat 2),
        mdet m != T0 -> m * (minv2 m) = mat1.
    Proof. lma; reverse_neq0_neq0. Qed.
    
    (* ==================================== *)
    (** ** Inversion matrix of dimension-3 *)
    (* Note, this formula could be provided from matlab, thus avoiding manual work *)
    Definition minv3 (m : smat 3) : smat 3 :=
      let d := mdet3 m in
      (l2m
         [[(m.22*m.33-m.23*m.32)/d; -(m.12*m.33-m.13*m.32)/d; (m.12*m.23-m.13*m.22)/d];
          [-(m.21*m.33-m.23*m.31)/d; (m.11*m.33-m.13*m.31)/d; -(m.11*m.23-m.13*m.21)/d];
          [(m.21*m.32-m.22*m.31)/d; -(m.11*m.32-m.12*m.31)/d; (m.11*m.22-m.12*m.21)/d]])%T.
    
    (** mdet m <> 0 -> minv3 m = inv m *)
    Lemma minv3_eq_inv : forall m, mdet m != T0 -> minv3 m = minv m.
    Proof.
      (* lma; reverse_neq0_neq0. *)
      Opaque Matrix.mdet Matrix.mdet3.
      lma;  rewrite mdet3_eq_mdet; field_simplify; f_equiv; auto.
      Transparent Matrix.mdet Matrix.mdet3.
      all: cbv; field; auto.
    Qed.
    
    (** minv3 m * m = mat1 *)
    Lemma minv3_correct_l : forall (m : smat 3),
        mdet m != T0 -> (minv3 m) * m = mat1.
    Proof.
      lma; reverse_neq0_neq0.
    Qed.
    
    (** m * minv3 m = mat1 *)
    Lemma minv3_correct_r : forall (m : smat 3),
        mdet m != T0 -> m * (minv3 m) = mat1.
    Proof. lma; reverse_neq0_neq0. Qed.

    (* ==================================== *)
    (** ** Inversion matrix of dimension-3 *)
    (* Note, this formula could be provided from matlab, thus avoiding manual work *)
    Definition minv4 (m : smat 4) : smat 4 :=
      let d := mdet4 m in
      l2m
        [[(m.22*m.33*m.44 - m.22*m.34*m.43 - m.23*m.32*m.44 + m.23*m.34*m.42 + m.24*m.32*m.43 - m.24*m.33*m.42)/d;
          -(m.12*m.33*m.44 - m.12*m.34*m.43 - m.13*m.32*m.44 + m.13*m.34*m.42 + m.14*m.32*m.43 - m.14*m.33*m.42)/d;
          (m.12*m.23*m.44 - m.12*m.24*m.43 - m.13*m.22*m.44 + m.13*m.24*m.42 + m.14*m.22*m.43 - m.14*m.23*m.42)/d;
          -(m.12*m.23*m.34 - m.12*m.24*m.33 - m.13*m.22*m.34 + m.13*m.24*m.32 + m.14*m.22*m.33 - m.14*m.23*m.32)/d];
         [-(m.21*m.33*m.44 - m.21*m.34*m.43 - m.23*m.31*m.44 + m.23*m.34*m.41 + m.24*m.31*m.43 - m.24*m.33*m.41)/d;
          (m.11*m.33*m.44 - m.11*m.34*m.43 - m.13*m.31*m.44 + m.13*m.34*m.41 + m.14*m.31*m.43 - m.14*m.33*m.41)/d;
          -(m.11*m.23*m.44 - m.11*m.24*m.43 - m.13*m.21*m.44 + m.13*m.24*m.41 + m.14*m.21*m.43 - m.14*m.23*m.41)/d;
          (m.11*m.23*m.34 - m.11*m.24*m.33 - m.13*m.21*m.34 + m.13*m.24*m.31 + m.14*m.21*m.33 - m.14*m.23*m.31)/d];
         [(m.21*m.32*m.44 - m.21*m.34*m.42 - m.22*m.31*m.44 + m.22*m.34*m.41 + m.24*m.31*m.42 - m.24*m.32*m.41)/d;
          -(m.11*m.32*m.44 - m.11*m.34*m.42 - m.12*m.31*m.44 + m.12*m.34*m.41 + m.14*m.31*m.42 - m.14*m.32*m.41)/d;
          (m.11*m.22*m.44 - m.11*m.24*m.42 - m.12*m.21*m.44 + m.12*m.24*m.41 + m.14*m.21*m.42 - m.14*m.22*m.41)/d;
          -(m.11*m.22*m.34 - m.11*m.24*m.32 - m.12*m.21*m.34 + m.12*m.24*m.31 + m.14*m.21*m.32 - m.14*m.22*m.31)/d];
         [-(m.21*m.32*m.43 - m.21*m.33*m.42 - m.22*m.31*m.43 + m.22*m.33*m.41 + m.23*m.31*m.42 - m.23*m.32*m.41)/d;
          (m.11*m.32*m.43 - m.11*m.33*m.42 - m.12*m.31*m.43 + m.12*m.33*m.41 + m.13*m.31*m.42 - m.13*m.32*m.41)/d;
          -(m.11*m.22*m.43 - m.11*m.23*m.42 - m.12*m.21*m.43 + m.12*m.23*m.41 + m.13*m.21*m.42 - m.13*m.22*m.41)/d;
          (m.11*m.22*m.33 - m.11*m.23*m.32 - m.12*m.21*m.33 + m.12*m.23*m.31 + m.13*m.21*m.32 - m.13*m.22*m.31)/d]]%T.
    
    (** mdet m <> 0 -> minv4 m = inv m *)
    Lemma minv4_eq_inv : forall m, mdet m != T0 -> minv4 m = minv m.
    (* Proof. *)
    (*   (* lma; reverse_neq0_neq0. *) *)
    (*   Opaque Matrix.mdet Matrix.mdet3. *)
    (*   lma;  rewrite mdet4_eq_mdet; field_simplify; f_equiv; auto. *)
    (*   Transparent Matrix.mdet Matrix.mdet3. *)
    (*   all: cbv; field; auto. *)
    (*   Qed. *)
    Admitted.

    (** minv4 m * m = mat1 *)
    Lemma minv4_correct_l : forall (m : smat 4),
        mdet m != T0 -> (minv4 m) * m = mat1.
    (* Proof. lma; reverse_neq0_neq0. Qed. *)
    Admitted.
    
    (** m * minv4 m = mat1 *)
    Lemma minv4_correct_r : forall (m : smat 4),
        mdet m != T0 -> m * (minv4 m) = mat1.
    (* Proof. lma; reverse_neq0_neq0. Qed. *)
    Admitted.
  
  End concrete.

End matrix_inversion.

Section test.
  (* T Formal Proof of Sasaki-Murao Algorithm
     https://pdfs.semanticscholar.org/ddc3/e8185e10a1d476497de676a3fd1a6ae29595.pdf
   *)
  Import ZArith.
  Open Scope Z.
  Let m1 := @l2m _ 0 4 4 [[2;2;4;5];[5;8;9;3];[1;2;8;5];[6;6;7;1]].
  Notation mdet := (mdet (Tadd:=Z.add) (Topp:=Z.opp) (Tmul:=Z.mul) (T0:=0) (T1:=1)).
  (* Compute mdet m1. *)
End test.


(* ==================================== *)
(** ** Orthogonal matrix *)
Section OrthogonalMatrix.

  (*
  Ref: 
  1. https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group
  2. https://en.wikipedia.org/wiki/Orthogonal_matrix

  -------------------------- O(n) -----------------------------------
  In mathematics, the orthogonal group in dimension n, denoted O(n), is the 
  group of distance-preserving transformations of a Euclidean space of dimension
  n that preserve a fixed point, where the group operation is given by composing
  transformations. 

  The orthogonal group is sometimes called the general orthogonal group, by 
  analogy with the general linear group. Equivalently, it is the group of 
  n × n matrices, where the group operation is given by matrix multiplication 
  (an orthogonal matrix is a real matrix whose inverse equals its transpose). 

  By extension, for any field F, an n × n matrix with entries in F such that its 
  inverse equals its transpose is called an orthogonal matrix over F. 
  The n × n orthogonal matrices form a subgroup, denoted O(n,F), of the general 
  linear group GL(n,F); that is 
         O(n,F) = {Q ∈ GL(n,F) ∣ Q\T * Q = Q * Q\T = I}.
  
  -------------------------- O(3) -----------------------------------
  Every rotation maps an orthonormal basis of R^3 to another orthonormal basis.
  Like any linear transformation of finite-dimensional vector spaces, a rotation 
  can always be represented by a matrix.

  Let R be a given rotation. With respect to the standard basis e1, e2, e3 of R^3 
  the columns of R are given by (Re1, Re2, Re3). Since the standard basis is 
  orthonormal, and since R preserves angles and length, the columns of R form 
  another orthonormal basis. This orthonormality condition can be expressed in 
  the form 
     R\T * R = R * R\T = I,
  where R\T denotes the transpose of R and I is the 3 × 3 identity matrix. 
  Matrices for which this property holds are called orthogonal matrices.

  The group of all 3 × 3 orthogonal matrices is denoted O(3), and consists of all 
  proper and improper rotations.

  In addition to preserving length, proper rotations must also preserve 
  orientation. 
  T matrix will preserve or reverse orientation according to whether the 
  determinant of the matrix is positive or negative. 
  For an orthogonal matrix R, note that "det R\T = det R" implies 
  "(det R)^2 = 1", so that "det R = ±1".

  The subgroup of orthogonal matrices with determinant +1 is called the special 
  orthogonal group, denoted SO(3). 
  Thus every rotation can be represented uniquely by an orthogonal matrix with unit 
  determinant. Moreover, since composition of rotations corresponds to matrix 
  multiplication, the rotation group is isomorphic to the special orthogonal group 
  SO(3).

  Improper rotations correspond to orthogonal matrices with determinant −1, and 
  they do not form a group because the product of two improper rotations is a 
  proper rotation. 

  ----------- 中文笔记 ---------------
  Orthogonal: 正交的，一般用于描述一组基是相互正交的（垂直的）
  Orthonormal Basic: 标准正交基，两两正交，并且单个向量具有单位长度。
  Gram-Schmidt: 施密特正交化。以2维为例，该算法保持r1不变，r3的改变最多。
  有一种无偏差的递增正交化算法，不偏向特定轴，需要多次迭代（比如10次），然后用1次
    标准的Gram-Schmidt算法来保证完全正交。
  O(n): Orthogonal Group 正交群（保距，行列式为±1）
  SO(n): Special Orthogonal Group 特殊正交群（保持手性，行列式为1）
    Proper rotation: 正确的旋转 (行列式为1)
    Improper rotation: 错误的旋转（行列式为-1）, rotation-reflect, 旋转反射，瑕旋转
  ----------------------
  补充一些理论：
  1. 特殊矩阵：对称（自伴）、斜对称（斜伴）、正交（酉）、正规矩阵
      实矩阵                      复矩阵
      条件           名称         条件            名称
  (1) T = A\T        对称阵       T = A\H         自伴阵
  (2) T = -A\T       斜称阵       T = -A\H        斜伴阵
  (3) AA\T = E       正交阵       AA\H = E        酉矩阵
  (4)                            T A\H=A\H T      正规矩阵
  其中，(1),(2),(3)都是正规矩阵

  正规矩阵的一个定理：每个 n*n 正规矩阵A，都有一个由对应于特征值λ1,...,λn的特征向量
  组成的完全正交基 x1,...,xn。
  若设 U = (x1,...,xn)，则 U 是酉矩阵，并且有
  U^{-1} T U = 对角阵 {λ1,...,λn}

  正交矩阵的应用（旋转）：若一个 n*n 实矩阵A是正交的，则其特征值等于
  ±1 或 e^{±iϕ}成对出现（ϕ是实数）。
  
  2. 特征值、特征向量、矩阵的谱
  (1) 方阵A，使方程 T x = λ x 有非零解时，λ(复数)称一个特征值，x称对应的特征向量
  (2) A的所有特征值的集合称为A的谱 σ(A)，A的特征值的绝对值的最大值称为A的谱半径，记做 r(A)
  (3) 特征方程：det(A-λE)=0，其解是A的特征值λ，λ的重数称为代数重数。
  (4) 设矩阵U是正交的（酉的），U的谱由数 e^{±iϕ} 组成，
      变换 x' = U x 对应于笛卡尔坐标系中的正向旋转，旋转角ϕ
      x1' = x1 * cos ϕ + x2 * sin ϕ
      y1' = - x1 * sin ϕ + x2 * cos ϕ
  (5) 谱定理
  (i) 自伴矩阵的谱在实直线上
  (ii) 斜伴矩阵的谱在虚轴上
  (iii) 酉矩阵的谱在单位圆上

  3. 正交性

   *)

  Context `{F : Field}.
  Add Field field_inst : (make_field_theory F).
  Notation "1" := T1 : T_scope.
  Notation "0" := T0 : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "=" := Teq : T_scope.
  Infix "=" := (@meq _ Teq _ _) : mat_scope.
  Infix "*" := (@mmul _ Tadd T0 Tmul _ _ _) : mat_scope.
  Notation "m ⁻¹" := (@minv _ Tadd T0 Topp Tmul T1 Tinv _ m) : mat_scope.
  Notation smat n := (smat T n).
  Notation mat1 n := (@mat1 _ T0 T1 n).
  Notation minvertible := (@minvertible _ Tadd T0 Tmul T1 Teq _).
  Notation mdet := (@mdet _ Tadd T0 Topp Tmul T1 _).

  (* ================== *)
  (** *** Orthogonal matrix *)

  (** T square matrix m is an orthogonal matrix *)
  Definition morth {n} (m : smat n) : Prop := m\T * m = mat1 n.

  (** orthogonal m -> invertible m *)
  Lemma morth_invertible : forall {n} (m : smat n),
      morth m -> minvertible m.
  Proof. intros. hnf in *. exists (m\T). auto. Qed.

  (** orthogonal m -> m⁻¹ = m\T *)
  Lemma morth_imply_inv_eq_trans : forall {n} (m : smat n),
      morth m -> m⁻¹ = m\T.
  Proof. intros. red in H. apply mmul_eq1_iff_minv_r in H. auto. Qed.

  (** m⁻¹ = m\T -> orthogonal m*)
  Lemma minv_eq_trans_imply_morth : forall {n} (m : smat n),
      m⁻¹ = m\T -> morth m.
  Proof. intros. apply mmul_eq1_iff_minv_r in H. auto. Qed.

  (** orthogonal m <-> m\T * m = mat1 *)
  Lemma morth_iff_mul_trans_l : forall {n} (m : smat n),
      morth m <-> m\T * m = mat1 n.
  Proof. intros. red. auto. Qed.

  (** orthogonal m <-> m * m\T = mat1 *)
  Lemma morth_iff_mul_trans_r : forall {n} (m : smat n),
      morth m <-> m * m\T = mat1 n.
  Proof.
    intros. split; intros H.
    - apply mmul_eq1_iff_minv_r in H. rewrite <- H. apply mmul_minv_r.
    - red. apply mmul_eq1_iff_minv_l in H. rewrite <- H. apply mmul_minv_l.
  Qed.

  (** orthogonal mat1 *)
  Lemma morth_1 : forall {n}, morth (mat1 n).
  Proof. intros. red. rewrite mtrans_1, mmul_1_r. easy. Qed.

  (** orthogonal m -> orthogonal p -> orthogonal (m * p) *)
  Lemma morth_mul : forall {n} (m p : smat n),
      morth m -> morth p -> morth (m * p).
  Proof.
    intros. red. red in H, H0. rewrite mtrans_mmul.
    rewrite mmul_assoc. rewrite <- (mmul_assoc _ m).
    rewrite H. rewrite mmul_1_l. rewrite H0. easy.
  Qed.

  (** orthogonal m -> orthogonal m\T *)
  Lemma morth_mtrans : forall {n} (m : smat n), morth m -> morth (m\T).
  Proof.
    intros. red. rewrite mtrans_mtrans.
    apply morth_iff_mul_trans_r in H. auto.
  Qed.

  (** orthogonal m -> orthogonal m⁻¹ *)
  Lemma morth_minv : forall {n} (m : smat n), morth m -> morth (m⁻¹).
  Proof.
    intros. red.
    rewrite morth_imply_inv_eq_trans; auto. rewrite mtrans_mtrans.
    apply morth_iff_mul_trans_r; auto.
  Qed.
  
  (* ================== *)
  (** *** O(n): General Orthogonal Group, General Linear Group *)
  (* https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group *)
  Section GOn.
    
    (** The set of GOn *)
    Record GOn (n: nat) := {
        GOn_mat :> smat n;
        GOn_props : morth GOn_mat
      }.

    (** Equality of elements in GOn *)
    Definition GOn_eq {n} (s1 s2 : GOn n) : Prop := GOn_mat _ s1 = GOn_mat _ s2.

    (** GOn_eq is equivalence relation *)
    Lemma GOn_eq_equiv : forall n, Equivalence (@GOn_eq n).
    Proof.
      intros. unfold GOn_eq. constructor; hnf; intros; try easy.
      rewrite H; easy.
    Qed.

    (** Multiplication of elements in GOn *)
    Definition GOn_mul {n} (s1 s2 : GOn n) : GOn n.
      refine (Build_GOn n (s1 * s2) _).
      destruct s1 as [s1 H1], s2 as [s2 H2]. simpl.
      apply morth_mul; auto.
    Defined.

    (** Identity element in GOn *)
    Definition GOn_1 {n} : GOn n.
      refine (Build_GOn n (mat1 n) _).
      apply morth_1.
    Defined.

    (** GOn_mul is a proper morphism respect to GOn_eq *)
    Lemma GOn_mul_proper : forall n, Proper (GOn_eq => GOn_eq => GOn_eq) (@GOn_mul n).
    Proof. unfold GOn_eq in *. simp_proper. intros. simpl. rewrite H,H0. easy. Qed.

    (** GOn_mul is associative *)
    Lemma GOn_mul_assoc : forall n, Associative GOn_mul (@GOn_eq n).
    Proof. unfold GOn_eq. intros. constructor. intros; simpl. apply mmul_assoc. Qed.

    (** GOn_1 is left-identity-element of GOn_mul operation *)
    Lemma GOn_mul_id_l : forall n, IdentityLeft GOn_mul GOn_1 (@GOn_eq n).
    Proof. unfold GOn_eq. intros. constructor. intros; simpl. apply mmul_1_l. Qed.
    
    (** GOn_1 is right-identity-element of GOn_mul operation *)
    Lemma GOn_mul_id_r : forall n, IdentityRight GOn_mul GOn_1 (@GOn_eq n).
    Proof. unfold GOn_eq. intros. constructor. intros; simpl. apply mmul_1_r. Qed.

    (** <GOn, +, 1> is a monoid *)
    Lemma Monoid_GOn : forall n, Monoid (@GOn_mul n) GOn_1 GOn_eq.
    Proof.
      intros. constructor.
      - apply GOn_mul_proper.
      - apply GOn_eq_equiv.
      - apply GOn_mul_assoc.
      - apply GOn_mul_id_l.
      - apply GOn_mul_id_r.
    Qed.

    (** Inverse operation of multiplication in GOn *)
    Definition GOn_inv {n} (s : GOn n) : GOn n.
      refine (Build_GOn n (s\T) _). destruct s as [s H1]. simpl.
      apply morth_mtrans; auto.
    Defined.

    (** GOn_inv is a proper morphism respect to GOn_eq *)
    Lemma GOn_inv_proper : forall n, Proper (GOn_eq => GOn_eq) (@GOn_inv n).
    Proof. unfold GOn_eq in *. simp_proper. intros. simpl. rewrite H. easy. Qed.

    (** GOn_inv is left-inversion of <GOn_mul,GOn_1> *)
    Lemma GOn_mul_inv_l : forall n, InverseLeft GOn_mul GOn_1 GOn_inv (@GOn_eq n).
    Proof. unfold GOn_eq. intros. constructor. intros; simpl. apply a. Qed.

    (** GOn_inv is right-inversion of <GOn_mul,GOn_1> *)
    Lemma GOn_mul_inv_r : forall n, InverseRight GOn_mul GOn_1 GOn_inv (@GOn_eq n).
    Proof.
      unfold GOn_eq. intros. constructor. intros; simpl.
      apply morth_iff_mul_trans_r. apply a.
    Qed.

    (** <GOn, +, 1, /s> is a group *)
    Theorem Group_GOn : forall n, Group (@GOn_mul n) GOn_1 GOn_inv GOn_eq.
    Proof.
      intros. constructor.
      - apply Monoid_GOn.
      - apply GOn_mul_inv_l.
      - apply GOn_mul_inv_r.
      - apply GOn_mul_proper.
      - apply GOn_inv_proper.
    Qed.
  
    (** *** Extract the properties of GOn to its carrier *)

    (** m⁻¹ = m\T *)
    Lemma GOn_imply_inv_eq_trans : forall {n} (s : GOn n),
        let m := GOn_mat n s in
        m⁻¹ = m\T.
    Proof.
      intros. unfold m. destruct s as [m' H]. simpl in *.
      rewrite morth_imply_inv_eq_trans; auto. easy.
    Qed.

  End GOn.

  
  (* ================== *)
  (** ** SO(n): Special Orthogonal Group, Rotation Group *)
  (* https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group *)
  Section SOn.

    (** The set of SOn *)
    Record SOn (n: nat) := {
        SOn_mat :> smat n;
        SOn_props : (morth SOn_mat) /\ (mdet SOn_mat = 1)%T
      }.

    Definition SOn_eq {n} (s1 s2 : SOn n) : Prop := SOn_mat _ s1 = SOn_mat _ s2.

    Definition SOn_mul {n} (s1 s2 : SOn n) : SOn n.
      refine (Build_SOn n (s1 * s2) _).
      destruct s1 as [s1 [H1 H1']], s2 as [s2 [H2 H2']]. simpl. split.
      - apply morth_mul; auto.
      - rewrite mdet_mmul. rewrite H1', H2'. ring.
    Defined.

    Definition SOn_1 {n} : SOn n.
      refine (Build_SOn n (mat1 n) _). split.
      apply morth_1. apply mdet_1.
    Defined.

    (** SOn_eq is equivalence relation *)
    Lemma SOn_eq_equiv : forall n, Equivalence (@SOn_eq n).
    Proof.
      intros. unfold SOn_eq. constructor; hnf; intros; try easy.
      rewrite H; easy.
    Qed.

    (** SOn_mul is a proper morphism respect to SOn_eq *)
    Lemma SOn_mul_proper : forall n, Proper (SOn_eq => SOn_eq => SOn_eq) (@SOn_mul n).
    Proof. unfold SOn_eq in *. simp_proper. intros. simpl. rewrite H,H0. easy. Qed.

    (** SOn_mul is associative *)
    Lemma SOn_mul_assoc : forall n, Associative SOn_mul (@SOn_eq n).
    Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_assoc. Qed.

    (** SOn_1 is left-identity-element of SOn_mul operation *)
    Lemma SOn_mul_id_l : forall n, IdentityLeft SOn_mul SOn_1 (@SOn_eq n).
    Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_1_l. Qed.
    
    (** SOn_1 is right-identity-element of SOn_mul operation *)
    Lemma SOn_mul_id_r : forall n, IdentityRight SOn_mul SOn_1 (@SOn_eq n).
    Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_1_r. Qed.
    
    (** <SOn, +, 1> is a monoid *)
    Lemma Monoid_SOn : forall n, Monoid (@SOn_mul n) SOn_1 SOn_eq.
    Proof.
      intros. constructor.
      - apply SOn_mul_proper.
      - apply SOn_eq_equiv.
      - apply SOn_mul_assoc.
      - apply SOn_mul_id_l.
      - apply SOn_mul_id_r.
    Qed.

    Definition SOn_inv {n} (s : SOn n) : SOn n.
      refine (Build_SOn n (s\T) _).
      destruct s as [s [H1 H2]]; simpl. split.
      apply morth_mtrans; auto. rewrite mdet_mtrans. auto.
    Defined.

    (** SOn_inv is a proper morphism respect to SOn_eq *)
    Lemma SOn_inv_proper : forall n, Proper (SOn_eq => SOn_eq) (@SOn_inv n).
    Proof. unfold SOn_eq in *. simp_proper. intros. simpl. rewrite H. easy. Qed.

    (** SOn_inv is left-inversion of <SOn_mul,SOn_1> *)
    Lemma SOn_mul_inv_l : forall n, InverseLeft SOn_mul SOn_1 SOn_inv (@SOn_eq n).
    Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply a. Qed.

    (** SOn_inv is right-inversion of <SOn_mul,SOn_1> *)
    Lemma SOn_mul_inv_r : forall n, InverseRight SOn_mul SOn_1 SOn_inv (@SOn_eq n).
    Proof.
      unfold SOn_eq. intros. constructor. intros; simpl.
      apply morth_iff_mul_trans_r. apply a.
    Qed.

    (** <SOn, +, 1, /s> is a group *)
    Theorem Group_SOn : forall n, Group (@SOn_mul n) SOn_1 SOn_inv SOn_eq.
    Proof.
      intros. constructor.
      - apply Monoid_SOn.
      - apply SOn_mul_inv_l.
      - apply SOn_mul_inv_r.
      - apply SOn_mul_proper.
      - apply SOn_inv_proper.
    Qed.

    (** *** Extract the properties of SOn to its carrier *)

    (** m⁻¹ = m\T *)
    Lemma SOn_imply_inv_eq_trans : forall {n} (s : SOn n),
        let m := SOn_mat n s in
        m⁻¹ = m\T.
    Proof.
      intros. unfold m. destruct s as [m' [H1 H2]]. simpl in *.
      rewrite morth_imply_inv_eq_trans; auto. easy.
    Qed.

  End SOn.

End OrthogonalMatrix.


(* ==================================== *)
(** ** Matrix inversion by Gauss Elimination, original by Shen Nan *)
Section gauss_elimination.
  Context `{F:Field}.
  Add Field field_inst : (make_field_theory F).

  Context {Teqdec: Dec Teq}.

  Infix "=" := Teq : T_scope.
  Infix "!=" := (fun a b => ~(a = b)) : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Asub := (fun x y => Tadd x (Topp y)).
  Infix "-" := Asub : T_scope.
  Infix "*" := Tmul : T_scope.

  Infix "+" := (@madd T Tadd _ _) : mat_scope.
  Infix "*" := (@mmul T Tadd T0 Tmul _ _ _) : mat_scope.
  Notation "/ a" := (Tinv a) : T_scope.
  Infix "c*" := (@mcmul T Tmul _ _) : mat_scope.
  Infix "=" := (meq (Teq:=Teq)) : mat_scope.
  (* Notation "m ! i ! j " := (mnth T0 m i j) : mat_scope. *)
  Notation mat1 := (@mat1 _ T0 T1).
  (* Notation l2m := (@l2m T T0 _ _). *)

  (** *** 初等行变换 (brt: Basic Row Transform) *)

  (* 
     0 0 0
     0 0 0
     0 c 0
   *)
  (* T matrix which only one element is non-zero *)
  Definition brt_e {r c} (ri rj : nat) (k : T) : mat r c :=
    f2m (fun i j => if (i =? ri) && (j =? rj) then k else T0).

  
  (* Multiply k times of a row *)
  (*
    1 0 0
    0 c 0
    0 0 1
   *)
  Definition brt_cmul {r c} (ri : nat) (k : T) : mat r c :=
    f2m (fun i j => if i =? j then (if i =? ri then k else T1) else T0).

  (* 第 y 行的 k 倍加到第 x 行 *)
  (* 
     1 0 0
     0 1 0
     0 c 1
   *)
  (* Definition row_add_to_row {n} (x y : nat) (k : T) : mat n n := *)
  (*   mat1 + (brt_e x y k). *)

  (** Add k times of rj-th row to rj-th row *)
  Definition brt_add {n} (ri rj : nat) (k : T) : mat n n :=
    (* f2m (fun i j => *)
    (*           if (i =? ri) && (j =? rj) *)
    (*           then k *)
    (*           else (if i =? j then T1 else T0)). *)
    mat1 + (brt_e ri rj k).

  
  (** 交换两行 *)
  (*
    x =1 , y=2

    1 0 0  -1 0 0   0 0 0   0 0 0   0 1 0    0 1 0
    0 1 0 + 0 0 0 + 0-1 0 + 1 0 0 + 0 0 0  = 1 0 0
    0 0 1   0 0 0   0 0 0   0 0 0   0 0 0    0 0 1
   *)
  (* Definition swap {n} (x y : nat) : mat n n := *)
  (*   mat1 + (e x x (-T1)) + (e y y (-T1)) + (e x y T1) + (e y x T1). *)

  Definition brt_swap {n} (ri rj : nat) : mat n n :=
    (* f2m (fun i j => *)
    (*           if i =? ri *)
    (*           then (if j =? rj then T1 else T0) *)
    (*           else (if i =? rj *)
    (*                 then (if j =? ri then T1 else T0) *)
    (*                 else (if i =? j then T1 else T0))). *)
    mat1
    + (brt_e ri ri (-T1))
    + (brt_e rj rj (-T1))
    + (brt_e ri rj T1)
    + (brt_e rj ri T1).

  Definition invertible {n} (M : mat n n) :=
    exists M', M * M' = mat1 /\ M' * M = mat1.

  (* 
 1 2 1      
-1-3 1  =>  return 0
 1 0 6     
[(n - i)++, y] , i 
得到第一个非0 *)
  (** 从第i行开始，检查第y列的第一个非零元素的序号 *)
  Fixpoint get_first_none_zero {n} (MA: mat n n) (i: nat) (y: nat) : nat :=
    match i with
    | O => n
    | S i' =>
        if ((MA $ (n - i) $ y) =? T0) then
          get_first_none_zero MA i' y
        else
          n - i
    end.

  (* 某一行加到另一行 *)
  Fixpoint elem_change_down {n} (MA: mat n n) (x: nat) (cur: nat) : mat n n * mat n n :=
    match cur with
    | O => (mat1, MA)
    | S cur' =>
        (* 将第 n-cur 行的 MA[n-cur,x] 倍加到第 n 行 *)
        let ee := brt_add (n - cur) x (- (MA $ (n - cur) $ x)) in
        (* 递归进行，左侧是构造的初等矩阵的累乘，右侧是变换后的矩阵 *)
        let (E', EA') := elem_change_down (ee * MA) x cur' in
        (E' * ee, EA')
    end.

  Fixpoint row_echelon_form {n} (MA: mat n n) (i: nat) : option (mat n n * mat n n) :=
    match i with
    | O => Some (mat1, MA)
    | S i' =>
        let r := get_first_none_zero MA i (n - i) in
        if (r =? n) then
          None
        else
          let M0 := (brt_swap (n - i) r) * MA in
          (* 把当前0行和第一个非0行互换 *)
          let ee := (brt_cmul (n - i) (/(M0 $ (n - i) $ (n - i)))) in
          (* 保证这一列第一个数字是1 *)
          let (E', EA') := elem_change_down (ee * M0) (n - i) (i - 1) in
          (* 下面元素全部与当前行相减，变成0 *)
          let ret := row_echelon_form EA' i' in
          match ret with
          | None => None
          | Some (E'', EA'') => Some (E'' * E' * ee * brt_swap (n - i) r, EA'')
          end
    end.

  Fixpoint elem_change_up {n} (MA: mat n n) (x: nat) (i: nat) :=
    match i with
    | O => (mat1, MA)
    | S i' =>
        let ee := brt_add i' x (- (MA $ i' $ x)) in
        let (E, MT) := elem_change_up (ee * MA) x i' in
        (E * ee, MT)
    end.

  Fixpoint fst_to_I {n} (MA: mat n n) (i: nat) :=
    match i with
    | O => (mat1, MA)
    | S i' =>
        let (E, MT) := elem_change_up (MA) i' i' in
        let (E', MT') := fst_to_I MT i' in
        (E' * E, MT')
    end.

  Definition minv_gauss {n} (MA: mat n n) := 
    match row_echelon_form MA n with
    | None => None
    | Some (E, MT) => Some (fst (fst_to_I MT n) * E)
    end.

End gauss_elimination.

Section test.
  Import ZArith.
  Open Scope Z.

  Definition z_brt_swap := (@brt_swap _ Z.add 0 Z.opp 1).
  (* Compute m2l (z_brt_swap 3 0 2). *)
  (* Compute m2l (z_brt_swap 3 1 2). *)
  
  Definition z_elem_change_down {n} (m:mat n n) i j :=
    @elem_change_down _ Z.add 0 Z.opp Z.mul 1 _ m i j. 

  Let m1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  
  (* Compute get_first_none_zero (T0:=0) m1 3 0. *)
  
  (* Compute let (m1,m2) := z_elem_change_down m1 0 0 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 1 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 2 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 3 in m2l m2. *)
  
End test.


(* ==================================== *)
(** ** test *)
Section test.
  Import QArith Qcanon.
  Open Scope Q.
  Open Scope Qc_scope.
  Open Scope mat_scope.

  Infix "=" := (meq (Teq:=eq)) : mat_scope.


  Coercion Q2Qc : Q >-> Qc.

  Definition m1 := (mk_mat_3_3 (T0:=0) 1 2 3 4 5 6 7 8 9)%Qc.
  (* Compute mtrace (Tadd:=Qcplus)(T0:=0)(n:=3) m1. *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Qc.
  Definition m2 := mk_mat_3_3 (T0:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
  (* Compute mrow 1 m2. *)

  (** *** rewrite support test *)
  Notation mcmul := (mcmul (Tmul:=Qcmult)).
  Infix "c*" := mcmul : mat_scope.

  Goal forall r c (m1 m2 : mat r c) (x : Qc), m1 = m2 -> x c* m1 = x c* m2.
  Proof. intros. f_equiv. easy. Qed.

  (** *** rewrite support test (cont.) *)
  Notation msub := (msub (Tadd:=Qcplus)(Topp:=Qcopp)).
  Infix "-" := msub : mat_scope.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 = m2 -> m3 = m4 -> m1 - m3 = m2 - m4.
  Proof. clear. intros. rewrite H,H0. easy. Qed.

End test.
