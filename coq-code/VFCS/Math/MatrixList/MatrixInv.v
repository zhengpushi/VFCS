(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Inverse Matrix
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. 有两种逆矩阵计算方法
     (1) minvGE
         基于高斯消元(Gauss Elimination)的逆矩阵。
         适合于数值计算，不可符号计算。
         适用于 r*c 的任意形状的矩阵，所以可以计算左逆和右逆。
     (2) minvAM
         基于伴随矩阵(Adjoint)的逆矩阵。
         适合于符号计算，也可数值计算(但可能效率较低)。
         仅适用于 n*n 的方阵。
  2. 命名风格
     (1) minvGE, minvAM, 这是两种求逆矩阵的运算
     (2) AM_xx, GE_xx，这是有关的引理。
  3. 在Coq中计算的不同方式及其速度比较
     (1) 直接查看结果，不保存
         Eval cbn/cbv/compute in exp. 速度慢
         Eval vm_compute/native_compute in exp. 速度快
         Compute exp.  速度快
     (2) 不查看结果，而是保存到一个标识符。
         Let a := Eval cbn/cbv/compute in exp. 速度慢
         Let a := Eval vm_compute/native_compute in exp. 速度快
     (3) 原因：
         Compute xx 是 Eval vm_compute in xx 的缩写。
         vm_compute 是基于字节码的虚拟机执行
         native_compute 默认是 vm_compute，还可以进一步定制
 *)


Require Import NatExt.
Require Import MatrixList.ElementType.
Require Import MatrixList.Matrix.
Require Import MatrixList.MatrixDet.
Require Import MatrixList.MatrixGauss.
Require Import CoqExt.Basic.
Require Import CoqExt.MyExtrOCamlR.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ======================================================================= *)
(** ** Matrix is invertible  *)
Section minvitible.
  Context `{R:Ring}.
  Add Ring ring_thy_inst : make_ring_theory.

  Infix "*" := (@mmul A Aadd Azero Amul _ _ _) : mat_scope.
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone).

  (* Infix "+" := Aadd : A_scope. *)
  (* Notation "- a" := (Aopp a) : A_scope. *)
  (* Infix "-" := (fun x y => Aadd x (Aopp y)). *)
  (* Infix "*" := Amul : A_scope. *)
  (* Infix "c*" := (@mcmul A Amul _ _) : mat_scope. *)
  
  (** A square matrix is invertible *)
  Definition minvertible {n} (M : smat n) : Prop :=
    exists M' : smat n, (M * M' = mat1) \/ (M' * M = mat1).

  (** invertible mat1 *)
  Lemma minvertible_mat1 : forall n : nat, @minvertible n mat1.
  Proof.
  Admitted.

  (** A square matrix is invertible, if its determinant is nonzero *)
  Lemma minvertible_iff_mdet_nonZero : forall {n} (M : smat n),
      minvertible M <-> mdet M <> Azero.
  Proof.
  Admitted.

  (** invertible M -> invertible (M\T) *)
  Lemma minvertible_trans : forall n (M : smat n),
      minvertible M -> minvertible (M\T).
  Proof.
  Admitted.

  (** invertible M1 -> invertible M2 -> invertible (M1 * M2) *)
  Lemma minvertible_mul : forall n (M1 M2 : smat n),
      minvertible M1 -> minvertible M2 -> minvertible (M1 * M2).
  Proof.
  Admitted.

End minvitible.


(* ======================================================================= *)
(** ** Inverse Matrix by Gauss Elimination *)
Section minvGE.
  Context `{HField : Field} `{HDec : @Dec A}.

  Notation rowEchelon := (@rowEchelon _ Aadd Azero Aopp Amul Ainv HDec).
  Notation minRowEchelon := (@minRowEchelon _ Aadd Azero Aopp Amul Aone Ainv HDec).
  Notation listFirstNonZero := (@listFirstNonZero _ Azero Aeqb).
  Notation rowOpList2mat := (@rowOpList2mat _ Aadd Azero Amul Aone).

  (* 计算矩阵的行秩。利用阶梯形矩阵可很容易判定 *)
  Definition mrowRank {r c} (M : @mat A r c) : nat :=
    let d1 := mdata M in
    let d2 := map listFirstNonZero d1 in
    let d3 := map (fun o => match o with Some _ => 1 | _ => O end) d2 in
    fold_left Nat.add d3 0.

  (* 计算逆矩阵(option版本)。
     1. 先计算阶梯形矩阵
     2. 如果秩不是n，则该矩阵不可逆，否则再计算行最简阶梯形
   *)
  Definition minvGEo {n} (M : @smat A n) : option (@smat A n) :=
    let p1 := rowEchelon M in
    let r := mrowRank (snd p1) in
    match Nat.eqb r n with
    | false => None
    | _ =>
        let p2 := minRowEchelon (snd p1) in
        Some (rowOpList2mat (fst p2 ++ fst p1) n)
    end.

  (* 计算逆矩阵(带有默认值的版本) *)
  Definition minvGE {n} (M : @smat A n) : @smat A n :=
    match minvGEo M with
    | Some M' => M'
    | _ => (@mat1 _ Azero Aone n)
    end.

  (* (* 要证明 Some M1 = Some M2 时，不知为何 f_equal 会卡住，所以设计了这个引理 *) *)
  (* Lemma Some_mat_eq_if_dlist_eq : forall {A n} (M1 M2 : @smat A n), *)
  (*     mdata M1 = mdata M2 -> Some M1 = Some M2. *)
  (* Proof. intros. f_equal. apply meq_if_mdata. auto. Qed. *)
  
End minvGE.


(* ==================================== *)
(** ** Inverse Matrix by Adjoint Matrix *)
Section minvAM.
  Context `{HField:Field}.
  Add Field field_thy_inst : make_field_theory.

  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun x y => x * (/ y)) : A_scope.

  Infix "*" := (@mmul A Aadd Azero Amul _ _ _) : mat_scope.
  Infix "c*" := (@mcmul A Amul _ _) : mat_scope.
  Notation "dl ! i ! j" := (nth j (nth i dl []) Azero).
  Notation "M $ i $ j " := (mnth Azero M i j) : mat_scope.
  Notation "M .11" := (M $ 0 $ 0) : mat_scope.
  Notation "M .12" := (M $ 0 $ 1) : mat_scope.
  Notation "M .13" := (M $ 0 $ 2) : mat_scope.
  Notation "M .14" := (M $ 0 $ 3) : mat_scope.
  Notation "M .21" := (M $ 1 $ 0) : mat_scope.
  Notation "M .22" := (M $ 1 $ 1) : mat_scope.
  Notation "M .23" := (M $ 1 $ 2) : mat_scope.
  Notation "M .24" := (M $ 1 $ 3) : mat_scope.
  Notation "M .31" := (M $ 2 $ 0) : mat_scope.
  Notation "M .32" := (M $ 2 $ 1) : mat_scope.
  Notation "M .33" := (M $ 2 $ 2) : mat_scope.
  Notation "M .34" := (M $ 2 $ 3) : mat_scope.
  Notation "M .41" := (M $ 3 $ 0) : mat_scope.
  Notation "M .42" := (M $ 3 $ 1) : mat_scope.
  Notation "M .43" := (M $ 3 $ 2) : mat_scope.
  Notation "M .44" := (M $ 3 $ 3) : mat_scope.
  
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation l2m := (@l2m A Azero _ _).
  Notation smat n := (@smat A n).
  Notation msubmat := (@msubmat _ Azero).
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone).
  (* Check mdet2. *)
  (* Check @mdet2 _ Aadd Azero. *)
  Notation mdet2 := (@mdet2 _ Aadd Azero Aopp Amul).
  Notation mdet3 := (@mdet3 _ Aadd Azero Aopp Amul).
  Notation mdet4 := (@mdet4 _ Aadd Azero Aopp Amul).
  Notation minvertible := (@minvertible _ Aadd Azero Amul Aone).


  (** *** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (* adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  Definition madj {n} : smat n -> smat n := 
    match n with
    | O => fun M => M 
    | S n' =>
        fun M =>
          f2m (fun i j =>
                 let s := if Nat.even (i + j) then Aone else (-Aone)%A in
                 let d := mdet (msubmat M j i) in 
                 (s * d)%A)
    end.

  
  (** *** Cramer rule *)

  (** Set one column of a square matrix *)
  Definition msetcol {n} (M : smat n) (k : nat) (V : mat n 1) : smat n :=
    f2m (fun i j => if (Nat.eqb j k) then (V$i$0)%nat else M$i$j).
  
  (** Cramer rule, which can solving the equation with the form of A*x=b.
      Note, the result is valid only when |A| is not zero *)
  Definition cramerRule {n} (A : smat n) (b : mat n 1) : mat n 1 :=
    let D := mdet A in
    f2m (fun i j => let Di := mdet (msetcol A i b) in (Di / D)).

  
  (** *** Matrix Inversion *)

  (** Inverse matrix by adjoint matrix method *)
  Definition minvAM {n} (M : smat n) := (Aone / mdet M) c* (madj M).
  Notation "M \-1" := (minvAM M) : mat_scope.


  (** M1 * M2 = mat1 -> M1 \-1 = M2 *)
  Lemma AM_mmul_eq1_iff_minv_l : forall {n} (M1 M2 : smat n),
      M1 * M2 = mat1 <-> minvAM M1 = M2.
  Proof.
  Admitted.

  (** M1 * M2 = mat1 <-> M2 \-1 = M1 *)
  Lemma AM_mmul_eq1_iff_minv_r : forall {n} (M1 M2 : smat n),
      M1 * M2 = mat1 <-> minvAM M2 = M1.
  Proof.
  Admitted.

  (** invertible (M\-1) *)
  Lemma AM_minv_invertible : forall {n} (M : smat n),
      minvertible M -> minvertible (M\-1).
  Proof.
  Admitted.

  (** M * M\-1 = mat1 *)
  Lemma AM_mmul_minv_r : forall {n} (M : smat n), M * M\-1 = mat1.
  Proof.
  Admitted.

  (** M\-1 * M = mat1 *)
  Lemma AM_mmul_minv_l : forall {n} (M : smat n), (minvAM M) * M = mat1.
  Proof.
  Admitted.

  (** mat1 \-1 = mat1 *)
  Lemma AM_minv_mat1 : forall {n}, @minvAM n mat1 = mat1.
  Proof.
  Admitted.

  (** M \-1 \-1 = M *)
  Lemma AM_minv_minv : forall {n} (M : smat n), minvertible M -> M \-1 \-1 = M.
  Proof.
  Admitted.

  (** (M1 * M2) \-1 = M2\-1 * M1\-1 *)
  Lemma AM_minv_mmul : forall {n} (M1 M2 : smat n),
      minvertible M1 -> minvertible M2 -> (M1 * M2)\-1 = M2 \-1 * M1 \-1.
  Proof.
  Admitted.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma AM_minv_mtrans : forall {n} (M : smat n), minvertible M -> (M\T)\-1 = (M\-1)\T.
  Proof.
  Admitted.

  (** mdet (M\-1) = 1 / (mdet M) *)
  Lemma AM_mdet_minv : forall {n} (M : smat n), mdet (M \-1) = Aone / (mdet M).
  Admitted.

  (** Direct compute inversion of a symbol matrix of 1~4 order. *)
  Section CheckInvMatFormula.
    Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : A.
    Let m1 := mk_mat_1_1 a11.
    Let m2 := mk_mat_2_2 a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
    Let m4 := mk_mat_4_4 a11 a12 a13 a14 a21 a22 a23 a24
                a31 a32 a33 a34 a41 a42 a43 a44.

    (* Compute (m2l (minvAM m1)). *)
    (* Compute (m2l (minvAM m2)). *)
    (* Compute (m2l (minvAM m3)). *)
    (* Compute (m2l (minvAM m4)). *)
    (* Although this is correct, but the expression is too long. *)
    (* We want to simplify it with RAST *)
  End CheckInvMatFormula.

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
    
    Definition minv1AM (m : smat 1) : smat 1 := l2m [[Aone/m.11]].

    (** |M| <> 0 -> minv1 M = inv M *)
    Lemma AM_minv1_eq_inv : forall m, mdet m <> Azero -> minv1AM m = minvAM m.
    Proof.
      intros. destruct m. lma. cbn; field. solve_neq0_neq0.
    Qed.

    Definition minv2AM (M : smat 2) : smat 2 :=
      let d := mdet2 M in
      l2m [[M.22/d; -M.12/d]; [-M.21/d; M.11/d]].

    (** |M| <> 0 -> minv2 M = inv M *)
    Lemma AM_minv2_eq_inv : forall M, mdet M <> Azero -> minv2AM M = minvAM M.
    Proof.
      intros. destruct M as [m pH pW].
      pose proof (dl2elems_2_2 (Azero:=Azero) m pH pW) as H1.
      rewrite mdet_eq_mdetList in H; simpl in H; rewrite H1 in H; cbn in H.
      lma; unfold mdet,mdet2,mnth; simpl;
        rewrite H1; simpl; field_simplify_eq; auto;
        solve_neq0_neq0.
    Qed.
    
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
      intros. destruct M as [m pH pW].
      pose proof (dl2elems_3_3 (Azero:=Azero) m pH pW) as H1.
      rewrite mdet_eq_mdetList in H; simpl in H; rewrite H1 in H; cbn in H.
      lma; unfold mdet,mdet3,mnth; simpl;
        rewrite H1; simpl; field_simplify_eq; auto;
        solve_neq0_neq0; solve_eq0_eq0.
    Qed.

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
      intros. destruct M as [m pH pW].
      pose proof (dl2elems_4_4 (Azero:=Azero) m pH pW) as H1.
      rewrite mdet_eq_mdetList in H; simpl in H; rewrite H1 in H; cbn in H.
      (* NEED 10 Seconds, JUST TURN OFF TO SPEED UP *)
      (*
      lma; unfold mdet,mdet4,mnth; simpl;
        rewrite H1; simpl; field_simplify_eq; auto;
        solve_neq0_neq0; solve_eq0_eq0.
        Qed.
       *)
    Admitted.
    
  End concrete.
  
End minvAM.

Section test.
  Import QcExt.
  Notation "dl ! i ! j" := (nth j (nth i dl []) 0).
  Notation "M $ i $ j " := (mnth 0 M i j) : mat_scope.
  Notation mdet := (@mdet _ Qcplus 0 Qcopp Qcmult 1).
  Notation mat1 := (@mat1 _ 0 1).
  Notation minvAM := (@minvAM _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation minv3AM := (@minv3AM _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation minvGE := (@minvGE _ Qcplus 0 Qcopp Qcmult 1 Qcinv).

  Notation rowEchelon := (@rowEchelon _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation minRowEchelon := (@minRowEchelon _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation rowOp2mat := (@rowOp2mat _ Qcplus 0 Qcmult 1).
  Notation rowOpList2mat := (@rowOpList2mat _ Qcplus 0 Qcmult 1).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Notation l2m := (@l2m _ 0 _ _).
  Notation mrowRank := (@mrowRank _ 0).
  Infix "*" := mmul.

  (* 简单的 2x2 矩阵 *)
  Section ex0.
    (* 
          [2 4]    [2  4]    [1 2]    [1 0]
        A=[6 3] => [0 -9] => [0 1] => [0 1]
       ----------------------------------
          [1  0]     [1    0]     [1/2 0]     [1 -2]
       P1=[-3 1]  P2=[0 -1/9]  P3=[0   1]  P4=[0  1]

                            [-1/6; 2/9]
       So, A'=P4*P3*P2*P1 = [1/3; -1/9]
     *)

    Let m1 : @smat Qc 2 := l2m (Q2Qc_dlist [[2;4];[6;3]]).
    Let m2 : @smat Qc 2 := l2m (Q2Qc_dlist [[-1/6;2/9];[1/3;-1/9]]%Q).
    (* Compute m2l (minvGE m1). *)

    Goal m2l (minvGE m1 * m1) = m2l (r:=2)(c:=2) mat1.
    Proof. cbv. lma; f_equal; apply UIP. Qed.
  End ex0.

  (* 利用伴随矩阵求逆矩阵(数值矩阵) *)
  Section ex1.
    (*
      来自《线性代数》同济，第5版，P64，例2
      [[  0; -2;  1];
       [  3;  0; -2];
       [ -2;  3;  0]]

      [[  6;  3;  4];
       [  4;  2;  3];
       [  9;  4;  6]]
     *)
    Let r : nat := 3. Let c : nat := 3.
    Let m1 : mat r c :=
        l2m (Q2Qc_dlist
               [[  0; -2;  1];
                [  3;  0; -2];
                [ -2;  3;  0]]%Q).
    Let m2 : mat r c :=
        l2m (Q2Qc_dlist
               [[  6;  3;  4];
                [  4;  2;  3];
                [  9;  4;  6]]%Q).

    Goal m1 * m2 = mat1.
    Proof. lma. Qed.
    
    Goal m2l (minvAM m1) = m2l m2.
    Proof. cbv. auto. Qed.
    
    Goal m2l (minvAM m2) = m2l m1.
    Proof. cbv. auto. Qed.

    Goal m2l (minvGE m1) = m2l m2.
    Proof. cbv. lma; f_equal; apply UIP. Qed.
    
    Goal m2l (minvAM m2) = m2l m1.
    Proof. cbv. lma. Qed.
  End ex1.

  (* 在 matlab 中的一些测试 *)
  Section ex2.
    (* 在 matlab 命令行中：
       A = [1 2 3 4 5 6; 7 9 10 12 11 14; 20 25 27 29 24 26; ...
       31 33 37 39 36 34; 45 58 43 55 42 47; 70 90 99 78 82 93]
       inv(A)
       结果：
   -0.6879    0.5586   -0.3097    0.1479   -0.0114   -0.0015
    0.4940   -0.4636    0.1002   -0.1035    0.0638    0.0155
   -0.1782   -0.0225    0.1582   -0.0363   -0.0601    0.0143
   -0.0802    0.0372    0.1845   -0.0277   -0.0083   -0.0377
    0.7734   -0.5560   -0.0659    0.0881    0.0316    0.0041
   -0.3853    0.5112   -0.1290   -0.0269   -0.0102    0.0097       
     *)
    Let m1 : @mat Qc 6 6 := l2m
                (Q2Qc_dlist
                   [[ 1; 2; 3; 4; 5; 6];
                    [ 7; 9;10;12;11;14];
                    [20;25;27;29;24;26];
                    [31;33;37;39;36;34];
                    [45;58;43;55;42;47];
                    [70;90;99;78;82;93]]%Q).
    (* 0.1s *)
    (* Time Compute (m2l (minvAM m1)). *)

    Goal m2l ((minvAM m1) * m1) = m2l (c:=6) mat1.
    Proof. cbv. lma; f_equal; apply UIP. Qed.

    (* 0.05s *)
    (* Time Compute (m2l (minvGE m1)). *)
    Goal m2l ((minvGE m1) * m1) = m2l (c:=6) mat1.
    Proof. cbv. lma; f_equal; try apply UIP.
           Abort.               (* 第一行有问题 *)
  End ex2.

  (* 性能测试，看可以解多大规模的矩阵 *)
  Section ex3.
    (* Performance of minvAM in Coq
       dim    time(s)
       5      0.009
       6      0.035
       7      0.288
       8      3.116
     *)
    (* Time Compute m2l (minvAM (@mat1 7)). *)

    (* Performance of minvGE in Coq
       dim    time(s)
       7      0.006
       10     0.009
       20     0.03
       30     0.06
       40     0.109
       50     0.165
       100    0.918
       200    8.666
     *)
    (* Time Compute m2l (minvGE (@mat1 50)). *)
  End ex3.
  
End test.

(*

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
  A matrix will preserve or reverse orientation according to whether the 
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
  (1) A = A\T        对称阵       A = A\H         自伴阵
  (2) A = -A\T       斜称阵       A = -A\H        斜伴阵
  (3) AA\T = E       正交阵       AA\H = E        酉矩阵
  (4)                            A A\H=A\H A      正规矩阵
  其中，(1),(2),(3)都是正规矩阵

  正规矩阵的一个定理：每个 n*n 正规矩阵A，都有一个由对应于特征值λ1,...,λn的特征向量
  组成的完全正交基 x1,...,xn。
  若设 U = (x1,...,xn)，则 U 是酉矩阵，并且有
  U^{-1} A U = 对角阵 {λ1,...,λn}

  正交矩阵的应用（旋转）：若一个 n*n 实矩阵A是正交的，则其特征值等于
  ±1 或 e^{±iϕ}成对出现（ϕ是实数）。
  
  2. 特征值、特征向量、矩阵的谱
  (1) 方阵A，使方程 A x = λ x 有非零解时，λ(复数)称一个特征值，x称对应的特征向量
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
  Notation "1" := Aone : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "=" := Teq : A_scope.
  Infix "=" := (@meq _ Teq _ _) : mat_scope.
  Infix "*" := (@mmul _ Aadd Azero Amul _ _ _) : mat_scope.
  Notation "m \-1" := (@minvAM _ Aadd Azero Aopp Amul Aone Ainv _ m) : mat_scope.
  Notation smat n := (smat A n).
  Notation mat1 n := (@mat1 _ Azero Aone n).
  Notation minvertible := (@minvertible _ Aadd Azero Amul Aone Teq _).
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone _).

  (* ================== *)
  (** *** Orthogonal matrix *)

  (** A square matrix m is an orthogonal matrix *)
  Definition morth {n} (m : smat n) : Prop := m\T * m = mat1 n.

  (** orthogonal m -> invertible m *)
  Lemma morth_invertible : forall {n} (m : smat n),
      morth m -> minvertible m.
  Proof. intros. hnf in *. exists (m\T). auto. Qed.

  (** orthogonal m -> m\-1 = m\T *)
  Lemma morth_imply_inv_eq_trans : forall {n} (m : smat n),
      morth m -> m\-1 = m\T.
  Proof. intros. red in H. apply mmul_eq1_iff_AM_minv_r in H. auto. Qed.

  (** m\-1 = m\T -> orthogonal m*)
  Lemma AM_minv_eq_trans_imply_morth : forall {n} (m : smat n),
      m\-1 = m\T -> morth m.
  Proof. intros. apply mmul_eq1_iff_AM_minv_r in H. auto. Qed.

  (** orthogonal m <-> m\T * m = mat1 *)
  Lemma morth_iff_mul_trans_l : forall {n} (m : smat n),
      morth m <-> m\T * m = mat1 n.
  Proof. intros. red. auto. Qed.

  (** orthogonal m <-> m * m\T = mat1 *)
  Lemma morth_iff_mul_trans_r : forall {n} (m : smat n),
      morth m <-> m * m\T = mat1 n.
  Proof.
    intros. split; intros H.
    - apply mmul_eq1_iff_AM_minv_r in H. rewrite <- H. apply mmul_AM_minv_r.
    - red. apply mmul_eq1_iff_AM_minv_l in H. rewrite <- H. apply mmul_AM_minv_l.
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

  (** orthogonal m -> orthogonal m\-1 *)
  Lemma morth_minvAM : forall {n} (m : smat n), morth m -> morth (m\-1).
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

    (** m\-1 = m\T *)
    Lemma GOn_imply_inv_eq_trans : forall {n} (s : GOn n),
        let m := GOn_mat n s in
        m\-1 = m\T.
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
        SOn_props : (morth SOn_mat) /\ (mdet SOn_mat = 1)%A
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

    (** m\-1 = m\T *)
    Lemma SOn_imply_inv_eq_trans : forall {n} (s : SOn n),
        let m := SOn_mat n s in
        m\-1 = m\T.
    Proof.
      intros. unfold m. destruct s as [m' [H1 H2]]. simpl in *.
      rewrite morth_imply_inv_eq_trans; auto. easy.
    Qed.

  End SOn.

End OrthogonalMatrix.


(* ======================================================================= *)
(** ** test *)
Section test.
  Import QArith Qcanon.
  Open Scope Q.
  Open Scope Qc_scope.
  Open Scope mat_scope.

  Infix "=" := (meq (Teq:=eq)) : mat_scope.


  Coercion Q2Qc : Q >-> Qc.

  Definition m1 := (mk_mat_3_3 (Azero:=0) 1 2 3 4 5 6 7 8 9)%Qc.
  (* Compute mtrace (Aadd:=Qcplus)(Azero:=0)(n:=3) m1. *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Qc.
  Definition m2 := mk_mat_3_3 (Azero:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
  (* Compute mrow 1 m2. *)

  (** *** rewrite support test *)
  Notation mcmul := (mcmul (Amul:=Qcmult)).
  Infix "c*" := mcmul : mat_scope.

  Goal forall r c (m1 m2 : mat r c) (x : Qc), m1 = m2 -> x c* m1 = x c* m2.
  Proof. intros. f_equiv. easy. Qed.

  (** *** rewrite support test (cont.) *)
  Notation msub := (msub (Aadd:=Qcplus)(Aopp:=Qcopp)).
  Infix "-" := msub : mat_scope.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 = m2 -> m3 = m4 -> m1 - m3 = m2 - m4.
  Proof. clear. intros. rewrite H,H0. easy. Qed.

End test.

*)
