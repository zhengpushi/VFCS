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


Require Import Basic NatExt.
Require Import MyExtrOCamlR.
Require Export Matrix.
Require Export MatrixDet.
Require Export MatrixGauss.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ======================================================================= *)
(** ** Matrix is invertible  *)
Section minvertible.
  Context `{HRing:ARing}.
  Add Ring ring_thy_inst : (make_ring_theory HRing).

  Infix "*" := (@mmul A Aadd Azero Amul _ _ _) : mat_scope.
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone).

  (* Infix "+" := Aadd : A_scope. *)
  (* Notation "- a" := (Aopp a) : A_scope. *)
  (* Infix "-" := (fun x y => Aadd x (Aopp y)). *)
  (* Infix "*" := Amul : A_scope. *)
  (* Infix "c*" := (@mcmul A Amul _ _) : mat_scope. *)
  
  (** A square matrix is invertible *)
  Definition minvertible {n} (M : smat A n) : Prop :=
    exists M' : smat A n, (M * M' = mat1) \/ (M' * M = mat1).

  (** invertible mat1 *)
  Lemma minvertible_mat1 : forall n : nat, @minvertible n mat1.
  Proof.
  Admitted.

  (** A square matrix is invertible, if its determinant is nonzero *)
  Lemma minvertible_iff_mdet_neq0 : forall {n} (M : smat A n),
      minvertible M <-> mdet M <> Azero.
  Proof.
  Admitted.

  (** invertible M -> invertible (M\T) *)
  Lemma minvertible_mtrans : forall n (M : smat A n),
      minvertible M -> minvertible (M\T).
  Proof.
  Admitted.

  (** invertible M -> invertible N -> invertible (M * N) *)
  Lemma minvertible_mmul : forall n (M N : smat A n),
      minvertible M -> minvertible N -> minvertible (M * N).
  Proof.
  Admitted.

End minvertible.


(* ======================================================================= *)
(** ** Inverse Matrix by Gauss Elimination *)
Section minvGE.
  Context `{HField : Field} {AeqDec : Dec (@eq A)}.

  Notation echelon := (@echelon _ Aadd Azero Aopp Amul Ainv AeqDec).
  Notation minEchelon :=
    (@minEchelon _ Aadd Azero Aopp Amul Aone Ainv AeqDec).
  Notation Aeqb := (Acmpb AeqDec).
  Notation vfirstNonZero := (@vfirstNonZero _ _ Azero).
  Notation rowOpList2mat := (@rowOpList2mat _ Aadd Azero Amul Aone).

  (* 计算阶梯形矩阵的行秩 = 非零行的个数 *)
  Definition mrowRankOfEchelon {r c} (M : @mat A r c) : nat :=
    let v1 := vmap vfirstNonZero M in
    let v2 := vmap (fun o => match o with Some _ => 1 | _ => O end) v1 in
    @vsum _ add 0 _ v2.

  (* 计算逆矩阵(option版本)。
     1. 先计算阶梯形矩阵
     2. 如果秩不是n，则该矩阵不可逆，否则再计算行最简阶梯形
   *)
  Definition minvGEo {n} (M : @smat A n) : option (@smat A n) :=
    let p1 := echelon M in
    let r := mrowRankOfEchelon (snd p1) in
    match Nat.eqb r n with
    | false => None
    | _ =>
        let p2 := minEchelon (snd p1) in
        Some (rowOpList2mat (fst p2 ++ fst p1))
    end.

  (* 计算逆矩阵(带有默认值的版本) *)
  Definition minvGE {n} (M : @smat A n) : @smat A n :=
    match minvGEo M with
    | Some M' => M'
    | _ => (@mat1 _ Azero Aone n)
    end.

  (* (* 要证明 Some M = Some N 时，不知为何 f_equal 会卡住，所以设计了这个引理 *) *)
  (* Lemma Some_mat_eq_if_dlist_eq : forall {A n} (M N : @smat A n), *)
  (*     mdata M = mdata N -> Some M = Some N. *)
  (* Proof. intros. f_equal. apply meq_if_mdata. auto. Qed. *)
End minvGE.


Lemma vnth_eq : forall {A n} (V : @vec A n) i j (Hi: i < n) (Hj: j < n),
    i = j -> V (exist _ i Hi) = V (exist _ j Hj).
Proof. intros. subst. f_equal. apply sig_eq_iff; auto. Qed.

Lemma mnth_eq : forall {A r c} (M : @mat A r c) i1 j1 i2 j2
                  (Hi1: i1 < r) (Hi2: i2 < r) (Hj1: j1 < c) (Hj2: j2 < c),
    i1 = i2 -> j1 = j2 ->
    M (exist _ i1 Hi1) (exist _ j1 Hj1) =
      M (exist _ i2 Hi2) (exist _ j2 Hj2).
Proof. intros. subst. f_equal; apply sig_eq_iff; auto. Qed.


(* ==================================== *)
(** ** Inverse Matrix by Adjoint Matrix *)
Section minvAM.
  Context `{HField:Field}.
  Add Field field_thy_inst : (make_field_theory HField).

  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun x y => x * (/ y)) : A_scope.

  Infix "*" := (@mmul A Aadd Azero Amul _ _ _) : mat_scope.
  Infix "\.*" := (@mcmul A Amul _ _) : mat_scope.
  
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation l2m := (@l2m A Azero _ _).
  Notation mat r c := (@mat A r c).
  Notation smat n := (@smat A n).
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone).
  Notation mdet2 := (@mdet2 _ Aadd Aopp Amul).
  Notation mdet3 := (@mdet3 _ Aadd Aopp Amul).
  Notation mdet4 := (@mdet4 _ Aadd Aopp Amul).
  Notation minvertible := (@minvertible _ Aadd Azero Amul Aone).


  (** *** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (* adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  Definition madj {n} : smat n -> smat n := 
    match n with
    | O => fun M => M 
    | S n' =>
        fun (M : smat (S n')) =>
        fun (i:fin (S n')) (j:fin (S n')) =>
          let s :=
            if Nat.even (fin2nat i + fin2nat j)
            then Aone
            else (-Aone)%A in
          let d := mdet (msubmat M j i) in 
          (s * d)%A
    end.

  
  (** *** Cramer rule *)

  (** Cramer rule, which can solving the equation with the form of A*x=b.
      Note, the result is valid only when |A| is not zero *)
  Definition cramerRule {n} (A0 : smat n) (b : @vec A n) : @vec A n :=
    let D := mdet A0 in
    fun i => mdet (msetc A0 b i) / D.

  
  (** *** Matrix Inversion *)

  (** Inverse matrix by adjoint matrix method *)
  Definition minvAM {n} (M : smat n) := (Aone / mdet M) \.* (madj M).
  Notation "M \-1" := (minvAM M) : mat_scope.

  (** M * M\-1 = mat1 *)
  Lemma AM_mmul_minv_r : forall {n} (M : smat n), minvertible M -> M * M\-1 = mat1.
  Proof.
  Admitted.

  (** M\-1 * M = mat1 *)
  Lemma AM_mmul_minv_l : forall {n} (M : smat n), minvertible M -> (minvAM M) * M = mat1.
  Proof.
  Admitted.

  (** M * N = mat1 -> M \-1 = N *)
  Lemma AM_mmul_eq1_iff_minv_l : forall {n} (M N : smat n),
      M * N = mat1 <-> minvAM M = N.
  Proof.
  Admitted.

  (** M * N = mat1 <-> N \-1 = M *)
  Lemma AM_mmul_eq1_iff_minv_r : forall {n} (M N : smat n),
      M * N = mat1 <-> minvAM N = M.
  Proof.
  Admitted.

  (** invertible (M\-1) *)
  Lemma AM_minv_invertible : forall {n} (M : smat n),
      minvertible M -> minvertible (M\-1).
  Proof.
    intros. hnf. hnf in H. destruct H as [N [H|H]].
    - exists N; auto.
  Admitted.

  (** mat1 \-1 = mat1 *)
  Lemma AM_minv_mat1 : forall {n}, @minvAM n mat1 = mat1.
  Proof.
  Admitted.

  (** M \-1 \-1 = M *)
  Lemma AM_minv_minv : forall {n} (M : smat n), minvertible M -> M \-1 \-1 = M.
  Proof.
  Admitted.

  (* P \/ P = P *)
  Lemma or_same : forall (P : Prop), P \/ P -> P.
  Proof. intros. destruct H; auto. Qed.
  
  (** (M * N) \-1 = N\-1 * M\-1 *)
  Lemma AM_minv_mmul : forall {n} (M N : smat n),
      minvertible M -> minvertible N -> (M * N)\-1 = N \-1 * M \-1.
  Proof.
    intros. hnf in H,H0. destruct H as [M' H], H0 as [N' H0].
    rewrite AM_mmul_eq1_iff_minv_r in H,H0.
    rewrite AM_mmul_eq1_iff_minv_l in H,H0.
    apply or_same in H,H0.
  Admitted.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma AM_minv_mtrans : forall {n} (M : smat n), minvertible M -> (M\T)\-1 = (M\-1)\T.
  Proof.
  Admitted.

  (** mdet (M\-1) = 1 / (mdet M) *)
  Lemma AM_mdet_minv : forall {n} (M : smat n), mdet (M \-1) = Aone / (mdet M).
  Admitted.

  (** minvertible M -> M * N = M * O -> N = O *)
  Lemma mmul_cancel_l : forall {r c} (M : smat r) (N O : mat r c),
      minvertible M -> M * N = M * O -> N = O.
  Proof.
    intros. assert (M\-1 * (M * N) = M\-1 * (M * O)). rewrite H0; auto.
    rewrite <- !mmul_assoc in H1. rewrite !AM_mmul_minv_l, !mmul_1_l in H1; auto.
  Qed.

  (** minvertible M -> N * M = O * M -> N = O *)
  Lemma mmul_cancel_r : forall {r c} (M : smat c) (N O : mat r c),
      minvertible M -> N * M = O * M -> N = O.
  Proof.
    intros. assert ((N * M) * M\-1 = (O * M) * M\-1). rewrite H0; auto.
    rewrite !mmul_assoc in H1. rewrite !AM_mmul_minv_r, !mmul_1_r in H1; auto.
  Qed.
  

  (** Direct compute inversion of a symbol matrix of 1~4 order. *)
  Section CheckInvMatFormula.
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
    
    Definition minv1AM (M : smat 1) : smat 1 := l2m [[Aone/M.11]].

    (** |M| <> 0 -> minv1 M = inv M *)
    Lemma AM_minv1_eq_inv : forall M, mdet M <> Azero -> minv1AM M = minvAM M.
    Proof.
      intros. rewrite (meq_iff_nth_m2f Azero); intros. cbv.
      destruct i,j; auto. field. solve_neq0_neq0.
    Qed.

    Definition minv2AM (M : smat 2) : smat 2 :=
      let d := mdet2 M in
      l2m [[M.22/d; -M.12/d]; [-M.21/d; M.11/d]].

    (** |M| <> 0 -> minv2 M = inv M *)
    Lemma AM_minv2_eq_inv : forall M, mdet M <> Azero -> minv2AM M = minvAM M.
    Proof.
      intros. rewrite (meq_iff_nth_m2f Azero); intros.
      repeat (try destruct i; try destruct j; try lia); cbv;
        rewrite !(mnth_eq_nth_m2f Azero M) in *; try field.
      all: try solve_neq0_neq0; rewrite !(mnth_eq_nth_m2f Azero M) in *.
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
    
  End concrete.
  
End minvAM.


Section test.
  Import QcExt.
  Notation mat r c := (mat Qc r c).
  Notation mdet := (@mdet _ Qcplus 0 Qcopp Qcmult 1).
  Notation mat1 := (@mat1 _ 0 1).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Notation l2m := (@l2m _ 0 _ _).
  
  Infix "*" := mmul.

  Notation echelon := (@echelon _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation minEchelon := (@minEchelon _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation rowOp2mat := (@rowOp2mat _ Qcplus 0 Qcmult 1).
  Notation rowOpList2mat := (@rowOpList2mat _ Qcplus 0 Qcmult 1).
  Notation mrowRankOfEchelon := (@mrowRankOfEchelon _ 0).
  Notation minvGE := (@minvGE _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  
  Notation minvAM := (@minvAM _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation minv3AM := (@minv3AM _ Qcplus 0 Qcopp Qcmult Qcinv).

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

    Let m1 : @smat Qc 2 := l2m (Q2Qc_dlist [[2;4];[6;3]]%Q).
    Let m2 : @smat Qc 2 := l2m (Q2Qc_dlist [[-1/6;2/9];[1/3;-1/9]]%Q).
    (* Compute m2l (minvGE m1). *)

    Goal m2l (minvGE m1 * m1) = m2l (r:=2)(c:=2) mat1.
    Proof. cbv. list_eq; f_equal; apply UIP. Qed.
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
    Proof. apply m2l_inj; cbv; f_equal. Qed.
    
    Goal m2l (minvAM m1) = m2l m2.
    Proof. cbv. auto. Qed.
    
    Goal m2l (minvAM m2) = m2l m1.
    Proof. cbv. auto. Qed.

    Goal m2l (minvGE m1) = m2l m2.
    Proof. cbv. list_eq. f_equal; apply UIP. Qed.
    
    Goal m2l (minvGE m2) = m2l m1.
    Proof. cbv. list_eq. f_equal; apply UIP. Qed.
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
    Let m1 : mat 6 6 := l2m
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
    Proof.
      (* 为了加速编译，暂时屏蔽 *)
      (* cbv. list_eq; f_equal; apply UIP. Qed. *)
    Abort.

    (* 0.05s *)
    (* Time Compute (m2l (minvGE m1)). *)
    Goal m2l ((minvGE m1) * m1) = m2l (c:=6) mat1.
    Proof.
      (* 为了加速编译，暂时屏蔽 *)
      (* cbv. list_eq; f_equal; apply UIP. Qed. *)
    Abort.
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
    (* Time Compute m2l (minvGE (@mat1 200)). *)
  End ex3.
  
End test.
