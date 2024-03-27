(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Inverse Matrix
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. 有多种逆矩阵计算方法
     (1) minvGE: 基于高斯消元(Gauss Elimination)的逆矩阵。
         适合于数值计算，不可符号计算。
         适用于 r*c 的任意形状的矩阵，所以可以计算左逆和右逆。
         不过目前只支持了 n*n 方阵的情形。
     (2) minvAM: 基于伴随矩阵(Adjoint)的逆矩阵。
         适合于符号计算，也可数值计算(但可能效率较低)。
         仅适用于 n*n 的方阵。
  2. 在Coq中计算的不同方式及其速度比较
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


(* ############################################################################ *)
(** * Matrix is invertible  *)

Section minvertible.
  Context `{HField : Field} `{HAeqDec : Dec _ (@eq A)}.
  Add Field field_thy_inst : (make_field_theory HField).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.

  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*" := mmulv : vec_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  
  Notation minvertibleAM := (@minvertibleAM _ Aadd 0 Aopp Amul Aone).
  Notation minvAMo := (@minvAMo _ Aadd 0 Aopp Amul 1 Ainv).
  Notation minvAM := (@minvAM _ Aadd 0 Aopp Amul 1 Ainv).

  Notation minvertibleGE := (@minvertibleGE _ Aadd 0 Aopp Amul Ainv).
  Notation minvGEo := (@minvGEo _ Aadd 0 Aopp Amul 1 Ainv).
  Notation minvGE := (@minvGE _ Aadd 0 Aopp Amul 1 Ainv).

  
  (* ======================================================================= *)
  (** ** Invertible (nonsingular, nondegenerate) matrix *)
  
  (** The matrix `M` is invertible *)
  Definition minvertible {n} (M : smat n) : Prop := exists M', M' * M = mat1 /\ M * M' = mat1.

  (** The matrix `M` has a left inverse under matrix multiplication *)
  Definition minvertibleL {n} (M : smat n) : Prop := exists N, N * M = mat1.

  (** The matrix `M` has a right inverse under matrix multiplication *)
  Definition minvertibleR {n} (M : smat n) : Prop := exists N, M * N = mat1.
  
  (** A square matrix is invertible, iff minvertibleAM is true *)
  Lemma minvertible_iff_minvertibleAM_true : forall {n} (M : smat n),
      minvertible M <-> minvertibleAM M = true.
  Proof.
    intros. split; intros.
    - apply minvertibleAM_true_iff_mdet_neq0.
      destruct H as [M' [Hl Hr]].
      assert (mdet (M * M') = 1). rewrite Hr. apply mdet_mat1.
      rewrite mdet_mmul in H.
      intro. rewrite H0 in H. rewrite ring_mul_0_l in H. apply field_1_neq_0; auto.
    - hnf. apply minvertibleAM_true_iff_mdet_neq0 in H.
      exists (minvAM M). split.
      apply mmul_minvAM_l; auto. apply mmul_minvAM_r; auto.
  Qed.

  (** Invertible is equivalent to left invertible *)
  Lemma minvertible_iff_minvertibleL : forall {n} (M : smat n),
      minvertible M <-> minvertibleL M.
  Proof.
    intros. rewrite minvertible_iff_minvertibleAM_true.
    rewrite minvertibleAM_true_iff_mdet_neq0.
    split; intros; hnf in *.
    - exists (minvAM M). apply mmul_minvAM_l; auto.
    - destruct H as [N H].
      apply mmul_eq1_imply_mdet_neq0_r in H; auto.
  Qed.

  (** Invertible is equivalent to right invertible *)
  Lemma minvertible_iff_minvertibleR : forall {n} (M : smat n),
      minvertible M <-> minvertibleR M.
  Proof.
    intros. rewrite minvertible_iff_minvertibleAM_true.
    rewrite minvertibleAM_true_iff_mdet_neq0.
    split; intros; hnf in *.
    - exists (minvAM M). apply mmul_minvAM_r; auto.
    - destruct H as [N H].
      apply mmul_eq1_imply_mdet_neq0_l in H; auto.
  Qed.

  (** Left invertible is equivalent to right invertible *)
  Lemma minvertibleL_iff_minvertibleR : forall {n} (M : smat n),
      minvertibleL M <-> minvertibleR M.
  Proof.
    intros.
    rewrite <- minvertible_iff_minvertibleL.
    rewrite <- minvertible_iff_minvertibleR.
    easy.
  Qed.
  
  (** A square matrix is invertible, iff minvertibleGE is true *)
  Lemma minvertible_iff_minvertibleGE_true : forall {n} (M : smat n),
      minvertible M <-> minvertibleGE M = true.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [M' [Hl Hr]].
      apply mmul_eq1_imply_invertibleGE_true_r in Hl; auto.
    - apply mmul_minvGE_l in H.
      rewrite minvertible_iff_minvertibleL. hnf.
      exists (minvGE M); auto.
  Qed.
  
  (** From `M * N = mat1`, we know `M` is invertible *)
  Lemma mmul_eq1_imply_invertible_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvertible M.
  Proof.
    intros. apply mmul_eq1_imply_invertibleGE_true_l in H.
    apply minvertible_iff_minvertibleGE_true in H. auto.
  Qed.

  (** From `M * N = mat1`, we know `N` is invertible *)
  Lemma mmul_eq1_imply_invertible_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvertible N.
  Proof.
    intros. apply mmul_eq1_imply_invertibleGE_true_r in H.
    apply minvertible_iff_minvertibleGE_true in H. auto.
  Qed.

  (** Left cancellation law of matrix multiplication *)
  Lemma mmul_cancel_l : forall {r c} (M : smat r) (N1 N2 : mat r c) ,
      minvertibleL M -> M * N1 = M * N2 -> N1 = N2.
  Proof.
    intros. hnf in H. destruct H as [N H].
    assert (N * M * N1 = N * M * N2). rewrite !mmul_assoc, H0; auto.
    rewrite H in H1. rewrite !mmul_1_l in H1. auto.
  Qed.

  (** Right cancellation law of matrix multiplication *)
  Lemma mmul_cancel_r : forall {r c} (M : smat c) (N1 N2 : mat r c) ,
      minvertibleR M -> N1 * M = N2 * M -> N1 = N2.
  Proof.
    intros. hnf in H. destruct H as [N H].
    assert (N1 * M * N = N2 * M * N). rewrite H0; auto.
    rewrite !mmul_assoc, H in H1. rewrite !mmul_1_r in H1. auto.
  Qed.

  (** Left cancellation law of matrix multiplication with vector *)
  Lemma mmulv_cancel_l : forall {n} (M : smat n) (u v : vec n),
      minvertibleL M -> (M * u = M * v)%V -> u = v.
  Proof.
    intros. hnf in *. destruct H as [N H].
    assert (N * (M * u) = N * (M * v))%V. rewrite H0; auto.
    rewrite <- !mmulv_assoc in H1. rewrite H, !mmulv_1_l in H1; auto.
  Qed.

  (** M * v = N * v -> M = N *)
  Lemma mmulv_cancel_r : forall {n} (M N : smat n) (v : vec n),
      (M * v = N * v)%V -> M = N.
  Proof.
    intros.
  Abort.

  (** mat1 is invertible *)
  Lemma mat1_invertible : forall {n}, minvertible (@mat1 n).
  Proof. intros. hnf. exists mat1. split; hnf; rewrite mmul_1_l; auto. Qed.

  (** Multiplication preserve `invertible` property *)
  Lemma mmul_invertible: forall {n} (M N : smat n), 
      minvertible M -> minvertible N -> minvertible (M * N).
  Proof.
    intros. hnf in *. destruct H as [M' [HL HR]], H0 as [N' [HL1 HR1]]; hnf in *.
    exists (N' * M'). split; hnf.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc M' M). rewrite HL, mmul_1_l; auto.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc N N'). rewrite HR1, mmul_1_l; auto.
  Qed.

  (** Transpose preserve `invertible` property *)
  Lemma mtrans_invertible : forall n (M : smat n),
      minvertible M -> minvertible (M\T).
  Proof.
    intros. hnf in *. destruct H as [E [Hl Hr]]. exists (E\T). split.
    - hnf. rewrite <- mtrans_mmul. rewrite Hr. apply mtrans_mat1.
    - hnf. rewrite <- mtrans_mmul. rewrite Hl. apply mtrans_mat1.
  Qed.

  (** Left inverse is unique *)
  Lemma minverse_unique_l : forall {n} (M N1 N2 : smat n),
      N1 * M = mat1 -> N2 * M = mat1 -> N1 = N2.
  Proof.
    intros. rewrite <- H in H0.
    apply mmul_cancel_r in H0; auto.
    apply mmul_eq1_imply_invertible_r in H.
    apply minvertible_iff_minvertibleR; auto.
  Qed.

  (** Right inverse is unique *)
  Lemma minverse_unique_r : forall {n} (M N1 N2 : smat n),
      M * N1 = mat1 -> M * N2 = mat1 -> N1 = N2.
  Proof.
    intros. rewrite <- H in H0.
    apply mmul_cancel_l in H0; auto.
    apply mmul_eq1_imply_invertible_l in H.
    apply minvertible_iff_minvertibleL; auto.
  Qed.

  
  (* ======================================================================= *)
  (** ** Singular (degenerate, not invertible) matrix *)
    
  (** The matrix `M` is singular (i.e., not invertible) *)
  Definition msingular {n} (M : smat n) : Prop := ~(minvertible M).
  
  (** A square matrix is singular, iff minvertibleGE is false *)
  Lemma msingular_iff_minvertibleGE_false : forall {n} (M : smat n),
      msingular M <-> minvertibleGE M = false.
  Proof.
    intros. unfold msingular. rewrite minvertible_iff_minvertibleGE_true.
    rewrite not_true_iff_false. easy.
  Qed.

  (** A square matrix is singular, iff minvertibleAM is false *)
  Lemma msingular_iff_minvertibleAM_false : forall {n} (M : smat n),
      msingular M <-> minvertibleAM M = false.
  Proof.
    intros. unfold msingular. rewrite minvertible_iff_minvertibleAM_true.
    rewrite not_true_iff_false. easy.
  Qed.
  
End minvertible.


(* ############################################################################ *)
(** * Inverse Matrix by Gauss Elimination *)
Section minvGE.
  Context `{HField : Field} {AeqDec : Dec (@eq A)}.
  Add Field field_thy_inst : (make_field_theory HField).
  
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.

  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*" := mmulv : vec_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  
  Notation minvertible := (@minvertible _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).
  Notation minvertibleGE := (@minvertibleGE _ Aadd 0 Aopp Amul Ainv).
  Notation minvGEo := (@minvGEo _ Aadd 0 Aopp Amul 1 Ainv).
  Notation minvGE := (@minvGE _ Aadd 0 Aopp Amul 1 Ainv).

  
  (* ======================================================================= *)
  (** ** Invertibility of matrix *)
  
  (** If `minvGEo M` return `Some M'`, then `M` is invertible *)
  Lemma minvGEo_Some_imply_invertible : forall {n} (M M' : smat n),
      minvGEo M = Some M' -> minvertible M.
  Proof.
    intros. apply minvGEo_imply_eq in H.
    apply mmul_eq1_imply_invertible_r in H; auto.
  Qed.

  (** If [minvGEo M] return [Some M'], then [M'] is invertible *)
  Lemma minvGEo_Some_imply_invertible_inv : forall {n} (M M' : smat n),
      minvGEo M = Some M' -> minvertible M'.
  Proof.
    intros. apply minvGEo_imply_eq in H.
    apply mmul_eq1_imply_invertible_l in H; auto.
  Qed.

  (** If [minvGEo M] return [None], then [M] is singular *)
  Lemma minvGEo_None_imply_singular : forall {n} (M : smat n),
      minvGEo M = None -> msingular M.
  Proof.
    intros.
    apply minvGEo_None_iff_invertibleGE_false in H.
    apply msingular_iff_minvertibleGE_false; auto.
  Qed.
  
End minvGE.


(* ############################################################################ *)
(** * Inverse Matrix by Adjoint Matrix *)
Section minvAM.
  Context `{HField : Field} {AeqDec : Dec (@eq A)}.
  Add Field field_thy_inst : (make_field_theory HField).
  
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * /b).
  Infix "/" := Adiv : A_scope.

  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*" := mmulv : vec_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  
  Notation minvertible := (@minvertible _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).
  Notation minvertibleAM := (@minvertibleAM _ Aadd 0 Aopp Amul Ainv).
  Notation minvAMo := (@minvAMo _ Aadd 0 Aopp Amul 1 Ainv).
  Notation minvAM := (@minvAM _ Aadd 0 Aopp Amul 1 Ainv).
  Notation "M \-1" := (minvAM M) : mat_scope.

  
  (* ======================================================================= *)
  (** ** Invertibility of matrix *)
  
  (** If `minvAMo M` return `Some M'`, then `M` is invertible *)
  Lemma minvAMo_Some_imply_invertible : forall {n} (M M' : smat n),
      minvAMo M = Some M' -> minvertible M.
  Proof.
    intros. apply minvAMo_imply_eq in H.
    apply mmul_eq1_imply_invertible_r in H; auto.
  Qed.

  (** If [minvAMo M] return [Some M'], then [M'] is invertible *)
  Lemma minvAMo_Some_imply_invertible_inv : forall {n} (M M' : smat n),
      minvAMo M = Some M' -> minvertible M'.
  Proof.
    intros. apply minvAMo_imply_eq in H.
    apply mmul_eq1_imply_invertible_l in H; auto.
  Qed.

  (** If [minvAMo M] return [None], then [M] is singular *)
  Lemma minvAMo_None_imply_singular : forall {n} (M : smat n),
      minvAMo M = None -> msingular M.
  Proof.
    intros.
    apply minvAMo_None_iff_invertibleAM_false in H.
    apply msingular_iff_minvertibleAM_false; auto.
  Qed.

  (** If `M` is invertible, then `minvAM M` is also invertible *)
  Lemma minvAM_invertible : forall {n} (M : smat n),
      minvertible M -> minvertible (M\-1).
  Proof.
    intros.
    apply minvertible_iff_minvertibleAM_true in H.
    apply (minvAM_imply_minvAMo_Some (Ainv:=Ainv)) in H.
    apply minvAMo_Some_imply_invertible_inv in H. auto.
  Qed.

  (** M \-1 \-1 = M *)
  Lemma minvAM_minvAM : forall {n} (M : smat n), minvertible M -> M\-1\-1 = M.
  Proof.
    intros.
    assert (M\-1 * M = mat1).
    { apply mmul_minvAM_l. apply minvertibleAM_true_iff_mdet_neq0.
      apply minvertible_iff_minvertibleAM_true. auto. }
    apply mmul_eq1_imply_minvAM_l in H0; auto.
  Qed.

  (** (M * N) \-1 = N\-1 * M\-1 *)
  Lemma minvAM_mmul : forall {n} (M N : smat n),
      minvertible M -> minvertible N -> (M * N)\-1 = (N\-1) * (M\-1).
  Proof.
    intros.
    assert (mdet M <> 0).
    { apply minvertibleAM_true_iff_mdet_neq0.
      apply minvertible_iff_minvertibleAM_true; auto. }
    assert (mdet N <> 0).
    { apply minvertibleAM_true_iff_mdet_neq0.
      apply minvertible_iff_minvertibleAM_true; auto. }
    assert ((M * N) * (N\-1 * M\-1) = mat1).
    { rewrite <- !mmul_assoc. rewrite (mmul_assoc M).
      rewrite mmul_minvAM_r; auto.
      rewrite mmul_1_r. rewrite mmul_minvAM_r; auto. }
    apply mmul_eq1_imply_minvAM_l in H3. auto.
  Qed.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma minvA_mtrans : forall {n} (M : smat n), minvertible M -> (M\T)\-1 = (M\-1)\T.
  Proof.
  Admitted.

  (** mdet (M\-1) = 1 / (mdet M) *)
  Lemma mdet_minvAM : forall {n} (M : smat n), mdet (M \-1) = 1 / (mdet M).
  Admitted.
  
End minvAM.



Section test.
  Context `{HField : Field} {AeqDec : Dec (@eq A)}.
  
  Notation minvAM := (@minvAM _ Aadd Azero Aopp Amul Aone Ainv).
  Notation minvGE := (@minvGE _ Aadd Azero Aopp Amul Aone Ainv).
  Notation mat1 := (@mat1 _ Azero Aone).
  
  (* 性能测试，看可以解多大规模的矩阵 *)
  Section ex3.
  (* Performance of minvAM in Coq
       dim    time(s)    time(s) 基于 Fin
       5      0.009      0.326
       6      0.035      2.9s
       7      0.288
       8      3.116
   *)
    (* Time Compute m2l (minvAM (@mat1 6)). *)

  (* Performance of minvGE in Coq
       dim    time(s)    time(s) 基于Fin
       7      0.006
       10     0.009
       20     0.03
       30     0.06
       40     0.109
       50     0.165
       100    0.918
       200    8.666
   *)
    (* Time Compute m2l (minvGE (@mat1 2)). *)
  End ex3.
End test.

