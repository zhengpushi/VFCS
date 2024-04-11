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
Require Export MatrixInvAM.
(* Require Export MatrixGauss. *)


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ******************************************************************* *)
(** ** Test two inversion algorithms (GE, AM) in OCaml *)

Require Import ExtrOcamlBasic ExtrOcamlNatInt.
Require Import MyExtrOCamlR.

Definition mmul_R := @mmul _ Rplus R0 Rmult.
Definition minvGE_R := @minvGE _ Rplus R0 Ropp Rmult R1 Rinv R_eq_Dec.
Definition minvGE_Rlist := @minvGE_list _ Rplus R0 Ropp Rmult R1 Rinv R_eq_Dec.
Definition minvAM_R := @minvAM _ Rplus R0 Ropp Rmult R1 Rinv.
Definition minvAM_Rlist := @minvAM_list _ Rplus R0 Ropp Rmult R1 Rinv.

(* Recursive Extraction *)
(*   minvertibleGE minvGEo minvertibleGE_list minvGE_list *)
(*   minvertibleAM minvAMo minvertibleAM_list minvAM_list. *)

(* Extraction "ocaml_test/matrix2.ml" *)
(*   m2l l2m mmul_R *)
(*   minvGE_R minvGE_Rlist *)
(*   minvAM_R minvAM_Rlist. *)


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
  Lemma minvAM_mtrans : forall {n} (M : smat n), minvertible M -> (M\T)\-1 = (M\-1)\T.
  Proof.
  Admitted.

  (** mdet (M\-1) = 1 / (mdet M) *)
  Lemma mdet_minvAM : forall {n} (M : smat n), mdet (M \-1) = 1 / (mdet M).
  Admitted.
  
End minvAM.


Section test.
  Import RExt.
  Import QcExt.
  (* (* Context `{HField : Field} {AeqDec : Dec (@eq A)}. *) *)
  (* Notation "0" := Azero : A_scope. *)
  (* Notation "1" := Aone : A_scope. *)
  (* Infix "+" := Aadd : A_scope. *)
  (* Infix "*" := Amul : A_scope. *)
  (* Notation "- a" := (Aopp a) : A_scope. *)
  (* Notation "/ a" := (Ainv a) : A_scope. *)
  
  (* Notation minvAM := (@minvAM _ Rplus R0 Ropp Rmult 1 Rinv). *)
  (* Notation minvGE := (@minvGE _ Rplus R0 Ropp Rmult 1 Rinv). *)
  (* Notation mat1 := (@mat1 _ 0 1). *)
  Notation minvAM := (@minvAM _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation minvGE := (@minvGE _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation mat1 := (@mat1 _ 0 1).
  
  (* 性能测试，看可以解多大规模的矩阵 *)
  Section ex3.
  (* Performance of minvAM in Coq
       dim    time(s)    time(s) 基于 Fin
       5      0.009      0.01
       6      0.035      0.08
       7      0.288      0.74
       8      3.116      8.2
   *)
    (* Time Compute m2l (minvAM (@mat1 7)). *)

  (* Performance of minvGE in Coq
       dim    time(s)    time(s) 基于Fin
       7      0.006
       10     0.009
       20     0.03       0.04
       30     0.06       0.098
       40     0.109      0.2
       50     0.165      0.37
       100    0.918      3.54
       200    8.666
   *)
    (* Time Compute m2l (minvGE (@mat1 200)). *)
  End ex3.
End test.

