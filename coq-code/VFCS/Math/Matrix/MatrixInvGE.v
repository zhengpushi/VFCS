(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Gauss elimination of matrix
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. First stage, we use a simple case of `n × n` matrix
  2. Second stage, we should consider the case of `m × n` matrix
 *)

Require Import NatExt.
Require Import Hierarchy.
Require Import Matrix.
Require Import MyExtrOCamlR.
Require Import Utils.           (* LDict *)
Require Export Matrix MatrixInvBase MatrixGauss.
Require QcExt RExt.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * Inverse matrix based on Gauss elimination *)
Module MinvGE (E : FieldElementType) <: Minv E.
  Export E.
  Open Scope A_scope.
  Open Scope mat_scope.
  
  Add Field field_inst : (make_field_theory Field).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun a b => a * / b) : A_scope.
  
  Notation smat n := (smat A n).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.
  Notation minvertible := (@minvertible _ Aadd 0 Amul 1).

  Notation rowEchelon := (@rowEchelon _ Aadd 0 Aopp Amul Ainv _).
  Notation minRowEchelon := (@minRowEchelon _ Aadd 0 Aopp Amul _).
  Notation rowOps2mat := (@rowOps2mat _ Aadd 0 Amul 1).
  
  (* ******************************************************************* *)
  (** ** Compute that if a matrix is invertible *)

  (** If the matrix `M` is invertible *)
  Definition minvertibleb {n} : smat n -> bool :=
    match n with
    | O => fun _ => false   (* zero-dims matrix is not invertible *)
    | S n' =>
        fun (M : smat (S n')) =>
          match rowEchelon M (S n') with
          | None => false
          | Some (l1, M1) => true
          end
    end.

  (* From `M * N = mat1`, the `minvertibleb M` return true *)
  Lemma mmul_eq1_imply_minvertibleb_true_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvertibleb M = true.
  Proof.
  Admitted.

  (* From `M * N = mat1`, the `minvertibleb N` return true *)
  Lemma mmul_eq1_imply_minvertibleb_true_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvertibleb N = true.
  Proof.
  Admitted.


  (* ******************************************************************* *)
  (** ** Inverse matrix (option version) *)
  
  (** 计算逆矩阵(option版本) *)
  Definition minvo {n} : smat n -> option (smat n) :=
    match n with
    | O => fun _ => None
    | S n' =>
        fun (M : smat (S n')) =>
          match rowEchelon M (S n') with
          | None => None
          | Some (l1, M1) =>
              let (l2, M2) := minRowEchelon M1 (S n') in
              Some (rowOps2mat (l2 ++ l1))
          end
    end.

  (** If `minvo M` return `Some M'`, then `M'` is left inverse of `M` *)
  Theorem minvo_imply_eq : forall {n} (M M' : smat n),
      minvo M = Some M' -> M' * M = mat1.
  Proof.
    intros. unfold minvo in H. destruct n; try easy.
    destruct rowEchelon as [[l1 M1]|] eqn:T1; try easy.
    destruct minRowEchelon as [l2 M2] eqn:T2. inv H.
    copy T1. copy T2.
    apply rowEchelon_imply_eq in T1.
    apply minRowEchelon_imply_eq in T2.
    rewrite rowOps2mat_app. rewrite mmul_assoc. rewrite T1,T2.
    apply minRowEchelon_imply_mat1 in HC0; auto.
    apply rowEchelon_NormedLowerTriangle in HC; auto.
  Qed.

  (** `minvo` return `Some`, iff, `minvertibleb` return true *)
  Lemma minvo_Some_iff_minvertibleb_true : forall {n} (M : smat n),
      (exists M', minvo M = Some M') <-> minvertibleb M = true.
  Proof.
    intros. unfold minvo, minvertibleb in *.
    destruct n; split; intros; try easy.
    - destruct H. easy.
    - destruct H. destruct rowEchelon as [[l1 M1]|]; try easy.
    - destruct rowEchelon as [[l1 M1]|] eqn:T1; try easy.
      destruct (minRowEchelon M1 (S n)) as [l2 M2] eqn:T2.
      exists (rowOps2mat (l2 ++ l1)). auto.
  Qed.

  (** `minvo` return `None`, iff, `minvertibleb` return false *)
  Lemma minvo_None_iff_minvertibleb_false : forall {n} (M : smat n),
      minvo M = None <-> minvertibleb M = false.
  Proof.
    intros. unfold minvo, minvertibleb in *.
    destruct n; split; intros; try easy.
    - destruct rowEchelon as [[l1 M1]|]; try easy.
      destruct minRowEchelon as [l2 M2] eqn:T2; try easy.
    - destruct rowEchelon as [[l1 M1]|]; try easy.
  Qed.

  (** minvertible M <-> minvertibleb M = true *)
  Lemma minvertible_iff_minvertibleb_true : forall {n} (M : smat n),
      minvertible M <-> minvertibleb M = true.
  Proof.
    intros. split; intros.
    - hnf in *. destruct H as [M' [H H0]].
      apply mmul_eq1_imply_minvertibleb_true_l in H0. auto.
    - apply minvo_Some_iff_minvertibleb_true in H. destruct H as [M' H].
      apply minvo_imply_eq in H.
      Search MatrixInvBase.minvertible.
      ?
      hnf.
      Search minvertibleL. ?
      hnf. exists M'.
      ?
      unfold minvertibleb in H. destruct n; try easy.
      destruct rowEchelon as [[l1 M1]|] eqn:T1; try easy.
      Search MatrixGauss.minRowEchelon.
      pose proof (minRowEchelon_imply_eq).
      destruct (minRowEchelon M1 (S n)) .
      apply rowEchelon_imply_eq in T1.
      Search 
      
      Search minvertible.
  
  (** msingular M <-> minvertibleb M = false *)
  Lemma msingular_iff_minvertibleb_false : forall {n} (M : smat n),
      msingular M <-> minvertibleb M = false.


  (* ******************************************************************* *)
  (** ** Inverse matrix (default value version) *)
  
  (** Inverse matrix (default value is identity matrix) *)
  Definition minv {n} : smat n -> smat n :=
    match n with
    | O => fun _ => mat1
    | S n' =>
        fun (M : smat (S n')) =>
          match rowEchelon M n with
          | None => mat1
          | Some (l1, M1) =>
              let (l2, M2) := minRowEchelon M1 n in
              rowOps2mat (l2 ++ l1)
          end
    end.
  Notation "M \-1" := (minv M) : mat_scope.
  
  (* If `minvo M` return `Some M'`, then `minv M` return same output `M'` *)
  Lemma minv_eq_minvo : forall {n} (M M' : smat n),
      minvo M = Some M' -> minv M = M'.
  Proof.
    intros. unfold minvo, minv in *. destruct n; try easy.
    destruct rowEchelon as [[l1 M1]|] eqn:T1; try easy.
    destruct minRowEchelon as [l2] eqn:T2.
    inv H. auto.
  Qed.

  (** If `minvertibleb M` return `false`, then `minv M` return identity matrix *)
  Lemma minvertibleb_false_imply_minv_eq_I : forall {n} (M : smat n),
      minvertibleb M = false -> minv M = mat1.
  Proof.
    intros. unfold minvertibleb, minv in *. destruct n; try easy.
    destruct rowEchelon as [[l1 M1]|] eqn:T1; try easy.
  Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minv_l : forall {n} (M : smat n),
      minvertible M -> M\-1 * M = mat1.
  Proof.
    intros.
    Search minvertibleb.
    apply ?
    unfold minvertibleb, minv in *. destruct n; try easy.
    destruct rowEchelon as [[l1 M1]|] eqn:T1; try easy.
    destruct minRowEchelon as [l2 M2] eqn:T2.
    rewrite rowOps2mat_app. rewrite mmul_assoc.
    copy T1. apply rowEchelon_imply_eq in T1. rewrite T1.
    copy T2. apply minRowEchelon_imply_eq in T2. rewrite T2.
    apply minRowEchelon_imply_mat1 in HC0; auto.
    apply rowEchelon_NormedLowerTriangle in HC; auto.
  Qed.

  (** M * M\-1 = mat1 *)
  Lemma mmul_minv_r : forall {n} (M : smat n),
      minvertibleb M = true -> M * M\-1 = mat1.
  Proof.
  Admitted.
  
  (** M * N = mat1 -> M \-1 = N *)
  Lemma mmul_eq1_imply_minv_l : forall {n} (M N : smat n), M * N = mat1 -> M\-1 = N.
  Proof.
  Admitted.

  (** M * N = mat1 -> N \-1 = M *)
  Lemma mmul_eq1_imply_minv_r : forall {n} (M N : smat n), M * N = mat1 -> N\-1 = M.
  Proof.
  Admitted.
  
  (** minvertibleb M = true -> M \-1 = N -> M * N = mat1 *)
  Lemma mmul_eq1_if_minv_l : forall {n} (M N : smat n),
      minvertibleb M = true -> M\-1 = N -> M * N = mat1.
  Proof.
  Admitted.

  (** minvertibleb N = true -> N \-1 = M -> M * N = mat1 *)
  Lemma mmul_eq1_if_minv_r : forall {n} (M N : smat n),
      minvertibleb N = true -> N\-1 = M ->  M * N = mat1.
  Proof.
  Admitted.
  

  (* ******************************************************************* *)
  (** ** Inverse matrix with lists for input and output *)
  
  (** Check matrix invertibility with lists as input *)
  Definition minvertibleb_list (n : nat) (dl : dlist A) : bool :=
    @minvertibleb n (l2m 0 dl).

  (** Inverse matrix with lists for input and output *)
  Definition minv_list (n : nat) (dl : dlist A) : dlist A :=
    m2l (@minv n (l2m 0 dl)).

  (** `minvertibleb_list` is equal to `minvertibleb`, by definition *)
  Lemma minvertibleb_list_spec : forall (n : nat) (dl : dlist A),
      minvertibleb_list n dl = @minvertibleb n (l2m 0 dl).
  Proof. intros. auto. Qed.

  (** If the matrix `M` created by [dl] is invertible, then the matrix `M'`  *)
  (*     created by [minv_list dl] is the left inverse of `M` *)
  Theorem minv_list_spec : forall (n : nat) (dl : dlist A),
      let M : smat n := l2m 0 dl in
      let M' : smat n := l2m 0 (minv_list n dl) in
      minvertibleb_list n dl = true ->
      M' * M = mat1.
  Proof.
    intros. unfold minvertibleb_list in H. unfold minv_list in M'.
    unfold M', M. rewrite l2m_m2l. apply mmul_minv_l; auto.
  Qed.
  
End MinvGE.


(* ############################################################################ *)
(** * Test *)

(* ******************************************************************* *)
(** ** Test inverse matrix on Qc *)

Module MinvGE_Qc := MinvGE FieldElementTypeQc.

Section test_Qc.
  Import MinvGE_Qc.

  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
  
  (** Example 1: a `3x3` matrix *)
  Section ex1.

    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)
    Let d1 := Q2Qc_dlist [[1;3;1];[2;1;1];[2;2;1]]%Q.
    Let d2 := Q2Qc_dlist [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q.
    (* Note, we need the `Q2Qc` function to typing term of `Qc` type *)
    
    (* Compute minvertibleb_list 3 d1. *)
    (* Compute minv_list 3 d1. *)
    (* Compute minv_list 3 d2. *)

    Goal minv_list 3 d1 = d2.
    Proof. cbv. list_eq; f_equal; apply proof_irrelevance. Qed.
    
    (* Note, the `canon` part is unnecessary for users. 
       But we can remove the proof part easily *)
    (* Compute Qc2Q_dlist (minv_list 3 d1). *)
  End ex1.

  (* Using Qc type, in summary:
     1. the input need `Q2Qc` function
     2. the output has unnecessary proofs *)

  (* We can define more convenient functions with Q type *)
  Open Scope Q_scope.

  (** Check matrix invertibility with rational number lists *)
  Definition minvertibleb_listQ (n : nat) (d : dlist Q) : bool :=
    minvertibleb_list n (Q2Qc_dlist d).
  
  (** Inverse matrix with rational number lists *)
  Definition minv_listQ (n : nat) (dl : dlist Q) : dlist Q :=
    Qc2Q_dlist (minv_list n (Q2Qc_dlist dl)).
  
  (** Example 2: a `3x3` matrix *)
  Section ex2.

    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)
    Let d1 := [[1;3;1];[2;1;1];[2;2;1]].
    Let d2 := [[-1;-1;2];[0;-1;1];[2;4;-5]].
    
    (* Compute minvertibleb_listQ 3 d1. *)
    (* Compute minv_listQ 3 d1. *)
    (* Compute minv_listQ 3 d2. *)
    (* Note, we get a friendly experience for typing and printing *)

    (* Meanwhile, the equality of the result with Q type also satisfy canonical form,
       that means we can use Leibniz equal instad of setoid equal `Qeq` *)
    Goal minv_listQ 3 d1 = d2.
    Proof. cbv. auto. Qed.
  End ex2.

  (* Example 3: another matrix *)
  Section ex3.
    (* A manually given random matrix *)
    Let d1 :=
          [[1;2;3;4;5;6;7;8];
           [2;4;5;6;7;8;9;1];
           [3;5;7;6;8;4;2;1];
           [4;5;7;6;9;8;3;2];
           [5;4;3;7;9;6;8;1];
           [6;5;3;4;7;8;9;2];
           [7;8;6;5;9;2;1;3];
           [8;9;6;3;4;5;2;1]].
    (* Time Compute minv_listQ 6 d1. (* 0.04 s *) *)
    (* Time Compute minv_listQ 7 d1. (* 0.14 s *) *)
    (* Time Compute minv_listQ 8 d1. (* 0.62 s *) *)
    (* Note that many elements are in the fraction format of rational numbers.
       This is reasonable, as fractions typically do not possess a finite decimal 
       representation. *)
    
    (* How to verify the inverse matrix in MATLAB ?
     (1) change the format of rational numbers between fractions and floating
         point numbers.
     >> format rat
     >> format short

     (2) inverse matrix of a 6x6 matrix
     >> M = [1 2 3 4 5 6; ...
             2 4 5 6 7 8; ...
             3 5 7 6 8 4; ...
             4 5 7 6 9 8; ...
             5 4 3 7 9 6; ...
             6 5 3 4 7 8]
     >> M1 = inv(M)
     Note that, the result is equal.

     (3) inverse matrix of a 8x8 matrix
     >> M = [1 2 3 4 5 6 7 8; ...
             2 4 5 6 7 8 9 1; ...
             3 5 7 6 8 4 2 1; ...
             4 5 7 6 9 8 3 2; ...
             5 4 3 7 9 6 8 1; ...
             6 5 3 4 7 8 9 2; ...
             7 8 6 5 9 2 1 3; ...
             8 9 6 3 4 5 2 1]
     >> M1 = inv(M) 
     Note that, the result is a bit different with in Coq.
     For example:
         in COQ,     M1(0,2)=41846/50943 = 0.8214278704
         in MATLAB,  M1(0,2)=23/28       = 0.8214285714
     *)

    Goal ~(Qmake 41846 50943 == Qmake 23 28).
    Proof.
      intro. cbv in H.          (* 1171688%Z = 1171689%Z *)
      easy.
    Qed.

    (* The possible reason is that MATLAB performs calculations using floating-point 
       numbers, and converting the inaccurate results into fractions cannot compensate
       for the difference.
       On the contrary, Coq uses completely precise results.
       While the exact benefits are unclear, this precision could be beneficial. *)
  End ex3.

  (* Example 4 : a `8x8` matrix with decimal numbers *)
  Section ex4.
  (* In MATLAB, 
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
     >> M1 = inv(M)
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

    (* Time Compute minvertibleb_listQ 8 d1. (* 0.15s *) *)
    (* Time Compute minv_listQ 5 d1. (* 0.34 *) *)
    (* Time Compute minv_listQ 6 d1. (* 1.28 *) *)
    (* Time Compute minv_listQ 7 d1. (* 4.8 *) *)
    (* Time Compute minv_listQ 8 d1. (* 20.5 *) *)
  End ex4.
  
  (* In summary, for computing inverse matrices with listQ:
     1. simple input format, and relatively simple output format.
     2. more accuately result compared to MATLAB, but fractions are not intuitive.
     3. Leibniz equal is supported.
   *)
End test_Qc.
