(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Base for matrix inversion
  author    : ZhengPu Shi
  date      : 2023.12

  content   :
  1. minvertible
  2. interface for matrix inversion
 *)

Require Export ElementType Matrix MatrixDet.


(* ############################################################################ *)
(** * Matrix is invertible  *)

Section minvertible.
  Context `{HField : Field} `{HAeqDec : Dec _ (@eq A)}.
  Add Field field_thy_inst : (make_field_theory HField).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation "a / b" := ((a * /b)%A) : A_scope.

  Notation vdot := (@vdot _ Aadd 0 Amul).
  Notation "< a , b >" := (vdot a b) : vec_scope.

  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.
  Notation mvmul := (@mvmul _ Aadd 0 Amul).
  Infix "v*" := mvmul : mat_scope.
  Notation mcmul := (@mcmul _ Amul).
  Infix "\.*" := mcmul : mat_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation "| M |" := (mdet M) : mat_scope.
  Notation madj := (@madj _ Aadd 0 Aopp Amul 1).
  Notation "M \A" := (madj M) : mat_scope.
  
  (* Notation minvAM := (@minvAM _ Aadd 0 Aopp Amul 1 Ainv). *)
  (* Notation "M \-1" := (minvAM M) : mat_scope. *)
  (* (* Notation minvertibleAM := (@minvertibleAM _ Aadd 0 Aopp Amul Aone). *) *)
  (* Notation minvAMo := (@minvAMo _ Aadd 0 Aopp Amul 1 Ainv). *)
  (* Notation minvAM := (@minvAM _ Aadd 0 Aopp Amul 1 Ainv). *)

  (* Notation minvertibleGE := (@minvertibleGE _ Aadd 0 Aopp Amul Ainv). *)
  (* Notation minvGEo := (@minvGEo _ Aadd 0 Aopp Amul 1 Ainv). *)
  (* Notation minvGE := (@minvGE _ Aadd 0 Aopp Amul 1 Ainv). *)

  
  (* ======================================================================= *)
  (** ** Invertible (nonsingular, nondegenerate) matrix *)
  
  (** The matrix `M` is invertible *)
  Definition minvertible {n} (M : smat n) : Prop :=
    exists M', M' * M = mat1 /\ M * M' = mat1.

  (** The matrix `M` is left invertible (i.e., exist a left inverse) *)
  Definition minvertibleL {n} (M : smat n) : Prop := exists N, N * M = mat1.

  (** The matrix `M` is right invertible (i.e., exist a right inverse) *)
  Definition minvertibleR {n} (M : smat n) : Prop := exists N, M * N = mat1.

  (** matrix `M` is invertible, imply `M` is left invertible *)
  Lemma minvertible_imply_minvertibleL : forall {n} (M : smat n),
      minvertible M -> minvertibleL M.
  Proof. intros. hnf in *. destruct H as [M' [H H0]]. exists M'; auto. Qed.

  (** matrix `M` is invertible, imply `M` is right invertible *)
  Lemma minvertible_imply_minvertibleR : forall {n} (M : smat n),
      minvertible M -> minvertibleR M.
  Proof. intros. hnf in *. destruct H as [M' [H H0]]. exists M'; auto. Qed.

  (** matrix `M` is left invertible, if and only if the determinant is not zero *)
  Lemma minvertibleL_iff_mdet_neq0 : forall {n} (M : smat n), minvertibleL M <-> |M| <> 0.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [M' H].
      apply mmul_eq1_imply_mdet_neq0_r in H. auto.
    - hnf. apply mdet_neq0_imply_mmul_eq1_l. auto.
  Qed.

  (** matrix `M` is right invertible, if and only if the determinant is not zero *)
  Lemma minvertibleR_iff_mdet_neq0 : forall {n} (M : smat n), minvertibleR M <-> |M| <> 0.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [M' H].
      apply mmul_eq1_imply_mdet_neq0_l in H. auto.
    - hnf. apply mdet_neq0_imply_mmul_eq1_r. auto.
  Qed.

  (** A matrix `M` is invertible, if and only if the determinant is not zero *)
  Lemma minvertible_iff_mdet_neq0 : forall {n} (M : smat n), minvertible M <-> |M| <> 0.
  Proof.
    intros. split; intros.
    - apply minvertible_imply_minvertibleL in H.
      apply minvertibleL_iff_mdet_neq0; auto.
    - hnf. apply mdet_neq0_imply_mmul_eq1. auto.
  Qed.

  (** matrix `M` is left invertible, imply `M` is invertible *)
  Lemma minvertibleL_imply_minvertible : forall {n} (M : smat n),
      minvertibleL M -> minvertible M.
  Proof.
    intros. rewrite minvertibleL_iff_mdet_neq0 in H.
    rewrite minvertible_iff_mdet_neq0. auto.
  Qed.

  (** matrix `M` is right invertible, imply `M` is invertible *)
  Lemma minvertibleR_imply_minvertible : forall {n} (M : smat n),
      minvertibleR M -> minvertible M.
  Proof.
    intros. rewrite minvertibleR_iff_mdet_neq0 in H.
    rewrite minvertible_iff_mdet_neq0. auto.
  Qed.

  (** matrix `M` is invertible, if and only if `M` is left invertible *)
  Lemma minvertible_iff_minvertibleL : forall {n} (M : smat n),
      minvertible M <-> minvertibleL M.
  Proof.
    intros. split; intros.
    apply minvertible_imply_minvertibleL; auto.
    apply minvertibleL_imply_minvertible; auto.
  Qed.

  (** matrix `M` is invertible, if and only if `M` is right invertible *)
  Lemma minvertible_iff_minvertibleR : forall {n} (M : smat n),
      minvertible M <-> minvertibleR M.
  Proof.
    intros. split; intros.
    apply minvertible_imply_minvertibleR; auto.
    apply minvertibleR_imply_minvertible; auto.
  Qed.

  (** matrix `M` is left invertible, if and only if `M` is right invertible *)
  Lemma minvertibleL_iff_minvertibleR : forall {n} (M : smat n),
      minvertibleL M <-> minvertibleR M.
  Proof.
    intros. rewrite <- minvertible_iff_minvertibleL.
    rewrite <- minvertible_iff_minvertibleR. tauto.
  Qed.

  (** `M * N = mat1` imply `M` is invertible *)
  Lemma mmul_eq1_imply_minvertible_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvertible M.
  Proof. intros. rewrite minvertible_iff_minvertibleR. hnf. exists N; auto. Qed.

  (** `M * N = mat1` imply `N` is invertible *)
  Lemma mmul_eq1_imply_minvertible_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvertible N.
  Proof. intros. rewrite minvertible_iff_minvertibleL. hnf. exists M; auto. Qed.


  (** Transpose preserve `invertible` property *)
  Lemma mtrans_minvertible : forall n (M : smat n),
      minvertible M -> minvertible (M\T).
  Proof.
    intros. hnf in *. destruct H as [E [Hl Hr]]. exists (E\T). split.
    - hnf. rewrite <- mtrans_mmul. rewrite Hr. apply mtrans_mat1.
    - hnf. rewrite <- mtrans_mmul. rewrite Hl. apply mtrans_mat1.
  Qed.

  (** Multiplication preserve `invertible` property *)
  Lemma mmul_minvertible: forall {n} (M N : smat n), 
      minvertible M -> minvertible N -> minvertible (M * N).
  Proof.
    intros. hnf in *. destruct H as [M' [HL HR]], H0 as [N' [HL1 HR1]]; hnf in *.
    exists (N' * M'). split; hnf.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc M' M). rewrite HL, mmul_1_l; auto.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc N N'). rewrite HR1, mmul_1_l; auto.
  Qed.

  (** mat1 is invertible *)
  Lemma mat1_minvertible : forall {n}, minvertible (@mat1 n).
  Proof. intros. hnf. exists mat1. split; hnf; rewrite mmul_1_l; auto. Qed.


  (** Left cancellation law of matrix multiplication *)
  Lemma mmul_cancel_l : forall {r c} (M : smat r) (N1 N2 : mat r c) ,
      minvertible M -> M * N1 = M * N2 -> N1 = N2.
  Proof.
    intros. hnf in H. destruct H as [N [Hl Hr]].
    assert (N * M * N1 = N * M * N2). rewrite !mmul_assoc. rewrite H0. auto.
    rewrite Hl in H. rewrite !mmul_1_l in H. auto.
  Qed.

  (** Right cancellation law of matrix multiplication *)
  Lemma mmul_cancel_r : forall {r c} (M : smat c) (N1 N2 : mat r c) ,
      minvertible M -> N1 * M = N2 * M -> N1 = N2.
  Proof.
    intros. hnf in H. destruct H as [N [Hl Hr]].
    assert (N1 * M * N = N2 * M * N). rewrite H0. auto.
    rewrite !mmul_assoc in H. rewrite Hr in H. rewrite !mmul_1_r in H. auto.
  Qed.

  (** Cancellation law of matrix multiply vector *)
  Lemma mmulv_cancel : forall {n} (M : smat n) (a b : vec n),
      minvertible M -> M *v a = M *v b -> a = b.
  Proof.
    intros. hnf in *. destruct H as [N [Hl Hr]].
    assert (N *v (M *v a) = N *v (M *v b)). rewrite H0. auto.
    rewrite <- !mmulv_assoc in H. rewrite Hl in H. rewrite !mmulv_1_l in H. auto.
  Qed.

  (** Cancellation law of vector multipliy matrix *)
  Lemma mvmul_cancel : forall {n} (M : smat n) (a b : vec n),
      minvertible M -> a v* M = b v* M -> a = b.
  Proof.
    intros. hnf in *. destruct H as [N [Hl Hr]].
    assert (a v* M v* N = b v* M v* N). rewrite H0; auto.
    rewrite <- !mvmul_assoc in H. rewrite Hr in H. rewrite !mvmul_1_r in H. auto.
  Qed.

  (** N1 * M = mat1 -> N2 * M = mat1 -> N1 = N2 *)
  Lemma mmul_eq1_uniq_l : forall {n} (M N1 N2 : smat n),
      N1 * M = mat1 -> N2 * M = mat1 -> N1 = N2.
  Proof.
    intros. rewrite <- H in H0. apply mmul_cancel_r in H0; auto.
    apply mmul_eq1_imply_minvertible_r in H. auto.
  Qed.

  (** M * N1 = mat1 -> M * N2 = mat1 -> N1 = N2 *)
  Lemma mmul_eq1_uniq_r : forall {n} (M N1 N2 : smat n),
      M * N1 = mat1 -> M * N2 = mat1 -> N1 = N2.
  Proof.
    intros. rewrite <- H in H0. apply mmul_cancel_l in H0; auto.
    apply mmul_eq1_imply_minvertible_l in H. auto.
  Qed.

  (** M * N = mat1 -> M = /|N| .* N\A *)
  Lemma mmul_eq1_imply_det_cmul_adj_l : forall {n} (M N : smat n),
      M * N = mat1 -> M = /|N| \.* N\A.
  Proof.
    intros. apply mmul_eq1_uniq_l with (M:=N); auto.
    apply mmul_det_cmul_adj_l. apply mmul_eq1_imply_mdet_neq0_r in H. auto.
  Qed.

  (** M * N = mat1 -> N = /|M| .* M\A *)
  Lemma mmul_eq1_imply_det_cmul_adj_r : forall {n} (M N : smat n),
      M * N = mat1 -> N = /|M| \.* M\A.
  Proof.
    intros. apply mmul_eq1_uniq_r with (M:=M); auto.
    apply mmul_det_cmul_adj_r. apply mmul_eq1_imply_mdet_neq0_l in H. auto.
  Qed.
    
  (** M1 * M2 = mat1 -> M2 * M1 = mat1 *)
  Lemma mmul_eq1_comm : forall {n} (M1 M2 : smat n),
      M1 * M2 = mat1 -> M2 * M1 = mat1.
  Proof.
    (* Tips: I CAN'T PROVE IT ONLY USE INDUCTION *)
    intros.
    apply mmul_eq1_imply_det_cmul_adj_l in H as H0. rewrite H0.
    apply mmul_det_cmul_adj_r. apply mmul_eq1_imply_mdet_neq0_r in H. auto.
  Qed.
    
  (* (** A square matrix is invertible, iff minvertibleGE is true *) *)
  (* Lemma minvertible_iff_minvertibleGE_true : forall {n} (M : smat n), *)
  (*     minvertible M <-> minvertibleGE M = true. *)
  (* Proof. *)
  (*   intros. split; intros. *)
  (*   - hnf in H. destruct H as [M' [Hl Hr]]. *)
  (*     apply mmul_eq1_imply_invertibleGE_true_r in Hl; auto. *)
  (*   - apply mmul_minvGE_l in H. *)
  (*     rewrite minvertible_iff_minvertibleL. hnf. *)
  (*     exists (minvGE M); auto. *)
  (* Qed. *)

  
  (* ======================================================================= *)
  (** ** Singular (degenerate, not invertible) matrix *)
  
  (** The matrix `M` is singular (i.e., not invertible) *)
  Definition msingular {n} (M : smat n) : Prop := ~(minvertible M).
  
  (* (** A square matrix is singular, iff minvertibleGE is false *) *)
  (* Lemma msingular_iff_minvertibleGE_false : forall {n} (M : smat n), *)
  (*     msingular M <-> minvertibleGE M = false. *)
  (* Proof. *)
  (*   intros. unfold msingular. rewrite minvertible_iff_minvertibleGE_true. *)
  (*   rewrite not_true_iff_false. easy. *)
  (* Qed. *)

  (* (** A square matrix is singular, iff minvertibleAM is false *) *)
  (* Lemma msingular_iff_minvertibleAM_false : forall {n} (M : smat n), *)
  (*     msingular M <-> minvertibleAM M = false. *)
  (* Proof. *)
  (*   intros. unfold msingular. rewrite minvertible_iff_minvertibleAM_true. *)
  (*   rewrite not_true_iff_false. easy. *)
  (* Qed. *)
  
End minvertible.


(* ############################################################################ *)
(** * Interface of matrix inversion *)
Module Type Minv (E : FieldElementType).
  Export E.
  Open Scope A_scope.
  Open Scope mat_scope.

  Notation smat n := (smat A n).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.

  Notation minvertible := (@minvertible _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).


  (* ======================================================================= *)
  (** ** Check matrix invertibility *)

  (** Check the invertibility of matrix `M` *)
  Parameter minvertibleb : forall {n} (M : smat n), bool.

  (** minvertible M <-> minvertibleb M = true *)
  Axiom minvertible_iff_minvertibleb_true : forall {n} (M : smat n),
      minvertible M <-> minvertibleb M = true.
  
  (** msingular M <-> minvertibleb M = false *)
  Axiom msingular_iff_minvertibleb_false : forall {n} (M : smat n),
      msingular M <-> minvertibleb M = false.
  
  (* (* From `M * N = mat1`, the `minvertibleb M` return true *) *)
  (* Axiom mmul_eq1_imply_minvertibleb_true_l : forall {n} (M N : smat n), *)
  (*     M * N = mat1 -> minvertibleb M = true. *)

  (* (* From `M * N = mat1`, the `minvertibleb N` return true *) *)
  (* Axiom mmul_eq1_imply_minvertibleb_true_r : forall {n} (M N : smat n), *)
  (*     M * N = mat1 -> minvertibleb N = true. *)


  (* ======================================================================= *)
  (** ** Inverse matrix (option version) *)

  (** Inverse matrix (option version) *)
  Parameter minvo : forall {n} (M : smat n), option (smat n).
  
  (** `minvo` return `Some`, iff M is invertible *)
  Axiom minvo_Some_iff_minvertible : forall {n} (M : smat n),
      (exists M', minvo M = Some M') <-> minvertible M.

  (** `minvo` return `None`, iff M is singular *)
  Axiom minvo_None_iff_msingular : forall {n} (M : smat n),
      minvo M = None <-> msingular M.

  (** If `minvo M` return `Some M'`, then `M' * M = mat1` *)
  Axiom minvo_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvo M = Some M' -> M' * M = mat1.

  (** If `minvo M` return `Some M'`, then `M * M' = mat1` *)
  Axiom minvo_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvo M = Some M' -> M * M' = mat1.

  
  (* ======================================================================= *)
  (** ** Inverse matrix (default value version) *)

  (** Inverse matrix (with identity matrix as default value) *)
  Parameter minv : forall {n} (M : smat n), smat n.
  Notation "M \-1" := (minv M) : mat_scope.

  (** If `minvo M` return `Some N`, then `M\-1` equal to `N` *)
  Axiom minvo_Some_imply_minv : forall {n} (M N : smat n), minvo M = Some N -> M\-1 = N.

  (** If `minvo M` return `None`, then `M\-1` equal to `mat1` *)
  Axiom minvo_None_imply_minv : forall {n} (M  : smat n), minvo M = None -> M\-1 = mat1.
  
  (** M\-1 * M = mat1 *)
  Axiom mmul_minv_l : forall {n} (M : smat n), minvertible M -> M\-1 * M = mat1.

  (** M * M\-1 = mat1 *)
  Axiom mmul_minv_r : forall {n} (M : smat n), minvertible M -> M * M\-1 = mat1.

  (** M * N = mat1 -> M = N \-1 *)
  Axiom mmul_eq1_imply_minv_l : forall {n} (M N : smat n), M * N = mat1 -> M = N\-1.
  
  (** M * N = mat1 -> N = M \-1 *)
  Axiom mmul_eq1_imply_minv_r : forall {n} (M N : smat n), M * N = mat1 -> N = M\-1.
  

  (* ******************************************************************* *)
  (** ** Inverse matrix with lists for input and output *)

  (** Check matrix invertibility with lists as input *)
  Parameter minvertibleb_list : forall (n : nat) (dl : dlist A), bool.

  (** `minvertibleb_list` is equal to `minvertibleb` *)
  Axiom minvertibleb_list_spec : forall (n : nat) (dl : dlist A),
      minvertibleb_list n dl = @minvertibleb n (l2m Azero dl).


  (** Inverse matrix with lists for input and output *)
  Parameter minv_list : forall (n : nat) (dl : dlist A), dlist A.

  (** The matrix of [minv_list dl] is the inverse of the matrix of [dl] *)
  Axiom minv_list_spec : forall (n : nat) (dl : dlist A),
      minvertibleb_list n dl = true ->
      (@l2m _ Azero n n (minv_list n dl)) * (l2m Azero dl) = mat1.
End Minv.
