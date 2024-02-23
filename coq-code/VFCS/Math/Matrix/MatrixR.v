(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on R.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Export RExt.
Require Export MatrixModule.


(* ======================================================================= *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryR := FieldMatrixTheory FieldElementTypeR.

Open Scope R_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** * Matrix theory applied to this type *)


(* ==================================== *)
(** ** matrix norm *)
Section matrix_norm.

  (** Specification of norm *)
  Class Norm `{Ring} (f : A -> R) (cmul : R -> A -> A) := {
      Norm_pos : forall a : A, 0 <= f a;
      Norm_eq0_iff : forall a : A, f a = 0 <-> a = Azero;
      Norm_cmul_compat : forall (c : R) (a : A), f (cmul c a) = ((Rabs c) * f a)%A
    }.
  
  Section spec.
    Context {r c : nat}.
    Variable mnorm : mat r c -> R.

    Definition mnorm_spec_pos := forall M : mat r c,
        (M <> mat0 -> mnorm M > 0) /\ (M = mat0 -> mnorm M = 0).
    Definition mnorm_spec_mcmul := forall (M : mat r c) (k : R),
        mnorm (k \.* M) = ((Rabs k) * (mnorm M))%R.
    Definition mnorm_spec_trig := forall (M N : mat r c),
        mnorm (M + N) <= mnorm M + mnorm N.
  End spec.

  Section mnormF.
    Notation vsum := (@vsum _ Aadd 0 _).
    
    (* F-norm (M) := √(∑∑M(i,j)²) *)
    Definition mnormF {r c} (M : mat r c) : R :=
      sqrt (vsum (fun i => vsum (fun j => (M$i$j)²))).

    (** mnormF m = √ tr (M\T * M) *)
    Lemma mnormF_eq_trace : forall {r c} (M : mat r c),
        mnormF M = sqrt (tr (M\T * M)).
    Proof.
      intros. unfold mnormF. f_equal. unfold mtrace, Matrix.mtrace, vsum.
      rewrite fseqsum_fseqsum_exchg. apply fseqsum_eq. intros j.
      apply fseqsum_eq. intros i. cbv. auto.
    Qed.

    Lemma mnormF_spec_pos : forall r c, mnorm_spec_pos (@mnormF r c).
    Proof.
      intros. hnf. intros. split; intros.
      - unfold mnormF. apply sqrt_lt_R0. apply vsum_gt0.
        + intros. apply vsum_ge0. intros. apply sqr_ge0.
        + apply mneq_iff_exist_mnth_neq in H. destruct H as [i [j H]].
          exists i. intro. apply vsum_eq0_rev with (i:=j) in H0; auto.
          * rewrite mnth_mat0 in H. cbv in H. ra.
          * intros. ra.
      - rewrite H. unfold mnormF.
        apply sqrt_0_eq0. apply vsum_eq0; intros. apply vsum_eq0; intros.
        rewrite mnth_mat0. ra.
    Qed.

    ?
    Lemma mnormF_spec_mcmul : forall r c, mnorm_spec_mcmul (@mnormF r c).
    Proof.
    Admitted.


    Lemma mnormF_spec_trig : forall r c, mnorm_spec_trig (@mnormF r c).
    Proof.
    Admitted.
    
  End mnormF.
  
End matrix_norm.


(* ==================================== *)
(** ** Orthogonal matrix *)
Section morth.

  (** orthogonal m -> |m| = ± 1 *)
  Lemma morth_mdet : forall {n} (m : smat n),
      morth m -> (mdet m = 1 \/ mdet m = - (1))%T.
  Proof.
    intros.
    assert (m\T * m = mat1).
    { unfold morth in H. unfold Matrix.morth in H. rewrite H. easy. }
    assert (mdet (m\T * m)%M = mdet (@mat1 n))%T.
    { rewrite H0. easy. }
    rewrite mdet_mmul in H1. rewrite mdet_mtrans in H1. rewrite mdet_1 in H1.
    apply Rsqr_eq1 in H1. easy.
  Qed.

End morth.


(* ==================================== *)
(** ** SO(n): special orthogonal group *)

Section SOn.

  (** SO2 *)
  Definition SO2 := SOn 2.

  (** SO3 *)
  Definition SO3 := SOn 3.

  Variable m : SO3.

  Goal m\T = m⁻¹.
  Proof. destruct m. rewrite morth_imply_inv_eq_trans; try easy. Qed.

End SOn.


(* ==================================== *)
(** ** Usage demo *)
Section test.
  Let l1 := [[1;2];[3;4]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Ropp m1). *)
  (* Compute m2l (m1 * m1). *)

  Variable a11 a12 a21 a22 : T.
  Variable f : T -> T.
  Let m2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.     (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  (* Compute m2l (m2 * m2). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 = m2 + m1.
  Proof. intros. apply madd_comm. Qed.

  (** Simulate Outer/inner product of two vectors *)
  Variables a1 a2 a3 b1 b2 b3 : T.
  Let m31 := @l2m 3 1 [[a1];[a2];[a3]].
  Let m13 := @l2m 1 3 [[b1;b2;b3]].
  (* Compute m2l (m31 * m13). *)
  (* Compute m2l (m13 * m31). *)

  (** mmul_sub_distr_r *)
  Goal forall r c s (m1 m2 : mat r c) (m3 : mat c s), (m1 - m2) * m3 = m1 * m3 - m2 * m3.
    intros. rewrite mmul_msub_distr_r. easy. Qed.

  (* test rewriting *)
  Goal forall r c (m1 m2 : mat r c) x, m1 = m2 -> x \.* m1 = x \.* m2.
  Proof. intros. f_equiv. easy. Qed.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 = m2 -> m3 = m4 -> m1 - m3 = m2 - m4.
  Proof. clear. intros. f_equiv. easy. easy. Qed.

  (* test_monoid. *)
  Goal forall r c (m1 m2 : mat r c), mat0 + m1 = m1.
    monoid_simp. Qed.
End test.


Section Example4CoordinateSystem.
  Variable ψ θ φ: R.
  Let Rx := (mk_mat_3_3 1 0 0 0 (cos φ) (sin φ) 0 (-sin φ) (cos φ))%R.
  Let Ry := (mk_mat_3_3 (cos θ) 0 (-sin θ) 0 1 0 (sin θ) 0 (cos θ))%R.
  Let Rz := (mk_mat_3_3 (cos ψ) (sin ψ) 0 (-sin ψ) (cos ψ) 0 0 0 1)%R.
  Let Rbe := (mk_mat_3_3
                (cos θ * cos ψ) (cos ψ * sin θ * sin φ - sin ψ * cos φ)
                (cos ψ * sin θ * cos φ + sin φ * sin ψ) (cos θ * sin ψ)
                (sin ψ * sin θ * sin φ + cos ψ * cos φ)
                (sin ψ * sin θ * cos φ - cos ψ * sin φ)
                (-sin θ) (sin φ * cos θ) (cos φ * cos θ))%R.
  Lemma Rbe_ok : (Rbe = Rz\T * Ry\T * Rx\T).
  Proof. lma. Qed.
    
End Example4CoordinateSystem.


(** example for symbol matrix *)
Module Exercise_Ch1_Symbol.

  (* for better readibility *)
  Notation "0" := R0.
  Notation "1" := R1.
  Notation "2" := (R1 + R1)%R.
  Notation "3" := (R1 + (R1 + R1))%R.
  Notation "4" := ((R1 + R1) * (R1 + R1))%R.
  
  Example ex6_1 : forall a b : R,
      (let m := mk_mat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1 in
      mdet m = (a - b)^3)%R.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_2 : forall a b x y z : T,
      (let m1 := mk_mat_3_3
                   (a*x+b*y) (a*y+b*z) (a*z+b*x)
                   (a*y+b*z) (a*z+b*x) (a*x+b*y)
                   (a*z+b*x) (a*x+b*y) (a*y+b*z) in
       let m2 := mk_mat_3_3 x y z y z x z x y in
       mdet m1 = (a^3 + b^3) * mdet m2)%R.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_3 : forall a b e d : T,
      (let m := mk_mat_4_4
                 (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
                 (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
                 (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
                 (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2) in
      mdet m = 0)%R.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_4 : forall a b e d : T,
      let m := mk_mat_4_4
                 1 1 1 1
                 a b e d
                 (a^2) (b^2) (e^2) (d^2)
                 (a^4) (b^4) (e^4) (d^4) in
      (mdet m = (a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%R.
  Proof. intros. cbv. ring. Qed.
  
  (* (** 6.(5), it is an infinite structure, need more work, later... *) *)

End Exercise_Ch1_Symbol.
