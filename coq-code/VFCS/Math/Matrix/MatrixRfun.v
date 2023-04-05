(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on function of R to R.
  author    : ZhengPu Shi
  date      : 2023.04
*)

Require Export Matrix.
Require Export RExt.
Require Export RealFunction.


(* ======================================================================= *)
(** ** Matrix theory come from common implementations *)

Open Scope R_scope.
Open Scope fun_scope.
Open Scope mat_scope.

(** general notations *)
Notation A := tpRFun.
Notation A0 := fzero.
Notation A1 := fone.
Notation Aadd := fadd.
Notation Aopp := fopp.
Notation Amul := fmul.
Notation Ainv := finv.

(** *** matrix type and basic operation *)
Definition mat (r c : nat) : Type := @mat A r c.
Notation smat n := (smat A n).

Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope.

Lemma meq_iff_mnth : forall {r c} (m1 m2 : mat r c),
    m1 == m2 <-> (forall i j : nat, i < r -> j < c -> m1!i!j = m2!i!j)%nat.
Proof. apply meq_iff_mnth. Qed.

(** *** convert between list and matrix *)
Definition l2m (r c : nat) (dl : dlist A) : mat r c := l2m A0 dl.
Definition m2l {r c : nat} (m : mat r c) : dlist A := m2l m.

Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
Proof. intros. apply m2l_length. Qed.

Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
Proof. intros. apply m2l_width. Qed.

Lemma m2l_l2m_id : forall {r c} (dl : dlist A),
    length dl = r -> width dl c -> m2l (l2m r c dl) = dl.
Proof. intros. apply m2l_l2m_id; auto. Qed.

Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m r c (m2l m) == m.
Proof. intros. apply l2m_m2l_id; auto. Qed.

Lemma l2m_inj : forall {r c} (d1 d2 : dlist A),
    length d1 = r -> width d1 c -> length d2 = r -> width d2 c -> 
    d1 <> d2 -> ~(l2m r c d1 == l2m r c d2).
Proof. intros. apply l2m_inj; auto. Qed.

Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m r c d == m). 
Proof. intros. apply l2m_surj; auto. Qed.

Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~ (m1 == m2) -> m2l m1 <> m2l m2.
Proof. intros. apply (m2l_inj A0); auto. Qed.

Lemma m2l_surj : forall {r c} (d : dlist A), length d = r -> width d c -> 
    (exists m : mat r c, m2l m = d).
Proof. intros. apply (m2l_surj A0); auto. Qed.

(** *** convert between tuple and matrix *)
Definition t2m_3_3 (t : T_3_3) : mat 3 3 := t2m_3_3 A0 t.
Definition m2t_3_3 (m : mat 3 3) : T_3_3 := m2t_3_3 m.
Definition m2t_1_1 (m : mat 1 1) := m2t_1_1 m.

(** *** construct matrix with vector and matrix *)

(** construct a matrix with a row vector and a matrix *)
Definition mconsr {r c} (v : mat 1 c) (m : mat r c) : mat (S r) c := mconsr v m.
(** construct a matrix with a column vector and a matrix *)
Definition mconsc {r c} (v : mat r 1) (m : mat r c) : mat r (S c) := mconsc v m.

(** *** build matrix from elements *)
Definition mk_mat_1_1 a11 : mat 1 1 :=
  mk_mat_1_1 (A0:=A0) a11.
Definition mk_mat_3_1 a11 a12 a13 : mat 3 1 :=
  mk_mat_3_1 (A0:=A0) a11 a12 a13.
Definition mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
  mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

(** *** matrix transposition *)
Definition mtrans {r c : nat} (m : mat r c) : mat c r := mtrans m.
Notation "m \T" := (mtrans m) : mat_scope.

Lemma mtrans_trans : forall {r c} (m : mat r c), m \T\T == m.
Proof. intros. apply mtrans_trans. Qed.

(** *** matrix mapping *)
Definition mmap {r c} f (m : mat r c) : mat r c := mmap f m.
Definition mmap2 {r c} f (m1 m2 : mat r c) : mat r c := mmap2 f m1 m2.

Lemma mmap2_comm : forall {r c} (m1 m2 : mat r c) f (fcomm : Commutative f),
    mmap2 f m1 m2 == mmap2 f m2 m1.
Proof. intros. apply mmap2_comm; auto. Qed.

Lemma mmap2_assoc : forall {r c} f (m1 m2 m3 : mat r c) (fassoc : Associative f),
    mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
Proof. intros. apply mmap2_assoc; auto. Qed.

(** *** zero matrix *)
Definition mat0 {r c} : mat r c := mat0 A0 r c.

(** *** unit matrix *)
Definition mat1 {n} : mat n n := mat1 A0 A1 n.

(** *** matrix addition *)
Definition madd {r c} (m1 m2 : mat r c) : mat r c := madd m1 m2 (Aadd:=Aadd).
Infix "+" := madd : mat_scope.

Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == m2 + m1.
Proof. intros. apply madd_comm. Qed.

Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
Proof. intros. apply madd_assoc. Qed.

Lemma madd_0_l : forall {r c} (m : mat r c), mat0 + m == m.
Proof. intros. apply madd_0_l. Qed.

(** *** matrix opposition *)
Definition mopp {r c} (m : mat r c) : mat r c := mopp m (Aopp:=Aopp).
Notation "- m" := (mopp m) : mat_scope.

Lemma madd_opp_l : forall {r c} (m : mat r c), (-m) + m == mat0.
Proof. intros. apply madd_opp_l. Qed.

Lemma madd_opp_r : forall {r c} (m : mat r c), m + (-m) == mat0.
Proof. intros. apply madd_opp_r. Qed.

Lemma mopp_opp : forall {r c} (m : mat r c), - - m == m.
Proof. intros. apply mopp_opp. Qed.

(** *** matrix subtraction *)
Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
  msub m1 m2 (Aadd:=Aadd)(Aopp:=Aopp).
Infix "-" := msub : mat_scope.

Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
Proof. intros. apply msub_comm. Qed.

Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
Proof. intros. apply msub_assoc. Qed.

Lemma msub_0_l : forall {r c} (m : mat r c), mat0 - m == - m.
Proof. intros. apply msub_0_l. Qed.

Lemma msub_0_r : forall {r c} (m : mat r c), m - mat0 == m.
Proof. intros. apply msub_0_r. Qed.

Lemma msub_self : forall {r c} (m : mat r c), m - m == mat0.
Proof. intros. apply msub_self. Qed.

(** *** matrix scalar multiplication *)
Definition mcmul {r c} a (m : mat r c) : mat r c := mcmul a m (Amul:=Amul).
Infix " 'c*' " := mcmul : mat_scope.

Global Instance mcmul_mor : forall r c,  Proper (eq ==> meq ==> meq) (@mcmul r c).
Proof. intros. apply (mcmul_mor (A0:=A0)). Qed.

Lemma mcmul_assoc : forall {r c} a b (m : mat r c), a c* (b c* m) == (a * b) c* m.
Proof. intros. apply mcmul_assoc. Qed.

Lemma mcmul_perm : forall {r c} a b (m : mat r c),  a c* (b c* m) == b c* (a c* m).
Proof. intros. apply mcmul_perm. Qed.

Lemma mcmul_add_distr_l : forall {r c} a (m1 m2 : mat r c),
    a c* (m1 + m2) == (a c* m1) + (a c* m2).
Proof. intros. apply mcmul_add_distr_l. Qed.

Lemma mcmul_add_distr_r : forall {r c} a b (m : mat r c),
    (a + b)%F c* m == (a c* m) + (b c* m).
Proof. intros. apply mcmul_add_distr_r. Qed.

Lemma mcmul_1_l : forall {r c} (m : mat r c), A1 c* m == m.
Proof. intros. apply mcmul_1_l. Qed.

Lemma mcmul_0_l : forall {r c} (m : mat r c), A0 c* m == mat0.
Proof. intros. apply mcmul_0_l. Qed.

(** *** matrix multiplication *)
Definition mmul {r c s} (m1 : mat r c) (m2 : mat c s) : mat r s :=
  mmul m1 m2 (Aadd:=Aadd) (A0:=A0) (Amul:=Amul).
Infix "*" := mmul : mat_scope.

Lemma mmul_add_distr_l : forall {r c s} (m1 : mat r c) (m2 m3 : mat c s),
    m1 * (m2 + m3) == (m1 * m2) + (m1 * m3).
Proof. intros. apply mmul_add_distr_l. Qed.

Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s),
    (m1 + m2) * m3 == (m1 * m3) + (m2 * m3).
Proof. intros. apply mmul_add_distr_r. Qed.

Lemma mmul_assoc : forall {r c s t} (m1 : mat r c) (m2 : mat c s) (m3 : mat s t),
    (m1 * m2) * m3 == m1 * (m2 * m3).
Proof. intros. apply mmul_assoc. Qed.

Lemma mmul_0_l : forall {r c s} (m : mat c s), (@mat0 r c) * m == mat0.
Proof. intros. apply mmul_0_l. Qed.

Lemma mmul_0_r : forall {r c s} (m : mat r c), m * (@mat0 c s) == mat0.
Proof. intros. apply mmul_0_r. Qed.

Lemma mmul_1_l : forall {r c} (m : mat r c), mat1 * m == m.
Proof. intros. apply mmul_1_l. Qed.

Lemma mmul_1_r : forall {r c} (m : mat r c), m * mat1 == m. 
Proof. intros. apply mmul_1_r. Qed.


(* ======================================================================= *)
(** ** Matrix theory applied to this type *)


(* ======================================================================= *)
(** ** Usage demo *)

Section test.
  Let f11 : A := fun t => 1.
  Let f12 : A := fun t => 2.
  Let f21 : A := fun t => 3.
  Let f22 : A := fun t => 4.
  Let l1 := [[f11;f12];[f21;f22]].
  Let m1 := l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Aopp m1). *)
  (* Compute m2l (m1 * m1). *)

  Variable a11 a12 a21 a22 : A.
  Variable f : A -> A.
  Let m2 := l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.       (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  (* Compute m2l (m2 * m2). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

End test.

Section Example4CoordinateSystem.
  Add Ring ring_inst : (make_ring_theory (A:=(R->R))).

  Open Scope fun_scope.
  Notation "1" := A1 : fun_scope.
  Notation "0" := A0 : fun_scope.
  Infix "+" := Aadd : fun_scope.
  Notation "- a" := (Aopp a) : fun_scope.
  Infix "*" := Amul : fun_scope.
  
  Variable ψ θ ϕ : A.
  Let cθ : A := fun t => cos (θ t).
  Let sθ : A := fun t => sin (θ t).
  Let cψ : A := fun t => cos (ψ t).
  Let sψ : A := fun t => sin (ψ t).
  Let cϕ : A := fun t => cos (ϕ t).
  Let sϕ : A := fun t => sin (ϕ t).
  
  Let Rx := mk_mat_3_3 1 0 0 0 cϕ sϕ 0 (-sϕ) cϕ.
  Let Ry := mk_mat_3_3 cθ 0 (-sθ) 0 1 0 sθ 0 cθ.
  Let Rz := mk_mat_3_3 cψ sψ 0 (-sψ) cψ 0 0 0 1.
  Let Rbe :=
        mk_mat_3_3
          (cθ * cψ) (cψ * sθ * sϕ - sψ * cϕ)
          (cψ * sθ * cϕ + sϕ * sψ) (cθ * sψ)
          (sψ * sθ * sϕ + cψ * cϕ)
          (sψ * sθ * cϕ - cψ * sϕ)
          (-sθ) (sϕ * cθ) (cϕ * cθ).
  Lemma Rbe_ok : (Rbe == Rz\T * Ry\T * Rx\T)%mat.
  Proof. lma; ring_simplify; auto. Qed.
    
End Example4CoordinateSystem.

