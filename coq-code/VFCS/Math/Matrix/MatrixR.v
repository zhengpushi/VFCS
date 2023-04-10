(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on R.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export Matrix.
Require Export RExt.


(* ======================================================================= *)
(** ** Matrix theory come from common implementations *)

Open Scope R_scope.
Open Scope mat_scope.

(** general notations *)
Notation A := R.
Notation A0 := R0.
Notation A1 := R1.
Notation Aadd := Rplus.
Notation Aopp := Ropp.
Notation Amul := Rmult.
Notation Ainv := Rinv.

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
Definition scalar_of_mat (m : mat 1 1) := m2t_1_1 m.


(** *** construct matrix with vector and matrix *)

(** construct a matrix with a row vector and a matrix *)
Definition mconsr {r c} (v : mat 1 c) (m : mat r c) : mat (S r) c := mconsr v m.
(** construct a matrix with a column vector and a matrix *)
Definition mconsc {r c} (v : mat r 1) (m : mat r c) : mat r (S c) := mconsc v m.


(** *** build matrix from elements *)
Definition mk_mat_0_c c : mat 0 c := mk_mat_0_c (A0:=A0) c.
Definition mk_mat_1_1 a11 : mat 1 1 := mk_mat_1_1 (A0:=A0) a11.
Definition mk_mat_1_2 a11 a12 : mat 1 2 := mk_mat_1_2 (A0:=A0) a11 a12.
Definition mk_mat_1_3 a11 a12 a13 : mat 1 3 := mk_mat_1_3 (A0:=A0) a11 a12 a13.
Definition mk_mat_1_4 a11 a12 a13 a14 : mat 1 4 := mk_mat_1_4 (A0:=A0) a11 a12 a13 a14.
Definition mk_mat_1_c c (l : list A) : mat 1 c := mk_mat_1_c (A0:=A0) c l.
                         
Definition mk_mat_r_0 r : mat r 0 := mk_mat_r_0 (A0:=A0) r.
Definition mk_mat_2_1 a11 a21 : mat 2 1 := mk_mat_2_1 (A0:=A0) a11 a21.
Definition mk_mat_2_2 a11 a12 a21 a22 : mat 2 2 := mk_mat_2_2 (A0:=A0) a11 a12 a21 a22.
Definition mk_mat_3_1 a11 a12 a13 : mat 3 1 := mk_mat_3_1 (A0:=A0) a11 a12 a13.
Definition mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
  mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
Definition mk_mat_4_1 a11 a21 a31 a41 : mat 4 1 := mk_mat_4_1 (A0:=A0) a11 a21 a31 a41.
Definition mk_mat_4_4 a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44
  : mat 4 4 :=
  mk_mat_4_4 (A0:=A0) a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44.
Definition mk_mat_r_1 r (l : list A) : mat r 1 := mk_mat_r_1 (A0:=A0) r l.


(** *** matrix transposition *)
Definition mtrans {r c : nat} (m : mat r c) : mat c r := mtrans m.
Notation "m \T" := (mtrans m) : mat_scope.

(** show it is a proper morphism *)
Global Instance mtrans_mor : forall r c, Proper (meq ==> meq) (mtrans (r:=r)(c:=c)).
Proof. apply mtrans_mor. Qed.

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
Definition mat0 {r c} : mat r c := @mat0 _ A0 r c.

Lemma mtrans_0 : forall {r c : nat}, (@mat0 r c)\T == mat0.
Proof. intros. apply mtrans_0. Qed.


(** *** unit matrix *)
Definition mat1 {n} : mat n n := @mat1 _ A0 A1 n.

Lemma mtrans_1 : forall {n : nat}, (@mat1 n)\T == mat1.
Proof. intros. apply mtrans_1. Qed.


(** *** Matrix trace *)
Definition mtrace {n : nat} (m : smat n) : A := mtrace m (Aadd:=Aadd)(A0:=A0).
Notation "'tr' m" := (mtrace m) : mat_scope.

(** show it is a proper morphism *)
Global Instance mtrace_mor : forall n, Proper (meq ==> eq) (mtrace (n:=n)).
Proof. apply mtrace_mor. Qed.

(** tr(m\T) = tr(m) *)
Lemma mtrace_trans : forall {n} (m : smat n), tr (m\T) = tr(m).
Proof. intros. apply mtrace_trans. Qed.


(** *** matrix addition *)
Definition madd {r c} (m1 m2 : mat r c) : mat r c := madd m1 m2 (Aadd:=Aadd).
Infix "+" := madd : mat_scope.

(** show it is a proper morphism *)
Global Instance madd_mor : forall r c, Proper (meq ==> meq ==> meq) (madd (r:=r)(c:=c)).
Proof. apply (madd_mor (A0:=A0)). Qed.

Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == m2 + m1.
Proof. intros. apply madd_comm. Qed.

Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
Proof. intros. apply madd_assoc. Qed.

Lemma madd_0_l : forall {r c} (m : mat r c), mat0 + m == m.
Proof. intros. apply madd_0_l. Qed.

Lemma madd_0_r : forall {r c} (m : mat r c), m + mat0 == m.
Proof. intros. apply madd_0_r. Qed.

Lemma mtrans_add : forall {r c} (m1 m2 : mat r c), (m1 + m2)\T == m1\T + m2\T.
Proof. intros. apply mtrans_add. Qed.

Lemma mtrace_add : forall {n} (m1 m2 : smat n), tr (m1 + m2) = (tr(m1) + tr(m2))%R.
Proof. intros. apply mtrace_add. Qed.


(** *** matrix opposition *)
Definition mopp {r c} (m : mat r c) : mat r c := mopp m (Aopp:=Aopp).
Notation "- m" := (mopp m) : mat_scope.

(** show it is a proper morphism *)
Global Instance mopp_mor : forall r c, Proper (meq ==> meq) (mopp (r:=r)(c:=c)).
Proof. apply (mopp_mor (A0:=A0)). Qed.

Lemma mopp_add : forall {r c : nat} (m1 m2 : mat r c), - (m1 + m2) == (-m1) + (-m2).
Proof. intros. apply mopp_add. Qed.

Lemma madd_opp_l : forall {r c} (m : mat r c), (-m) + m == mat0.
Proof. intros. apply madd_opp_l. Qed.

Lemma madd_opp_r : forall {r c} (m : mat r c), m + (-m) == mat0.
Proof. intros. apply madd_opp_r. Qed.

Lemma mopp_opp : forall {r c} (m : mat r c), - - m == m.
Proof. intros. apply mopp_opp. Qed.

Lemma mopp_0 : forall {r c}, - (@mat0 r c) == mat0.
Proof. intros. apply mopp_0. Qed.

Lemma mtrans_opp : forall {r c} (m : mat r c), (- m)\T == - (m\T).
Proof. intros. apply mtrans_opp. Qed.

(** tr(- m) = - (tr(m)) *)
Lemma mtrace_opp : forall {n} (m : smat n), tr (- m) = (- (tr(m)))%R.
Proof. intros. apply mtrace_opp. Qed.


(** *** matrix subtraction *)
Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
  msub m1 m2 (Aadd:=Aadd)(Aopp:=Aopp).
Infix "-" := msub : mat_scope.

(** show it is a proper morphism *)
Global Instance msub_mor : forall r c, Proper (meq ==> meq ==> meq) (msub (r:=r)(c:=c)).
Proof. apply (msub_mor (A0:=A0)). Qed.

Lemma msub_rw : forall {r c} (m1 m2 : mat r c), m1 - m2 == m1 + (-m2).
Proof. intros. apply msub_rw. Qed.

Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
Proof. intros. apply msub_comm. Qed.

Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
Proof. intros. apply msub_assoc. Qed.

Lemma msub_assoc1 : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) - m3 == m1 + (m2 - m3).
Proof. intros. apply msub_assoc1. Qed.

Lemma msub_assoc2 : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == (m1 - m3) - m2.
Proof. intros. apply msub_assoc2. Qed.

Lemma msub_0_l : forall {r c} (m : mat r c), mat0 - m == - m.
Proof. intros. apply msub_0_l. Qed.

Lemma msub_0_r : forall {r c} (m : mat r c), m - mat0 == m.
Proof. intros. apply msub_0_r. Qed.

Lemma msub_self : forall {r c} (m : mat r c), m - m == mat0.
Proof. intros. apply msub_self. Qed.

Lemma mtrans_sub : forall {r c} (m1 m2 : mat r c), (m1 - m2)\T == m1\T - m2\T.
Proof. intros. apply mtrans_sub. Qed.

Lemma mtrace_sub : forall {n} (m1 m2 : smat n), tr (m1 - m2) = (tr(m1) - tr(m2))%R.
Proof. intros. apply mtrace_sub. Qed.


(** *** matrix scalar multiplication *)
Definition mcmul {r c} a (m : mat r c) : mat r c := mcmul a m (Amul:=Amul).
Infix " 'c*' " := mcmul : mat_scope.

(** show it is a proper morphism *)
Global Instance mcmul_mor : forall r c,  Proper (eq ==> meq ==> meq) (@mcmul r c).
Proof. apply mcmul_mor. Qed.

Lemma mcmul_assoc : forall {r c} a b (m : mat r c), a c* (b c* m) == (a * b) c* m.
Proof. intros. apply mcmul_assoc. Qed.

Lemma mcmul_perm : forall {r c} a b (m : mat r c),  a c* (b c* m) == b c* (a c* m).
Proof. intros. apply mcmul_perm. Qed.

Lemma mcmul_add_distr_l : forall {r c} a (m1 m2 : mat r c),
    a c* (m1 + m2) == (a c* m1) + (a c* m2).
Proof. intros. apply mcmul_add_distr_l. Qed.

Lemma mcmul_add_distr_r : forall {r c} a b (m : mat r c),
    (a + b) c* m == (a c* m) + (b c* m).
Proof. intros. apply mcmul_add_distr_r. Qed.

Lemma mcmul_1_l : forall {r c} (m : mat r c), A1 c* m == m.
Proof. intros. apply mcmul_1_l. Qed.

Lemma mcmul_0_l : forall {r c} (m : mat r c), A0 c* m == mat0.
Proof. intros. apply mcmul_0_l. Qed.

Lemma mtrans_cmul : forall {r c} (a : A) (m : mat r c), (a c* m)\T == a c* (m\T).
Proof. intros. apply mtrans_cmul. Qed.

Lemma mtrace_cmul : forall {n} (a : A) (m : smat n), tr (a c* m) = a * tr (m).
Proof. intros. apply mtrace_cmul. Qed.

(** Right scalar multiplication of matrix *)
Definition mmulc {r c} (m : mat r c) (a : A) : mat r c := mmulc m a (Amul:=Amul).
Infix "*c" := mmulc : mat_scope.

Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
Proof. intros. apply mmulc_eq_mcmul. Qed.

Global Instance mmulc_mor : forall r c, Proper (meq ==> eq ==> meq) (mmulc (r:=r)(c:=c)).
Proof. apply mmulc_mor. Qed.


(** *** matrix multiplication *)
Definition mmul {r c s} (m1 : mat r c) (m2 : mat c s) : mat r s :=
  mmul m1 m2 (Aadd:=Aadd) (A0:=A0) (Amul:=Amul).
Infix "*" := mmul : mat_scope.

(** show it is a proper morphism *)
Global Instance mmul_mor : forall r c s,
    Proper (meq ==> meq ==> meq) (mmul (r:=r)(c:=c)(s:=s)).
Proof. apply mmul_mor. Qed.

Lemma mmul_assoc : forall {r c s t} (m1 : mat r c) (m2 : mat c s) (m3 : mat s t),
    (m1 * m2) * m3 == m1 * (m2 * m3).
Proof. intros. apply mmul_assoc. Qed.

Lemma mmul_add_distr_l : forall {r c s} (m1 : mat r c) (m2 m3 : mat c s),
    m1 * (m2 + m3) == (m1 * m2) + (m1 * m3).
Proof. intros. apply mmul_add_distr_l. Qed.

Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s),
    (m1 + m2) * m3 == (m1 * m3) + (m2 * m3).
Proof. intros. apply mmul_add_distr_r. Qed.

Lemma mmul_sub_distr_l : forall {r c s : nat} (m1 : mat r c) (m2 m3 : mat c s), 
    m1 * (m2 - m3) == m1 * m2 - m1 * m3.
Proof. intros. apply mmul_sub_distr_l. Qed.

Lemma mmul_sub_distr_r : forall {r c s : nat} (m1 m2 : mat r c) (m3 : mat c s),
    (m1 - m2) * m3 == m1 * m3 - m2 * m3.
Proof. intros. apply mmul_sub_distr_r. Qed.

(** - (m1 * m2) = (-m1) * m2 *)
Lemma mopp_mul_l : forall {r c s : nat} (m1 : mat r c) (m2 : mat c s),
    - (m1 * m2) == (-m1) * m2.
Proof. intros. apply mopp_mul_l. Qed.

(** - (m1 * m2) = m1 * (-m2) *)
Lemma mopp_mul_r : forall {r c s : nat} (m1 : mat r c) (m2 : mat c s),
    - (m1 * m2) == m1 * (-m2).
Proof. intros. apply mopp_mul_r. Qed.

Lemma mmul_0_l : forall {r c s} (m : mat c s), (@mat0 r c) * m == mat0.
Proof. intros. apply mmul_0_l. Qed.

Lemma mmul_0_r : forall {r c s} (m : mat r c), m * (@mat0 c s) == mat0.
Proof. intros. apply mmul_0_r. Qed.

Lemma mmul_1_l : forall {r c} (m : mat r c), mat1 * m == m.
Proof. intros. apply mmul_1_l. Qed.

Lemma mmul_1_r : forall {r c} (m : mat r c), m * mat1 == m. 
Proof. intros. apply mmul_1_r. Qed.

Lemma mtrans_mul : forall {r c s} (m1 : mat r c) (m2 : mat c s), (m1 * m2)\T == m2\T * m1\T.
Proof. intros. apply mtrans_mul. Qed.

(** tr (m1 * m2) = tr (m2 * m1) *)
Lemma mtrace_mul : forall {r c} (m1 : mat r c) (m2 : mat c r), tr (m1 * m2) = tr (m2 * m1).
Proof. intros. apply mtrace_mul. Qed.

(** inverse matrix by gauss elimination *)
Definition minv_gauss {n} (m : mat n n) : option (mat n n) :=
  @minv_gauss A Aadd A0 Aopp Amul A1 Ainv _ _ m.



(* ======================================================================= *)
(** ** Matrix theory applied to this type *)


(* ======================================================================= *)
(** ** Usage demo *)

Section test.
  Let l1 := [[1;2];[3;4]].
  Let m1 := l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Ropp m1). *)
  (* Compute m2l (m1 * m1). *)

  Variable a11 a12 a21 a22 : R.
  Variable f : R -> R.
  Let m2 := l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.       (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  (* Compute m2l (m2 * m2). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

  (** Outer/inner product of two vectors *)
  Variables a1 a2 a3 b1 b2 b3 : A.
  Let m10 := l2m 3 1 [[a1];[a2];[a3]].
  Let m11 := l2m 1 3 [[b1;b2;b3]].
  (* Compute m2l (m10 * m11). *)
  (* Compute m2l (m11 * m10). *)

  (** mmul_sub_distr_r *)
  Goal forall r c s (m1 m2 : mat r c) (m3 : mat c s), (m1 - m2) * m3 == m1 * m3 - m2 * m3.
    intros. rewrite mmul_sub_distr_r. easy. Qed.

  (* test rewriting *)
  Goal forall r c (m1 m2 : mat r c) x, m1 == m2 -> x c* m1 == x c* m2.
  Proof. intros. f_equiv. easy. Qed.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 == m2 -> m3 == m4 -> m1 - m3 == m2 - m4.
  Proof. clear. intros. f_equiv. easy. easy. Qed.

End test.

Section test_monoid.
  Goal forall r c (m1 m2 : mat r c), mat0 + m1 == m1.
    ASS.monoid_simp. Qed.
End test_monoid.


Section Example4CoordinateSystem.
  Variable ψ θ φ: R.
  Let Rx := mk_mat_3_3 1 0 0 0 (cos φ) (sin φ) 0 (-sin φ) (cos φ).
  Let Ry := mk_mat_3_3 (cos θ) 0 (-sin θ) 0 1 0 (sin θ) 0 (cos θ).
  Let Rz := mk_mat_3_3 (cos ψ) (sin ψ) 0 (-sin ψ) (cos ψ) 0 0 0 1.
  Let Rbe := mk_mat_3_3
    (cos θ * cos ψ) (cos ψ * sin θ * sin φ - sin ψ * cos φ)
    (cos ψ * sin θ * cos φ + sin φ * sin ψ) (cos θ * sin ψ)
    (sin ψ * sin θ * sin φ + cos ψ * cos φ)
    (sin ψ * sin θ * cos φ - cos ψ * sin φ)
    (-sin θ) (sin φ * cos θ) (cos φ * cos θ).
  Lemma Rbe_ok : (Rbe == Rz\T * Ry\T * Rx\T).
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
  
  (* Example ex6_1 : forall a b : R, *)
  (*     let m := (mk_mat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1)%R in *)
  (*     (det m == (a - b)^3)%A. *)
  (* Proof. *)
  (*   intros. cbv. ring. *)
  (* Qed. *)
  
  (* Example ex6_2 : forall a b x y z : A, *)
  (*     let m1 := (mk_mat_3_3 *)
  (*                  (a*x+b*y) (a*y+b*z) (a*z+b*x) *)
  (*                  (a*y+b*z) (a*z+b*x) (a*x+b*y) *)
  (*                  (a*z+b*x) (a*x+b*y) (a*y+b*z))%A in *)
  (*     let m2 := mk_mat_3_3 x y z y z x z x y in *)
  (*     (det m1 == (a^3 + b^3) * det m2)%A. *)
  (* Proof. *)
  (*   intros. cbv. ring. *)
  (* Qed. *)
  
  (* Example ex6_3 : forall a b e d : A, *)
  (*     let m := (mk_mat_4_4 *)
  (*                 (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2) *)
  (*                 (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2) *)
  (*                 (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2) *)
  (*                 (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2))%A in *)
  (*     (det m == 0)%A. *)
  (* Proof. *)
  (*   intros. cbv. ring. *)
  (* Qed. *)
  
  (* Example ex6_4 : forall a b e d : A, *)
  (*     let m := (mk_mat_4_4 *)
  (*                 1 1 1 1 *)
  (*                 a b e d *)
  (*                 (a^2) (b^2) (e^2) (d^2) *)
  (*                 (a^4) (b^4) (e^4) (d^4))%A in *)
  (*     (det m == (a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%A. *)
  (* Proof. *)
  (*   intros. cbv. ring. *)
  (* Qed. *)
  
  (* (** 6.(5), it is an infinite structure, need more work, later... *) *)

End Exercise_Ch1_Symbol.
