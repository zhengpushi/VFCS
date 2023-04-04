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
Notation dlistA := (dlist R).

(** *** matrix type and basic operation *)
Definition mat (r c : nat) : Type := @mat R r c.
Notation smat n := (smat R n).

Notation "m ! i ! j " := (mnth 0 m i j) : mat_scope.

Lemma meq_iff_mnth : forall {r c} (m1 m2 : mat r c),
    m1 == m2 <-> (forall i j : nat, i < r -> j < c -> m1!i!j = m2!i!j)%nat.
Proof. apply meq_iff_mnth. Qed.

(** *** convert between list and matrix *)
Definition l2m (r c : nat) (dl : dlistA) : mat r c := l2m 0 dl.
Definition m2l {r c : nat} (m : mat r c) : dlistA := m2l m.

Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
Proof. intros. apply m2l_length. Qed.

Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
Proof. intros. apply m2l_width. Qed.

Lemma m2l_l2m_id : forall {r c} (dl : dlistA),
    length dl = r -> width dl c -> m2l (l2m r c dl) = dl.
Proof. intros. apply m2l_l2m_id; auto. Qed.

Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m r c (m2l m) == m.
Proof. intros. apply l2m_m2l_id; auto. Qed.

Lemma l2m_inj : forall {r c} (d1 d2 : dlistA),
    length d1 = r -> width d1 c -> length d2 = r -> width d2 c -> 
    d1 <> d2 -> ~(l2m r c d1 == l2m r c d2).
Proof. intros. apply l2m_inj; auto. Qed.

Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m r c d == m). 
Proof. intros. apply l2m_surj; auto. Qed.

Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~ (m1 == m2) -> m2l m1 <> m2l m2.
Proof. intros. apply (m2l_inj 0); auto. Qed.

Lemma m2l_surj : forall {r c} (d : dlistA), length d = r -> width d c -> 
    (exists m : mat r c, m2l m = d).
Proof. intros. apply (m2l_surj 0); auto. Qed.

(** *** convert between tuple and matrix *)
Definition t2m_3_3 (t : T_3_3) : mat 3 3 := t2m_3_3 0 t.
Definition m2t_3_3 (m : mat 3 3) : T_3_3 := m2t_3_3 m.
Definition m2t_1_1 (m : mat 1 1) := m2t_1_1 m.

(** *** construct matrix with vector and matrix *)

(** construct a matrix with a row vector and a matrix *)
Definition mconsr {r c} (v : mat 1 c) (m : mat r c) : mat (S r) c := mconsr v m.
(** construct a matrix with a column vector and a matrix *)
Definition mconsc {r c} (v : mat r 1) (m : mat r c) : mat r (S c) := mconsc v m.

(** *** build matrix from elements *)
Definition mk_mat_1_1 a11 : mat 1 1 :=
  mk_mat_1_1 (A0:=0) a11.
Definition mk_mat_3_1 a11 a12 a13 : mat 3 1 :=
  mk_mat_3_1 (A0:=0) a11 a12 a13.
Definition mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
  mk_mat_3_3 (A0:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

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
Definition mat0 {r c} : mat r c := mat0 0 r c.

(** *** unit matrix *)
Definition matI {n} : mat n n := matI 0 1 n.

(** *** matrix addition *)
Definition madd {r c} (m1 m2 : mat r c) : mat r c := madd m1 m2 (Aadd:=Rplus).
Infix "+" := madd : mat_scope.

Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == m2 + m1.
Proof. intros. apply madd_comm. Qed.

Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
Proof. intros. apply madd_assoc. Qed.

Lemma madd_0_l : forall {r c} (m : mat r c), mat0 + m == m.
Proof. intros. apply madd_0_l. Qed.

(** *** matrix opposition *)
Definition mopp {r c} (m : mat r c) : mat r c := mopp m (Aopp:=Ropp).
Notation "- m" := (mopp m) : mat_scope.

Lemma madd_opp_l : forall {r c} (m : mat r c), (-m) + m == mat0.
Proof. intros. apply madd_opp_l. Qed.

Lemma madd_opp_r : forall {r c} (m : mat r c), m + (-m) == mat0.
Proof. intros. apply madd_opp_r. Qed.

Lemma mopp_opp : forall {r c} (m : mat r c), - - m == m.
Proof. intros. apply mopp_opp. Qed.

(** *** matrix subtraction *)
Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
  msub m1 m2 (Aadd:=Rplus)(Aopp:=Ropp).
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
Definition mcmul {r c} a (m : mat r c) : mat r c := mcmul a m (Amul:=Rmult).
Infix " 'c*' " := mcmul : mat_scope.

Global Instance mcmul_mor : forall r c,  Proper (eq ==> meq ==> meq) (@mcmul r c).
Proof. intros. apply (mcmul_mor (A0:=0)). Qed.

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

Lemma mcmul_1_l : forall {r c} (m : mat r c), 1 c* m == m.
Proof. intros. apply mcmul_1_l. Qed.

Lemma mcmul_0_l : forall {r c} (m : mat r c), 0 c* m == mat0.
Proof. intros. apply mcmul_0_l. Qed.

(** *** matrix multiplication *)
Definition mmul {r c s} (m1 : mat r c) (m2 : mat c s) : mat r s :=
  mmul m1 m2 (Aadd:=Rplus) (A0:=0) (Amul:=Rmult).
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

Lemma mmul_I_l : forall {r c} (m : mat r c), matI * m == m.
Proof. intros. apply mmul_I_l. Qed.

Lemma mmul_I_r : forall {r c} (m : mat r c), m * matI == m. 
Proof. intros. apply mmul_I_r. Qed.


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

End test.

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
