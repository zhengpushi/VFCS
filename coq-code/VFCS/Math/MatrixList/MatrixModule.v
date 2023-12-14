(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix module
  author    : ZhengPu Shi
  date      : 2023.04

  remark    :
  1. use functor to generate many similiar modules, and help the type inference
     at specify domain, so that simplify the coding.
  2. The matrix theory is orgainized at several levels
  (1) BasicMatrixTheory
      matrix theory on element with equivalence relaton.
  (2) RingMatrixTheory
      matrix theory on element with ring structure.
  (3) FieldMatrixTheory
      matrix theory on element with field structure.
  (4) DecFieldTheory
      matrix theory on element with decidable field structure.

 *)


Require Export MatrixList.Matrix.
Require Export MatrixList.MatrixDet.
Require Export MatrixList.MatrixInv.
Require Export MatrixList.ElementType.


(* ######################################################################### *)
(** * Basic matrix theory *)

Module BasicMatrixTheory (E : ElementType).

  (* ==================================== *)
  (** ** Matrix element type *)
  Export E.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.
  

  (* ==================================== *)
  (** ** Matrix type and basic operations *)
  Definition mat r c : Type := @mat A r c.

  (** square matrix type *)
  Definition smat n := mat n n.

  (** Vector type *)
  Definition rvec n := mat 1 n.
  Definition cvec n := mat n 1.

  (** Convert between function and matrix *)
  Definition f2m {r c} (f : nat -> nat -> A) : mat r c := f2m f.
  Definition m2f {r c} (M : mat r c) : nat -> nat -> A := m2f Azero M.

  (** Get element of a matrix (nth means n-th) *)
  Definition mnth {r c} (M : mat r c) (i j : nat) : A := mnth Azero M i j.
  Notation "M $ i $ j " := (mnth M i j) : mat_scope.

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

  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (M1 M2 : mat r c),
      M1 = M2 <-> (forall ri ci, ri < r -> ci < c -> mnth M1 ri ci = mnth M2 ri ci).
  Proof. intros. apply meq_iff_mnth. Qed.


  (* ==================================== *)
  (** ** Convert between list list and matrix *)

  (** dlist to matrix with specified row and column numbers *)
  Definition l2m {r c} (dl : dlist A) : mat r c := l2m Azero r c dl.
  
  (** mat to dlist *)
  Definition m2l {r c} (M : mat r c) : dlist A := m2l M.

  Lemma m2l_length : forall {r c} (M : mat r c), length (m2l M) = r.
  Proof. intros. apply m2l_length. Qed.
  
  Lemma m2l_width : forall {r c} (M : mat r c), width (m2l M) c.
  Proof. intros. apply m2l_width. Qed.

  Lemma l2m_m2l_id : forall {r c} (M : mat r c), @l2m r c (m2l M) = M.
  Proof. intros. apply l2m_m2l_id. Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : dlist A),
      length dl = r -> width dl c -> m2l (@l2m r c dl) = dl.
  Proof. intros. apply m2l_l2m_id; auto. Qed.

  Lemma l2m_inj : forall {r c} (d1 d2 : dlist A),
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      d1 <> d2 -> @l2m r c d1 <> l2m d2.
  Proof. intros. apply l2m_inj; auto. Qed.
  
  Lemma l2m_surj : forall {r c} (M : mat r c), (exists d, l2m d = M).
  Proof. intros. apply l2m_surj. Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), m1 <> m2 -> m2l m1 <> m2l m2.
  Proof. intros. apply m2l_inj; auto. Qed.
  
  Lemma m2l_surj : forall {r c} (d : dlist A),
      length d = r -> width d c -> (exists M : mat r c, m2l M = d).
  Proof. intros. apply m2l_surj; auto. Qed.

  
  (* ==================================== *)
  (** ** Construct matrix with one-row or one-column matrix and another matrix *)

  (** Construct a matrix by rows, i.e., a row vector and a matrix *)
  Definition mconsr {r c} (V : rvec c) (M : mat r c) : mat (S r) c := mconsr V M.

  (** Construct a matrix by columns, i.e., a column vector and a matrix *)
  Definition mconsc {r c} (V : cvec r) (M : mat r c) : mat r (S c) := mconsc Azero V M.
  
  (** Construct a matrix by rows with the matrix which row number is 0 *)
  Lemma mconsr_mr0 : forall {n} (V : rvec n) (M : mat 0 n), mconsr V M = V.
  Proof. intros. apply mconsr_mr0. Qed.
  
  (** Construct a matrix by columns with the matrix which column number is 0 *)
  Lemma mconsc_mc0 : forall {n} (V : cvec n) (M : mat n 0), mconsc V M = V.
  Proof. intros. apply mconsc_mc0. Qed.

  
  (* ==================================== *)
  (** ** Construct matrix with two matrices *)
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (M1 : mat r1 c) (M2 : mat r2 c) : mat (r1 + r2) c :=
    mappr M1 M2.
  
  (** Append matrix by column *)
  Definition mappc {r c1 c2} (M1 : mat r c1) (M2 : mat r c2) : mat r (c1 + c2) :=
    mappc M1 M2.

  
  (* ==================================== *)
  (** ** Make concrete matrix *)

  Definition mk_mat_0_c c : mat 0 c :=
    mk_mat_0_c c.
  Definition mk_mat_1_1 (a11 : A) : mat 1 1 :=
    mk_mat_1_1 a11.
  Definition mk_mat_1_2 (a11 a12 : A) : mat 1 2 :=
    mk_mat_1_2 a11 a12.
  Definition mk_mat_1_3 (a11 a12 a13 : A) : mat 1 3 :=
    mk_mat_1_3 a11 a12 a13.
  Definition mk_mat_1_4 (a11 a12 a13 a14 : A) : mat 1 4 :=
    mk_mat_1_4 a11 a12 a13 a14.
  Definition mk_mat_1_c (l : list A) : mat 1 (length l) :=
    mk_mat_1_c l.
  
  Definition mk_mat_r_0 r : mat r 0 :=
    mk_mat_r_0 r.
  Definition mk_mat_2_1 (a11 a21 : A) : mat 2 1 :=
    mk_mat_2_1 a11 a21.
  Definition mk_mat_3_1 (a11 a21 a31 : A) : mat 3 1 :=
    mk_mat_3_1 a11 a21 a31.
  Definition mk_mat_4_1 (a11 a21 a31 a41 : A) : mat 4 1 :=
    mk_mat_4_1 a11 a21 a31 a41.
  Definition mk_mat_r_1 (l : list A) : mat (length l) 1 :=
    mk_mat_r_1 l.

  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2 :=
    mk_mat_2_2 a11 a12 a21 a22.
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 :=
    mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
  Definition mk_mat_4_4 (a11 a12 a13 a14 a21 a22 a23 a24
                           a31 a32 a33 a34 a41 a42 a43 a44 : A) : mat 4 4 :=
    mk_mat_4_4
      a11 a12 a13 a14
      a21 a22 a23 a24
      a31 a32 a33 a34
      a41 a42 a43 a44.

  
  (* ==================================== *)
  (** ** Mapping of matrix *)

  Definition mmap {r c} (f : A -> A) (M : mat r c) : mat r c := mmap f M.
  
  Definition mmap2 {r c} (f : A -> A -> A) (M1 M2 : mat r c) : mat r c :=
    mmap2 f M1 M2.

  Lemma mmap2_comm : forall {r c} (f : A -> A -> A) (M1 M2 : mat r c)
                       {Comm : Commutative f}, 
      mmap2 f M1 M2 = mmap2 f M2 M1.
  Proof. intros. apply mmap2_comm; auto. Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A) (M1 M2 M3 : mat r c)
                        {Assoc : Associative f}, 
      mmap2 f (mmap2 f M1 M2) M3 = mmap2 f M1 (mmap2 f M2 M3).
  Proof. intros. apply mmap2_assoc; auto. Qed.

  
  (* ==================================== *)
  (** ** Diagonal Matrix *)
  
  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (m : smat n) : Prop := mdiag Azero m.

  (** Construct a diagonal matrix *)
  Definition mdiagMk n (l : list A) : smat n := mdiagMk Azero n l.

  (** mdiagMk is correct *)
  Lemma mdiagMk_spec : forall {n} (l : list A), mdiag (@mdiagMk n l).
  Proof. intros. apply mdiagMk_spec. Qed.

  (** (mdiagMk l)[i,j] = 0 *)
  Lemma mdiagMk_ij : forall {n} (l : list A) i j,
      i < n -> j < n -> i <> j -> (mdiagMk n l)$i$j = Azero.
  Proof. intros. apply mdiagMk_ij; auto. Qed.

  (** (mdiagMk l)[i,i] = l[i] *)
  Lemma mdiagMk_ii : forall {n} (l : list A) i,
      i < n -> (mdiagMk n l)$i$i = nth i l Azero.
  Proof. intros. apply mdiagMk_ii; auto. Qed.
  
  
  (* ==================================== *)
  (** ** Matrix transposition *)

  Definition mtrans {r c} (M : mat r c): mat c r := mtrans M.
  Notation "M \T" := (mtrans M) : mat_scope.

  (** Transpose twice keep unchanged. *)
  Lemma mtrans_mtrans : forall {r c} (M : mat r c), M \T \T = M.
  Proof. intros. apply mtrans_trans. Qed.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (M : smat n), mdiag M -> M\T = M.
  Proof. intros. apply (mtrans_diag Azero); auto. Qed.

End BasicMatrixTheory.


(* ######################################################################### *)
(** * Ring matrix theory *)
Module RingMatrixTheory (E : RingElementType).
  Include (BasicMatrixTheory E).

  (* ==================================== *)
  (** ** Zero matrirx and identity matrix *)

  (** Zero matrix *)
  Definition mat0 {r c : nat} : mat r c := mat0 (Azero:=Azero).

  (** Identity matrix *)
  Definition mat1 {n : nat} : mat n n := mat1 (Azero:=Azero) (Aone:=Aone).

  (** mat1 is diagonal matrix *)
  Lemma mat1_diag : forall {n : nat}, mdiag (@mat1 n).
  Proof. intros. apply mat1_diag. Qed.
  
  (** mat0\T = mat0 *)
  Lemma mtrans_0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. apply mtrans_0. Qed.
  
  (** mat1\T = mat1 *)
  Lemma mtrans_1 : forall {n : nat}, (@mat1 n)\T = mat1.
  Proof. intros. apply mtrans_1. Qed.

  (** i < n -> j < n -> i <> j -> mat1[i,j] = 0 *)
  Lemma mat1_ij : forall {n} i j,
      i < n -> j < n -> i <> j -> ((@mat1 n) $ i $ j = Azero)%A.
  Proof. intros. apply mat1_ij; auto. Qed.

  (** i < n -> mat1[i,i] = 1 *)
  Lemma mat1_ii : forall {n} i, i < n -> ((@mat1 n) $ i $ i = Aone)%A.
  Proof. intros. apply mat1_ii; auto. Qed.


  (* ==================================== *)
  (** ** Matrix trace *)
  Definition mtrace {n : nat} (M : smat n) : A :=
    mtrace M (Aadd:=Aadd) (Azero:=Azero).
  Notation "'tr' M" := (mtrace M) : mat_scope.

  (** tr(m\T) = tr(m) *)
  Lemma mtrace_trans : forall {n} (m : smat n), (tr (m\T) = tr(m))%A.
  Proof. intros. apply mtrace_trans. Qed.


  (* ==================================== *)
  (** ** Matrix addition *)
  
  Definition madd {r c} (M1 M2 : mat r c) : mat r c := madd M1 M2 (Aadd:=Aadd).
  Infix "+" := madd : mat_scope.

  (** M1 + M2 = M2 + M1 *)
  Lemma madd_comm : forall {r c} (M1 M2 : mat r c), M1 + M2 = (M2 + M1).
  Proof. intros. apply madd_comm. Qed.

  (** (M1 + M2) + M3 = M1 + (M2 + M3) *)
  Lemma madd_assoc : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) + M3 = M1 + (M2 + M3).
  Proof. intros. apply madd_assoc. Qed.

  (** (M1 + M2) + M3 = (M1 + M3) + M2 *)
  Lemma madd_perm : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) + M3 = (M1 + M3) + M2.
  Proof. intros. apply madd_perm. Qed.

  (** mat0 + M = M *)
  Lemma madd_0_l : forall {r c} (M : mat r c), mat0 + M = M. 
  Proof. intros. apply madd_0_l. Qed.

  (** M + mat0 = M *)
  Lemma madd_0_r : forall {r c} (M : mat r c), M + mat0 = M. 
  Proof. intros. apply madd_0_r. Qed.
  
  (** Get element of addition with two matrics equal to additon of corresponded 
      elements. *)
  Lemma mnth_madd : forall {r c} (M1 M2 : mat r c) i j,
      (M1 + M2)%M $ i $ j = (M1$i$j + M2$i$j)%A.
  Proof. intros. apply mnth_madd. Qed.

  (** (M1 + M2)\T = M1\T + M2\T *)
  Lemma mtrans_madd : forall {r c} (M1 M2 : mat r c), (M1 + M2)\T = M1\T + M2\T.
  Proof. intros. apply mtrans_madd. Qed.

  (** tr(M1 + M2) = tr(M1) + tr(M2) *)
  Lemma mtrace_madd : forall {n} (M1 M2 : smat n), (tr (M1 + M2)%M = tr(M1) + tr(M2))%A.
  Proof. intros. apply mtrace_madd. Qed.

  
  (* ==================================== *)
  (** ** Monoid structure over {madd,mat0,meq} *)
  Global Instance Monoid_madd : forall r c, Monoid (@madd r c) mat0.
  Proof. apply Monoid_madd. Qed.

  Section test.
    Goal forall r c (M1 M2 : mat r c), mat0 + M1 = M1.
      monoid_simpl. Qed.
  End test.

  
  (* ==================================== *)
  (** ** Matrix opposition *)
  
  Definition mopp {r c} (M : mat r c) : mat r c := mopp M (Aopp:=Aopp).
  Notation "- a" := (mopp a) : mat_scope.

  (** - (m1 + m2) = (-m1) + (-m2) *)
  Lemma mopp_madd : forall {r c : nat} (M1 M2 : mat r c), - (M1 + M2) = (-M1) + (-M2).
  Proof. intros. apply mopp_madd. Qed.

  (** (-m) + m = mat0 *)
  Lemma madd_mopp_l : forall r c (M : mat r c), (-M) + M = mat0.
  Proof. intros. apply madd_opp_l. Qed.

  (** m + (-m) = mat0 *)
  Lemma madd_mopp_r : forall r c (M : mat r c), M + (-M) = mat0.
  Proof. intros. apply madd_opp_r. Qed.

  (** - (- M) = m *)
  Lemma mopp_mopp : forall {r c} (M : mat r c), - (- M) = M.
  Proof. intros. apply mopp_mopp. Qed.

  (** - mat0 = mat0 *)
  Lemma mopp_0 : forall {r c}, - (@mat0 r c) = mat0.
  Proof. intros. apply mopp_mat0. Qed.

  (** (- M)\T = - (M\T) *)
  Lemma mtrans_mopp : forall {r c} (M : mat r c), (- M)\T = - (M\T).
  Proof. intros. apply mtrans_mopp. Qed.

  (** tr(- M) = - (tr(m)) *)
  Lemma mtrace_mopp : forall {n} (M : smat n), mtrace (-M) = (- (mtrace M))%A.
  Proof. intros. apply mtrace_mopp. Qed.

  
  (* ==================================== *)
  (** ** Matrix subtraction *)
  
  Definition msub {r c} (M1 M2 : mat r c) : mat r c :=
    msub M1 M2 (Aadd:=Aadd)(Aopp:=Aopp).
  Infix "-" := msub : mat_scope.

  (** M1 - M2 = M1 + (-M2) *)
  Lemma msub_rw : forall {r c} (M1 M2 : mat r c), M1 - M2 = M1 + (-M2).
  Proof. intros. reflexivity. Qed.

  (** M1 - M2 = -(M2 - M1) *)
  Lemma msub_comm : forall {r c} (M1 M2 : mat r c), M1 - M2 = - (M2 - M1).
  Proof. intros. apply msub_comm. Qed.

  (** (M1 - M2) - M3 = M1 - (M2 + M3) *)
  Lemma msub_assoc : forall {r c} (M1 M2 M3 : mat r c), (M1 - M2) - M3 = M1 - (M2 + M3).
  Proof. intros. apply msub_assoc. Qed.

  (** (M1 + M2) - M3 = M1 + (M2 - M3) *)
  Lemma msub_assoc1 : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) - M3 = M1 + (M2 - M3).
  Proof. intros. apply msub_assoc1. Qed.

  (** (M1 - M2) - M3 = M1 - (M3 - M2) *)
  Lemma msub_assoc2 : forall {r c} (M1 M2 M3 : mat r c), (M1 - M2) - M3 = (M1 - M3) - M2.
  Proof. intros. apply msub_assoc2. Qed.

  (** mat0 - M = - M *)
  Lemma msub_0_l : forall {r c} (M : mat r c), mat0 - M = - M.
  Proof. intros. apply msub_0_l. Qed.

  (** M - mat0 = M *)
  Lemma msub_0_r : forall {r c} (M : mat r c), M - mat0 = M.
  Proof. intros. apply msub_0_r. Qed.

  (** M - M = mat0 *)
  Lemma msub_self : forall {r c} (M : mat r c), M - M = mat0.
  Proof. intros. apply msub_self. Qed.

  (** (M1 - M2)\T = M1\T - M2\T *)
  Lemma mtrans_msub : forall {r c} (M1 M2 : mat r c), (M1 - M2)\T = M1\T - M2\T.
  Proof. intros. apply mtrans_msub. Qed.

  (** tr(M1 - M2) = tr(M1) - tr(M2) *)
  Lemma mtrace_msub : forall {n} (M1 M2 : smat n),
      (tr ((M1 - M2)%M) = tr(M1) - tr(M2))%A.
  Proof. intros. apply mtrace_msub. Qed.

  
  (* ==================================== *)
  (** ** Abelian group structure over {madd,mat0,mopp} *)
  Global Instance AGroup_MatAdd : forall r c, AGroup (@madd r c) mat0 mopp.
  Proof. apply AGroup_madd. Qed.

  Section test.
    Goal forall r c (M1 M2 : mat r c), mat0 + M1 + (-M2) + M2 = M1.
      intros.
      (* rewrite identityLeft. *)
      (* rewrite associative. *)
      (* rewrite inverseLeft. *)
      group_simp.
    Qed.
  End test.


  (* ==================================== *)
  (** ** Scalar multiplication of matrix *)

  (** Left scalar multiplication of matrix *)
  Definition mcmul {r c} (a : A) (M : mat r c) : mat r c := mcmul a M (Amul:=Amul).
  Infix "c*" := mcmul : mat_scope.

  (** 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (M : mat r c), Azero c* M = mat0.
  Proof. intros. apply mcmul_0_l. Qed.

  (** a c* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a c* (@mat0 r c) = mat0.
  Proof. intros. apply mcmul_0_r. Qed.

  (** 1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (M : mat r c), Aone c* M = M.
  Proof. intros. apply mcmul_1_l. Qed.

  (** a c* mat1 = mdiag([a,a,...]) *)
  Lemma mcmul_1_r : forall {n} a, a c* (@mat1 n) = mdiagMk n (repeat a n). 
  Proof. intros. apply mcmul_1_r. Qed.

  (** a c* (b c* M) = (a * b) c* m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (M : mat r c), a c* (b c* M) = (a * b) c* M.
  Proof. intros. apply mcmul_assoc. Qed.

  (** a c* (b c* M) = b c* (a c* M) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (M : mat r c), a c* (b c* M) = b c* (a c* M).
  Proof. intros. apply mcmul_perm. Qed.

  (** (a + b) c* M = (a c* M) + (b c* M) *)
  Lemma mcmul_add_distr : forall {r c} (a b : A) (M : mat r c), 
      (a + b)%A c* M = (a c* M) + (b c* M).
  Proof. intros. apply mcmul_add_distr. Qed.

  (** a c* (M1 + M2) = (a c* M1) + (a c* M2) *)
  Lemma mcmul_madd_distr : forall {r c} (a : A) (M1 M2 : mat r c), 
      a c* (M1 + M2) = (a c* M1) + (a c* M2).
  Proof. intros. apply mcmul_madd_distr. Qed.
  
  (** (-a) c* M  = - (a c* M) *)
  Lemma mcmul_opp : forall {r c} a (M : mat r c), (-a)%A c* M = - (a c* M).
  Proof. intros. apply mcmul_opp. Qed.
  
  (** a c* (-M)  = - (a c* M) *)
  Lemma mcmul_mopp : forall {r c} a (M : mat r c), a c* (-M) = - (a c* M).
  Proof. intros. apply mcmul_mopp. Qed.

  (** a c* (m1 - m2) = (a c* m1) - (a c* m2) *)
  Lemma mcmul_msub : forall {r c} a (M1 M2 : mat r c),
      a c* (M1 - M2) = (a c* M1) - (a c* M2).
  Proof. intros. apply mcmul_msub. Qed.

  (** (a c* M)\T = a c* (m\T) *)
  Lemma mtrans_mcmul : forall {r c} (a : A) (M : mat r c), (a c* M)\T = a c* (M\T).
  Proof. intros. apply (mtrans_mcmul (Azero:=Azero)). Qed.

  (** tr (a c* M) = a * tr (m) *)
  Lemma mtrace_mcmul : forall {n} (a : A) (M : smat n), (tr (a c* M) = a * tr (M))%A.
  Proof. intros. apply mtrace_mcmul. Qed.

  
  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (M : mat r c) (a : A) : mat r c := mmulc M a (Amul:=Amul).
  Infix "*c" := mmulc : mat_scope.

  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (M : mat r c), M *c a = a c* M.
  Proof. intros. apply mmulc_eq_mcmul. Qed.

    (** (m *c a) *c b = m *c (a * b) *)
  Lemma mmulc_assoc : forall {r c} (M : mat r c) (a b : A), (M *c a) *c b = M *c (a * b).
  Proof. intros. rewrite !mmulc_eq_mcmul, mcmul_perm, mcmul_assoc. auto. Qed.

  (** (m *c a) *c b = (m *c b) c* a *)
  Lemma mmulc_perm : forall {r c} (M : mat r c) (a b : A), (M *c a) *c b = (M *c b) *c a.
  Proof. intros. rewrite !mmulc_eq_mcmul, mcmul_perm. auto. Qed.

  
  (* ==================================== *)
  (** ** Matrix multiplication *)
  Definition mmul {r c s : nat} (M1 : mat r c) (M2 : mat c s) : mat r s :=
    mmul M1 M2 (Amul:=Amul)(Azero:=Azero)(Aadd:=Aadd).
  Infix "*" := mmul : mat_scope.

  (** (M1 * M2) * M3 = M1 * (M2 * M3) *)
  Lemma mmul_assoc : forall {r c s t : nat} (M1 : mat r c) (M2 : mat c s) (M3 : mat s t), 
      (M1 * M2) * M3 = M1 * (M2 * M3).
  Proof. intros. apply mmul_assoc. Qed.

  (** M1 * (M2 + M3) = M1 * M2 + M1 * M3 *)
  Lemma mmul_madd_distr_l : forall {r c s : nat} (M1 : mat r c) (M2 M3 : mat c s), 
      M1 * (M2 + M3) = M1 * M2 + M1 * M3.
  Proof. intros. apply mmul_madd_distr_l. Qed.
  
  (** (M1 + M2) * M3 = M1 * M3 + M2 * M3 *)
  Lemma mmul_madd_distr_r : forall {r c s : nat} (M1 M2 : mat r c) (M3 : mat c s),
      (M1 + M2) * M3 = M1 * M3 + M2 * M3.
  Proof. intros. apply mmul_madd_distr_r. Qed.

  (** M1 * (M2 - M3) = M1 * M2 - M1 * M3 *)
  Lemma mmul_msub_distr_l : forall {r c s : nat} (M1 : mat r c) (M2 M3 : mat c s), 
      M1 * (M2 - M3) = M1 * M2 - M1 * M3.
  Proof. intros. apply mmul_msub_distr_l. Qed.
  
  (** (M1 - M2) * M3 = M1 * M3 - M2 * M3 *)
  Lemma mmul_msub_distr_r : forall {r c s : nat} (M1 M2 : mat r c) (M3 : mat c s),
      (M1 - M2) * M3 = M1 * M3 - M2 * M3.
  Proof. intros. apply mmul_msub_distr_r. Qed.

  (** (-M1) * M2 = - (M1 * M2) *)
  Lemma mmul_mopp_l : forall {r c s : nat} (M1 : mat r c) (M2 : mat c s),
      (-M1) * M2 = - (M1 * M2).
  Proof. intros. apply mmul_mopp_l. Qed.

  (** M1 * (-M2) = - (M1 * M2) *)
  Lemma mmul_mopp_r : forall {r c s : nat} (M1 : mat r c) (M2 : mat c s),
      M1 * (-M2) = - (M1 * M2).
  Proof. intros. apply mmul_mopp_r. Qed.

  (** mat0 * M = mat0 *)
  Lemma mmul_0_l : forall {r c s} (M : mat c s), (@mat0 r c) * M = mat0.
  Proof. intros. apply mmul_0_l. Qed.

  (** M * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c s} (M : mat r c), M * (@mat0 c s) = mat0.
  Proof. intros. apply mmul_0_r. Qed.

  (** mat1 * m = m *)
  Lemma mmul_1_l : forall {r c : nat} (M : mat r c), mat1 * M = M.
  Proof. intros. apply mmul_1_l. Qed.

  (** M * mat1 = M *)
  Lemma mmul_1_r : forall {r c : nat} (M : mat r c), M * mat1 = M.
  Proof. intros. apply mmul_1_r. Qed.
  
  (** (a * b) c* M = a c* (b c* M) *)
  Lemma mcmul_mul_assoc : forall {r c} (a b : A) (M : mat r c),
      (a * b)%A c* M = a c* (b c* M).
  Proof. intros. apply mcmul_mul_assoc. Qed.

  (** a c* (M1 * M2) = (a c* M1) * M2. *)
  Lemma mmul_mcmul_l : forall {r c s} (a : A) (M1 : mat r c) (M2 : mat c s), 
      (a c* M1) * M2 = a c* (M1 * M2).
  Proof. intros. apply mmul_mcmul_l. Qed.
  
  (** a c* (M1 * M2) = M1 * (a c* M2) *)
  Lemma mmul_mcmul_r : forall {r c s} (a : A) (M1 : mat r c) (M2 : mat c s), 
      M1 * (a c* M2) = a c* (M1 * M2).
  Proof. intros. apply mmul_mcmul_r. Qed.
  
  (** (M1 * M2)\T = M2\T * M1\T *)
  Lemma mtrans_mmul : forall {r c s} (M1 : mat r c) (M2 : mat c s),
      (M1 * M2)\T = M2\T * M1\T.
  Proof. intros. apply mtrans_mmul. Qed.

  (* (** tr (M1 * M2) = tr (M2 * M1) *) *)
  (* Lemma mtrace_mmul_comm : forall {r c} (M1 : mat r c) (M2 : mat c r), *)
  (*     tr (M1 * M2) = tr (M2 * M1). *)
  (* Proof. intros. apply mtrace_mmul_comm. Qed. *)

  
  (* ==================================== *)
  (** ** Hardmard product *)
  
  (** Hardmard product (also known as the element-wise product, entrywise product 
      or Schur product).
      It is a binary operation that takes two matrices of the same dimensions and 
      produces another matrix of the same dimension as the operandds, where each 
      element i,j is the product of elements i,j of the original two matrices.

      The hardmard product is associative, distribute and commutative *)
  (* Definition mhp {n : nat} (M1 M2 : smat n) : smat n := mhp m1 m2 (Amul:=Amul). *)
  (* Infix "⦿" := mhp : mat_scope. *)

  
  (* ==================================== *)
  (** ** Determinant of a matrix *)

  (** Determinant of a square matrix *)
  Definition mdet {n} (M : smat n) : A := @mdet _ Aadd Azero Aopp Amul Aone _ M.

  (* |M\T| = |M| *)
  Lemma mdet_mtrans : forall {n} (M : smat n), (mdet (M\T) = mdet M)%A.
  Proof. intros. apply mdet_mtrans. Qed.

  (* |M1*M2| = |M1| * |M2| *)
  Lemma mdet_mmul : forall {n} (M1 M2 : smat n),
      (mdet (M1 * M2)%M = mdet M1 * mdet M2)%A.
  Proof. intros. apply mdet_mmul. Qed.

  (* |mat1| = 1 *)
  Lemma mdet_mat1 : forall {n}, (@mdet n mat1 = Aone)%A.
  Proof. intros. apply mdet_mat1. Qed.

  
  (* ==================================== *)
  (** ** Determinant on matrix of 1-,2-, or 3-dim*)

  (** Determinant of a matrix of given dimension *)
  Definition mdet1 (M : smat 1) := @mdet1 _ Azero M.
  Definition mdet2 (M : smat 2) := @mdet2 _ Aadd Azero Aopp Amul M.
  Definition mdet3 (M : smat 3) := @mdet3 _ Aadd Azero Aopp Amul M.

  (** |M_1x1| = mdet1 M *)
  Lemma mdet_eq_mdet1 : forall M, mdet M = mdet1 M.
  Proof. intros. apply mdet_eq_mdet1. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet1_neq0_iff : forall (M : smat 1), mdet M <> Azero <-> M.11 <> Azero.
  Proof. intros. apply mdet1_neq0_iff. Qed.

  (** mdet2 M = |M| *)
  Lemma mdet_eq_mdet2 : forall M, mdet M = mdet2 M.
  Proof. intros. apply mdet_eq_mdet2. Qed.

  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet2_neq0_iff : forall (M : smat 2),
      (mdet M <> Azero <-> M.11*M.22 - M.12*M.21 <> Azero)%A.
  Proof. intros. apply mdet2_neq0_iff. Qed.

  (** mdet3 M = |M| *)
  Lemma mdet_eq_mdet3 : forall M, mdet M = mdet3 M.
  Proof. intros. apply mdet_eq_mdet3. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet3_neq0_iff : forall (M : smat 3),
      (mdet M <> Azero <->
         M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
           M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
           M.13 * M.21 * M.32 - M.13 * M.22 * M.31 <> Azero)%A.
  Proof. intros. apply mdet3_neq0_iff. Qed.
  
  
  (* ==================================== *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix: adj(A)[i,j] = algebraic remainder of A[i,j]. *)
  Definition madj {n} (M : smat n) : smat n := @madj _ Aadd Azero Aopp Amul Aone _ m.

  Global Instance madj_mor (n:nat) : Proper (meq ==> meq) (@madj n).
  Proof. apply madj_mor. Qed.
  

  (* ==================================== *)
  (** ** Invertible matrix *)
  
  (** A square matrix is invertible, if exists an inverse matrix *)
  Definition minvertible {n} (M : smat n) : Prop :=
    exists m' : smat n, (m * m' = mat1) \/ (m' * m = mat1).

  (** invertible mat1 *)
  Lemma minvertible_1 : forall n : nat, @minvertible n mat1.
  Proof. apply minvertible_1. Qed.

  (** A square matrix is invertible, if its determinant is nonzero *)
  Lemma minvertible_iff_mdet_n0 : forall {n} (M : smat n),
      minvertible m <-> mdet m <> Azero.
  Proof. intros. apply minvertible_iff_mdet_n0. Qed.

  (** invertible m -> invertible (m\T) *)
  Lemma minvertible_trans : forall n (M : smat n),
      minvertible m -> minvertible (m\T).
  Proof. intros. apply minvertible_trans; auto. Qed.

  (** invertible m -> invertible p -> invertible (m * p) *)
  Lemma minvertible_mul : forall n (m p : smat n),
      minvertible m -> minvertible p -> minvertible (m * p).
  Proof. intros. apply minvertible_mul; auto. Qed.

End RingMatrixTheory.


(* ######################################################################### *)
(** * Field matrix theory *)

Module FieldMatrixTheory (E : FieldElementType).
  
  Include (RingMatrixTheory E).

  (* ==================================== *)
  (** ** Gauss Elimination *)
  

  

(* Check l2m 0 3 3 [[1;2;3];[4;5;6];[7;8;10]]. *)
(* Print Matrix.mat. *)

Check rowEchelonForm.

Example m1 : mat 3 3 := l2m 0 3 3 [[1;2;3];[4;5;6];[7;8;10]].
Extraction GaussElimR. rowEchelonForm.
Import GaussElim.


  
  (* ==================================== *)
  (** ** Cramer rule *)
  
  (** Exchange one column of a square matrix *)
  Definition mchgcol {n} (M : smat n) (k : nat) (v : mat n 1) : smat n :=
    mchgcol m k v.
  
  (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid only when D is not zero *)
  Definition cramerRule {n} (a : smat n) (b : mat n 1) : mat n 1 :=
    @cramerRule _ Aadd Azero Aopp Amul Aone Tinv _ a b.

  
  (* ==================================== *)
  (** ** Matrix Inversion *)

  Definition minv {n} (M : smat n) := @minv _ Aadd Azero Aopp Amul Aone Tinv _ m.
  Notation "m ⁻¹" := (minv M) : mat_scope.

  Global Instance minv_mor (n : nat) : Proper (meq ==> meq) (@minv n).
  Proof. apply minv_mor. Qed.
  
  (** m * p = mat1 <-> m ⁻¹ = p *)
  Lemma mmul_eq1_iff_minv_l : forall {n} (m p : smat n),
      m * p = mat1 <-> minv m = p.
  Proof. intros. apply mmul_eq1_iff_minv_l; auto. Qed.

  (** m * p = mat1 <-> p ⁻¹ = m *)
  Lemma mmul_eq1_iff_minv_r : forall {n} (m p : smat n),
      m * p = mat1 <-> minv p = m.
  Proof. intros. apply mmul_eq1_iff_minv_r; auto. Qed.

  (** invertible m -> invertible (m⁻¹) *)
  Lemma minvertible_inv : forall {n} (M : smat n), minvertible m -> minvertible (m⁻¹).
  Proof. intros. apply minvertible_inv; auto. Qed.

  (** m⁻¹ * m = mat1 *)
  Lemma mmul_minv_l : forall n (M : smat n), (minv M) * m = mat1.
  Proof. intros. apply mmul_minv_l. Qed.
  
  (** m * m⁻¹ = mat1 *)
  Lemma mmul_minv_r : forall n (M : smat n), m * m⁻¹ = mat1.
  Proof. intros. apply mmul_minv_r. Qed.

  (** mat1 ⁻¹ = mat1 *)
  Lemma minv_1 : forall n, @minv n mat1 = mat1.
  Proof. intros. apply minv_1. Qed.

  (** m ⁻¹ ⁻¹ = m *)
  Lemma minv_minv : forall n (M : smat n), minvertible m -> m ⁻¹ ⁻¹ = m.
  Proof. intros. apply minv_minv; auto. Qed.

  (** (m * m') ⁻¹ = m' ⁻¹ * m ⁻¹ *)
  Lemma minv_mmul : forall n (m m' : smat n),
      minvertible m -> minvertible m' -> (m * m')⁻¹ = m' ⁻¹ * m ⁻¹.
  Proof. intros. apply minv_mmul; auto. Qed.

  (** (m\T) ⁻¹ = (m ⁻¹)\T *)
  Lemma minv_mtrans : forall n (M : smat n), minvertible m -> (m\T) ⁻¹ = (m ⁻¹)\T.
  Proof. intros. apply minv_mtrans; auto. Qed.
  
  (** mdet (m⁻¹) = 1 / (|M|) *)
  Lemma mdet_minv : forall {n} (M : smat n), (mdet (m⁻¹) = Aone / (mdet M))%A.
  Proof. intros. apply mdet_minv; auto. Qed.
  

  (* ==================================== *)
  (** ** Inversion matrix of common finite dimension *)
  
  (** Inversion matrix of dimension-1 *)
  Definition minv1 (M : smat 1) : smat 1 := @minv1 _ Azero Amul Aone Tinv m.

  (** |M| <> 0 -> minv1 m = inv m *)
  Lemma minv1_eq_inv : forall m, (mdet m <> Azero)%A -> minv1 m = minv m.
  Proof. intros. apply minv1_eq_inv; auto. Qed.

  (** minv1 m * m = mat1 *)
  Lemma minv1_correct_l : forall (M : smat 1), (mdet m <> Azero)%A -> (minv1 M) * m = mat1.
  Proof. intros. apply minv1_correct_l; auto. Qed.

  (** m * minv1 m = mat1 *)
  Lemma minv1_correct_r : forall (M : smat 1), (mdet m <> Azero)%A -> m * (minv1 M) = mat1.
  Proof. intros. apply minv1_correct_r; auto. Qed.

  
  (** Inversion matrix of dimension-2 *)
  Definition minv2 (M : smat 2) : smat 2 := @minv2 _ Aadd Azero Aopp Amul Tinv m.

  (** |M| <> 0 -> minv2 m = inv m *)
  Lemma minv2_eq_inv : forall m, (mdet m <> Azero)%A -> minv2 m = minv m.
  Proof. intros. apply minv2_eq_inv; auto. Qed.
  
  (** minv2 m * m = mat1 *)
  Lemma minv2_correct_l : forall (M : smat 2), (mdet m <> Azero)%A -> (minv2 M) * m = mat1.
  Proof. intros. apply minv2_correct_l; auto. Qed.
  
  (** m * minv2 m = mat1 *)
  Lemma minv2_correct_r : forall (M : smat 2), (mdet m <> Azero)%A -> m * (minv2 M) = mat1.
  Proof. intros. apply minv2_correct_r; auto. Qed.
  
  (** Inversion matrix of dimension-3 *)
  Definition minv3 (M : smat 3) : smat 3 := @minv3 _ Aadd Azero Aopp Amul Tinv m.
  
  (** |M| <> 0 -> minv3 m = inv m *)
  Lemma minv3_eq_inv : forall m, (mdet m <> Azero)%A -> minv3 m = minv m.
  Proof. intros. apply minv3_eq_inv; auto. Qed.
  
  (** minv3 m * m = mat1 *)
  Lemma minv3_correct_l : forall (M : smat 3), (mdet m <> Azero)%A -> (minv3 M) * m = mat1.
  Proof. intros. apply minv3_correct_l; auto. Qed.
  
  (** m * minv3 m = mat1 *)
  Lemma minv3_correct_r : forall (M : smat 3), (mdet m <> Azero)%A -> m * (minv3 M) = mat1.
  Proof. intros. apply minv3_correct_r; auto. Qed.

  (** Inversion matrix of dimension-4 *)
  Definition minv4 (M : smat 4) : smat 4 := @minv4 _ Aadd Azero Aopp Amul Tinv m.
  
  (** |M| <> 0 -> minv4 m = inv m *)
  Lemma minv4_eq_inv : forall m, (mdet m <> Azero)%A -> minv4 m = minv m.
  Proof. intros. apply minv4_eq_inv; auto. Qed.
  
  (** minv4 m * m = mat1 *)
  Lemma minv4_correct_l : forall (M : smat 4), (mdet m <> Azero)%A -> (minv4 M) * m = mat1.
  Proof. intros. apply minv4_correct_l; auto. Qed.
  
  (** m * minv4 m = mat1 *)
  Lemma minv4_correct_r : forall (M : smat 4), (mdet m <> Azero)%A -> m * (minv4 M) = mat1.
  Proof. intros. apply minv4_correct_r; auto. Qed.


  (* ==================================== *)
  (** ** orthogonal matrix *)
  
  (** A square matrix m is an orthogonal matrix *)
  Definition morth {n} (M : smat n) : Prop :=
   (@morth _ Aadd Azero Amul Aone Teq _ M).

  (** orthogonal m -> invertible m *)
  Lemma morth_invertible : forall {n} (M : smat n),
      morth m -> minvertible m.
  Proof. intros. apply morth_invertible; auto. Qed.

  (** orthogonal m -> m⁻¹ = m\T *)
  Lemma morth_imply_inv_eq_trans : forall {n} (M : smat n),
      morth m -> m⁻¹ = m\T.
  Proof. intros. apply morth_imply_inv_eq_trans; auto. Qed.

  (** m⁻¹ = m\T -> orthogonal m*)
  Lemma minv_eq_trans_imply_morth : forall {n} (M : smat n),
      m⁻¹ = m\T -> morth m.
  Proof. intros. apply minv_eq_trans_imply_morth; auto. Qed.

  (** orthogonal m <-> m\T * m = mat1 *)
  Lemma morth_iff_mul_trans_l : forall {n} (M : smat n),
      morth m <-> m\T * m = mat1.
  Proof. intros. apply morth_iff_mul_trans_l; auto. Qed.

  (** orthogonal m <-> m * m\T = mat1 *)
  Lemma morth_iff_mul_trans_r : forall {n} (M : smat n),
      morth m <-> m * m\T = mat1.
  Proof. intros. apply morth_iff_mul_trans_r; auto. Qed.

  (** orthogonal mat1 *)
  Lemma morth_1 : forall {n}, morth (@mat1 n).
  Proof. intros. apply morth_1; auto. Qed.

  (** orthogonal m -> orthogonal p -> orthogonal (m * p) *)
  Lemma morth_mul : forall {n} (m p : smat n),
      morth m -> morth p -> morth (m * p).
  Proof. intros. apply morth_mul; auto. Qed.

  (** orthogonal m -> orthogonal m\T *)
  Lemma morth_mtrans : forall {n} (M : smat n), morth m -> morth (m\T).
  Proof. intros. apply morth_mtrans; auto. Qed.

  (** orthogonal m -> orthogonal m⁻¹ *)
  Lemma morth_minv : forall {n} (M : smat n), morth m -> morth (m⁻¹).
  Proof. intros. apply morth_minv; auto. Qed.

  (* (** orthogonal m -> |m| = ± 1 *) *)
  (* Lemma morth_mdet : forall {n} (M : smat n) (HDec : Dec Teq), *)
  (*     morth m -> (|M| = Aone \/ |M| = - (Aone))%A. *)
  (* Proof. intros. apply morth_mdet; auto. Qed. *)

  
  (* ==================================== *)
  (** ** O(n): General Orthogonal Group, General Linear Group *)
  
  (** The set of GOn *)
  Definition GOn (n : nat) := (@GOn _ Aadd Azero Amul Aone Teq n).

  (** Equality of elements in GOn *)
  Definition GOn_eq {n} (s1 s2 : GOn n) : Prop := GOn_eq s1 s2.

  (** Multiplication of elements in GOn *)
  Definition GOn_mul {n} (s1 s2 : GOn n) : GOn n := GOn_mul s1 s2.

  (** Identity element in GOn *)
  Definition GOn_1 {n} : GOn n :=  GOn_1.

  (** Inverse operation of multiplication in GOn *)
  Definition GOn_inv {n} (s : GOn n) : GOn n := GOn_inv s.

  (** GOn_eq is equivalence relation *)
  Lemma GOn_eq_equiv : forall n, Equivalence (@GOn_eq n).
  Proof. intros. apply GOn_eq_equiv; auto. Qed.

  (** GOn_mul is a proper morphism respect to GOn_eq *)
  Lemma GOn_mul_proper : forall n, Proper (GOn_eq ==> GOn_eq ==> GOn_eq) (@GOn_mul n).
  Proof. intros. apply GOn_mul_proper. Qed.

  (** GOn_inv is a proper morphism respect to GOn_eq *)
  Lemma GOn_inv_proper : forall n, Proper (GOn_eq ==> GOn_eq) (@GOn_inv n).
  Proof. intros. apply GOn_inv_proper. Qed.

  (** GOn_mul is associative *)
  Lemma GOn_mul_assoc : forall n, Associative GOn_mul (@GOn_eq n).
  Proof. intros. apply GOn_mul_assoc; auto. Qed.

  (** GOn_1 is left-identity-element of GOn_mul operation *)
  Lemma GOn_mul_id_l : forall n, IdentityLeft GOn_mul GOn_1 (@GOn_eq n).
  Proof. intros. apply GOn_mul_id_l. Qed.
  
  (** GOn_1 is right-identity-element of GOn_mul operation *)
  Lemma GOn_mul_id_r : forall n, IdentityRight GOn_mul GOn_1 (@GOn_eq n).
  Proof. intros. apply GOn_mul_id_r. Qed.

  (** GOn_inv is left-inversion of <GOn_mul,GOn_1> *)
  Lemma GOn_mul_inv_l : forall n, InverseLeft GOn_mul GOn_1 GOn_inv (@GOn_eq n).
  Proof. intros. apply GOn_mul_inv_l. Qed.

  (** GOn_inv is right-inversion of <GOn_mul,GOn_1> *)
  Lemma GOn_mul_inv_r : forall n, InverseRight GOn_mul GOn_1 GOn_inv (@GOn_eq n).
  Proof. intros. apply GOn_mul_inv_r. Qed.
  
  (** <GOn, +, 1> is a monoid *)
  Lemma Monoid_GOn : forall n, Monoid (@GOn_mul n) GOn_1 GOn_eq.
  Proof. intros. apply Monoid_GOn. Qed.

  (** <GOn, +, 1, /s> is a group *)
  Theorem Group_GOn : forall n, Group (@GOn_mul n) GOn_1 GOn_inv GOn_eq.
  Proof. intros. apply Group_GOn. Qed.

  (** m⁻¹ = m\T *)
  Lemma GOn_imply_inv_eq_trans : forall {n} (s : GOn n),
      let m := GOn_mat n s in
      m⁻¹ = m\T.
  Proof. intros. apply GOn_imply_inv_eq_trans. Qed.
  
  (* ==================================== *)
  (** ** SO(n): Special Orthogonal Group, Rotation Group *)

  (** The set of SOn *)
  Definition SOn (n: nat) := (@SOn _ Aadd Azero Aopp Amul Aone Teq n).

  Definition mk_SOn {n : nat} (M : smat n) (H : morth m /\ (mdet m = Aone)%A)
    : SOn n := Build_SOn n m H.

  Definition SOn_eq {n} (s1 s2 : SOn n) : Prop := SOn_mat _ s1 = SOn_mat _ s2.

  Definition SOn_mul {n} (s1 s2 : SOn n) : SOn n := SOn_mul s1 s2.

  Definition SOn_1 {n} : SOn n := SOn_1.

  (** SOn_eq is equivalence relation *)
  Lemma SOn_eq_equiv : forall n, Equivalence (@SOn_eq n).
  Proof. intros. apply SOn_eq_equiv. Qed.

  (** SOn_mul is a proper morphism respect to SOn_eq *)
  Lemma SOn_mul_proper : forall n, Proper (SOn_eq ==> SOn_eq ==> SOn_eq) (@SOn_mul n).
  Proof. intros. apply SOn_mul_proper. Qed.

  (** SOn_mul is associative *)
  Lemma SOn_mul_assoc : forall n, Associative SOn_mul (@SOn_eq n).
  Proof. intros. apply SOn_mul_assoc. Qed.

  (** SOn_1 is left-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_l : forall n, IdentityLeft SOn_mul SOn_1 (@SOn_eq n).
  Proof. intros. apply SOn_mul_id_l. Qed.
  
  (** SOn_1 is right-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_r : forall n, IdentityRight SOn_mul SOn_1 (@SOn_eq n).
  Proof. intros. apply SOn_mul_id_r. Qed.
  
  (** <SOn, +, 1> is a monoid *)
  Lemma Monoid_SOn : forall n, Monoid (@SOn_mul n) SOn_1 SOn_eq.
  Proof. intros. apply Monoid_SOn. Qed.

  Definition SOn_inv {n} (s : SOn n) : SOn n := SOn_inv s.

  (** SOn_inv is a proper morphism respect to SOn_eq *)
  Lemma SOn_inv_proper : forall n, Proper (SOn_eq ==> SOn_eq) (@SOn_inv n).
  Proof. intros. apply SOn_inv_proper. Qed.

  (** SOn_inv is left-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_l : forall n, InverseLeft SOn_mul SOn_1 SOn_inv (@SOn_eq n).
  Proof. intros. apply SOn_mul_inv_l. Qed.

  (** SOn_inv is right-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_r : forall n, InverseRight SOn_mul SOn_1 SOn_inv (@SOn_eq n).
  Proof. intros. apply SOn_mul_inv_r. Qed.

  (** <SOn, +, 1, /s> is a group *)
  Theorem Group_SOn : forall n, Group (@SOn_mul n) SOn_1 SOn_inv SOn_eq.
  Proof. intros. apply Group_SOn. Qed.

  (** m⁻¹ = m\T *)
  Lemma SOn_imply_inv_eq_trans : forall {n} (s : SOn n),
      let m := SOn_mat n s in
      m⁻¹ = m\T.
  Proof. intros. apply SOn_imply_inv_eq_trans. Qed.

  
  (* ==================================== *)
  (** ** Other un-sorted properties *)
  

  (* (** k * m = 0 -> (m = 0) \/ (k = 0) *) *)
  (* Axiom mcmul_eq0_imply_m0_or_k0 : forall {r c} (M : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     (k c* m = m0) -> (m = m0) \/ (k = Azero)%A. *)

  (* (** (m <> 0 \/ k * m = 0) -> k = 0 *) *)
  (* Axiom mcmul_mnonzero_eq0_imply_k0 : forall {r c} (M : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     ~(m = m0) -> k c* m = m0 -> (k = Azero)%A. *)

  (* (** k * m = m -> k = 1 \/ m = 0 *) *)
  (* Axiom mcmul_same_imply_coef1_or_mzero : forall {r c} k (M : mat r c), *)
  (*     k c* m = m -> (k = Aone)%A \/ (m = mat0 r c). *)

  (* (** (m1 <> 0 /\ m2 <> 0 /\ k * m1 = m2) -> k <> 0 *) *)
  (* Axiom mcmul_eq_mat_implfy_not_k0 : forall {r c} (M1 M2 : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     ~(m1 = m0) -> ~(m2 = m0) -> k c* m1 = m2 -> ~(k = Azero)%A. *)
  
End FieldMatrixTheory.


(* ######################################################################### *)
(** * Decidable matrix theory *)

Module DecidableMatrixTheory (E : DecidableElementType).
  Include (BasicMatrixTheory E).

  (** equality of two matrices is decidable *)
  Lemma meq_dec : forall {r c}, Dec (meq (r:=r) (c:=c)).
  Proof. intros. apply meq_dec. Qed.

End DecidableMatrixTheory.


(* ######################################################################### *)
(** * Decidable field matrix theory *)

Module DecidableFieldMatrixTheory (E : DecidableFieldElementType).

  Include (FieldMatrixTheory E).

  (** equality of two matrices is decidable *)
  Lemma meq_dec : forall {r c}, Dec (meq (r:=r) (c:=c)).
  Proof. intros. apply meq_dec. Qed.

  (* ==================================== *)
  (** ** Gauss elimination *)

  (** inverse matrix by gauss elimination *)
  Definition minv_gauss {n} (m : mat n n) : option (mat n n) :=
    @minv_gauss T Aadd Azero Aopp Amul Aone Tinv _ _ _ m.
  
End DecidableFieldMatrixTheory.
