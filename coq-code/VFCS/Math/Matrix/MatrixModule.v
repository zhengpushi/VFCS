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
  (2) DecidableMatrixTheory
      matrix theory on element with decidable relation
  (3) RingMatrixTheory
      matrix theory on element with ring structure.
  (4) FieldMatrixTheory
      matrix theory on element with field structure.
  (5) DecidableFieldTheory
      matrix theory on element with decidable field structure.

 *)


Require Export Matrix.
Require Export ElementType.


(* ######################################################################### *)
(** * Basic matrix theory *)

Module BasicMatrixTheory (E : ElementType).

  (* ==================================== *)
  (** ** Matrix element type *)
  Export E.

  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "!=" := (fun l1 l2 => ~(l1 == l2)%list) : list_scope.
  Infix "==" := (eqlistA (eqlistA Teq)) : dlist_scope.
  Infix "!=" := (fun d1 d2 => ~(d1 == d2)%dlist) : dlist_scope.

  Open Scope nat_scope.
  Open Scope T_scope.
  Open Scope mat_scope.
  

  (* ==================================== *)
  (** ** Matrix type and basic operations *)
  Definition mat r c : Type := @mat T r c.

  (** square matrix *)
  Notation smat n := (smat T n).

  (** Convert between function and matrix *)
  Definition f2m {r c} (f : nat -> nat -> T) : mat r c := f2m f.
  Definition m2f {r c} (m : mat r c) : nat -> nat -> T := m2f m.

  (** matrix equality *)
  Definition meq {r c} (m1 m2 : mat r c) : Prop := meq (Teq:=Teq) m1 m2.
  Infix "==" := meq : mat_scope.
  Infix "!=" := (fun m1 m2 => ~(m1 == m2)%M) : mat_scope.

  (** meq is equivalence relation *)
  Lemma meq_equiv : forall r c, Equivalence (meq (r:=r) (c:=c)).
  Proof. apply meq_equiv. Qed.

  (** Get element of a matrix (nth means n-th) *)
  Definition mnth {r c} (m : mat r c) (i j : nat) : T := mnth T0 m i j.
  Notation "m $ i $ j " := (m2f m i j) : mat_scope.
  Notation "m ! i ! j " := (mnth m i j) : mat_scope.

  Notation "m .11" := (m $ 0 $ 0) : mat_scope.
  Notation "m .12" := (m $ 0 $ 1) : mat_scope.
  Notation "m .13" := (m $ 0 $ 2) : mat_scope.
  Notation "m .14" := (m $ 0 $ 3) : mat_scope.
  Notation "m .21" := (m $ 1 $ 0) : mat_scope.
  Notation "m .22" := (m $ 1 $ 1) : mat_scope.
  Notation "m .23" := (m $ 1 $ 2) : mat_scope.
  Notation "m .24" := (m $ 1 $ 3) : mat_scope.
  Notation "m .31" := (m $ 2 $ 0) : mat_scope.
  Notation "m .32" := (m $ 2 $ 1) : mat_scope.
  Notation "m .33" := (m $ 2 $ 2) : mat_scope.
  Notation "m .34" := (m $ 2 $ 3) : mat_scope.
  Notation "m .41" := (m $ 3 $ 0) : mat_scope.
  Notation "m .42" := (m $ 3 $ 1) : mat_scope.
  Notation "m .43" := (m $ 3 $ 2) : mat_scope.
  Notation "m .44" := (m $ 3 $ 3) : mat_scope.

  (** mnth is equal to mnthRaw *)
  Lemma mnth_eq_mnthRaw : forall {r c : nat} (m : mat r c),
    forall i j, i < r -> j < c -> (m!i!j == m$i$j)%T.
  Proof. intros. apply mnth_eq_mnth_raw; auto. Qed.
  
  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (mnth m1 ri ci == mnth m2 ri ci)%T).
  Proof. intros. apply meq_iff_mnth. Qed.


  (* ==================================== *)
  (** ** Convert between list list and matrix *)

  (** dlist to matrix with specified row and column numbers *)
  Definition l2m {r c} (dl : dlist T) : mat r c := l2m T0 dl.
  
  (** mat to dlist *)
  Definition m2l {r c} (m : mat r c) : dlist T := m2l m.

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof. intros. apply m2l_length. Qed.
  
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof. intros. apply m2l_width. Qed.

  Lemma l2m_m2l_id : forall {r c} (m : mat r c), (@l2m r c (m2l m)) == m.
  Proof. intros. apply l2m_m2l_id. Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : dlist T),
      length dl = r -> width dl c -> (m2l (@l2m r c dl) == dl)%dlist.
  Proof. intros. apply m2l_l2m_id; auto. Qed.

  Lemma l2m_inj : forall {r c} (d1 d2 : dlist T),
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      ~(d1 == d2)%dlist -> ~(@l2m r c d1 == l2m d2).
  Proof. intros. apply l2m_inj; auto. Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m d == m).
  Proof. intros. apply l2m_surj. Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist.
  Proof. intros. apply (m2l_inj (T0:=T0)); auto. Qed.
  
  Lemma m2l_surj : forall {r c} (d : dlist T),
      length d = r -> width d c -> (exists m : mat r c, (m2l m == d)%dlist).
  Proof. intros. apply (m2l_surj (T0:=T0)); auto. Qed.

  
  (* ==================================== *)
  (** ** matrix shift *)

  (** left shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *)
  Definition mcshl {r c} (m : mat r c) (k : nat) : mat r c := mcshl m k.

  (** right shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *)
  Definition mcshr {r c} (m : mat r c) (k : nat) : mat r c := mcshr m k (T0:=T0).

  (** left loop shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *)
  Definition mclshl {r c} (m : mat r c) (k : nat) : mat r c := mclshl m k.

  (** right shift column *)
  Definition mclshr {r c} (m : mat r c) (k : nat) : mat r c := mclshr m k.

  
  (* ==================================== *)
  (** ** Diagonal matrix *)

  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (m : smat n) : Prop := mdiag m (Teq:=Teq)(T0:=T0).

  (** Construct a diagonal matrix *)
  Definition mk_diag {n} (l : list T) : smat n := mk_diag l (T0:=T0).

  (** mk_diag is correct *)
  Lemma mk_diag_spec : forall {n} (l : list T), mdiag (@mk_diag n l).
  Proof. intros. apply mk_diag_spec. Qed.

  
  (* ==================================== *)
  (** ** Construct matrix with one-row or one-column matrix and another matrix *)
  (* Notation rvec n := (@mat T 1 n). *)
  (* Notation cvec n := (@mat T n 1). *)

  (** Construct a matrix by rows, i.e., a row vector and a matrix *)
  Definition mconsr {r c} (v : mat 1 c) (m : mat r c) : mat (S r) c := mconsr v m.

  (** Construct a matrix by columns, i.e., a column vector and a matrix *)
  Definition mconsc {r c} (v : mat r 1) (m : mat r c) : mat r (S c) := mconsc v m.
  
  (** mconsr rewrite *)
  (* Lemma mconsr_eq {r c} (v : vecr c) (m : mat r c) : mconsr v m == (v, m). *)
  (* Proof. unfold mconsr. auto. Qed. *)
  
  (** Construct a matrix by rows with the matrix which row number is 0 *)
  Lemma mconsr_mr0 : forall {n} (v : mat 1 n) (m : mat 0 n), mconsr v m == v.
  Proof. intros. apply mconsr_mr0. Qed.
  
  (** Construct a matrix by columns with the matrix which column number is 0 *)
  Lemma mconsc_mr0 : forall {n} (v : mat n 1) (m : mat n 0), mconsc v m == v.
  Proof. intros. apply mconsc_mr0. Qed.

  
  (* ==================================== *)
  (** ** Construct matrix with two matrices *)
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (m1 : mat r1 c) (m2 : mat r2 c) : mat (r1 + r2) c :=
    mappr m1 m2.
  
  (** Append matrix by column *)
  Definition mappc {r c1 c2} (m1 : mat r c1) (m2 : mat r c2) : mat r (c1 + c2) :=
    mappc m1 m2.

  
  (* ==================================== *)
  (** ** Make concrete matrix *)

  Definition mk_mat_0_c c : mat 0 c :=
    mk_mat_0_c c (T0:=T0).
  Definition mk_mat_1_1 (a11 : T) : mat 1 1 :=
    mk_mat_1_1 a11 (T0:=T0).
  Definition mk_mat_1_2 (a11 a12 : T) : mat 1 2 :=
    mk_mat_1_2 a11 a12 (T0:=T0).
  Definition mk_mat_1_3 (a11 a12 a13 : T) : mat 1 3 :=
    mk_mat_1_3 a11 a12 a13 (T0:=T0).
  Definition mk_mat_1_4 (a11 a12 a13 a14 : T) : mat 1 4 :=
    mk_mat_1_4 a11 a12 a13 a14 (T0:=T0).
  Definition mk_mat_1_c c (l : list T) : mat 1 c :=
    mk_mat_1_c c l (T0:=T0).
  
  Definition mk_mat_r_0 r : mat r 0 :=
    mk_mat_r_0 r (T0:=T0).
  Definition mk_mat_2_1 (a11 a21 : T) : mat 2 1 :=
    mk_mat_2_1 a11 a21 (T0:=T0).
  Definition mk_mat_3_1 (a11 a21 a31 : T) : mat 3 1 :=
    mk_mat_3_1 a11 a21 a31 (T0:=T0).
  Definition mk_mat_4_1 (a11 a21 a31 a41 : T) : mat 4 1 :=
    mk_mat_4_1 a11 a21 a31 a41 (T0:=T0).
  Definition mk_mat_r_1 r (l : list T) : mat r 1 :=
    mk_mat_r_1 r l (T0:=T0).

  Definition mk_mat_2_2 (a11 a12 a21 a22 : T) : mat 2 2 :=
    mk_mat_2_2 a11 a12 a21 a22 (T0:=T0).
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : T) : mat 3 3 :=
    mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 (T0:=T0).
  Definition mk_mat_4_4 (a11 a12 a13 a14 a21 a22 a23 a24
                           a31 a32 a33 a34 a41 a42 a43 a44 : T) : mat 4 4 :=
    mk_mat_4_4
      a11 a12 a13 a14
      a21 a22 a23 a24
      a31 a32 a33 a34
      a41 a42 a43 a44 (T0:=T0).

  
  (* ==================================== *)
  (** ** Convert between tuples and matrix *)
  
  (** Tuples 2x2 -> mat_2x2 *)
  Definition t2m_2_2 (t : @T_2_2 T) : mat 2 2 := t2m_2_2 T0 t.

  (** Tuples 3x3 -> mat_3x3 *)
  Definition t2m_3_3 (t : @T_3_3 T) : mat 3 3 := t2m_3_3 T0 t.

  (** m[0,0]: mat_1x1 -> T *)
  Definition m2t_1_1 (m : mat 1 1) := m2t_1_1 m.
  Definition scalar_of_mat (m : mat 1 1) := scalar_of_mat m.

  (** mat_2x2 -> tuple 2x2. That is: ((a11,a12),(a21,a22)) *)
  Definition m2t_2_2 (m : mat 2 2) : @T_2_2 T := m2t_2_2 m.

  (** mat_3x3 -> tuple 3x3. That is: ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) *)
  Definition m2t_3_3 (m : mat 3 3) : @T_3_3 T := m2t_3_3 m.

  
  (* ==================================== *)
  (** ** Mapping of matrix *)

  Definition mmap {r c} (f : T -> T) (m : mat r c) : mat r c := mmap f m.
  
  Definition mmap2 {r c} (f : T -> T -> T) (m1 m2 : mat r c) : mat r c :=
    mmap2 f m1 m2.

  Lemma mmap2_comm : forall {r c} (f : T -> T -> T) (m1 m2 : mat r c)
                            {Comm : Commutative f Teq}, 
      mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof. intros. apply mmap2_comm; auto. Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : T -> T -> T) (m1 m2 m3 : mat r c)
                             {Assoc : Associative f Teq}, 
      mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof. intros. apply mmap2_assoc; auto. Qed.

  
  (* ==================================== *)
  (** ** Matrix transposition *)

  Definition mtrans {r c} (m : mat r c): mat c r := mtrans m.
  Notation "m \T" := (mtrans m) : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mtrans_mor : forall r c, Proper (meq ==> meq) (mtrans (r:=r)(c:=c)).
  Proof. apply mtrans_mor. Qed.

  (** Transpose twice keep unchanged. *)
  Lemma mtrans_mtrans : forall {r c} (m : mat r c), m \T \T == m.
  Proof. intros. apply mtrans_mtrans. Qed.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (m : smat n), mdiag m -> m\T == m.
  Proof. intros. apply (mtrans_diag (T0:=T0)); auto. Qed.

End BasicMatrixTheory.


(* ######################################################################### *)
(** * Ring matrix theory *)
Module RingMatrixTheory (E : RingElementType).
  Include (BasicMatrixTheory E).

  Infix "+" := (ladd (Tadd:=Tadd)) : list_scope.
  Notation seqsum := (seqsum (Tadd:=Tadd) (T0:=T0)).

  
  (* ==================================== *)
  (** ** Zero matrirx and identity matrix *)

  (** Zero matrix *)
  Definition mat0 {r c : nat} : mat r c := mat0 T0.

  (** Identity matrix *)
  Definition mat1 {n : nat} : mat n n := mat1 T0 T1.

  (** mat1 is diagonal matrix *)
  Lemma mat1_is_diag : forall {n : nat}, mdiag (@mat1 n).
  Proof. intros. apply mat1_is_diag. Qed.
  
  (** mat0\T = mat0 *)
  Lemma mtrans_0 : forall {r c : nat}, (@mat0 r c)\T == mat0.
  Proof. intros. apply mtrans_0. Qed.
  
  (** mat1\T = mat1 *)
  Lemma mtrans_1 : forall {n : nat}, (@mat1 n)\T == mat1.
  Proof. intros. apply mtrans_1. Qed.

  (** i < n -> j < n -> i <> j -> mat1[i,j] = 0 *)
  Lemma mnth_mat1_diff : forall {n} i j,
      i < n -> j < n -> i <> j -> ((@mat1 n) $ i $ j == T0)%T.
  Proof. intros. apply mnth_mat1_diff; auto. Qed.

  (** i < n -> mat1[i,i] = 1 *)
  Lemma mnth_mat1_same : forall {n} i, i < n -> ((@mat1 n) $ i $ i == T1)%T.
  Proof. intros. apply mnth_mat1_same; auto. Qed.


  (* ==================================== *)
  (** ** Matrix trace *)
  Definition mtrace {n : nat} (m : smat n) : T := mtrace m (Tadd:=Tadd)(T0:=T0).
  Notation "'tr' m" := (mtrace m) : mat_scope.
  
  (** show it is a proper morphism *)
  Global Instance mtrace_mor : forall n, Proper (meq ==> Teq) (mtrace (n:=n)).
  Proof. apply mtrace_mor. Qed.

  (** tr(m\T) = tr(m) *)
  Lemma mtrace_trans : forall {n} (m : smat n), (tr (m\T) == tr(m))%T.
  Proof. intros. apply mtrace_trans. Qed.


  (* ==================================== *)
  (** ** Matrix addition *)
  
  Definition madd {r c} (m1 m2 : mat r c) : mat r c := madd m1 m2 (Tadd:=Tadd).
  Infix "+" := madd : mat_scope.

  (** show it is a proper morphism *)
  Global Instance madd_mor : forall r c, Proper (meq ==> meq ==> meq) (madd (r:=r)(c:=c)).
  Proof. apply madd_mor. Qed.

  (** m1 + m2 = m2 + m1 *)
  Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == (m2 + m1).
  Proof. intros. apply madd_comm. Qed.

  (** (m1 + m2) + m3 = m1 + (m2 + m3) *)
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof. intros. apply madd_assoc. Qed.

  (** (m1 + m2) + m3 = (m1 + m3) + m2 *)
  Lemma madd_perm : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == (m1 + m3) + m2.
  Proof. intros. apply madd_perm. Qed.

  (** mat0 + m = m *)
  Lemma madd_0_l : forall {r c} (m : mat r c), mat0 + m == m. 
  Proof. intros. apply madd_0_l. Qed.

  (** m + mat0 = m *)
  Lemma madd_0_r : forall {r c} (m : mat r c), m + mat0 == m. 
  Proof. intros. apply madd_0_r. Qed.
  
  (** Get element of addition with two matrics equal to additon of corresponded 
      elements. *)

  Lemma mnth_madd : forall {r c} (m1 m2 : mat r c) i j,
      ((m1 + m2)%M ! i ! j == (m1!i!j) + (m2!i!j))%T.
  Proof. intros. apply madd_nth. Qed.

  (* (** (m1 + m2)[i] = m1[i] + m2[i] *) *)
  (* Lemma mrow_madd : forall {r c} i (m1 m2 : mat r c), *)
  (*     i < r -> (mrow i (m1 + m2)%M == ((mrow i m1) + (mrow i m2))%list)%list. *)

  (** (m1 + m2)\T = m1\T + m2\T *)
  Lemma mtrans_madd : forall {r c} (m1 m2 : mat r c), (m1 + m2)\T == m1\T + m2\T.
  Proof. intros. apply mtrans_madd. Qed.

  (** tr(m1 + m2) = tr(m1) + tr(m2) *)
  Lemma mtrace_madd : forall {n} (m1 m2 : smat n), (tr (m1 + m2)%M == tr(m1) + tr(m2))%T.
  Proof. intros. apply mtrace_madd. Qed.

  
  (* ==================================== *)
  (** ** Monoid structure over {madd,mat0,meq} *)
  Global Instance Monoid_MatTadd : forall r c, Monoid (@madd r c) mat0 meq.
  Proof. apply Monoid_MatTadd. Qed.

  Section test.
    Goal forall r c (m1 m2 : mat r c), mat0 + m1 == m1.
      monoid_simp. Qed.
  End test.

  
  (* ==================================== *)
  (** ** Matrix opposition *)
  
  Definition mopp {r c} (m : mat r c) : mat r c := mopp m (Topp:=Topp).
  Notation "- a" := (mopp a) : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mopp_mor : forall r c, Proper (meq ==> meq) (mopp (r:=r)(c:=c)).
  Proof. apply mopp_mor. Qed.

  (** - (m1 + m2) = (-m1) + (-m2) *)
  Lemma mopp_madd : forall {r c : nat} (m1 m2 : mat r c), - (m1 + m2) == (-m1) + (-m2).
  Proof. intros. apply mopp_madd. Qed.

  (** (-m) + m = mat0 *)
  Lemma madd_mopp_l : forall r c (m : mat r c), (-m) + m == mat0.
  Proof. intros. apply madd_mopp_l. Qed.

  (** m + (-m) = mat0 *)
  Lemma madd_mopp_r : forall r c (m : mat r c), m + (-m) == mat0.
  Proof. intros. apply madd_mopp_r. Qed.

  (** - (- m) = m *)
  Lemma mopp_mopp : forall {r c} (m : mat r c), - (- m) == m.
  Proof. intros. apply mopp_mopp. Qed.

  (** - mat0 = mat0 *)
  Lemma mopp_0 : forall {r c}, - (@mat0 r c) == mat0.
  Proof. intros. apply mopp_0. Qed.

  (** (m1 + m2)\T = m1\T + m2\T *)
  Lemma mtrans_mopp : forall {r c} (m : mat r c), (- m)\T == - (m\T).
  Proof. intros. apply mtrans_mopp. Qed.

  (** tr(- m) = - (tr(m)) *)
  Lemma mtrace_mopp : forall {n} (m : smat n), (tr((-m)%M) == - (tr(m)))%T.
  Proof. intros. apply mtrace_mopp. Qed.

  
  (* ==================================== *)
  (** ** Matrix subtraction *)
  
  Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
    msub m1 m2 (Tadd:=Tadd)(Topp:=Topp).
  Infix "-" := msub : mat_scope.

  (** show it is a proper morphism *)
  Global Instance msub_mor : forall r c, Proper (meq ==> meq ==> meq) (msub (r:=r)(c:=c)).
  Proof. apply msub_mor. Qed.

  (** Rewrite msub: m1 - m2 = m1 + (-m2) *)
  Lemma msub_rw : forall {r c} (m1 m2 : mat r c), m1 - m2 == m1 + (-m2).
  Proof. intros. apply msub_rw. Qed.

  (** m1 - m2 = -(m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
  Proof. intros. apply msub_comm. Qed.

  (** (m1 - m2) - m3 = m1 - (m2 + m3) *)
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof. intros. apply msub_assoc. Qed.

  (** (m1 + m2) - m3 = m1 + (m2 - m3) *)
  Lemma msub_assoc1 : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) - m3 == m1 + (m2 - m3).
  Proof. intros. apply msub_assoc1. Qed.

  (** (m1 - m2) - m3 = m1 - (m3 - m2) *)
  Lemma msub_assoc2 : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == (m1 - m3) - m2.
  Proof. intros. apply msub_assoc2. Qed.

  (** mat0 - m = - m *)
  Lemma msub_0_l : forall {r c} (m : mat r c), mat0 - m == - m.
  Proof. intros. apply msub_0_l. Qed.

  (** m - mat0 = m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - mat0 == m.
  Proof. intros. apply msub_0_r. Qed.

  (** m - m = mat0 *)
  Lemma msub_self : forall {r c} (m : mat r c), m - m == mat0.
  Proof. intros. apply msub_self. Qed.

  (** (m1 - m2)\T = m1\T - m2\T *)
  Lemma mtrans_msub : forall {r c} (m1 m2 : mat r c), (m1 - m2)\T == m1\T - m2\T.
  Proof. intros. apply mtrans_msub. Qed.

  (** tr(m1 - m2) = tr(m1) - tr(m2) *)
  Lemma mtrace_msub : forall {n} (m1 m2 : smat n),
      (tr ((m1 - m2)%M) == tr(m1) - tr(m2))%T.
  Proof. intros. apply mtrace_msub. Qed.
  
  (* ==================================== *)
  (** ** Group structure over {madd,mat0,mopp,meq} *)
  Global Instance Group_MatAdd : forall r c, Group (@madd r c) mat0 mopp meq.
  Proof. apply Group_MatAdd. Qed.

  Section test.
    Goal forall r c (m1 m2 : mat r c), mat0 + m1 + (-m2) + m2 == m1.
      intros.
      (* rewrite identityLeft. *)
      (* rewrite associative. *)
      (* rewrite inverseLeft. *)
      group_simp.
    Qed.
  End test.

  
  (* ==================================== *)
  (** ** Abelian group structure over {madd,mat0,mopp,meq} *)
  Global Instance AGroup_MatAdd : forall r c, AGroup (@madd r c) mat0 mopp meq.
  Proof. apply AGroup_MatAdd. Qed.


  (* ==================================== *)
  (** ** Scalar multiplication of matrix *)

  (** Left scalar multiplication of matrix *)
  Definition mcmul {r c} (a : T) (m : mat r c) : mat r c := mcmul a m (Tmul:=Tmul).
  Infix "c*" := mcmul : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mcmul_mor : forall r c, Proper (Teq ==> meq ==> meq) (mcmul (r:=r)(c:=c)).
  Proof. apply mcmul_mor. Qed.

  (** 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), T0 c* m == mat0.
  Proof. intros. apply mcmul_0_l. Qed.

  (** a c* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a c* (@mat0 r c) == mat0.
  Proof. intros. apply mcmul_0_r. Qed.

  (** 1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), T1 c* m == m.
  Proof. intros. apply mcmul_1_l. Qed.

  (** a c* mat1 equal to a diagonal matrix which main diagonal elements all are a *)
  Lemma mcmul_1_r : forall {n} a,
      a c* (@mat1 n) == mk_mat (fun i j => if (i =? j)%nat then a else T0).
  Proof. intros. apply mcmul_1_r. Qed.

  (** a c* (b c* m) = (a * b) c* m *)
  Lemma mcmul_assoc : forall {r c} (a b : T) (m : mat r c), a c* (b c* m) == (a * b) c* m.
  Proof. intros. apply mcmul_assoc. Qed.

  (** a c* (b c* m) = b c* (a c* m) *)
  Lemma mcmul_perm : forall {r c} (a b : T) (m : mat r c), a c* (b c* m) == b c* (a c* m).
  Proof. intros. apply mcmul_perm. Qed.

  (** (a + b) c* m = (a c* m) + (b c* m) *)
  Lemma mcmul_add_distr : forall {r c} (a b : T) (m : mat r c), 
      (a + b)%T c* m == (a c* m) + (b c* m).
  Proof. intros. apply mcmul_add_distr. Qed.

  (** a c* (m1 + m2) = (a c* m1) + (a c* m2) *)
  Lemma mcmul_madd_distr : forall {r c} (a : T) (m1 m2 : mat r c), 
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof. intros. apply mcmul_madd_distr. Qed.
  
  (** - (a c* m) = (-a) c* m *)
  Lemma mopp_mcmul : forall {r c} a (m : mat r c), - (a c* m) == (-a)%T c* m.
  Proof. intros. apply mopp_mcmul. Qed.

  (** a c* (m1 - m2) = (a c* m1) - (a c* m2) *)
  Lemma mcmul_msub : forall {r c} a (m1 m2 : mat r c),
      a c* (m1 - m2) == (a c* m1) - (a c* m2).
  Proof. intros. apply mcmul_msub. Qed.

  (** (a c* m)\T = a c* (m\T) *)
  Lemma mtrans_mcmul : forall {r c} (a : T) (m : mat r c), (a c* m)\T == a c* (m\T).
  Proof. intros. apply mtrans_mcmul. Qed.

  (** tr (a c* m) = a * tr (m) *)
  Lemma mtrace_mcmul : forall {n} (a : T) (m : smat n), (tr (a c* m) == a * tr (m))%T.
  Proof. intros. apply mtrace_mcmul. Qed.

  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (m : mat r c) (a : T) : mat r c := mmulc m a (Tmul:=Tmul).
  Infix "*c" := mmulc : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mmulc_mor : forall r c, Proper (meq ==> Teq ==> meq) (mmulc (r:=r)(c:=c)).
  Proof. apply mmulc_mor. Qed.

  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : T) (m : mat r c), m *c a == a c* m.
  Proof. intros. apply mmulc_eq_mcmul. Qed.

    (** (m *c a) *c b = m *c (a * b) *)
  Lemma mmulc_assoc : forall {r c} (m : mat r c) (a b : T), (m *c a) *c b == m *c (a * b).
  Proof. intros. apply mmulc_assoc. Qed.

  (** (m *c a) *c b = (m *c b) c* a *)
  Lemma mmulc_perm : forall {r c} (m : mat r c) (a b : T), (m *c a) *c b == (m *c b) *c a.
  Proof. intros. apply mmulc_perm. Qed.

  
  (* ==================================== *)
  (** ** Matrix multiplication *)
  Definition mmul {r c s : nat} (m1 : mat r c) (m2 : mat c s) : mat r s :=
    mmul m1 m2 (Tmul:=Tmul)(T0:=T0)(Tadd:=Tadd).
  Infix "*" := mmul : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mmul_mor : forall r c s, Proper (meq ==> meq ==> meq) (@mmul r c s).
  Proof. apply mmul_mor. Qed.

  (** (m1 * m2) * m3 = m1 * (m2 * m3) *)
  Lemma mmul_assoc : forall {r c s t : nat} (m1 : mat r c) (m2 : mat c s) (m3: mat s t), 
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof. intros. apply mmul_assoc. Qed.

  (** m1 * (m2 + m3) = m1 * m2 + m1 * m3 *)
  Lemma mmul_madd_distr_l : forall {r c s : nat} (m1 : mat r c) (m2 m3 : mat c s), 
      m1 * (m2 + m3) == m1 * m2 + m1 * m3.
  Proof. intros. apply mmul_madd_distr_l. Qed.
  
  (** (m1 + m2) * m3 = m1 * m3 + m2 * m3 *)
  Lemma mmul_madd_distr_r : forall {r c s : nat} (m1 m2 : mat r c) (m3 : mat c s),
      (m1 + m2) * m3 == m1 * m3 + m2 * m3.
  Proof. intros. apply mmul_madd_distr_r. Qed.

  (** m1 * (m2 - m3) = m1 * m2 - m1 * m3 *)
  Lemma mmul_msub_distr_l : forall {r c s : nat} (m1 : mat r c) (m2 m3 : mat c s), 
      m1 * (m2 - m3) == m1 * m2 - m1 * m3.
  Proof. intros. apply mmul_msub_distr_l. Qed.
  
  (** (m1 - m2) * m3 = m1 * m3 - m2 * m3 *)
  Lemma mmul_msub_distr_r : forall {r c s : nat} (m1 m2 : mat r c) (m3 : mat c s),
      (m1 - m2) * m3 == m1 * m3 - m2 * m3.
  Proof. intros. apply mmul_msub_distr_r. Qed.

  (** - (m1 * m2) = (-m1) * m2 *)
  Lemma mopp_mmul_l : forall {r c s : nat} (m1 : mat r c) (m2 : mat c s),
      - (m1 * m2) == (-m1) * m2.
  Proof. intros. apply mopp_mmul_l. Qed.

  (** - (m1 * m2) = m1 * (-m2) *)
  Lemma mopp_mmul_r : forall {r c s : nat} (m1 : mat r c) (m2 : mat c s),
      - (m1 * m2) == m1 * (-m2).
  Proof. intros. apply mopp_mmul_r. Qed.

  (** mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c s} (m : mat c s), (@mat0 r c) * m == mat0.
  Proof. intros. apply mmul_0_l. Qed.

  (** m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c s} (m : mat r c), m * (@mat0 c s) == mat0.
  Proof. intros. apply mmul_0_r. Qed.

  (** mat1 * m = m *)
  Lemma mmul_1_l : forall {r c : nat} (m : mat r c), mat1 * m == m.
  Proof. intros. apply mmul_1_l. Qed.

  (** m * mat1 = m *)
  Lemma mmul_1_r : forall {r c : nat} (m : mat r c), m * mat1 == m.
  Proof. intros. apply mmul_1_r. Qed.
  
  (** (a * b) c* m = a c* (b c* m) *)
  Lemma mcmul_mul_assoc : forall {r c} (a b : T) (m : mat r c),
      (a * b)%T c* m == a c* (b c* m).
  Proof. intros. apply mcmul_mul_assoc. Qed.

  (** a c* (m1 * m2) = (a c* m1) * m2. *)
  Lemma mcmul_mmul_assoc_l : forall {r c s} (a : T) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == (a c* m1) * m2.
  Proof. intros. apply mcmul_mmul_assoc_l. Qed.
  
  (** a c* (m1 * m2) = m1 * (a c* m2) *)
  Lemma mcmul_mmul_assoc_r : forall {r c s} (a : T) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == m1 * (a c* m2).
  Proof. intros. apply mcmul_mmul_assoc_r. Qed.
  
  (** (m1 * m2)\T = m2\T * m1\T *)
  Lemma mtrans_mmul : forall {r c s} (m1 : mat r c) (m2 : mat c s),
      (m1 * m2)\T == m2\T * m1\T.
  Proof. intros. apply mtrans_mmul. Qed.

  (** tr (m1 * m2) = tr (m2 * m1) *)
  Lemma mtrace_mmul : forall {r c} (m1 : mat r c) (m2 : mat c r),
      (tr (m1 * m2)%M == tr (m2 * m1)%M)%T.
  Proof. intros. apply mtrace_mmul. Qed.

  
  (* ==================================== *)
  (** ** Hardmard product *)
  
  (** Hardmard product (also known as the element-wise product, entrywise product 
      or Schur product).
      It is a binary operation that takes two matrices of the same dimensions and 
      produces another matrix of the same dimension as the operandds, where each 
      element i,j is the product of elements i,j of the original two matrices.

      The hardmard product is associative, distribute and commutative *)
  Definition mhp {n : nat} (m1 m2 : smat n) : smat n := mhp m1 m2 (Tmul:=Tmul).
  Infix "⦿" := mhp : mat_scope.

  
  (* ==================================== *)
  (** ** Determinant of a matrix *)

  (** Determinant of a square matrix *)
  Definition mdet {n} (m : smat n) : T := @mdet _ Tadd T0 Topp Tmul T1 _ m.

  (** it is a proper morphism *)
  Global Instance mdet_mor (n : nat) : Proper (meq ==> Teq) (@mdet n).
  Proof. apply mdet_mor. Qed.

  (** *** Properties of determinant *)
  Lemma mdet_1 : forall {n}, (@mdet n mat1 == T1)%T.
  Proof. intros. apply mdet_1. Qed.

  Lemma mdet_mtrans : forall {n} (m : smat n), (mdet (m\T) == mdet m)%T.
  Proof. intros. apply mdet_mtrans. Qed.

  Lemma mdet_mmul : forall {n} (m p : smat n), (mdet (m * p)%M == mdet m * mdet p)%T.
  Proof. intros. apply mdet_mmul. Qed.

  (* ==================================== *)
  (** ** Determinant on matrix of 1-,2-, or 3-dim*)

  (** Determinant of a matrix of dimension-1 *)
  Definition mdet1 (m : smat 1) := mdet1 m.

  (** mdet1 m = mdet m *)
  Lemma mdet1_eq_mdet : forall m, (mdet1 m == mdet m)%T.
  Proof. intros. apply mdet1_eq_mdet. Qed.
  
  (** mdet m <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet1_neq0_iff : forall (m : smat 1), (mdet m != T0 <-> m.11 != T0)%T.
  Proof. intros. apply mdet1_neq0_iff. Qed.

  (** Determinant of a matrix of dimension-2 *)
  Definition mdet2 (m : smat 2) := @mdet2 _ Tadd Topp Tmul m.

  (** mdet2 m = mdet m *)
  Lemma mdet2_eq_mdet : forall m, (mdet2 m == mdet m)%T.
  Proof. intros. apply mdet2_eq_mdet. Qed.

  (** mdet m <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet2_neq0_iff : forall (m : smat 2),
      (mdet m != T0 <-> m.11*m.22 - m.12*m.21 != T0)%T.
  Proof. intros. apply mdet2_neq0_iff. Qed.

  (** Determinant of a matrix of dimension-3 *)
  Definition mdet3 (m : smat 3) := @mdet3 _ Tadd Topp Tmul m.

  (** mdet3 m = mdet m *)
  Lemma mdet3_eq_mdet : forall m, (mdet3 m == mdet m)%T.
  Proof. intros. apply mdet3_eq_mdet. Qed.
  
  (** mdet m <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet3_neq0_iff : forall (m : smat 3),
      (mdet m != T0 <->
         m.11 * m.22 * m.33 - m.11 * m.23 * m.32 - 
           m.12 * m.21 * m.33 + m.12 * m.23 * m.31 + 
           m.13 * m.21 * m.32 - m.13 * m.22 * m.31 != T0)%T.
  Proof. intros. apply mdet3_neq0_iff. Qed.
  
  
  (* ==================================== *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix: adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  Definition madj {n} (m : smat n) : smat n := @madj _ Tadd T0 Topp Tmul T1 _ m.

  Global Instance madj_mor (n:nat) : Proper (meq ==> meq) (@madj n).
  Proof. apply madj_mor. Qed.
  

  (* ==================================== *)
  (** ** Invertible matrix *)
  
  (** A square matrix is invertible, if exists an inverse matrix *)
  Definition minvertible {n} (m : smat n) : Prop :=
    exists m' : smat n, (m * m' == mat1) \/ (m' * m == mat1).

  (** invertible mat1 *)
  Lemma minvertible_1 : forall n : nat, @minvertible n mat1.
  Proof. apply minvertible_1. Qed.

  (** A square matrix is invertible, if its determinant is nonzero *)
  Lemma minvertible_iff_mdet_n0 : forall {n} (m : smat n),
      minvertible m <-> mdet m <> T0.
  Proof. intros. apply minvertible_iff_mdet_n0. Qed.

  (** invertible m -> invertible (m\T) *)
  Lemma minvertible_trans : forall n (m : smat n),
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
  (** ** Cramer rule *)
  
  (** Exchange one column of a square matrix *)
  Definition mchgcol {n} (m : smat n) (k : nat) (v : mat n 1) : smat n :=
    mchgcol m k v.
  
  (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid only when D is not zero *)
  Definition cramerRule {n} (a : smat n) (b : mat n 1) : mat n 1 :=
    @cramerRule _ Tadd T0 Topp Tmul T1 Tinv _ a b.

  
  (* ==================================== *)
  (** ** Matrix Inversion *)

  Definition minv {n} (m : smat n) := @minv _ Tadd T0 Topp Tmul T1 Tinv _ m.
  Notation "m ⁻¹" := (minv m) : mat_scope.

  Global Instance minv_mor (n : nat) : Proper (meq ==> meq) (@minv n).
  Proof. apply minv_mor. Qed.
  
  (** m * p = mat1 <-> m ⁻¹ = p *)
  Lemma mmul_eq1_iff_minv_l : forall {n} (m p : smat n),
      m * p == mat1 <-> minv m == p.
  Proof. intros. apply mmul_eq1_iff_minv_l; auto. Qed.

  (** m * p = mat1 <-> p ⁻¹ = m *)
  Lemma mmul_eq1_iff_minv_r : forall {n} (m p : smat n),
      m * p == mat1 <-> minv p == m.
  Proof. intros. apply mmul_eq1_iff_minv_r; auto. Qed.

  (** invertible m -> invertible (m⁻¹) *)
  Lemma minvertible_inv : forall {n} (m : smat n), minvertible m -> minvertible (m⁻¹).
  Proof. intros. apply minvertible_inv; auto. Qed.

  (** m⁻¹ * m = mat1 *)
  Lemma mmul_minv_l : forall n (m : smat n), (minv m) * m == mat1.
  Proof. intros. apply mmul_minv_l. Qed.
  
  (** m * m⁻¹ = mat1 *)
  Lemma mmul_minv_r : forall n (m : smat n), m * m⁻¹ == mat1.
  Proof. intros. apply mmul_minv_r. Qed.

  (** mat1 ⁻¹ = mat1 *)
  Lemma minv_1 : forall n, @minv n mat1 == mat1.
  Proof. intros. apply minv_1. Qed.

  (** m ⁻¹ ⁻¹ = m *)
  Lemma minv_minv : forall n (m : smat n), minvertible m -> m ⁻¹ ⁻¹ == m.
  Proof. intros. apply minv_minv; auto. Qed.

  (** (m * m') ⁻¹ = m' ⁻¹ * m ⁻¹ *)
  Lemma minv_mmul : forall n (m m' : smat n),
      minvertible m -> minvertible m' -> (m * m')⁻¹ == m' ⁻¹ * m ⁻¹.
  Proof. intros. apply minv_mmul; auto. Qed.

  (** (m\T) ⁻¹ = (m ⁻¹)\T *)
  Lemma minv_mtrans : forall n (m : smat n), minvertible m -> (m\T) ⁻¹ == (m ⁻¹)\T.
  Proof. intros. apply minv_mtrans; auto. Qed.
  
  (** mdet (m⁻¹) = 1 / (mdet m) *)
  Lemma mdet_minv : forall {n} (m : smat n), (mdet (m⁻¹) == T1 / (mdet m))%T.
  Proof. intros. apply mdet_minv; auto. Qed.
  

  (* ==================================== *)
  (** ** Inversion matrix of common finite dimension *)
  
  (** Inversion matrix of dimension-1 *)
  Definition minv1 (m : smat 1) : smat 1 := @minv1 _ T0 Tmul T1 Tinv m.

  (** mdet m <> 0 -> minv1 m = inv m *)
  Lemma minv1_eq_inv : forall m, (mdet m != T0)%T -> minv1 m == minv m.
  Proof. intros. apply minv1_eq_inv; auto. Qed.

  (** minv1 m * m = mat1 *)
  Lemma minv1_correct_l : forall (m : smat 1), (mdet m != T0)%T -> (minv1 m) * m == mat1.
  Proof. intros. apply minv1_correct_l; auto. Qed.

  (** m * minv1 m = mat1 *)
  Lemma minv1_correct_r : forall (m : smat 1), (mdet m != T0)%T -> m * (minv1 m) == mat1.
  Proof. intros. apply minv1_correct_r; auto. Qed.

  
  (** Inversion matrix of dimension-2 *)
  Definition minv2 (m : smat 2) : smat 2 := @minv2 _ Tadd T0 Topp Tmul Tinv m.

  (** mdet m <> 0 -> minv2 m = inv m *)
  Lemma minv2_eq_inv : forall m, (mdet m != T0)%T -> minv2 m == minv m.
  Proof. intros. apply minv2_eq_inv; auto. Qed.
  
  (** minv2 m * m = mat1 *)
  Lemma minv2_correct_l : forall (m : smat 2), (mdet m != T0)%T -> (minv2 m) * m == mat1.
  Proof. intros. apply minv2_correct_l; auto. Qed.
  
  (** m * minv2 m = mat1 *)
  Lemma minv2_correct_r : forall (m : smat 2), (mdet m != T0)%T -> m * (minv2 m) == mat1.
  Proof. intros. apply minv2_correct_r; auto. Qed.
  
  (** Inversion matrix of dimension-3 *)
  Definition minv3 (m : smat 3) : smat 3 := @minv3 _ Tadd T0 Topp Tmul Tinv m.
  
  (** mdet m <> 0 -> minv3 m = inv m *)
  Lemma minv3_eq_inv : forall m, (mdet m != T0)%T -> minv3 m == minv m.
  Proof. intros. apply minv3_eq_inv; auto. Qed.
  
  (** minv3 m * m = mat1 *)
  Lemma minv3_correct_l : forall (m : smat 3), (mdet m != T0)%T -> (minv3 m) * m == mat1.
  Proof. intros. apply minv3_correct_l; auto. Qed.
  
  (** m * minv3 m = mat1 *)
  Lemma minv3_correct_r : forall (m : smat 3), (mdet m != T0)%T -> m * (minv3 m) == mat1.
  Proof. intros. apply minv3_correct_r; auto. Qed.

  (** Inversion matrix of dimension-4 *)
  Definition minv4 (m : smat 4) : smat 4 := @minv4 _ Tadd T0 Topp Tmul Tinv m.
  
  (** mdet m <> 0 -> minv4 m = inv m *)
  Lemma minv4_eq_inv : forall m, (mdet m != T0)%T -> minv4 m == minv m.
  Proof. intros. apply minv4_eq_inv; auto. Qed.
  
  (** minv4 m * m = mat1 *)
  Lemma minv4_correct_l : forall (m : smat 4), (mdet m != T0)%T -> (minv4 m) * m == mat1.
  Proof. intros. apply minv4_correct_l; auto. Qed.
  
  (** m * minv4 m = mat1 *)
  Lemma minv4_correct_r : forall (m : smat 4), (mdet m != T0)%T -> m * (minv4 m) == mat1.
  Proof. intros. apply minv4_correct_r; auto. Qed.


  (* ==================================== *)
  (** ** orthogonal matrix *)
  
  (** A square matrix m is an orthogonal matrix *)
  Definition morthogonal {n} (m : smat n) : Prop :=
   (@morthogonal _ Tadd T0 Tmul T1 Teq _ m).

  (** orthogonal m -> invertible m *)
  Lemma morthogonal_invertible : forall {n} (m : smat n),
      morthogonal m -> minvertible m.
  Proof. intros. apply morthogonal_invertible; auto. Qed.

  (** orthogonal m -> m⁻¹ = m\T *)
  Lemma morthogonal_imply_inv_eq_trans : forall {n} (m : smat n),
      morthogonal m -> m⁻¹ == m\T.
  Proof. intros. apply morthogonal_imply_inv_eq_trans; auto. Qed.

  (** m⁻¹ = m\T -> orthogonal m*)
  Lemma minv_eq_trans_imply_morthogonal : forall {n} (m : smat n),
      m⁻¹ == m\T -> morthogonal m.
  Proof. intros. apply minv_eq_trans_imply_morthogonal; auto. Qed.

  (** orthogonal m <-> m\T * m = mat1 *)
  Lemma morthogonal_iff_mul_trans_l : forall {n} (m : smat n),
      morthogonal m <-> m\T * m == mat1.
  Proof. intros. apply morthogonal_iff_mul_trans_l; auto. Qed.

  (** orthogonal m <-> m * m\T = mat1 *)
  Lemma morthogonal_iff_mul_trans_r : forall {n} (m : smat n),
      morthogonal m <-> m * m\T == mat1.
  Proof. intros. apply morthogonal_iff_mul_trans_r; auto. Qed.

  (** orthogonal mat1 *)
  Lemma morthogonal_1 : forall {n}, morthogonal (@mat1 n).
  Proof. intros. apply morthogonal_1; auto. Qed.

  (** orthogonal m -> orthogonal p -> orthogonal (m * p) *)
  Lemma morthogonal_mul : forall {n} (m p : smat n),
      morthogonal m -> morthogonal p -> morthogonal (m * p).
  Proof. intros. apply morthogonal_mul; auto. Qed.

  (** orthogonal m -> orthogonal m\T *)
  Lemma morthogonal_mtrans : forall {n} (m : smat n), morthogonal m -> morthogonal (m\T).
  Proof. intros. apply morthogonal_mtrans; auto. Qed.

  (** orthogonal m -> orthogonal m⁻¹ *)
  Lemma morthogonal_minv : forall {n} (m : smat n), morthogonal m -> morthogonal (m⁻¹).
  Proof. intros. apply morthogonal_minv; auto. Qed.

  (* (** orthogonal m -> |m| = ± 1 *) *)
  (* Lemma morthogonal_mdet : forall {n} (m : smat n) (HDec : Dec Teq), *)
  (*     morthogonal m -> (mdet m == T1 \/ mdet m == - (T1))%T. *)
  (* Proof. intros. apply morthogonal_mdet; auto. Qed. *)

  
  (* ==================================== *)
  (** ** O(n): General Orthogonal Group, General Linear Group *)
  
  (** The set of GOn *)
  Definition GOn (n : nat) := (@GOn _ Tadd T0 Tmul T1 Teq n).

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
      m⁻¹ == m\T.
  Proof. intros. apply GOn_imply_inv_eq_trans. Qed.
  
  (* ==================================== *)
  (** ** SO(n): Special Orthogonal Group, Rotation Group *)

  (** The set of SOn *)
  Definition SOn (n: nat) := (@SOn _ Tadd T0 Topp Tmul T1 Teq n).

  Definition mk_SOn {n : nat} (m : smat n) (H : morthogonal m /\ (mdet m == T1)%T)
    : SOn n := Build_SOn n m H.

  Definition SOn_eq {n} (s1 s2 : SOn n) : Prop := SOn_mat _ s1 == SOn_mat _ s2.

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
      m⁻¹ == m\T.
  Proof. intros. apply SOn_imply_inv_eq_trans. Qed.

  
  (* ==================================== *)
  (** ** Other un-sorted properties *)
  

  (* (** k * m = 0 -> (m = 0) \/ (k = 0) *) *)
  (* Axiom mcmul_eq0_imply_m0_or_k0 : forall {r c} (m : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     (k c* m == m0) -> (m == m0) \/ (k == T0)%T. *)

  (* (** (m <> 0 \/ k * m = 0) -> k = 0 *) *)
  (* Axiom mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     ~(m == m0) -> k c* m == m0 -> (k == T0)%T. *)

  (* (** k * m = m -> k = 1 \/ m = 0 *) *)
  (* Axiom mcmul_same_imply_coef1_or_mzero : forall {r c} k (m : mat r c), *)
  (*     k c* m == m -> (k == T1)%T \/ (m == mat0 r c). *)

  (* (** (m1 <> 0 /\ m2 <> 0 /\ k * m1 = m2) -> k <> 0 *) *)
  (* Axiom mcmul_eq_mat_implfy_not_k0 : forall {r c} (m1 m2 : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     ~(m1 == m0) -> ~(m2 == m0) -> k c* m1 == m2 -> ~(k == T0)%T. *)
  
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
    @minv_gauss T Tadd T0 Topp Tmul T1 Tinv _ _ _ m.
  
End DecidableFieldMatrixTheory.
