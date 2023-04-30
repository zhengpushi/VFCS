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

  (** Basic library *)
  (* Export BasicConfig TupleExt. *)

  
  (* ==================================== *)
  (** ** Matrix element type *)
  Export E.

  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "!=" := (fun l1 l2 => ~(l1 == l2)%list) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "!=" := (fun d1 d2 => ~(d1 == d2)%dlist) : dlist_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.
  

  (* ==================================== *)
  (** ** Matrix type and basic operations *)
  Definition mat r c : Type := @mat A r c.

  (** square matrix *)
  Notation smat n := (smat A n).

  (** Convert between function and matrix *)
  Definition f2m {r c} (f : nat -> nat -> A) : mat r c := f2m f.
  Definition m2f {r c} (m : mat r c) : nat -> nat -> A := m2f m.

  (** matrix equality *)
  Definition meq {r c} (m1 m2 : mat r c) : Prop := meq (Aeq:=Aeq) m1 m2.
  Infix "==" := meq : mat_scope.
  Infix "!=" := (fun m1 m2 => ~(m1 == m2)%M) : mat_scope.

  (** meq is equivalence relation *)
  Lemma meq_equiv : forall r c, Equivalence (meq (r:=r) (c:=c)).
  Proof. apply meq_equiv. Qed.

  (** Get element of a matrix (nth means n-th) *)
  Definition mnth {r c} (m : mat r c) (i j : nat) : A := mnth Azero m i j.
  Notation "m $ i $ j " := (matf (A:=A) m i j) : mat_scope.
  Notation "m ! i ! j " := (mnth m i j) : mat_scope.

  Notation "m .00" := (m $ 0 $ 0) : mat_scope.
  Notation "m .00" := (m $ 0 $ 0) : mat_scope.
  Notation "m .01" := (m $ 0 $ 1) : mat_scope.
  Notation "m .02" := (m $ 0 $ 2) : mat_scope.
  Notation "m .03" := (m $ 0 $ 3) : mat_scope.
  Notation "m .10" := (m $ 1 $ 0) : mat_scope.
  Notation "m .11" := (m $ 1 $ 1) : mat_scope.
  Notation "m .12" := (m $ 1 $ 2) : mat_scope.
  Notation "m .13" := (m $ 1 $ 3) : mat_scope.
  Notation "m .20" := (m $ 2 $ 0) : mat_scope.
  Notation "m .21" := (m $ 2 $ 1) : mat_scope.
  Notation "m .22" := (m $ 2 $ 2) : mat_scope.
  Notation "m .23" := (m $ 2 $ 3) : mat_scope.
  Notation "m .30" := (m $ 3 $ 0) : mat_scope.
  Notation "m .31" := (m $ 3 $ 1) : mat_scope.
  Notation "m .32" := (m $ 3 $ 2) : mat_scope.
  Notation "m .33" := (m $ 3 $ 3) : mat_scope.


  (** mnth is equal to mnthRaw *)
  Lemma mnth_eq_mnthRaw : forall {r c : nat} (m : mat r c),
    forall i j, i < r -> j < c -> (m!i!j == m$i$j)%A.
  Proof. intros. apply mnth_eq_mnth_raw; auto. Qed.
  
  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (mnth m1 ri ci == mnth m2 ri ci)%A).
  Proof. intros. apply meq_iff_mnth. Qed.


  (* ==================================== *)
  (** ** Convert between list list and matrix *)

  (** dlist to matrix with specified row and column numbers *)
  Definition l2m {r c} (dl : dlist A) : mat r c := l2m Azero dl.
  
  (** mat to dlist *)
  Definition m2l {r c} (m : mat r c) : dlist A := m2l m.

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof. intros. apply m2l_length. Qed.
  
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof. intros. apply m2l_width. Qed.

  Lemma l2m_m2l_id : forall {r c} (m : mat r c), (@l2m r c (m2l m)) == m.
  Proof. intros. apply l2m_m2l_id. Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : dlist A),
      length dl = r -> width dl c -> (m2l (@l2m r c dl) == dl)%dlist.
  Proof. intros. apply m2l_l2m_id; auto. Qed.

  Lemma l2m_inj : forall {r c} (d1 d2 : dlist A),
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      ~(d1 == d2)%dlist -> ~(@l2m r c d1 == l2m d2).
  Proof. intros. apply l2m_inj; auto. Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m d == m).
  Proof. intros. apply l2m_surj. Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist.
  Proof. intros. apply (m2l_inj (Azero:=Azero)); auto. Qed.
  
  Lemma m2l_surj : forall {r c} (d : dlist A),
      length d = r -> width d c -> (exists m : mat r c, (m2l m == d)%dlist).
  Proof. intros. apply (m2l_surj (Azero:=Azero)); auto. Qed.

  
  (* ==================================== *)
  (** ** matrix shift *)

  (** left shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *)
  Definition mcshl {r c} (m : mat r c) (k : nat) : mat r c := mcshl m k.

  (** right shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *)
  Definition mcshr {r c} (m : mat r c) (k : nat) : mat r c := mcshr m k (Azero:=Azero).

  (** left loop shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *)
  Definition mclshl {r c} (m : mat r c) (k : nat) : mat r c := mclshl m k.

  (** right shift column *)
  Definition mclshr {r c} (m : mat r c) (k : nat) : mat r c := mclshr m k.

  
  (* ==================================== *)
  (** ** Diagonal matrix *)

  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (m : smat n) : Prop := mdiag m (Aeq:=Aeq)(Azero:=Azero).

  (** Construct a diagonal matrix *)
  Definition mk_diag {n} (l : list A) : smat n := mk_diag l (Azero:=Azero).

  (** mk_diag is correct *)
  Lemma mk_diag_spec : forall {n} (l : list A), mdiag (@mk_diag n l).
  Proof. intros. apply mk_diag_spec. Qed.

  
  (* ==================================== *)
  (** ** Construct matrix with one-row or one-column matrix and another matrix *)
  (* Notation rvec n := (@mat A 1 n). *)
  (* Notation cvec n := (@mat A n 1). *)

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
    mk_mat_0_c c (Azero:=Azero).
  Definition mk_mat_1_1 (a11 : A) : mat 1 1 :=
    mk_mat_1_1 a11 (Azero:=Azero).
  Definition mk_mat_1_2 (a11 a12 : A) : mat 1 2 :=
    mk_mat_1_2 a11 a12 (Azero:=Azero).
  Definition mk_mat_1_3 (a11 a12 a13 : A) : mat 1 3 :=
    mk_mat_1_3 a11 a12 a13 (Azero:=Azero).
  Definition mk_mat_1_4 (a11 a12 a13 a14 : A) : mat 1 4 :=
    mk_mat_1_4 a11 a12 a13 a14 (Azero:=Azero).
  Definition mk_mat_1_c c (l : list A) : mat 1 c :=
    mk_mat_1_c c l (Azero:=Azero).
  
  Definition mk_mat_r_0 r : mat r 0 :=
    mk_mat_r_0 r (Azero:=Azero).
  Definition mk_mat_2_1 (a11 a21 : A) : mat 2 1 :=
    mk_mat_2_1 a11 a21 (Azero:=Azero).
  Definition mk_mat_3_1 (a11 a21 a31 : A) : mat 3 1 :=
    mk_mat_3_1 a11 a21 a31 (Azero:=Azero).
  Definition mk_mat_4_1 (a11 a21 a31 a41 : A) : mat 4 1 :=
    mk_mat_4_1 a11 a21 a31 a41 (Azero:=Azero).
  Definition mk_mat_r_1 r (l : list A) : mat r 1 :=
    mk_mat_r_1 r l (Azero:=Azero).

  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2 :=
    mk_mat_2_2 a11 a12 a21 a22 (Azero:=Azero).
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 :=
    mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 (Azero:=Azero).
  Definition mk_mat_4_4 (a11 a12 a13 a14 a21 a22 a23 a24
                           a31 a32 a33 a34 a41 a42 a43 a44 : A) : mat 4 4 :=
    mk_mat_4_4
      a11 a12 a13 a14
      a21 a22 a23 a24
      a31 a32 a33 a34
      a41 a42 a43 a44 (Azero:=Azero).

  
  (* ==================================== *)
  (** ** Convert between tuples and matrix *)
  
  (** Tuples 2x2 -> mat_2x2 *)
  Definition t2m_2_2 (t : @T_2_2 A) : mat 2 2 := t2m_2_2 Azero t.

  (** Tuples 3x3 -> mat_3x3 *)
  Definition t2m_3_3 (t : @T_3_3 A) : mat 3 3 := t2m_3_3 Azero t.

  (** m[0,0]: mat_1x1 -> A *)
  Definition m2t_1_1 (m : mat 1 1) := m2t_1_1 m.
  Definition scalar_of_mat (m : mat 1 1) := scalar_of_mat m.

  (** mat_2x2 -> tuple 2x2. That is: ((a11,a12),(a21,a22)) *)
  Definition m2t_2_2 (m : mat 2 2) : @T_2_2 A := m2t_2_2 m.

  (** mat_3x3 -> tuple 3x3. That is: ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) *)
  Definition m2t_3_3 (m : mat 3 3) : @T_3_3 A := m2t_3_3 m.

  
  (* ==================================== *)
  (** ** Mapping of matrix *)

  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c := mmap f m.
  
  Definition mmap2 {r c} (f : A -> A -> A) (m1 m2 : mat r c) : mat r c :=
    mmap2 f m1 m2.

  Lemma mmap2_comm : forall {r c} (f : A -> A -> A) (m1 m2 : mat r c)
                            {Comm : Commutative f Aeq}, 
      mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof. intros. apply mmap2_comm; auto. Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A) (m1 m2 m3 : mat r c)
                             {Assoc : Associative f Aeq}, 
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
  Proof. intros. apply (mtrans_diag (Azero:=Azero)); auto. Qed.

End BasicMatrixTheory.



(* ######################################################################### *)
(** * Ring matrix theory *)
Module RingMatrixTheory (E : RingElementType).
  Include (BasicMatrixTheory E).

  Infix "+" := (ladd (Aadd:=Aadd)) : list_scope.
  Notation seqsum := (seqsum (Aadd:=Aadd) (Azero:=Azero)).

  
  (* ==================================== *)
  (** ** Zero matrirx and identity matrix *)

  (** Zero matrix *)
  Definition mat0 {r c : nat} : mat r c := mat0 Azero.

  (** Identity matrix *)
  Definition mat1 {n : nat} : mat n n := mat1 Azero Aone.

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
      i < n -> j < n -> i <> j -> ((@mat1 n) $ i $ j == Azero)%A.
  Proof. intros. apply mnth_mat1_diff; auto. Qed.

  (** i < n -> mat1[i,i] = 1 *)
  Lemma mnth_mat1_same : forall {n} i, i < n -> ((@mat1 n) $ i $ i == Aone)%A.
  Proof. intros. apply mnth_mat1_same; auto. Qed.


  (* ==================================== *)
  (** ** Matrix trace *)
  Definition mtrace {n : nat} (m : smat n) : A := mtrace m (Aadd:=Aadd)(Azero:=Azero).
  Notation "'tr' m" := (mtrace m) : mat_scope.
  
  (** show it is a proper morphism *)
  Global Instance mtrace_mor : forall n, Proper (meq ==> Aeq) (mtrace (n:=n)).
  Proof. apply mtrace_mor. Qed.

  (** tr(m\T) = tr(m) *)
  Lemma mtrace_trans : forall {n} (m : smat n), (tr (m\T) == tr(m))%A.
  Proof. intros. apply mtrace_trans. Qed.


  (* ==================================== *)
  (** ** Matrix addition *)
  
  Definition madd {r c} (m1 m2 : mat r c) : mat r c := madd m1 m2 (Aadd:=Aadd).
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
      ((m1 + m2)%M ! i ! j == (m1!i!j) + (m2!i!j))%A.
  Proof. intros. apply madd_nth. Qed.

  (* (** (m1 + m2)[i] = m1[i] + m2[i] *) *)
  (* Lemma mrow_madd : forall {r c} i (m1 m2 : mat r c), *)
  (*     i < r -> (mrow i (m1 + m2)%M == ((mrow i m1) + (mrow i m2))%list)%list. *)

  (** (m1 + m2)\T = m1\T + m2\T *)
  Lemma mtrans_madd : forall {r c} (m1 m2 : mat r c), (m1 + m2)\T == m1\T + m2\T.
  Proof. intros. apply mtrans_madd. Qed.

  (** tr(m1 + m2) = tr(m1) + tr(m2) *)
  Lemma mtrace_madd : forall {n} (m1 m2 : smat n), (tr (m1 + m2)%M == tr(m1) + tr(m2))%A.
  Proof. intros. apply mtrace_madd. Qed.

  
  (* ==================================== *)
  (** ** Monoid structure over {madd,mat0,meq} *)
  Global Instance Monoid_MatAadd : forall r c, Monoid (@madd r c) mat0 meq.
  Proof. apply Monoid_MatAadd. Qed.

  Section test.
    Goal forall r c (m1 m2 : mat r c), mat0 + m1 == m1.
      monoid_simp. Qed.
  End test.

  
  (* ==================================== *)
  (** ** Matrix opposition *)
  
  Definition mopp {r c} (m : mat r c) : mat r c := mopp m (Aopp:=Aopp).
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
  Lemma mtrace_mopp : forall {n} (m : smat n), (tr((-m)%M) == - (tr(m)))%A.
  Proof. intros. apply mtrace_mopp. Qed.

  
  (* ==================================== *)
  (** ** Matrix subtraction *)
  
  Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
    msub m1 m2 (Aadd:=Aadd)(Aopp:=Aopp).
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
      (tr ((m1 - m2)%M) == tr(m1) - tr(m2))%A.
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
  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c := mcmul a m (Amul:=Amul).
  Infix "c*" := mcmul : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mcmul_mor : forall r c, Proper (Aeq ==> meq ==> meq) (mcmul (r:=r)(c:=c)).
  Proof. apply mcmul_mor. Qed.

  (** 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), Azero c* m == mat0.
  Proof. intros. apply mcmul_0_l. Qed.

  (** a c* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a c* (@mat0 r c) == mat0.
  Proof. intros. apply mcmul_0_r. Qed.

  (** 1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), Aone c* m == m.
  Proof. intros. apply mcmul_1_l. Qed.

  (** a c* mat1 equal to a diagonal matrix which main diagonal elements all are a *)
  Lemma mcmul_1_r : forall {n} a,
      a c* (@mat1 n) == mk_mat (fun i j => if (i =? j)%nat then a else Azero).
  Proof. intros. apply mcmul_1_r. Qed.

  (** a c* (b c* m) = (a * b) c* m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == (a * b) c* m.
  Proof. intros. apply mcmul_assoc. Qed.

  (** a c* (b c* m) = b c* (a c* m) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == b c* (a c* m).
  Proof. intros. apply mcmul_perm. Qed.

  (** (a + b) c* m = (a c* m) + (b c* m) *)
  Lemma mcmul_add_distr : forall {r c} (a b : A) (m : mat r c), 
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof. intros. apply mcmul_add_distr. Qed.

  (** a c* (m1 + m2) = (a c* m1) + (a c* m2) *)
  Lemma mcmul_madd_distr : forall {r c} (a : A) (m1 m2 : mat r c), 
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof. intros. apply mcmul_madd_distr. Qed.
  
  (** - (a c* m) = (-a) c* m *)
  Lemma mopp_mcmul : forall {r c} a (m : mat r c), - (a c* m) == (-a)%A c* m.
  Proof. intros. apply mopp_mcmul. Qed.

  (** a c* (m1 - m2) = (a c* m1) - (a c* m2) *)
  Lemma mcmul_msub : forall {r c} a (m1 m2 : mat r c),
      a c* (m1 - m2) == (a c* m1) - (a c* m2).
  Proof. intros. apply mcmul_msub. Qed.

  (** (a c* m)\T = a c* (m\T) *)
  Lemma mtrans_mcmul : forall {r c} (a : A) (m : mat r c), (a c* m)\T == a c* (m\T).
  Proof. intros. apply mtrans_mcmul. Qed.

  (** tr (a c* m) = a * tr (m) *)
  Lemma mtrace_mcmul : forall {n} (a : A) (m : smat n), (tr (a c* m) == a * tr (m))%A.
  Proof. intros. apply mtrace_mcmul. Qed.

  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c := mmulc m a (Amul:=Amul).
  Infix "*c" := mmulc : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mmulc_mor : forall r c, Proper (meq ==> Aeq ==> meq) (mmulc (r:=r)(c:=c)).
  Proof. apply mmulc_mor. Qed.

  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
  Proof. intros. apply mmulc_eq_mcmul. Qed.

    (** (m *c a) *c b = m *c (a * b) *)
  Lemma mmulc_assoc : forall {r c} (m : mat r c) (a b : A), (m *c a) *c b == m *c (a * b).
  Proof. intros. apply mmulc_assoc. Qed.

  (** (m *c a) *c b = (m *c b) c* a *)
  Lemma mmulc_perm : forall {r c} (m : mat r c) (a b : A), (m *c a) *c b == (m *c b) *c a.
  Proof. intros. apply mmulc_perm. Qed.

  
  (* ==================================== *)
  (** ** Matrix multiplication *)
  Definition mmul {r c s : nat} (m1 : mat r c) (m2 : mat c s) : mat r s :=
    mmul m1 m2 (Amul:=Amul)(Azero:=Azero)(Aadd:=Aadd).
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
  Lemma mcmul_mul_assoc : forall {r c} (a b : A) (m : mat r c),
      (a * b)%A c* m == a c* (b c* m).
  Proof. intros. apply mcmul_mul_assoc. Qed.

  (** a c* (m1 * m2) = (a c* m1) * m2. *)
  Lemma mcmul_mmul_assoc_l : forall {r c s} (a : A) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == (a c* m1) * m2.
  Proof. intros. apply mcmul_mmul_assoc_l. Qed.
  
  (** a c* (m1 * m2) = m1 * (a c* m2) *)
  Lemma mcmul_mmul_assoc_r : forall {r c s} (a : A) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == m1 * (a c* m2).
  Proof. intros. apply mcmul_mmul_assoc_r. Qed.
  
  (** (m1 * m2)\T = m2\T * m1\T *)
  Lemma mtrans_mmul : forall {r c s} (m1 : mat r c) (m2 : mat c s),
      (m1 * m2)\T == m2\T * m1\T.
  Proof. intros. apply mtrans_mmul. Qed.

  (** tr (m1 * m2) = tr (m2 * m1) *)
  Lemma mtrace_mmul : forall {r c} (m1 : mat r c) (m2 : mat c r),
      (tr (m1 * m2)%M == tr (m2 * m1)%M)%A.
  Proof. intros. apply mtrace_mmul. Qed.

  
  (* ==================================== *)
  (** ** Hardmard product *)
  
  (** Hardmard product (also known as the element-wise product, entrywise product 
      or Schur product).
      It is a binary operation that takes two matrices of the same dimensions and 
      produces another matrix of the same dimension as the operandds, where each 
      element i,j is the product of elements i,j of the original two matrices.

      The hardmard product is associative, distribute and commutative *)
  Definition mhp {n : nat} (m1 m2 : smat n) : smat n := mhp m1 m2 (Amul:=Amul).
  Infix "⦿" := mhp : mat_scope.

  
  (* ==================================== *)
  (** ** Determinant of a matrix *)

  (** Determinant of a square matrix *)
  Definition mdet {n} (m : smat n) : A := @mdet _ Aadd Azero Aopp Amul Aone _ m.

  (** it is a proper morphism *)
  Global Instance mdet_mor (n : nat) : Proper (meq ==> Aeq) (@mdet n).
  Proof. apply mdet_mor. Qed.

  (** *** Properties of determinant *)
  Lemma mdet_1 : forall {n}, (@mdet n mat1 == Aone)%A.
  Proof. intros. apply mdet_1. Qed.

  Lemma mdet_mtrans : forall {n} (m : smat n), (mdet (m\T) == mdet m)%A.
  Proof. intros. apply mdet_mtrans. Qed.

  Lemma mdet_mmul : forall {n} (m p : smat n), (mdet (m * p)%M == mdet m * mdet p)%A.
  Proof. intros. apply mdet_mmul. Qed.

  (* ==================================== *)
  (** ** Determinant on matrix of 1-,2-, or 3-dim*)

  (** Determinant of a matrix of dimension-1 *)
  Definition mdet1 (m : smat 1) := mdet1 m.

  (** mdet1 m = mdet m *)
  Lemma mdet1_eq_mdet : forall m, (mdet1 m == mdet m)%A.
  Proof. intros. apply mdet1_eq_mdet. Qed.
  
  (** mdet m <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet1_neq0_iff : forall (m : smat 1), (mdet m != Azero <-> m.00 != Azero)%A.
  Proof. intros. apply mdet1_neq0_iff. Qed.

  (** Determinant of a matrix of dimension-2 *)
  Definition mdet2 (m : smat 2) := @mdet2 _ Aadd Aopp Amul m.

  (** mdet2 m = mdet m *)
  Lemma mdet2_eq_mdet : forall m, (mdet2 m == mdet m)%A.
  Proof. intros. apply mdet2_eq_mdet. Qed.

  (** mdet m <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet2_neq0_iff : forall (m : smat 2),
      (mdet m != Azero <-> m.00*m.11 - m.01*m.10 != Azero)%A.
  Proof. intros. apply mdet2_neq0_iff. Qed.

  (** Determinant of a matrix of dimension-3 *)
  Definition mdet3 (m : smat 3) := @mdet3 _ Aadd Aopp Amul m.

  (** mdet3 m = mdet m *)
  Lemma mdet3_eq_mdet : forall m, (mdet3 m == mdet m)%A.
  Proof. intros. apply mdet3_eq_mdet. Qed.
  
  (** mdet m <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet3_neq0_iff : forall (m : smat 3),
      (mdet m != Azero <->
         m.00 * m.11 * m.22 - m.00 * m.12 * m.21 - 
           m.01 * m.10 * m.22 + m.01 * m.12 * m.20 + 
           m.02 * m.10 * m.21 - m.02 * m.11 * m.20 != Azero)%A.
  Proof. intros. apply mdet3_neq0_iff. Qed.
  
  
  (* ==================================== *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix: adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  Definition madj {n} (m : smat n) : smat n := @madj _ Aadd Azero Aopp Amul Aone _ m.

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
      minvertible m <-> mdet m <> Azero.
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
    @cramerRule _ Aadd Azero Aopp Amul Aone Ainv _ a b.

  
  (* ==================================== *)
  (** ** Matrix Inversion *)

  Definition minv {n} (m : smat n) := @minv _ Aadd Azero Aopp Amul Aone Ainv _ m.
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
  Lemma mdet_minv : forall {n} (m : smat n), (mdet (m⁻¹) == Aone / (mdet m))%A.
  Proof. intros. apply mdet_minv; auto. Qed.
  

  (* ==================================== *)
  (** ** Inversion matrix of common finite dimension *)
  
  (** Inversion matrix of dimension-1 *)
  Definition minv1 (m : smat 1) : smat 1 := @minv1 _ Azero Amul Aone Ainv m.

  (** mdet m <> 0 -> minv1 m = inv m *)
  Lemma minv1_eq_inv : forall m, (mdet m != Azero)%A -> minv1 m == minv m.
  Proof. intros. apply minv1_eq_inv; auto. Qed.

  (** minv1 m * m = mat1 *)
  Lemma minv1_correct_l : forall (m : smat 1), (mdet m != Azero)%A -> (minv1 m) * m == mat1.
  Proof. intros. apply minv1_correct_l; auto. Qed.

  (** m * minv1 m = mat1 *)
  Lemma minv1_correct_r : forall (m : smat 1), (mdet m != Azero)%A -> m * (minv1 m) == mat1.
  Proof. intros. apply minv1_correct_r; auto. Qed.

  
  (** Inversion matrix of dimension-2 *)
  Definition minv2 (m : smat 2) : smat 2 := @minv2 _ Aadd Azero Aopp Amul Ainv m.

  (** mdet m <> 0 -> minv2 m = inv m *)
  Lemma minv2_eq_inv : forall m, (mdet m != Azero)%A -> minv2 m == minv m.
  Proof. intros. apply minv2_eq_inv; auto. Qed.
  
  (** minv2 m * m = mat1 *)
  Lemma minv2_correct_l : forall (m : smat 2), (mdet m != Azero)%A -> (minv2 m) * m == mat1.
  Proof. intros. apply minv2_correct_l; auto. Qed.
  
  (** m * minv2 m = mat1 *)
  Lemma minv2_correct_r : forall (m : smat 2), (mdet m != Azero)%A -> m * (minv2 m) == mat1.
  Proof. intros. apply minv2_correct_r; auto. Qed.
  
  (** Inversion matrix of dimension-3 *)
  Definition minv3 (m : smat 3) : smat 3 := @minv3 _ Aadd Azero Aopp Amul Ainv m.
  
  (** mdet m <> 0 -> minv3 m = inv m *)
  Lemma minv3_eq_inv : forall m, (mdet m != Azero)%A -> minv3 m == minv m.
  Proof. intros. apply minv3_eq_inv; auto. Qed.
  
  (** minv3 m * m = mat1 *)
  Lemma minv3_correct_l : forall (m : smat 3), (mdet m != Azero)%A -> (minv3 m) * m == mat1.
  Proof. intros. apply minv3_correct_l; auto. Qed.
  
  (** m * minv3 m = mat1 *)
  Lemma minv3_correct_r : forall (m : smat 3), (mdet m != Azero)%A -> m * (minv3 m) == mat1.
  Proof. intros. apply minv3_correct_r; auto. Qed.

  (** Inversion matrix of dimension-4 *)
  Definition minv4 (m : smat 4) : smat 4 := @minv4 _ Aadd Azero Aopp Amul Ainv m.
  
  (** mdet m <> 0 -> minv4 m = inv m *)
  Lemma minv4_eq_inv : forall m, (mdet m != Azero)%A -> minv4 m == minv m.
  Proof. intros. apply minv4_eq_inv; auto. Qed.
  
  (** minv4 m * m = mat1 *)
  Lemma minv4_correct_l : forall (m : smat 4), (mdet m != Azero)%A -> (minv4 m) * m == mat1.
  Proof. intros. apply minv4_correct_l; auto. Qed.
  
  (** m * minv4 m = mat1 *)
  Lemma minv4_correct_r : forall (m : smat 4), (mdet m != Azero)%A -> m * (minv4 m) == mat1.
  Proof. intros. apply minv4_correct_r; auto. Qed.

  (* (** k * m = 0 -> (m = 0) \/ (k = 0) *) *)
  (* Axiom mcmul_eq0_imply_m0_or_k0 : forall {r c} (m : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     (k c* m == m0) -> (m == m0) \/ (k == Azero)%A. *)

  (* (** (m <> 0 \/ k * m = 0) -> k = 0 *) *)
  (* Axiom mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     ~(m == m0) -> k c* m == m0 -> (k == Azero)%A. *)

  (* (** k * m = m -> k = 1 \/ m = 0 *) *)
  (* Axiom mcmul_same_imply_coef1_or_mzero : forall {r c} k (m : mat r c), *)
  (*     k c* m == m -> (k == Aone)%A \/ (m == mat0 r c). *)

  (* (** (m1 <> 0 /\ m2 <> 0 /\ k * m1 = m2) -> k <> 0 *) *)
  (* Axiom mcmul_eq_mat_implfy_not_k0 : forall {r c} (m1 m2 : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     ~(m1 == m0) -> ~(m2 == m0) -> k c* m1 == m2 -> ~(k == Azero)%A. *)
  
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
    @minv_gauss A Aadd Azero Aopp Amul Aone Ainv _ _ _ m.
  
End DecidableFieldMatrixTheory.
