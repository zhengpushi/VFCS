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
 *)


Require Export Matrix.
Require Export MatrixDet.
Require Export MatrixInv.
Require Export MatrixOrth.
Require Export ElementType.


(* ######################################################################### *)
(** * Basic matrix theory *)

Module BasicMatrixTheory (E : ElementType).

  (* ======================================================================= *)
  (** ** Matrix element type *)
  Export E.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.
  

  (* ======================================================================= *)
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

  (** Get n-th element of a matrix *)
  (* M $ i $ j *)

  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (M1 M2 : mat r c),
      M1 = M2 <-> (forall i j, M1 $ i $ j = M2 $ i $ j).
  Proof. intros. apply meq_iff_mnth. Qed.


  (* ======================================================================= *)
  (** ** Convert between dlist and matrix *)

  Definition l2m {r c} (dl : dlist A) : mat r c := l2m Azero dl.
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
      @l2m r c d1 = l2m d2 -> d1 = d2.
  Proof. intros. apply l2m_inj in H3; auto. Qed.
  
  Lemma l2m_surj : forall {r c} (M : mat r c), (exists d, l2m d = M).
  Proof. intros. apply l2m_surj. Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), m2l m1 = m2l m2 -> m1 = m2.
  Proof. intros. apply m2l_inj; auto. Qed.
  
  Lemma m2l_surj : forall {r c} (d : dlist A),
      length d = r -> width d c -> (exists M : mat r c, m2l M = d).
  Proof. intros. apply (m2l_surj Azero); auto. Qed.

  
  (* ======================================================================= *)
  (** ** Construct matrix with vector and matrix *)

  (** Construct a matrix by rows *)
  Definition mconsr {r c} (V : vec c) (M : mat r c) : mat (S r) c :=
    mconsr Azero V M.

  (** Construct a matrix by columns *)
  Definition mconsc {r c} (V : vec r) (M : mat r c) : mat r (S c) :=
    mconsc Azero V M.

  
  (* ======================================================================= *)
  (** ** Construct matrix with two matrices *)
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (M1 : mat r1 c) (M2 : mat r2 c) : mat (r1 + r2) c :=
    mappr (Azero:=Azero) M1 M2.
  
  (** Append matrix by column *)
  Definition mappc {r c1 c2} (M1 : mat r c1) (M2 : mat r c2) : mat r (c1 + c2) :=
    mappc (Azero:=Azero) M1 M2.

  
  (* ======================================================================= *)
  (** ** Make concrete matrix *)

  Definition mkmat_0_c c : mat 0 c := mkmat_0_c c (Azero:=Azero).
  Definition mkmat_r_0 r : mat r 0 := mkmat_r_0 r (Azero:=Azero).
  
  Definition mkmat_1_1 a11 : mat 1 1 := mkmat_1_1 a11 (Azero:=Azero).
  Definition mkmat_1_c c (v : vec c) : mat 1 c := mkmat_1_c c v.
  Definition mkmat_r_1 r (v : vec r) : mat r 1 := mkmat_r_1 r v.
  
  Definition mkmat_1_2 a11 a12 : mat 1 2 := mkmat_1_2 a11 a12 (Azero:=Azero).
  Definition mkmat_2_1 a11 a21 : mat 2 1 := mkmat_2_1 a11 a21 (Azero:=Azero).
  Definition mkmat_2_2 a11 a12 a21 a22 : mat 2 2 :=
    mkmat_2_2 a11 a12 a21 a22 (Azero:=Azero).
  
  Definition mkmat_1_3 a11 a12 a13 : mat 1 3 :=
    mkmat_1_3 a11 a12 a13 (Azero:=Azero).
  Definition mkmat_3_1 a11 a21 a31 : mat 3 1 :=
    mkmat_3_1 a11 a21 a31 (Azero:=Azero).
  Definition mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
    mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 (Azero:=Azero).
  
  Definition mkmat_1_4 a11 a12 a13 a14 : mat 1 4 :=
    mkmat_1_4 a11 a12 a13 a14 (Azero:=Azero).
  Definition mkmat_4_1 a11 a21 a31 a41 : mat 4 1 :=
    mkmat_4_1 a11 a21 a31 a41 (Azero:=Azero).
  Definition mkmat_4_4 a11 a12 a13 a14 a21 a22 a23 a24
    a31 a32 a33 a34 a41 a42 a43 a44 : mat 4 4 :=
    mkmat_4_4
      a11 a12 a13 a14
      a21 a22 a23 a24
      a31 a32 a33 a34
      a41 a42 a43 a44 (Azero:=Azero).

  
  (* ======================================================================= *)
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

  
  (* ======================================================================= *)
  (** ** Diagonal Matrix *)
  
  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (m : smat n) : Prop := mdiag Azero m.

  (** Construct a diagonal matrix *)
  Definition mdiagMk {n} (v : vec n) : smat n := mdiagMk Azero v.

  (** mdiagMk is correct *)
  Lemma mdiagMk_spec : forall {n} (v : vec n), mdiag (mdiagMk v).
  Proof. intros. apply mdiagMk_spec. Qed.

  (** (mdiagMk v)[i,i] = l[i] *)
  Lemma mnth_mdiagMk_same : forall {n} (v : vec n) i, (mdiagMk v)$i$i = v$i.
  Proof. intros. apply mnth_mdiagMk_same. Qed.

  (** (mdiagMk v)[i,j] = 0 *)
  Lemma mnth_mdiagMk_diff : forall {n} (v : vec n) i j, i <> j -> (mdiagMk v)$i$j = Azero.
  Proof. intros. apply mnth_mdiagMk_diff; auto. Qed.
  
  
  (* ======================================================================= *)
  (** ** Matrix transposition *)

  Definition mtrans {r c} (M : mat r c): mat c r := mtrans M.
  Notation "M \T" := (mtrans M) : mat_scope.

  (** Transpose twice keep unchanged. *)
  Lemma mtrans_mtrans : forall {r c} (M : mat r c), M \T \T = M.
  Proof. intros. apply mtrans_mtrans. Qed.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (M : smat n), mdiag M -> M\T = M.
  Proof. intros. apply (mtrans_diag Azero); auto. Qed.

End BasicMatrixTheory.


(* ######################################################################### *)
(** * Ring matrix theory *)
Module RingMatrixTheory (E : RingElementType).
  Include (BasicMatrixTheory E).

  (* ======================================================================= *)
  (** ** Zero matrirx and identity matrix *)

  (** Zero matrix *)
  Definition mat0 {r c : nat} : mat r c := mat0 (Azero:=Azero).

  (** Identity matrix *)
  Definition mat1 {n : nat} : mat n n := mat1 (Azero:=Azero) (Aone:=Aone).

  (** mat1 is diagonal matrix *)
  Lemma mat1_diag : forall {n : nat}, mdiag (@mat1 n).
  Proof. intros. apply mat1_diag. Qed.
  
  (** mat0\T = mat0 *)
  Lemma mtrans_mat0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. apply mtrans_mat0. Qed.
  
  (** mat1\T = mat1 *)
  Lemma mtrans_mat1 : forall {n : nat}, (@mat1 n)\T = mat1.
  Proof. intros. apply mtrans_mat1. Qed.

  (** mat1[i,i] = 1 *)
  Lemma mnth_mat1_same : forall {n} i, (@mat1 n) $ i $ i = Aone.
  Proof. intros. apply mnth_mat1_same; auto. Qed.

  (** mat1[i,j] = 0 *)
  Lemma mnth_mat1_diff : forall {n} i j,
      i <> j -> (@mat1 n) $ i $ j = Azero.
  Proof. intros. apply mnth_mat1_diff; auto. Qed.


  (* ======================================================================= *)
  (** ** Matrix trace *)
  Definition mtrace {n : nat} (M : smat n) : A :=
    mtrace M (Aadd:=Aadd) (Azero:=Azero).
  Notation "'tr' M" := (mtrace M) : mat_scope.

  (** tr(m\T) = tr(m) *)
  Lemma mtrace_mtrans : forall {n} (m : smat n), tr (m\T) = tr(m).
  Proof. intros. apply mtrace_mtrans. Qed.


  (* ======================================================================= *)
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
  Proof. intros. unfold madd. apply mnth_madd. Qed.

  (** (M1 + M2)\T = M1\T + M2\T *)
  Lemma mtrans_madd : forall {r c} (M1 M2 : mat r c), (M1 + M2)\T = M1\T + M2\T.
  Proof. intros. apply mtrans_madd. Qed.

  (** tr(M1 + M2) = tr(M1) + tr(M2) *)
  Lemma mtrace_madd : forall {n} (M1 M2 : smat n), (tr (M1 + M2)%M = tr(M1) + tr(M2))%A.
  Proof. intros. apply mtrace_madd. Qed.

  
  (* ======================================================================= *)
  (** ** Monoid structure over {madd,mat0,meq} *)
  Global Instance Monoid_madd : forall r c, Monoid (@madd r c) mat0.
  Proof. apply Monoid_madd. Qed.

  Section test.
    Goal forall r c (M1 M2 : mat r c), mat0 + M1 + M2 + mat0 = M1 + mat0 + M2.
    Proof. monoid. Qed.
  End test.

  
  (* ======================================================================= *)
  (** ** Matrix opposition *)
  
  Definition mopp {r c} (M : mat r c) : mat r c := mopp M (Aopp:=Aopp).
  Notation "- a" := (mopp a) : mat_scope.

  (** - (M1 + M2) = (-M1) + (-M2) *)
  Lemma mopp_madd : forall {r c : nat} (M1 M2 : mat r c), - (M1 + M2) = (-M1) + (-M2).
  Proof. intros. apply mopp_madd. Qed.

  (** (-M) + M = mat0 *)
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

  
  (* ======================================================================= *)
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

  
  (* ======================================================================= *)
  (** ** Abelian group structure over {madd,mat0,mopp} *)
  Global Instance AGroup_MatAdd : forall r c, AGroup (@madd r c) mat0 mopp.
  Proof. apply AGroup_madd. Qed.

  Section test.
    Goal forall r c (M1 M2 : mat r c), mat0 + M1 + (-M2) + M2 = M1.
    Proof.
      intros.
      (* rewrite associative. *)
      (* rewrite inverseLeft. *)
      (* rewrite identityRight. *)
      (* rewrite identityLeft. *)
      group.
    Qed.
  End test.


  (* ======================================================================= *)
  (** ** Scalar multiplication of matrix *)

  (** Scalar multiplication of matrix *)
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
  Lemma mcmul_1_r : forall {n} a, a c* (@mat1 n) = mdiagMk (vrepeat a).
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
  Proof. intros. apply mtrans_mcmul. Qed.

  (** tr (a c* M) = a * tr (m) *)
  Lemma mtrace_mcmul : forall {n} (a : A) (M : smat n), (tr (a c* M) = a * tr (M))%A.
  Proof. intros. apply mtrace_mcmul. Qed.

  (** (M1 <> 0 /\ M2 <> 0 /\ k * M1 = M2) -> k <> 0 *)
  Lemma mcmul_eq_implfy_not_k0 : forall {r c} (M1 M2 : mat r c) k,
      M1 <> mat0 -> M2 <> mat0 -> k c* M1 = M2 -> k <> Azero.
  Proof. intros. apply mcmul_eq_implfy_not_k0 in H1; auto. Qed.

  
  (* ======================================================================= *)
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

  (** tr (M1 * M2) = tr (M2 * M1) *)
  Lemma mtrace_mmul : forall {r c} (M1 : mat r c) (M2 : mat c r),
      tr (M1 * M2) = tr (M2 * M1).
  Proof. intros. apply mtrace_mmul. Qed.

  
  (* ======================================================================= *)
  (** ** Hardmard product *)
  
  (** Hardmard product (also known as the element-wise product, entrywise product 
      or Schur product).
      It is a binary operation that takes two matrices of the same dimensions and 
      produces another matrix of the same dimension as the operandds, where each 
      element i,j is the product of elements i,j of the original two matrices.

      The hardmard product is associative, distribute and commutative *)
  (* Definition mhp {n : nat} (M1 M2 : smat n) : smat n := mhp m1 m2 (Amul:=Amul). *)
  (* Infix "⦿" := mhp : mat_scope. *)

  
  (* ======================================================================= *)
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

  
  (* ======================================================================= *)
  (** ** Determinant on matrix of 1-,2-, or 3-dim*)

  (** Determinant of a matrix of given dimension *)
  Definition mdet1 (M : smat 1) := mdet1 M.
  Definition mdet2 (M : smat 2) := @mdet2 _ Aadd Aopp Amul M.
  Definition mdet3 (M : smat 3) := @mdet3 _ Aadd Aopp Amul M.

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
  
  
  (* ======================================================================= *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix: adj(A)[i,j] = algebraic remainder of A[i,j]. *)
  Definition madj {n} (M : smat n) : smat n := @madj _ Aadd Azero Aopp Amul Aone _ M.


  (* ======================================================================= *)
  (** ** Invertible matrix *)
  
  (** A square matrix is invertible, if exists an inverse matrix *)
  Definition minvertible {n} (M : smat n) : Prop :=
    exists M' : smat n, (M * M' = mat1) \/ (M' * M = mat1).

  (** invertible mat1 *)
  Lemma minvertible_mat1 : forall n : nat, @minvertible n mat1.
  Proof. apply minvertible_mat1. Qed.

  (** A square matrix is invertible, if its determinant is nonzero *)
  Lemma minvertible_iff_mdet_neq0 : forall {n} (M : smat n),
      minvertible M <-> mdet M <> Azero.
  Proof. intros. apply minvertible_iff_mdet_neq0. Qed.

  (** invertible M -> invertible (M\T) *)
  Lemma minvertible_mtrans : forall n (M : smat n),
      minvertible M -> minvertible (M\T).
  Proof. intros. apply minvertible_mtrans; auto. Qed.

  (** invertible M -> invertible N -> invertible (M * N) *)
  Lemma minvertible_mmul : forall n (M N : smat n),
      minvertible M -> minvertible N -> minvertible (M * N).
  Proof. intros. apply minvertible_mmul; auto. Qed.

End RingMatrixTheory.


(* ######################################################################### *)
(** * Field matrix theory *)

Module FieldMatrixTheory (E : FieldElementType).
  
  Include (RingMatrixTheory E).
  
  (* ======================================================================= *)
  (** ** Properties about zero or non-zero *)

  (** k * M = 0 -> (k = 0) \/ (M = 0) *)
  Lemma mcmul_eq0_imply_m0_or_k0 : forall {r c} (M : mat r c) k,
      k c* M = mat0 -> (k = Azero)%A \/ (M = mat0).
  Proof. intros. apply mcmul_eq0_imply_m0_or_k0; auto. Qed.

  (** (M <> 0 /\ k * M = 0) -> M = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (M : mat r c) k,
      M <> mat0 -> k c* M = mat0 -> (k = Azero)%A.
  Proof. intros. apply mcmul_mnonzero_eq0_imply_k0 with (M:=M); auto. Qed.

  (** k * M = M -> k = 1 \/ M = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} k (M : mat r c),
      k c* M = M -> (k = Aone)%A \/ (M = mat0).
  Proof. intros. apply mcmul_same_imply_coef1_or_mzero; auto. Qed.


  (* ======================================================================= *)
  (** ** Gauss Elimination *)

  (* (** inverse matrix by gauss elimination *) *)
  (* Definition minv_gauss {n} (m : mat n n) : option (mat n n) := *)
  (*   @minv_gauss T Aadd Azero Aopp Amul Aone Ainv _ _ _ m. *)
  
  
  (* ======================================================================= *)
  (** ** Cramer rule *)
  
  (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid only when D is not zero *)
  Definition cramerRule {n} (A : smat n) (b : vec n) : vec n :=
    @cramerRule _ Aadd Azero Aopp Amul Aone Ainv _ A b.


  (* ======================================================================= *)
  (** ** Matrix Inversion by AM/GE *)

  Definition minv {n} (M : smat n) := @minvAM _ Aadd Azero Aopp Amul Aone Ainv _ M.
  Notation "M \-1" := (minv M) : mat_scope.

  (** M * N = mat1 <-> M\-1 = N *)
  Lemma mmul_eq1_iff_minv_l : forall {n} (M N : smat n),
      M * N = mat1 <-> minv M = N.
  Proof. intros. apply AM_mmul_eq1_iff_minv_l; auto. Qed.

  (** M * N = mat1 <-> M\-1 = M *)
  Lemma mmul_eq1_iff_minv_r : forall {n} (M N : smat n),
      M * N = mat1 <-> minv N = M.
  Proof. intros. apply AM_mmul_eq1_iff_minv_r; auto. Qed.

  (** invertible M -> invertible (M\-1) *)
  Lemma minvertible_inv : forall {n} (M : smat n), minvertible M -> minvertible (M\-1).
  Proof. intros. apply AM_minv_invertible; auto. Qed.

  (** M\-1 * M = mat1 *)
  Lemma mmul_minv_l : forall n (M : smat n), (minv M) * M = mat1.
  Proof. intros. apply AM_mmul_minv_l. Qed.
  
  (** M * M\-1 = mat1 *)
  Lemma mmul_minv_r : forall n (M : smat n), M * M\-1 = mat1.
  Proof. intros. apply AM_mmul_minv_r. Qed.

  (** mat1\-1 = mat1 *)
  Lemma minv_1 : forall n, @minv n mat1 = mat1.
  Proof. intros. apply AM_minv_mat1. Qed.

  (** M\-1\-1 = M *)
  Lemma minv_minv : forall n (M : smat n), minvertible M -> M\-1\-1 = M.
  Proof. intros. apply AM_minv_minv; auto. Qed.

  (** (M * N)\-1 = N\-1 * M\-1 *)
  Lemma minv_mmul : forall n (M N : smat n),
      minvertible M -> minvertible N -> (M * N)\-1 = N\-1 * M\-1.
  Proof. intros. apply AM_minv_mmul; auto. Qed.

  (** (M\T)\-1 = (M\-1)\T *)
  Lemma minv_mtrans : forall n (M : smat n), minvertible M -> (M\T)\-1 = (M\-1)\T.
  Proof. intros. apply AM_minv_mtrans; auto. Qed.
  
  (** mdet (M\-1) = 1 / (|M|) *)
  Lemma mdet_minv : forall {n} (M : smat n), (mdet (M\-1) = Aone / (mdet M))%A.
  Proof. intros. apply AM_mdet_minv; auto. Qed.
  

  (* ======================================================================= *)
  (** ** Inversion matrix of common finite dimension *)
  
  (** Inversion matrix of dimension-1 *)
  Definition minv1 (M : smat 1) : smat 1 := @minv1AM _ Azero Amul Aone Ainv M.

  (** |M| <> 0 -> minv1 M = inv M *)
  Lemma minv1_eq_inv : forall M, (mdet M <> Azero)%A -> minv1 M = minv M.
  Proof. intros. apply AM_minv1_eq_inv; auto. Qed.
  
  (** Inversion matrix of dimension-2 *)
  Definition minv2 (M : smat 2) : smat 2 := @minv2AM _ Aadd Azero Aopp Amul Ainv M.

  (** |M| <> 0 -> minv2 M = inv M *)
  Lemma minv2_eq_inv : forall M, (mdet M <> Azero)%A -> minv2 M = minv M.
  Proof. intros. apply AM_minv2_eq_inv; auto. Qed.
  
  (** Inversion matrix of dimension-3 *)
  Definition minv3 (M : smat 3) : smat 3 := @minv3AM _ Aadd Azero Aopp Amul Ainv M.
  
  (** |M| <> 0 -> minv3 M = inv M *)
  Lemma minv3_eq_inv : forall M, (mdet M <> Azero)%A -> minv3 M = minv M.
  Proof. intros. apply AM_minv3_eq_inv; auto. Qed.

  (** Inversion matrix of dimension-4 *)
  Definition minv4 (M : smat 4) : smat 4 := @minv4AM _ Aadd Azero Aopp Amul Ainv M.
  
  (** |M| <> 0 -> minv4 M = inv M *)
  Lemma minv4_eq_inv : forall M, (mdet M <> Azero)%A -> minv4 M = minv M.
  Proof. intros. apply AM_minv4_eq_inv; auto. Qed.

  
  (* ======================================================================= *)
  (** ** Orthogonal matrix *)

  (** An orthogonal matrix *)
  Definition morth {n} (M : smat n) : Prop :=
   (@morth _ Aadd Azero Amul Aone _ M).

  (** orthogonal M -> invertible M *)
  Lemma morth_invertible : forall {n} (M : smat n),
      morth M -> minvertible M.
  Proof. intros. apply morth_invertible; auto. Qed.

  (** orthogonal M -> M\-1 = M\T *)
  Lemma morth_imply_inv_eq_trans : forall {n} (M : smat n),
      morth M -> M\-1 = M\T.
  Proof. intros. apply morth_imply_inv_eq_trans; auto. Qed.

  (** M\-1 = M\T -> orthogonal M *)
  Lemma minv_eq_trans_imply_morth : forall {n} (M : smat n),
      M\-1 = M\T -> morth M.
  Proof. intros. apply minv_eq_trans_imply_morth; auto. Qed.

  (** orthogonal M <-> M\T * M = mat1 *)
  Lemma morth_iff_mul_trans_l : forall {n} (M : smat n),
      morth M <-> M\T * M = mat1.
  Proof. intros. apply morth_iff_mul_trans_l; auto. Qed.

  (** orthogonal M <-> M * M\T = mat1 *)
  Lemma morth_iff_mul_trans_r : forall {n} (M : smat n),
      morth M <-> M * M\T = mat1.
  Proof. intros. apply morth_iff_mul_trans_r; auto. Qed.

  (** orthogonal mat1 *)
  Lemma morth_mat1 : forall {n}, morth (@mat1 n).
  Proof. intros. apply morth_mat1; auto. Qed.

  (** orthogonal M -> orthogonal N -> orthogonal (M * N) *)
  Lemma morth_mul : forall {n} (M N : smat n),
      morth M -> morth N -> morth (M * N).
  Proof. intros. apply morth_mul; auto. Qed.

  (** orthogonal M -> orthogonal M\T *)
  Lemma morth_mtrans : forall {n} (M : smat n), morth M -> morth (M\T).
  Proof. intros. apply morth_mtrans; auto. Qed.

  (** orthogonal M -> orthogonal M\-1 *)
  Lemma morth_minv : forall {n} (M : smat n), morth M -> morth (M\-1).
  Proof. intros. apply morth_minv; auto. Qed.

  (** orthogonal M -> |M| = ± 1 *)
  Lemma morth_mdet : forall {n} (M : smat n),
      morth M -> (mdet M = Aone \/ mdet M = - (Aone))%A.
  Proof. intros. apply morth_mdet; auto. Qed.

  
  (* ======================================================================= *)
  (** ** O(n): General Orthogonal Group, General Linear Group *)
  
  (** The set of GOn *)
  Definition GOn (n : nat) := (@GOn _ Aadd Azero Amul Aone n).

  (** Multiplication of elements in GOn *)
  Definition GOn_mul {n} (x1 x2 : GOn n) : GOn n := GOn_mul x1 x2.

  (** Identity element in GOn *)
  Definition GOn_1 {n} : GOn n :=  GOn_1.

  (** Inverse operation of multiplication in GOn *)
  Definition GOn_inv {n} (x : GOn n) : GOn n := GOn_inv x.

  (** GOn_mul is associative *)
  Lemma GOn_mul_assoc : forall n, Associative (@GOn_mul n).
  Proof. intros. apply GOn_mul_assoc; auto. Qed.

  (** GOn_1 is left-identity-element of GOn_mul operation *)
  Lemma GOn_mul_id_l : forall n, IdentityLeft GOn_mul (@GOn_1 n).
  Proof. intros. apply GOn_mul_id_l. Qed.
  
  (** GOn_1 is right-identity-element of GOn_mul operation *)
  Lemma GOn_mul_id_r : forall n, IdentityRight GOn_mul (@GOn_1 n).
  Proof. intros. apply GOn_mul_id_r. Qed.

  (** GOn_inv is left-inversion of <GOn_mul,GOn_1> *)
  Lemma GOn_mul_inv_l : forall n, InverseLeft GOn_mul GOn_1 (@GOn_inv n).
  Proof. intros. apply GOn_mul_inv_l. Qed.

  (** GOn_inv is right-inversion of <GOn_mul,GOn_1> *)
  Lemma GOn_mul_inv_r : forall n, InverseRight GOn_mul GOn_1 (@GOn_inv n).
  Proof. intros. apply GOn_mul_inv_r. Qed.
  
  (** <GOn, +, 1> is a monoid *)
  Lemma Monoid_GOn : forall n, Monoid (@GOn_mul n) GOn_1.
  Proof. intros. apply Monoid_GOn. Qed.

  (** <GOn, +, 1, /x> is a group *)
  Theorem Group_GOn : forall n, Group (@GOn_mul n) GOn_1 GOn_inv.
  Proof. intros. apply Group_GOn. Qed.

  (** M\-1 = M\T *)
  Lemma GOn_imply_inv_eq_trans : forall {n} (x : GOn n),
      let M := GOn_mat n x in
      M\-1 = M\T.
  Proof. intros. apply GOn_imply_inv_eq_trans. Qed.

  
  (* ======================================================================= *)
  (** ** SO(n): Special Orthogonal Group, Rotation Group *)

  (** The set of SOn *)
  Definition SOn (n: nat) := (@SOn _ Aadd Azero Aopp Amul Aone n).
  
  Definition SOn_mul {n} (x1 x2 : SOn n) : SOn n := SOn_mul x1 x2.
  
  Definition SOn_1 {n} : SOn n := SOn_1.

  (** SOn_mul is associative *)
  Lemma SOn_mul_assoc : forall n, Associative (@SOn_mul n).
  Proof. intros. apply SOn_mul_assoc. Qed.

  (** SOn_1 is left-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_l : forall n, IdentityLeft SOn_mul (@SOn_1 n).
  Proof. intros. apply SOn_mul_id_l. Qed.
  
  (** SOn_1 is right-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_r : forall n, IdentityRight SOn_mul (@SOn_1 n).
  Proof. intros. apply SOn_mul_id_r. Qed.
  
  (** <SOn, +, 1> is a monoid *)
  Lemma Monoid_SOn : forall n, Monoid (@SOn_mul n) SOn_1.
  Proof. intros. apply Monoid_SOn. Qed.

  Definition SOn_inv {n} (x : SOn n) : SOn n := SOn_inv x.

  (** SOn_inv is left-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_l : forall n, InverseLeft SOn_mul SOn_1 (@SOn_inv n).
  Proof. intros. apply SOn_mul_inv_l. Qed.

  (** SOn_inv is right-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_r : forall n, InverseRight SOn_mul SOn_1 (@SOn_inv n).
  Proof. intros. apply SOn_mul_inv_r. Qed.

  (** <SOn, +, 1, /x> is a group *)
  Theorem Group_SOn : forall n, Group (@SOn_mul n) SOn_1 SOn_inv.
  Proof. intros. apply Group_SOn. Qed.

  (** M\-1 = M\T *)
  Lemma SOn_imply_inv_eq_trans : forall {n} (x : SOn n),
      let M := GOn_mat n x in
      M\-1 = M\T.
  Proof. intros. apply SOn_imply_inv_eq_trans. Qed.
  
End FieldMatrixTheory.
