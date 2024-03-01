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
  2. Vector theory is contained in matrix theory, we simply called matrix.
     Note that, an old version has splitted the `vectorModule` and `matrixModule`,
     but later, I found that the `matrixModule` won't reuse the definitions in
     `vectorModule`, making a waste.
  3. The matrix theory is orgainized at several levels
  * BasicMatrixTheory: matrix theory over ElementType.
  * MonoidMatrixTheory, matrix theory over MonoidElementType.
  * RingMatrixTheory: matrix theory over RingElementType.
  * OrderedRingMatrixTheory: `RingMatrixTheory` with order relation.
  * FieldMatrixTheory: matrix theory over FieldElementType.
  * OrderedFieldMatrixTheory, `FieldMatrixTheory` with order relation.
  * NormedOrderedFieldMatrixTheory, `OrderedFieldMatrixTheory` with norm.
 *)


Require Export Matrix.
Require Export MatrixDet.
Require Export MatrixInv.
Require Export MatrixOrth.
Require Export ElementType.


(* ######################################################################### *)
(** * Basic matrix theory *)
Module BasicMatrixTheory (E : ElementType).

  (** import element *)
  Export E.

  (** default scope *)
  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope vec_scope.

  (* ======================================================================= *)
  (** ** Definition of the vector type *)
  
  (** vector type *)
  Definition vec (n : nat) := @vec A n.
  
  (* ======================================================================= *)
  (** ** Equalities of the vector *)
  
  (** veq is decidable *)
  #[export] Instance veq_dec : forall {n}, Dec (@eq (vec n)).
  Proof. intros. apply (veq_dec (Azero:=0)). Qed.
  
  (** Two vectors are equal, iff, element-wise equal *)
  Lemma veq_iff_vnth : forall {n} (u v : vec n), u = v <-> (forall i, u $ i = v $ i).
  Proof. intros. apply veq_iff_vnth. Qed.

  (** Two vectors are not equal, iff, exist one element-wise not equal *)
  Lemma vneq_iff_exist_vnth_neq : forall {n} (u v : vec n), u <> v <-> exists i, u $ i <> v $ i.
  Proof. intros. apply vneq_iff_exist_vnth_neq. Qed.

  (** Any two 0-D vectors are equal *)
  Lemma v0eq : forall (u v : vec 0), u = v.
  Proof. apply v0eq. Qed.

  (** No two 0-D vectors are unequal *)
  Lemma v0neq : forall (u v : vec 0), u <> v -> False.
  Proof. apply v0neq. Qed.

  (** The equality of 1-D, 2-D, ... vectors *)
  Section veq.
    Lemma v1eq_iff : forall (u v : vec 1), u = v <-> u.1 = v.1.
    Proof. apply v1eq_iff. Qed.

    Lemma v1neq_iff : forall (u v : vec 1), u <> v <-> u.1 <> v.1.
    Proof. apply v1neq_iff. Qed.

    Lemma v2eq_iff : forall (u v : vec 2), u = v <-> u.1 = v.1 /\ u.2 = v.2.
    Proof. apply v2eq_iff. Qed.

    Lemma v2neq_iff : forall (u v : vec 2), u <> v <-> (u.1 <> v.1 \/ u.2 <> v.2).
    Proof. apply v2neq_iff. Qed.

    Lemma v3eq_iff : forall (u v : vec 3),
        u = v <-> u.1 = v.1 /\ u.2 = v.2 /\ u.3 = v.3.
    Proof. apply v3eq_iff. Qed.

    Lemma v3neq_iff : forall (u v : vec 3),
        u <> v <-> (u.1 <> v.1 \/ u.2 <> v.2 \/ u.3 <> v.3).
    Proof. apply v3neq_iff. Qed.

    Lemma v4eq_iff : forall (u v : vec 4),
        u = v <-> u.1 = v.1 /\ u.2 = v.2 /\ u.3 = v.3 /\ u.4 = v.4.
    Proof. apply v4eq_iff. Qed.

    Lemma v4neq_iff : forall (u v : vec 4),
        u <> v <-> (u.1 <> v.1 \/ u.2 <> v.2 \/ u.3 <> v.3 \/ u.4 <> v.4).
    Proof. apply v4neq_iff. Qed.
  End veq.

  (* ======================================================================= *)
  (** ** Convert between vector and function *)
  Definition v2f {n} (v : vec n) : nat -> A := v2f 0 v.
  Definition f2v {n} (f : nat -> A) : vec n := f2v f.

  (* ======================================================================= *)
  (** ** Convert between vector and list *)
  Definition v2l {n} (v : vec n) : list A := v2l v.
  Definition l2v {n} (l : list A) : vec n := l2v 0 _ l.

  (** (l2v l).i = nth i l *)
  Lemma vnth_l2v : forall {n} (l : list A) i, (@l2v n l) $ i = nth (fin2nat i) l Azero.
  Proof. intros. apply vnth_l2v. Qed.
    
  (** nth i (v2l v) = v.i *)
  Lemma nth_v2l : forall {n} (v : vec n) (i : nat) (H: i < n),
      i < n -> nth i (v2l v) Azero = v (nat2fin i H).
  Proof. intros. apply nth_v2l; auto. Qed.
  
  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof. intros. apply v2l_length. Qed.

  Lemma v2l_l2v : forall {n} (l : list A), length l = n -> (v2l (@l2v n l) = l).
  Proof. intros. apply v2l_l2v; auto. Qed.

  Lemma l2v_v2l : forall {n} (v : vec n), @l2v n (v2l v) = v.
  Proof. intros. apply l2v_v2l. Qed.

  Lemma v2l_inj : forall {n} (u v : vec n), v2l u = v2l v -> u = v.
  Proof. intros. apply v2l_inj; auto. Qed.

  (* ======================================================================= *)
  (** ** Make concrete vector *)
  Definition mkvec1 (a1 : A) : vec 1 := mkvec1 (Azero:=0) a1.
  Definition mkvec2 (a1 a2 : A) : vec 2 := mkvec2 (Azero:=0) a1 a2.
  Definition mkvec3 (a1 a2 a3 : A) : vec 3 := mkvec3 (Azero:=0) a1 a2 a3.
  Definition mkvec4 (a1 a2 a3 a4 : A) : vec 4 := mkvec4 (Azero:=0) a1 a2 a3 a4.
  
  (* ======================================================================= *)
  (** ** Mapping of vector *)
  
  Definition vmap {n} (v : vec n) (f : A -> A) : vec n := vmap f v.
  Definition vmap2 {n} (u v : vec n) (f : A -> A -> A) : vec n := vmap2 f u v.
  
  (* ======================================================================= *)
  (** ** Constant vector and zero vector *)

  (** Vector with same elements *)
  Definition vrepeat n (a : A) : vec n := vrepeat a.

  (** (repeat a).i = a *)
  Lemma vnth_vrepeat : forall {n} a i, vrepeat n a $ i = a.
  Proof. intros. apply vnth_vrepeat. Qed.

  (** Make a zero vector *)
  Definition vzero {n} : vec n := vzero 0.

  (** vzero.i = 0 *)
  Lemma vnth_vzero : forall {n} i, @vzero n $ i = 0.
  Proof. intros. apply vnth_vzero. Qed.
  
  (* ======================================================================= *)
  (** ** Un-sorted operations for vector *)
  
  (** a :: v *)
  Definition vconsH {n} (a : A) (v : vec n) : vec (S n) := vconsH a v.
  
  (** v ++ [a] *)
  Definition vconsT {n} (v : vec n) (a : A) : vec (S n) := vconsT v a.

  (** Every element satisfy the `P` *)
  Definition vforall {n} (v : vec n) (P : A -> Prop) : Prop := vforall v P.
  
  (** There exist element of `v` satisfy the `P` *)
  Definition vexist {n} (v : vec n) (P : A -> Prop) : Prop := vexist v P.

  (** a ∈ v : Element `a` belongs to the vector `v` *)
  Definition vmem {n} (v : vec n) (a : A) : Prop := vmem v a.

  (** u ⊆ v : Every element of vector `u` belongs to vector `v` *)
  Definition vmems {r s} (u : vec r) (v : vec s) : Prop := vmems u v.

  (** ((a + v.1) + v.2) + ... *)
  Definition vfoldl {B} {n} (v : vec n) (b : B) (f : B -> A -> B) : B :=
    @vfoldl _ _ 0 _ v b f.
  
  (** ... + (v.(n-1) + (v.n + a)) *)
  Definition vfoldr {B} {n} (v : vec n) (b : B) (f : A -> B -> B) : B :=
    @vfoldr _ _ 0 _ v b f.

  (** Convert `vfoldl` to `seqfoldl` *)
  Lemma vfoldl_eq_seqfoldl :
    forall {B} {n} (v : vec n) (b : B) (f : B -> A -> B) (s : nat -> A),
      (forall i, v $ i = s (fin2nat i)) -> vfoldl v b f = seqfoldl s n b f.
  Proof. intros. apply vfoldl_eq_seqfoldl; auto. Qed.

  (* ======================================================================= *)
  (** ** Automation for vector equality proofs *)

  (** Convert equality of two vectors to point-wise element equalities *)
  Ltac veq :=
    apply v2l_inj; cbv; list_eq.
    
  Open Scope mat_scope.
  
  (* ======================================================================= *)
  (** ** Definition of the matrix type *)
  
  (** matrix type *)
  Definition mat r c : Type := @mat A r c.
  
  (** square matrix type *)
  Notation smat n := (mat n n).

  (** row vector type *)
  Notation rvec n := (mat 1 n).

  (** column vector type *)
  Notation cvec n := (mat n 1).
  
  (* ======================================================================= *)
  (** ** Equalities of the matrix *)

  (** Two matrices are equal, iff, element-wise equal *)
  Lemma meq_iff_mnth : forall {r c : nat} (M N : mat r c),
      M = N <-> (forall i j, M $ i $ j = N $ i $ j).
  Proof. intros. apply meq_iff_mnth. Qed.
    
  (** Two matrices are not equal, iff, exist one element-wise not equal *)
  Lemma mneq_iff_exist_mnth_neq : forall {r c} (M N : mat r c),
      M <> N <-> (exists i j, M $ i $ j <> N $ i $ j).
  Proof. intros. apply mneq_iff_exist_mnth_neq. Qed.

  (* ======================================================================= *)
  (** ** Convert between cvec and vec *)

  Definition cv2v {n} (v : cvec n) : vec n := cv2v v.
  Definition v2cv {n} (v : vec n) : cvec n := v2cv v.
  
  Lemma cv2v_spec : forall {n} (v : cvec n) i, v $ i $ fin0 = (cv2v v) $ i.
  Proof. intros. apply (cv2v_spec v). Qed.

  Lemma v2cv_spec : forall {n} (v : vec n) i, v $ i = (v2cv v) $ i $ fin0.
  Proof. intros. apply v2cv_spec. Qed.
  
  Lemma cv2v_v2cv : forall {n} (v : vec n), cv2v (v2cv v) = v.
  Proof. intros. apply cv2v_v2cv. Qed.
  
  Lemma v2cv_cv2v : forall {n} (v : cvec n), v2cv (cv2v v) = v.
  Proof. intros. apply v2cv_cv2v. Qed.

  Lemma cv2v_inj : forall {n} (u v : cvec n), cv2v u = cv2v v -> u = v.
  Proof. intros. apply cv2v_inj; auto. Qed.
  
  Lemma v2cv_inj : forall {n} (u v : vec n), v2cv u = v2cv v -> u = v.
  Proof. intros. apply v2cv_inj; auto. Qed.

  Lemma vnth_v2cv : forall {n} (v : vec n) i j, (v2cv v) $ i $ j  = v $ i.
  Proof. intros. apply vnth_v2cv. Qed.
  
  (* ======================================================================= *)
  (** ** Convert between rvec and vec *)
  
  Definition rv2v {n} (v : rvec n) : vec n := rv2v v.
  Definition v2rv {n} (v : vec n) : rvec n := v2rv v.

  Lemma rv2v_spec : forall {n} (v : rvec n) i, v $ fin0 $ i = (rv2v v) $ i.
  Proof. intros. apply rv2v_spec. Qed.

  Lemma v2rv_spec : forall {n} (v : vec n) i, v $ i = (v2rv v) $ fin0 $ i.
  Proof. intros. apply v2rv_spec. Qed.

  Lemma rv2v_v2rv : forall {n} (v : vec n), rv2v (v2rv v) = v.
  Proof. intros. apply cv2v_v2cv. Qed.

  Lemma v2rv_rv2v : forall {n} (v : rvec n), v2rv (rv2v v) = v.
  Proof. intros. apply v2rv_rv2v. Qed.
  
  Lemma vnth_v2rv : forall {n} (v : vec n) i, (v2rv v) $ i  = v.
  Proof. intros. apply vnth_v2rv. Qed.

  (* ======================================================================= *)
  (** ** Convert between matrix and function *)
  Definition m2f {r c} (M : mat r c) : nat -> nat -> A := m2f 0 M.
  Definition f2m {r c} (f : nat -> nat -> A) : mat r c := f2m f.

  (* ======================================================================= *)
  (** ** Convert between matrix and list *)
  Definition m2l {r c} (M : mat r c) : dlist A := m2l M.
  Definition l2m {r c} (dl : dlist A) : mat r c := l2m 0 dl.

  Lemma m2l_length : forall {r c} (M : mat r c), length (m2l M) = r.
  Proof. intros. apply m2l_length. Qed.
  
  Lemma m2l_width : forall {r c} (M : mat r c), width (m2l M) c.
  Proof. intros. apply m2l_width. Qed.

  Lemma l2m_m2l : forall {r c} (M : mat r c), @l2m r c (m2l M) = M.
  Proof. intros. apply l2m_m2l. Qed.

  Lemma m2l_l2m : forall {r c} (dl : dlist A),
      length dl = r -> width dl c -> m2l (@l2m r c dl) = dl.
  Proof. intros. apply m2l_l2m; auto. Qed.

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
  Proof. intros. apply (m2l_surj 0); auto. Qed.

  (* ======================================================================= *)
  (** ** Convert between `list of vectors` and mat *)
  

  (** mat to `list of row vectors` *)
  Definition m2rvl {r c} (M : mat r c) : list (vec c) := m2rvl M.

  (** `list of row vectors` to mat *)
  Definition rvl2m {r c} (l : list (vec c)) : mat r c := rvl2m 0 l.

  Lemma m2rvl_rvl2m : forall {r c} (l : list (vec c)),
      length l = r -> @m2rvl r c (rvl2m l) = l.
  Proof. apply m2rvl_rvl2m. Qed.
  
  Lemma rvl2m_m2rvl : forall {r c} (M : mat r c), rvl2m (m2rvl M) = M.
  Proof. apply rvl2m_m2rvl. Qed.

  (** mat to `list of column vectors` *)
  Definition m2cvl {r c} (M : mat r c) : list (vec r) := m2cvl M.
  
  (** `list of column vectors` to mat *)
  Definition cvl2m {r c} (l : list (vec r)) : mat r c := cvl2m 0 l.
  
  Lemma m2cvl_cvl2m : forall {r c} (l : list (vec r)),
      length l = c -> @m2cvl r c (cvl2m l) = l.
  Proof. apply m2cvl_cvl2m. Qed.
  
  Lemma cvl2m_m2cvl : forall {r c} (M : mat r c), cvl2m (m2cvl M) = M.
  Proof. apply cvl2m_m2cvl. Qed.
  
  (* ======================================================================= *)
  (** ** Make concrete matrix *)

  Definition mkmat_0_c c : mat 0 c := mkmat_0_c c (Azero:=0).
  Definition mkmat_r_0 r : mat r 0 := mkmat_r_0 r (Azero:=0).
  
  Definition mkmat_1_1 a11 : mat 1 1 := mkmat_1_1 a11 (Azero:=0).
  Definition mkmat_1_c c (v : vec c) : mat 1 c := mkmat_1_c c v.
  Definition mkmat_r_1 r (v : vec r) : mat r 1 := mkmat_r_1 r v.
  
  Definition mkmat_1_2 a11 a12 : mat 1 2 := mkmat_1_2 a11 a12 (Azero:=0).
  Definition mkmat_2_1 a11 a21 : mat 2 1 := mkmat_2_1 a11 a21 (Azero:=0).
  Definition mkmat_2_2 a11 a12 a21 a22 : mat 2 2 :=
    mkmat_2_2 a11 a12 a21 a22 (Azero:=0).
  
  Definition mkmat_1_3 a11 a12 a13 : mat 1 3 :=
    mkmat_1_3 a11 a12 a13 (Azero:=0).
  Definition mkmat_3_1 a11 a21 a31 : mat 3 1 :=
    mkmat_3_1 a11 a21 a31 (Azero:=0).
  Definition mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
    mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 (Azero:=0).
  
  Definition mkmat_1_4 a11 a12 a13 a14 : mat 1 4 :=
    mkmat_1_4 a11 a12 a13 a14 (Azero:=0).
  Definition mkmat_4_1 a11 a21 a31 a41 : mat 4 1 :=
    mkmat_4_1 a11 a21 a31 a41 (Azero:=0).
  Definition mkmat_4_4 a11 a12 a13 a14 a21 a22 a23 a24
    a31 a32 a33 a34 a41 a42 a43 a44 : mat 4 4 :=
    mkmat_4_4
      a11 a12 a13 a14 a21 a22 a23 a24
      a31 a32 a33 a34 a41 a42 a43 a44 (Azero:=0).

  (* ======================================================================= *)
  (** ** Get row and column of a matrix *)

  (* (* Note that, the notations such as M.1, M.x can be denoted mrow *) *)

  Notation "M &1" := (mcol M (nat2finS 0)) : mat_scope.
  Notation "M &2" := (mcol M (nat2finS 1)) : mat_scope.
  Notation "M &3" := (mcol M (nat2finS 2)) : mat_scope.
  Notation "M &4" := (mcol M (nat2finS 3)) : mat_scope.

  (* (* Definition mrow {r c} (M : mat r c) (i : fin r) : vec c := mrow M i. *) *)

  (* (* (** (mrow M i).j = M.i.j *) *) *)
  (* (* Lemma vnth_mrow : forall {r c} (M : mat r c) (i : fin r) (j : fin c), *) *)
  (* (*     (mrow M i) $ j = M $ i $ j. *) *)
  (* (* Proof. intros. auto. Qed. *) *)
    
  (* (* Definition mcol {r c} (M : mat r c) (j : fin c) : vec r := mcol M j. *) *)

  (* (** (mcol M j).i = M.i.j *) *)
  (* Lemma vnth_mcol : forall {r c} (M : mat r c) (i : fin r) (j : fin c), *)
  (*     (mcol M j) $ i = M $ i $ j. *)
  (* Proof. intros. auto. Qed. *)
    
  (* ======================================================================= *)
  (** ** Mapping of matrix *)

  Definition mmap {r c} (f : A -> A) (M : mat r c) : mat r c := mmap f M.
  Definition mmap2 {r c} (f : A -> A -> A) (M N : mat r c) : mat r c := mmap2 f M N.

  Lemma mmap2_comm :
    forall {r c} (f : A -> A -> A) (M N : mat r c) {Comm : Commutative f}, 
      mmap2 f M N = mmap2 f N M.
  Proof. intros. apply mmap2_comm; auto. Qed.
  
  Lemma mmap2_assoc :
    forall {r c} (f : A -> A -> A) (M N O : mat r c) {Assoc : Associative f}, 
      mmap2 f (mmap2 f M N) O = mmap2 f M (mmap2 f N O).
  Proof. intros. apply mmap2_assoc; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Zero matrix *)

  (** zero matrix *)
  Definition mat0 {r c} : mat r c := @mat0 _ 0 r c.

  (** mat0\T = mat0 *)
  Lemma mtrans_mat0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. apply mtrans_mat0. Qed.

  (** mat0[i,j] = 0 *)
  Lemma mnth_mat0 : forall {r c} i j, @mat0 r c $ i $ j = 0.
  Proof. intros. apply mnth_mat0. Qed.

  (** row mat0 i = vzero *)
  Lemma mrow_mat0 : forall {r c} i, @mat0 r c $ i = vzero.
  Proof. intros. apply mrow_mat0. Qed.

  (** col mat0 i = vzero *)
  Lemma mcol_mat0 : forall {r c} j, (fun k => @mat0 r c $ k $ j) = vzero.
  Proof. intros. apply mcol_mat0. Qed.
  
  (* ======================================================================= *)
  (** ** Diagonal Matrix *)
  
  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (m : smat n) : Prop := mdiag 0 m.

  (** Construct a diagonal matrix *)
  Definition mdiagMk {n} (v : vec n) : smat n := mdiagMk 0 v.

  (** mdiagMk is correct *)
  Lemma mdiagMk_spec : forall {n} (v : vec n), mdiag (mdiagMk v).
  Proof. intros. apply mdiagMk_spec. Qed.

  (** (mdiagMk v)[i,i] = l[i] *)
  Lemma mnth_mdiagMk_same : forall {n} (v : vec n) i, (mdiagMk v)$i$i = v$i.
  Proof. intros. apply mnth_mdiagMk_same. Qed.

  (** (mdiagMk v)[i,j] = 0 *)
  Lemma mnth_mdiagMk_diff : forall {n} (v : vec n) i j, i <> j -> (mdiagMk v)$i$j = 0.
  Proof. intros. apply mnth_mdiagMk_diff; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Matrix transposition *)

  Definition mtrans {r c} (M : mat r c): mat c r := mtrans M.
  Notation "M \T" := (mtrans M) : mat_scope.

  (** Transpose twice keep unchanged. *)
  Lemma mtrans_mtrans : forall {r c} (M : mat r c), M \T \T = M.
  Proof. intros. apply mtrans_mtrans. Qed.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (M : smat n), mdiag M -> M \T = M.
  Proof. intros. apply (mtrans_diag 0); auto. Qed.

  (* ======================================================================= *)
  (** ** Un-sorted operations for matrix *)

  (** Construct a matrix by rows *)
  Definition mconsr {r c} (v : vec c) (M : mat r c) : mat (S r) c := mconsr v M.

  (** Construct a matrix by columns *)
  Definition mconsc {r c} (v : vec r) (M : mat r c) : mat r (S c) := mconsc v M.
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (M : mat r1 c) (N : mat r2 c) : mat (r1 + r2) c :=
    mappr (Azero:=0) M N.
  
  (** Append matrix by column *)
  Definition mappc {r c1 c2} (M : mat r c1) (N : mat r c2) : mat r (c1 + c2) :=
    mappc (Azero:=0) M N.

  (* ======================================================================= *)
  (** ** Automation for matrix equality proofs *)

  (** Convert equality of two matrices to point-wise element equalities *)
  Ltac meq :=
    apply m2l_inj; cbv; list_eq.

End BasicMatrixTheory.


(* ######################################################################### *)
(** * Monoid matrix theory *)
Module MonoidMatrixTheory (E : MonoidElementType).

  Include (BasicMatrixTheory E).

  Open Scope vec_scope.

  (* ======================================================================= *)
  (** ** Vector addition *)
  
  Definition vadd {n} (u v : vec n) : vec n := vadd u v (Aadd:=Aadd).
  Infix "+" := vadd : vec_scope.

  (** (u + v) + w = u + (v + w) *)
  Lemma vadd_assoc : forall {n} (u v w : vec n), (u + v) + w = u + (v + w).
  Proof. intros. apply vadd_assoc. Qed.

  (** u + v = v + u *)
  Lemma vadd_comm : forall {n} (u v : vec n), u + v = v + u.
  Proof. intros. apply vadd_comm. Qed.

  (** 0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), vzero + v = v.
  Proof. intros. apply vadd_0_l. Qed.

  (** v + 0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + vzero = v.
  Proof. intros. apply vadd_0_r. Qed.

  #[export] Instance vadd_AMonoid : forall n, AMonoid (@vadd n) vzero.
  Proof. apply vadd_AMonoid. Qed.

  Open Scope mat_scope.
  
  (* ======================================================================= *)
  (** ** Matrix addition *)

  Definition madd {r c} (M N : mat r c) : mat r c := madd M N (Aadd:=Aadd).
  Infix "+" := madd : mat_scope.
  
  (** (M+N)[i,j] = M[i,j] + N[i,j] *)
  Lemma mnth_madd : forall {r c} (M N : mat r c) i j,
      (M + N) $ i $ j = (M $ i $ j + N $ i $ j)%A.
  Proof. intros. unfold madd. apply mnth_madd. Qed.

  (** cv2v (v1 + v2) = cv2v v1 + cv2v v2 *)
  Lemma cv2v_madd : forall {n} (v1 v2 : cvec n), cv2v (v1 + v2) = (cv2v v1 + cv2v v2)%V.
  Proof. intros. apply cv2v_madd. Qed.

  (** M + N = N + M *)
  Lemma madd_comm : forall {r c} (M N : mat r c), M + N = (N + M).
  Proof. intros. apply madd_comm. Qed.

  (** (M + N) + O = M + (N + O) *)
  Lemma madd_assoc : forall {r c} (M N O : mat r c), (M + N) + O = M + (N + O).
  Proof. intros. apply madd_assoc. Qed.

  (** (M + N) + O = (M + O) + N *)
  Lemma madd_perm : forall {r c} (M N O : mat r c), (M + N) + O = (M + O) + N.
  Proof. intros. apply madd_perm. Qed.

  (** mat0 + M = M *)
  Lemma madd_0_l : forall {r c} (M : mat r c), mat0 + M = M. 
  Proof. intros. apply madd_0_l. Qed.

  (** M + mat0 = M *)
  Lemma madd_0_r : forall {r c} (M : mat r c), M + mat0 = M. 
  Proof. intros. apply madd_0_r. Qed.

  (** (M + N) \T = M \T + N \T *)
  Lemma mtrans_madd : forall {r c} (M N : mat r c), (M + N) \T = M \T + N \T.
  Proof. intros. apply mtrans_madd. Qed.

End MonoidMatrixTheory.


(* ######################################################################### *)
(** * Ring matrix theory *)
Module RingMatrixTheory (E : RingElementType).
  
  Include (MonoidMatrixTheory E).

  Open Scope vec_scope.

  (* ======================================================================= *)
  (** ** Vector opposition *)

  Definition vopp {n} (v : vec n) : vec n := vopp (Aopp:=Aopp) v.
  Notation "- v" := (vopp v) : vec_scope.

  (** - v + v = 0 *)
  Lemma vadd_vopp_l : forall {n} (v : vec n), v + (- v) = vzero.
  Proof. intros. apply vadd_vopp_l. Qed.

  (** v + - v = 0 *)
  Lemma vadd_vopp_r : forall {n} (v : vec n), (- v) + v = vzero.
  Proof. intros. apply vadd_vopp_r. Qed.

  #[export] Instance vadd_AGroup : forall n, AGroup (@vadd n) vzero vopp.
  Proof. intros. apply vadd_AGroup. Qed.

  (** - (- v) = v *)
  Lemma vopp_vopp : forall {n} (v : vec n), - (- v) = v.
  Proof. intros. apply vopp_vopp. Qed.

  (** - u = v <-> u = - v *)
  Lemma vopp_exchange : forall {n} (u v : vec n), - u = v <-> u = - v.
  Proof. intros. apply vopp_exchange. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n}, - (@vzero n) = vzero.
  Proof. intros. apply vopp_vzero. Qed.

  (** - (u + v) = (- u) + (- v) *)
  Lemma vopp_vadd : forall {n} (u v : vec n), - (u + v) = (- u) + (- v).
  Proof. intros. apply vopp_vadd. Qed.

  (* ======================================================================= *)
  (** ** Vector subtraction *)

  Definition vsub {n} (u v : vec n) : vec n := u + (- v).
  Infix "-" := vsub : vec_scope.

  Lemma vsub_self : forall (n : nat) v, v - v = (@vzero n).
  Proof. intros. apply vsub_self. Qed.
  
  Lemma vsub_0_l : forall (n : nat) v, (@vzero n) - v = - v.
  Proof. intros. apply vsub_0_l. Qed.
  
  Lemma vsub_comm : forall (n : nat) (u v : vec n), u - v = - (v - u).
  Proof. intros. apply vsub_comm. Qed.
    
  Lemma vsub_assoc : forall (n : nat) (u v w : vec n), (u - v) - w = u - (v + w).
  Proof. intros. apply vsub_assoc. Qed.
    
  Lemma vsub_assoc1 : forall (n : nat) (u v w : vec n), (u + v) - w = u + (v - w).
  Proof. intros. apply vsub_assoc1. Qed.
    
  Lemma vsub_assoc2 : forall (n : nat) (u v w : vec n), (u - v) - w = (u - w) - v.
  Proof. intros. apply vsub_assoc2. Qed.

  (** ** Vector scalar multiplication *)

  Definition vcmul {n} k (v : vec n) : vec n := vcmul (Amul:=Amul) k v.
  Infix "\.*" := vcmul : vec_scope.

  (** (k * v)[i] = k * v[i] *)
  Lemma vnth_vcmul : forall {n} (v : vec n) k i, (k \.* v) $ i = k * (v $ i).
  Proof. intros. cbv. auto. Qed.

  (** k \.* (l \.* v) = (k * l) \.* v *)
  Lemma vcmul_assoc : forall {n} k l (v : vec n), k \.* (l \.* v) = (k * l)%A \.* v.
  Proof. intros. apply vcmul_assoc. Qed.

  (** k \.* (l \.* v) = l \.* (k \.* v) *)
  Lemma vcmul_perm : forall {n} k l (v : vec n), k \.* (l \.* v) = l \.* (k \.* v).
  Proof. intros. apply vcmul_perm. Qed.

  (** (k + l) \.* v = (k \.* v) + (l \.* v) *)
  Lemma vcmul_add : forall {n} k l (v : vec n),
      (k + l)%A \.* v = (k \.* v) + (l \.* v).
  Proof. intros. apply vcmul_add. Qed.

  (** k \.* (u + v) = (k \.* u) + (k \.* v) *)
  Lemma vcmul_vadd : forall {n} k (u v : vec n),
      k \.* (u + v) = (k \.* u) + (k \.* v).
  Proof. intros. apply vcmul_vadd. Qed.

  (** 1 \.* v = v *)
  Lemma vcmul_1_l : forall {n} (v : vec n), 1 \.* v = v.
  Proof. intros. apply vcmul_1_l. Qed.

  (** 0 \.* v = 0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), 0 \.* v = vzero.
  Proof. intros. apply vcmul_0_l. Qed.

  (** k \.* 0 = 0 *)
  Lemma vcmul_0_r : forall {n} k, k \.* (@vzero n) = vzero.
  Proof. intros. apply vcmul_0_r. Qed.
  
  (** (-a) * v = - (a * v) *)
  Lemma vcmul_opp : forall {n} a (v : vec n), (- a)%A \.* v = - (a \.* v).
  Proof. intros. apply vcmul_opp. Qed.
  
  (** a * (- v) = - (a * v) *)
  Lemma vcmul_vopp : forall {n} a (v : vec n), a \.* (- v) = - (a \.* v).
  Proof. intros. apply vcmul_vopp. Qed.

  (** (-a) * (- v) = a * v *)
  Lemma vcmul_opp_vopp : forall {n} a (v : vec n), (- a)%A \.* (- v) = a \.* v.
  Proof. intros. apply vcmul_opp_vopp. Qed.

  (** a \.* (u - v) = (a \.* u) - (a \.* v) *)
  Lemma vcmul_vsub : forall {n} a (u v : vec n),
      a \.* (u - v) = (a \.* u) - (a \.* v).
  Proof. intros. apply vcmul_vsub. Qed.

  (** k * u = v -> k <> 0 *)
  Lemma vcmul_eq_imply_k_neq0 : forall {n} (u v : vec n) k,
      k \.* u = v -> u <> vzero -> v <> vzero -> k <> 0.
  Proof. intros. apply vcmul_eq_imply_k_neq0 in H; auto. Qed.

  (* ======================================================================= *)
  (** ** Vector dot product *)

  Definition vdot {n : nat} (u v : vec n) : A := @vdot _ Aadd 0 Amul _ u v.
  Notation "< u , v >" := (vdot u v) : vec_scope.

  (** <u, v> = <v, u> *)
  Lemma vdot_comm : forall {n} (u v : vec n), <u, v> = <v, u>.
  Proof. intros. apply vdot_comm. Qed.

  (** <vzero, v> = 0 *)
  Lemma vdot_0_l : forall {n} (v : vec n), <vzero, v> = 0.
  Proof. intros. apply vdot_0_l. Qed.

  (** <v, vzero> = 0 *)
  Lemma vdot_0_r : forall {n} (v : vec n), <v, vzero> = 0.
  Proof. intros. apply vdot_0_r. Qed.

  (** <u + v, w> = <u, w> + <v, w> *)
  Lemma vdot_vadd_l : forall {n} (u v w : vec n), <u + v, w> = (<u, w> + <v, w>)%A.
  Proof. intros. apply vdot_vadd_l. Qed.

  (** <u, v + w> = <u, v> + <u, w> *)
  Lemma vdot_vadd_r : forall {n} (u v w : vec n), <u, v + w> = (<u, v> + <u, w>)%A.
  Proof. intros. apply vdot_vadd_r. Qed.

  (** <- u, v> = - <u, v> *)
  Lemma vdot_vopp_l : forall {n} (u v : vec n), < - u, v> = (- <u, v>)%A.
  Proof. intros. apply vdot_vopp_l. Qed.

  (** <u, - v> = - <u, v> *)
  Lemma vdot_vopp_r : forall {n} (u v : vec n), <u, - v> = (- <u, v>)%A.
  Proof. intros. apply vdot_vopp_r. Qed.

  (** <u - v, w> = <u, w> - <v, w> *)
  Lemma vdot_vsub_l : forall {n} (u v w : vec n), <u - v, w> = (<u, w> - <v, w>)%A.
  Proof. intros. apply vdot_vsub_l. Qed.

  (** <u, v - w> = <u, v> - <u, w> *)
  Lemma vdot_vsub_r : forall {n} (u v w : vec n), <u, v - w> = (<u, v> - <u, w>)%A.
  Proof. intros. apply vdot_vsub_r. Qed.

  (** <a \.* u, v> = a * <u, v> *)
  Lemma vdot_vcmul_l : forall {n} (u v : vec n) (a : A), <a \.* u, v> = a * <u, v>.
  Proof. intros. apply vdot_vcmul_l. Qed.

  (** <u, a \.* v> = a * <u, v> *)
  Lemma vdot_vcmul_r : forall {n} (u v : vec n) (a : A), <u, a \.* v> = a * <u, v>.
  Proof. intros. apply vdot_vcmul_r. Qed.
  
  (** <u, v> <> 0 -> u <> 0 *)
  Lemma vdot_neq0_imply_neq0_l : forall {n} (u v : vec n), <u, v> <> 0 -> u <> vzero.
  Proof. intros. apply vdot_neq0_imply_neq0_l in H; auto. Qed.

  (** <u, v> <> 0 -> v <> 0 *)
  Lemma vdot_neq0_imply_neq0_r : forall {n} (u v : vec n), <u, v> <> 0 -> v <> vzero.
  Proof. intros. apply vdot_neq0_imply_neq0_r in H; auto. Qed.

  (* ======================================================================= *)
  (** ** vsum *)
  Definition vsum {n} (v : vec n) := @vsum _ Aadd 0 _ v.
  
  (** (∀ i, u.i = v.i) -> Σu = Σv *)
  Lemma vsum_eq : forall {n} (u v : vec n), (forall i, u $ i = v $ i) -> vsum u = vsum v.
  Proof. intros. apply fseqsum_eq. auto. Qed.

  (** (∀ i, v.i = 0) -> Σv = 0 *)
  Lemma vsum_eq0 : forall {n} (v : vec n), (forall i, v $ i = 0) -> vsum v = 0.
  Proof. intros. apply vsum_eq0; auto. Qed.

  (** Convert `vsum` to `seqsum` *)
  Lemma vsum_eq_seqsum : forall {n} (v : vec n) (g : nat -> A),
      (forall i, v $ i = g (fin2nat i)) -> vsum v = @seqsum _ Aadd 0 g n.
  Proof. intros. apply vsum_eq_seqsum; auto. Qed.

  (** Convert `vsum` to `seqsum` (succ form) *)
  Lemma vsum_eq_seqsum_succ : forall {n} (v : vec (S n)),
      vsum v = ((@seqsum _ Aadd 0 (fun i => v $ (nat2finS i)) n)
                + v $ (nat2finS n))%A.
  Proof. intros. apply vsum_eq_seqsum_succ. Qed.
  
  (** `vsum` of (S n) elements, equal to addition of Sum and tail *)
  Lemma vsumS_tail : forall {n} (v : vec (S n)),
      vsum v = (vsum (fun i => v $ (fin2SuccRange i)) + v $ (nat2finS n))%A.
  Proof. intros. apply vsumS_tail; auto. Qed.

  (** `vsum` of (S n) elements, equal to addition of head and Sum *)
  Lemma vsumS_head : forall {n} (v : vec (S n)),
      vsum v = (v $ (nat2finS 0) + vsum (fun i => v $ (fin2SuccRangeSucc i)))%A.
  Proof. intros. apply vsumS_head; auto. Qed.

  (** (∀ i, u.i = v.i + w.i) -> Σu = Σv + Σw *)
  Lemma vsum_add : forall {n} (u v w : vec n),
      ((forall i, u $ i = v $ i + w $ i) -> vsum u = vsum v + vsum w)%A.
  Proof. intros. apply vsum_add; auto. Qed.
  
  (** (∀ i, u.i = - v.i) -> Σu = - Σv *)
  Lemma vsum_opp : forall {n} (u v : vec n),
      ((forall i, u $ i = - v $ i) -> vsum u = - vsum v)%A.
  Proof. intros. apply vsum_opp; auto. Qed.

  (** (∀ i, u.i = k * v.i) -> Σu = k * Σv *)
  Lemma vsum_cmul : forall {n} (u v : vec n) k,
      (forall i, u $ i = k * v $ i) -> vsum u = k * vsum v.
  Proof. intros. apply vsum_cmul; auto. Qed.
  
  (** `vsum` which only one item is nonzero, then got this item. *)
  Lemma vsum_unique : forall {n} (v : vec n) (a : A) i,
      v $ i = a -> (forall j, i <> j -> v $ j = 0) -> vsum v = a.
  Proof. intros. apply vsum_unique with (i:=i); auto. Qed.

  (** `vsum` of the m+n elements equal to plus of two parts.
      (i < m -> f.i = g.i) ->
      (i < n -> f.(m+i) = h.i) ->
      Σ[0,(m+n)] f = Σ[0,m] g + Σ[m,m+n] h. *)
  Lemma vsum_plusIdx : forall m n (f : vec (m + n)) (g : vec m) (h : vec n),
      (forall i : fin m, f $ (fin2AddRangeR i) = g $ i) ->
      (forall i : fin n, f $ (fin2AddRangeAddL i) = h $ i) ->
      vsum f = (vsum g + vsum h)%A.
  Proof. intros. apply vsum_plusIdx; auto. Qed.

  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] v_ij) = 
      v00 + v01 + ... + v0c + 
      v10 + v11 + ... + v1c + 
      ...
      vr0 + vr1 + ... + vrc = 
      ∑[j,0,c](∑[i,0,r] v_ij) *)
  Lemma vsum_vsum_exchg : forall r c (v : @Vector.vec (vec c) r),
      vsum (fun i => vsum (fun j => v $ i $ j)) =
        vsum (fun j => vsum (fun i => v $ i $ j)).
  Proof. intros. apply vsum_vsum_exchg. Qed.

  (* ======================================================================= *)
  (** ** Unit vector *)
  
  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec. *)
  Definition vunit {n} (v : vec n) : Prop := @vunit _ Aadd 0 Amul 1 _ v.

  (** vunit v <-> vunit (vopp u). *)
  Lemma vopp_vunit : forall {n} (v : vec n), vunit (vopp v) <-> vunit v.
  Proof. intros. apply vopp_vunit. Qed.

  (* ======================================================================= *)
  (** ** Orthogonal vectors *)

  (* Two vectors, u and v, in an inner product space v, are orthogonal (also called 
     perpendicular) if their inner-product is zero. It can be denoted as `u ⟂ v` *)
  
  Definition vorth {n} (u v : vec n) : Prop := <u, v> = 0.
  Infix "_|_" := vorth (at level 50).

  (** u _|_ v -> v _|_ u *)
  Lemma vorth_comm : forall {n} (u v : vec n), u _|_ v -> v _|_ u.
  Proof. intros. apply vorth_comm; auto. Qed.

  Open Scope mat_scope.

  (* ======================================================================= *)
  (** ** Identity matrix *)

  (** Identity matrix *)
  Definition mat1 {n : nat} : mat n n := @mat1 _ 0 1 _.

  (** mat1 is diagonal matrix *)
  Lemma mat1_diag : forall {n : nat}, mdiag (@mat1 n).
  Proof. intros. apply mat1_diag. Qed.
  
  (** mat1 \T = mat1 *)
  Lemma mtrans_mat1 : forall {n : nat}, (@mat1 n) \T = mat1.
  Proof. intros. apply mtrans_mat1. Qed.

  (** mat1[i,i] = 1 *)
  Lemma mnth_mat1_same : forall {n} i, (@mat1 n) $ i $ i = 1.
  Proof. intros. apply mnth_mat1_same; auto. Qed.

  (** mat1[i,j] = 0 *)
  Lemma mnth_mat1_diff : forall {n} i j, i <> j -> (@mat1 n) $ i $ j = 0.
  Proof. intros. apply mnth_mat1_diff; auto. Qed.

  (* ======================================================================= *)
  (** ** Matrix trace *)
  Definition mtrace {n : nat} (M : smat n) : A := @mtrace _ Aadd 0 _ M.
  Notation "'tr' M" := (mtrace M) : mat_scope.

  (** tr(M \T) = tr(M) *)
  Lemma mtrace_mtrans : forall {n} (M : smat n), tr (M \T) = tr(M).
  Proof. intros. apply mtrace_mtrans. Qed.

  (** tr(M + N) = tr(M) + tr(N) *)
  Lemma mtrace_madd : forall {n} (M N : smat n), tr (M + N) = (tr M + tr N)%A.
  Proof. intros. apply mtrace_madd. Qed.
  
  (* ======================================================================= *)
  (** ** Monoid structure over {madd,mat0,meq} *)
  #[export] Instance Monoid_madd : forall r c, Monoid (@madd r c) mat0.
  Proof. apply Monoid_madd. Qed.
  
  (* ======================================================================= *)
  (** ** Matrix opposition *)
  
  Definition mopp {r c} (M : mat r c) : mat r c := mopp M (Aopp:=Aopp).
  Notation "- a" := (mopp a) : mat_scope.

  (** - (M + N) = (- M) + (- N) *)
  Lemma mopp_madd : forall {r c : nat} (M N : mat r c), - (M + N) = (- M) + (- N).
  Proof. intros. apply mopp_madd. Qed.

  (** (- M) + M = mat0 *)
  Lemma madd_mopp_l : forall r c (M : mat r c), (- M) + M = mat0.
  Proof. intros. apply madd_opp_l. Qed.

  (** M + (-M) = mat0 *)
  Lemma madd_mopp_r : forall r c (M : mat r c), M + (- M) = mat0.
  Proof. intros. apply madd_opp_r. Qed.

  (** - (- M) = m *)
  Lemma mopp_mopp : forall {r c} (M : mat r c), - (- M) = M.
  Proof. intros. apply mopp_mopp. Qed.

  (** - mat0 = mat0 *)
  Lemma mopp_0 : forall {r c}, - (@mat0 r c) = mat0.
  Proof. intros. apply mopp_mat0. Qed.

  (** (- M) \T = - (M \T) *)
  Lemma mtrans_mopp : forall {r c} (M : mat r c), (- M) \T = - (M \T).
  Proof. intros. apply mtrans_mopp. Qed.

  (** tr(- M) = - (tr(m)) *)
  Lemma mtrace_mopp : forall {n} (M : smat n), mtrace (- M) = (- (mtrace M))%A.
  Proof. intros. apply mtrace_mopp. Qed.
  
  (* ======================================================================= *)
  (** ** Matrix subtraction *)
  
  Definition msub {r c} (M N : mat r c) : mat r c := @msub _ Aadd Aopp _ _ M N.
  Infix "-" := msub : mat_scope.

  (** M - N = M + (- N) *)
  Lemma msub_rw : forall {r c} (M N : mat r c), M - N = M + (- N).
  Proof. intros. reflexivity. Qed.

  (** M - N = - (N - M) *)
  Lemma msub_comm : forall {r c} (M N : mat r c), M - N = - (N - M).
  Proof. intros. apply msub_comm. Qed.

  (** (M - N) - O = M - (N + O) *)
  Lemma msub_assoc : forall {r c} (M N O : mat r c), (M - N) - O = M - (N + O).
  Proof. intros. apply msub_assoc. Qed.

  (** (M + N) - O = M + (N - O) *)
  Lemma msub_assoc1 : forall {r c} (M N O : mat r c), (M + N) - O = M + (N - O).
  Proof. intros. apply msub_assoc1. Qed.

  (** (M - N) - O = M - (O - N) *)
  Lemma msub_assoc2 : forall {r c} (M N O : mat r c), (M - N) - O = (M - O) - N.
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

  (** (M - N) \T = M \T - N \T *)
  Lemma mtrans_msub : forall {r c} (M N : mat r c), (M - N) \T = M \T - N \T.
  Proof. intros. apply mtrans_msub. Qed.

  (** tr(M - N) = tr(M) - tr(N) *)
  Lemma mtrace_msub : forall {n} (M N : smat n), tr (M - N) = (tr M - tr N)%A.
  Proof. intros. apply mtrace_msub. Qed.

  (* ======================================================================= *)
  (** ** Abelian group structure over {madd,mat0,mopp} *)
  #[export] Instance AGroup_MatAdd : forall r c, AGroup (@madd r c) mat0 mopp.
  Proof. apply AGroup_madd. Qed.

  (* ======================================================================= *)
  (** ** Scalar multiplication of matrix *)

  (** Scalar multiplication of matrix *)
  Definition mcmul {r c} (a : A) (M : mat r c) : mat r c := mcmul a M (Amul:=Amul).
  Infix "\.*" := mcmul : mat_scope.

  (** (a * M)[i,j] = a * M[i,j] *)
  Lemma mnth_mcmul : forall {r c} (M : mat r c) a i j, (a \.* M) $ i $ j = a * (M $ i $ j).
  Proof. intros. unfold mcmul. apply mnth_mcmul. Qed.

  (** cv2v (a .* v) = a .* (cv2v v) *)
  Lemma cv2v_mcmul : forall {n} (a : A) (v : cvec n), cv2v (a \.* v) = (a \.* (cv2v v))%V.
  Proof. intros. apply cv2v_mcmul. Qed.

  (** 0 \.* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (M : mat r c), 0 \.* M = mat0.
  Proof. intros. apply mcmul_0_l. Qed.

  (** a \.* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a \.* (@mat0 r c) = mat0.
  Proof. intros. apply mcmul_0_r. Qed.

  (** 1 \.* m = m *)
  Lemma mcmul_1_l : forall {r c} (M : mat r c), 1 \.* M = M.
  Proof. intros. apply mcmul_1_l. Qed.

  (** a \.* mat1 = mdiag([a,a,...]) *)
  Lemma mcmul_1_r : forall {n} a, a \.* mat1 = mdiagMk (vrepeat n a).
  Proof. intros. apply mcmul_1_r. Qed.

  (** a \.* (b \.* M) = (a * b) \.* m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (M : mat r c),
      a \.* (b \.* M) = (a * b) \.* M.
  Proof. intros. apply mcmul_assoc. Qed.

  (** a \.* (b \.* M) = b \.* (a \.* M) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (M : mat r c),
      a \.* (b \.* M) = b \.* (a \.* M).
  Proof. intros. apply mcmul_perm. Qed.

  (** (a + b) \.* M = (a \.* M) + (b \.* M) *)
  Lemma mcmul_add_distr : forall {r c} (a b : A) (M : mat r c), 
      (a + b)%A \.* M = (a \.* M) + (b \.* M).
  Proof. intros. apply mcmul_add_distr. Qed.

  (** a \.* (M + N) = (a \.* M) + (a \.* N) *)
  Lemma mcmul_madd_distr : forall {r c} (a : A) (M N : mat r c), 
      a \.* (M + N) = (a \.* M) + (a \.* N).
  Proof. intros. apply mcmul_madd_distr. Qed.
  
  (** (-a) \.* M  = - (a \.* M) *)
  Lemma mcmul_opp : forall {r c} a (M : mat r c), (- a)%A \.* M = - (a \.* M).
  Proof. intros. apply mcmul_opp. Qed.
  
  (** a \.* (- M)  = - (a \.* M) *)
  Lemma mcmul_mopp : forall {r c} a (M : mat r c), a \.* (- M) = - (a \.* M).
  Proof. intros. apply mcmul_mopp. Qed.

  (** a \.* (M - N) = (a \.* M) - (a \.* N) *)
  Lemma mcmul_msub : forall {r c} a (M N : mat r c),
      a \.* (M - N) = (a \.* M) - (a \.* N).
  Proof. intros. apply mcmul_msub. Qed.

  (** (a \.* M) \T = a \.* (M \T) *)
  Lemma mtrans_mcmul : forall {r c} (a : A) (M : mat r c), (a \.* M) \T = a \.* (M \T).
  Proof. intros. apply mtrans_mcmul. Qed.

  (** tr (a \.* M) = a * tr (m) *)
  Lemma mtrace_mcmul : forall {n} (a : A) (M : smat n), tr (a \.* M) = (a * tr M)%A.
  Proof. intros. apply mtrace_mcmul. Qed.

  (** (M <> 0 /\ N <> 0 /\ k * M = N) -> k <> 0 *)
  Lemma mcmul_eq_implfy_not_k0 : forall {r c} (M N : mat r c) k,
      M <> mat0 -> N <> mat0 -> k \.* M = N -> k <> 0.
  Proof. intros. apply mcmul_eq_implfy_not_k0 in H1; auto. Qed.

  (* ======================================================================= *)
  (** ** Matrix multiplication *)
  Definition mmul {r c s : nat} (M : mat r c) (N : mat c s) : mat r s :=
    mmul M N (Amul:=Amul)(Azero:=0)(Aadd:=Aadd).
  Infix "*" := mmul : mat_scope.

  (** N is cvec -> M * N = fun i => (vdot N) (M $ i) *)
  Lemma mmul_cvec : forall {r c} (M : mat r c) (N : cvec c),
      M * N = fun i j => <cv2v N, M $ i>.
  Proof. intros. apply mmul_cvec. Qed.

  (** M is rvec -> M * N = fun i j => (vdot M) (mcol N j) *)
  Lemma mmul_rvec : forall {r c} (M : rvec r) (N : mat r c),
      M * N = fun i j => <rv2v M, mcol N j>.
  Proof. intros. apply mmul_rvec. Qed.

  (** <row(M,i), col(N,j)> = [M * N].ij *)
  Lemma vdot_row_col : forall {r c s} (M : mat r c) (N : mat c s) i j,
      <mrow M i, mcol N j> = (M * N) $ i $ j.
  Proof. intros. apply vdot_row_col. Qed.

  (** <col(M,i), col(N,j)> = (M\T * N)[i,j] *)
  Lemma vdot_col_col : forall {n} (M N : smat n) i j,
      <mcol M i, mcol N j> = (M\T * N) $ i $ j.
  Proof. intros. apply vdot_col_col. Qed.

  (** <row(M,i), row(N,j)> = (M * N\T)[i,j] *)
  Lemma vdot_row_row : forall {n} (M N : smat n) i j,
      <mrow M i, mrow N j> = (M * N\T) $ i $ j.
  Proof. intros. apply vdot_row_row. Qed.

  (** <u,v> = (u\T * v).11 *)
  Lemma vdot_eq_mmul : forall {n} (u v : vec n), <u, v> = (v2rv u * v2cv v).11.
  Proof. intros. apply vdot_eq_mmul. Qed.

  (** (M * N) * O = M * (N * O) *)
  Lemma mmul_assoc : forall {r c s t : nat} (M : mat r c) (N : mat c s) (O : mat s t), 
      (M * N) * O = M * (N * O).
  Proof. intros. apply mmul_assoc. Qed.

  (** M * (N + O) = M * N + M * O *)
  Lemma mmul_madd_distr_l : forall {r c s : nat} (M : mat r c) (N O : mat c s), 
      M * (N + O) = M * N + M * O.
  Proof. intros. apply mmul_madd_distr_l. Qed.
  
  (** (M + N) * O = M * O + N * O *)
  Lemma mmul_madd_distr_r : forall {r c s : nat} (M N : mat r c) (O : mat c s),
      (M + N) * O = M * O + N * O.
  Proof. intros. apply mmul_madd_distr_r. Qed.

  (** M * (N - O) = M * N - M * O *)
  Lemma mmul_msub_distr_l : forall {r c s : nat} (M : mat r c) (N O : mat c s), 
      M * (N - O) = M * N - M * O.
  Proof. intros. apply mmul_msub_distr_l. Qed.
  
  (** (M - N) * O = M * O - N * O *)
  Lemma mmul_msub_distr_r : forall {r c s : nat} (M N : mat r c) (O : mat c s),
      (M - N) * O = M * O - N * O.
  Proof. intros. apply mmul_msub_distr_r. Qed.

  (** (- M) * N = - (M * N) *)
  Lemma mmul_mopp_l : forall {r c s : nat} (M : mat r c) (N : mat c s),
      (- M) * N = - (M * N).
  Proof. intros. apply mmul_mopp_l. Qed.

  (** M * (- N) = - (M * N) *)
  Lemma mmul_mopp_r : forall {r c s : nat} (M : mat r c) (N : mat c s),
      M * (- N) = - (M * N).
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

  (** a \.* (M * N) = (a \.* M) * N. *)
  Lemma mmul_mcmul_l : forall {r c s} (a : A) (M : mat r c) (N : mat c s), 
      (a \.* M) * N = a \.* (M * N).
  Proof. intros. apply mmul_mcmul_l. Qed.
  
  (** a \.* (M * N) = M * (a \.* N) *)
  Lemma mmul_mcmul_r : forall {r c s} (a : A) (M : mat r c) (N : mat c s), 
      M * (a \.* N) = a \.* (M * N).
  Proof. intros. apply mmul_mcmul_r. Qed.
  
  (** (M * N) \T = N \T * M \T *)
  Lemma mtrans_mmul : forall {r c s} (M : mat r c) (N : mat c s),
      (M * N) \T = N \T * M \T.
  Proof. intros. apply mtrans_mmul. Qed.

  (** tr (M * N) = tr (N * M) *)
  Lemma mtrace_mmul : forall {r c} (M : mat r c) (N : mat c r), tr (M * N) = tr (N * M).
  Proof. intros. apply mtrace_mmul. Qed.
  
  (* ======================================================================= *)
  (** ** Matrix multiply vector (treat vector as column vector) *)

  Open Scope vec_scope.
  
  Definition mmulv {r c : nat} (M : mat r c) (v : vec c) : vec r :=
    @mmulv _ Aadd 0 Amul _ _ M v.
  Infix "*" := mmulv : vec_scope.

  (** (M * v)[i] = <row M i, v> *)
  Lemma vnth_mmulv : forall {r c} (M : mat r c) (v : vec c) i,
      (M * v) $ i = <M $ i, v>.
  Proof. intros. apply vnth_mmulv. Qed.

  (** (M * N) * v = M * (N * v) *)
  Lemma mmulv_assoc : forall {m n r} (M : mat m n) (N : mat n r) (v : vec r),
      (M * N)%M * v = M * (N * v).
  Proof. intros. apply mmulv_assoc. Qed.

  (** M * (u + v) = M * u + M * v *)
  Lemma mmulv_vadd : forall {r c} (M : mat r c) (u v : vec c),
      M * (u + v) = (M * u) + (M * v).
  Proof. intros. apply mmulv_vadd. Qed.
  
  (** (M + N) * v = M * v + N * v *)
  Lemma mmulv_madd : forall {r c} (M N : mat r c) (v : vec c),
      (M + N)%M * v = (M * v) + (N * v).
  Proof. intros. apply mmulv_madd. Qed.

  (** (- M) * v = - (M * v) *)
  Lemma mmulv_mopp : forall {r c} (M : mat r c) (v : vec c), (- M)%M * v = - (M * v).
  Proof. intros. apply mmulv_mopp. Qed.

  (** M * (- v) = - (M * v) *)
  Lemma mmulv_vopp : forall {r c} (M : mat r c) (v : vec c), M * (- v) = - (M * v).
  Proof. intros. apply mmulv_vopp. Qed.

  (** M * (u - v) = M * u - M * v *)
  Lemma mmulv_vsub : forall {r c} (M : mat r c) (u v : vec c),
      M * (u - v) = (M * u) - (M * v).
  Proof. intros. apply mmulv_vsub. Qed.
  
  (** (M - N) * v = M * v - N * v *)
  Lemma mmulv_msub : forall {r c} (M N : mat r c) (v : vec c),
      (M - N)%M * v = (M * v) - (N * v).
  Proof. intros. apply mmulv_msub. Qed.
  
  (** 0 * v = 0 *)
  Lemma mmulv_0_l : forall {r c} (v : vec c), (@mat0 r c) * v = vzero.
  Proof. intros. apply mmulv_0_l. Qed.
  
  (** M * 0 = 0 *)
  Lemma mmulv_0_r : forall {r c} (M : mat r c), M * vzero = vzero.
  Proof. intros. apply mmulv_0_r. Qed.
  
  (** 1 * v = v *)
  Lemma mmulv_1_l : forall {n} (v : vec n), mat1 * v = v.
  Proof. intros. apply mmulv_1_l. Qed.

  (** (a \.* M) * v = a \.* (M * v) *)
  Lemma mmulv_mcmul : forall {r c} (a : A) (M : mat r c) (v : vec c), 
      (a \.* M)%M * v = a \.* (M * v).
  Proof. intros. apply mmulv_mcmul. Qed.
  
  (** M * (a \.* v) = a \.* (M * v) *)
  Lemma mmulv_vcmul : forall {r c} (a : A) (M : mat r c) (v : vec c), 
      M * (a \.* v) = a \.* (M * v).
  Proof. intros. apply mmulv_vcmul. Qed.

  (** <u,v> = (u\T * v).1 *)
  Lemma vdot_eq_mmulv : forall {n} (u v : vec n), <u, v> = (v2rv u * v).1.
  Proof. intros. apply vdot_eq_mmulv. Qed.
  
  (** v2cv (M * v) = M * v2cv v *)
  Lemma v2cv_mmulv : forall {r c} (M : mat r c) (v : vec c),
      v2cv (M * v) = (M * v2cv v)%M.
  Proof. intros. apply v2cv_mmulv. Qed.

  (** v2rv (M * v) = (v2rv v) * M\T *)
  Lemma v2rv_mmulv : forall {r c} (M : mat r c) (v : vec c),
      v2rv (M * v) = (v2rv v * M\T)%M.
  Proof. intros. apply v2rv_mmulv. Qed.


  Open Scope mat_scope.
  
  (* ======================================================================= *)
  (** ** Skew-symmetric matrix *)
  
  (** Given matrix is skew-symmetric matrices *)
  Definition skewP {n} (M : smat n) : Prop := - M = M\T.

  (** Make suere skewP is equal to Matrix.skewP  *)
  Lemma skewP_eq : forall {n} (M : smat n), skewP M = @Matrix.skewP _ Aopp _ M.
  Proof. intros. auto. Qed.

  (* ======================================================================= *)
  (** ** Hardmard product *)

  (** Hardmard product (also known as the element-wise product, entrywise product 
      or Schur product).
      It is a binary operation that takes two matrices of the same dimensions and 
      produces another matrix of the same dimension as the operandds, where each 
      element i,j is the product of elements i,j of the original two matrices.

      The hardmard product is associative, distribute and commutative *)
  (* Definition mhp {n : nat} (M N : smat n) : smat n := mhp m1 m2 (Amul:=Amul). *)
  (* Infix "⦿" := mhp : mat_scope. *)

  (* ======================================================================= *)
  (** ** Determinant of a matrix *)

  (** Determinant of a square matrix *)
  Definition mdet {n} (M : smat n) : A := @mdet _ Aadd 0 Aopp Amul 1 _ M.

  (** |M \T| = |M| *)
  Lemma mdet_mtrans : forall {n} (M : smat n), mdet (M \T) = mdet M.
  Proof. intros. apply mdet_mtrans. Qed.

  (** |M * N| = |M| * |N| *)
  Lemma mdet_mmul : forall {n} (M N : smat n), mdet (M * N) = (mdet M * mdet N)%A.
  Proof. intros. apply mdet_mmul. Qed.

  (** |mat1| = 1 *)
  Lemma mdet_mat1 : forall {n}, mdet (@mat1 n) = 1.
  Proof. intros. apply mdet_mat1. Qed.

  (* ======================================================================= *)
  (** ** Determinant on matrix of 1-,2-, or 3-dim*)

  (** Determinant of a matrix of given dimension *)
  Definition mdet1 (M : smat 1) := mdet1 M.
  Definition mdet2 (M : smat 2) := @mdet2 _ Aadd Aopp Amul M.
  Definition mdet3 (M : smat 3) := @mdet3 _ Aadd Aopp Amul M.

  (** mdet1 M = |M| *)
  Lemma mdet1_eq_mdet : forall M, mdet1 M = mdet M.
  Proof. intros. apply mdet1_eq_mdet. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet1_neq0_iff : forall (M : smat 1), mdet M <> 0 <-> M.11 <> 0.
  Proof. intros. apply mdet1_neq0_iff. Qed.

  (** mdet2 M = |M| *)
  Lemma mdet2_eq_mdet : forall M, mdet2 M = mdet M.
  Proof. intros. apply mdet2_eq_mdet. Qed.

  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet2_neq0_iff : forall (M : smat 2),
      mdet M <> 0 <-> (M.11*M.22 - M.12*M.21)%A <> 0.
  Proof. intros. apply mdet2_neq0_iff. Qed.

  (** mdet3 M = |M| *)
  Lemma mdet3_eq_mdet : forall M, mdet3 M = mdet M.
  Proof. intros. apply mdet3_eq_mdet. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet3_neq0_iff : forall (M : smat 3),
      mdet M <> 0 <->
         (M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
            M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
            M.13 * M.21 * M.32 - M.13 * M.22 * M.31)%A <> 0.
  Proof. intros. apply mdet3_neq0_iff. Qed.
  
  (* ======================================================================= *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix: adj(A)[i,j] = algebraic remainder of A[i,j]. *)
  Definition madj {n} (M : smat n) : smat n :=
    @madj _ Aadd 0 Aopp Amul 1 _ M.

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
      minvertible M <-> mdet M <> 0.
  Proof. intros. apply minvertible_iff_mdet_neq0. Qed.

  (** invertible M -> invertible (M \T) *)
  Lemma minvertible_mtrans : forall n (M : smat n),
      minvertible M -> minvertible (M \T).
  Proof. intros. apply minvertible_mtrans; auto. Qed.

  (** invertible M -> invertible N -> invertible (M * N) *)
  Lemma minvertible_mmul : forall n (M N : smat n),
      minvertible M -> minvertible N -> minvertible (M * N).
  Proof. intros. apply minvertible_mmul; auto. Qed.

End RingMatrixTheory.


(* ######################################################################### *)
(** * Ordered ring matrix theory *)
Module OrderedRingMatrixTheory (E : OrderedRingElementType).

  Include (RingMatrixTheory E).

  Open Scope vec_scope.
  
  (** 0 <= <v, v> *)
  Lemma vdot_ge0 : forall {n} (v : vec n), 0 <= (<v, v>).
  Proof. intros. apply vdot_ge0. Qed.
  
  (** <u, v> ² <= <u, u> * <v, v> *)
  Lemma vdot_sqr_le : forall {n} (u v : vec n), (<u, v> ²) <= (<u, u> * <v, v>)%A.
  Proof. intros. apply vdot_sqr_le. Qed.

  (** (v i)² <= <v, v> *)
  Lemma vnth_sqr_le_vdot : forall {n} (v : vec n) (i : fin n), (v i) ² <= <v, v>.
  Proof. intros. apply vnth_sqr_le_vdot. Qed.

  (** (∀ i, 0 <= v.i) -> v.i <= ∑v *)
  Lemma vsum_ge_any : forall {n} (v : vec n) i, (forall i, 0 <= v $ i) -> v $ i <= vsum v.
  Proof. intros. apply vsum_ge_any; auto. Qed.
  
  (** (∀ i, 0 <= v.i) -> 0 <= ∑v *)
  Lemma vsum_ge0 : forall {n} (v : vec n), (forall i, 0 <= v $ i) -> 0 <= vsum v.
  Proof. intros. apply vsum_ge0; auto. Qed.
  
  (** (∀ i, 0 <= v.i) -> (∃ i, v.i <> 0) -> 0 < ∑v *)
  Lemma vsum_gt0 : forall {n} (v : vec n),
      (forall i, 0 <= v $ i) -> (exists i, v $ i <> 0) -> 0 < vsum v.
  Proof. intros. apply vsum_gt0; auto. Qed.

End OrderedRingMatrixTheory.


(* ######################################################################### *)
(** * Field matrix theory *)

Module FieldMatrixTheory (E : FieldElementType).
  
  Include (RingMatrixTheory E).

  Open Scope vec_scope.

  (* ======================================================================= *)
  (** ** Properties about vcmul *)
  
  (** k * v = 0 -> (k = 0) \/ (v = 0) *)
  Lemma vcmul_eq0_imply_k0_or_v0 : forall {n} k (v : vec n),
      k \.* v = vzero -> (k = 0) \/ (v = vzero).
  Proof. intros. apply vcmul_eq0_imply_k0_or_v0; auto. Qed.

  (** k * v = 0 -> v <> 0 -> k = 0 *)
  Lemma vcmul_eq0_imply_k0 : forall {n} k (v : vec n),
      k \.* v = vzero -> v <> vzero -> k = 0.
  Proof. intros. apply (vcmul_eq0_imply_k0 k v); auto. Qed.

  (** k * v = 0 -> k <> 0 -> v = 0 *)
  Lemma vcmul_eq0_imply_v0 : forall {n} k (v : vec n),
      k \.* v = vzero -> k <> 0 -> v = vzero.
  Proof. intros. apply (vcmul_eq0_imply_v0 k v); auto. Qed.
  
  (** k * v = v -> k = 1 \/ v = 0 *)
  Lemma vcmul_same_imply_k1_or_v0 : forall {n} k (v : vec n),
      k \.* v = v -> (k = 1 \/ v = vzero).
  Proof. intros. apply vcmul_same_imply_k1_or_v0; auto. Qed.
  
  (** k = 1 \/ v = 0 -> k * v = v *)
  Lemma vcmul_same_if_k1_or_v0 : forall {n} k (v : vec n),
      (k = 1 \/ v = vzero) -> k \.* v = v.
  Proof. intros. apply vcmul_same_if_k1_or_v0; auto. Qed.
  
  (** k * v = v -> v <> 0 -> k = 1 *)
  Lemma vcmul_same_imply_k1 : forall {n} k (v : vec n),
      k \.* v = v -> v <> vzero -> k = 1.
  Proof. intros. apply (vcmul_same_imply_k1 k v); auto. Qed.
  
  (** k * v = v -> k <> 1 -> v = 0 *)
  Lemma vcmul_same_imply_v0 : forall {n} k (v : vec n),
      k \.* v = v -> k <> 1 -> v = vzero.
  Proof. intros. apply (vcmul_same_imply_v0 k v); auto. Qed.

  (* k1 * v = k2 * v -> (k1 = k2 \/ v = 0) *)
  Lemma vcmul_sameV_imply_eqK_or_v0 : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> (k1 = k2 \/ v = vzero).
  Proof. intros. apply vcmul_sameV_imply_eqK_or_v0; auto. Qed.

  (* k1 * v = k2 * v -> v <> 0 -> k1 = k2 *)
  Lemma vcmul_sameV_imply_eqK : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> v <> vzero -> k1 = k2.
  Proof. intros. apply vcmul_sameV_imply_eqK in H; auto. Qed.

  (* k1 * v = k2 * v -> k1 <> k2 -> v = 0 *)
  Lemma vcmul_sameV_imply_v0 : forall {n} k1 k2 (v : vec n), 
      k1 \.* v = k2 \.* v -> k1 <> k2 -> v = vzero.
  Proof. intros. apply vcmul_sameV_imply_v0 in H; auto. Qed.

  (** (k \.* u) _|_ v <-> u _|_ v *)
  Lemma vorth_vcmul_l : forall {n} k (u v : vec n),
      k <> 0 -> ((k \.* u) _|_ v <-> u _|_ v).
  Proof. intros. apply vorth_vcmul_l; auto. Qed.
  
  (** u _|_ (k \.* v) <-> u _|_ v *)
  Lemma vorth_vcmul_r : forall {n} k (u v : vec n),
      k <> 0 -> (u _|_ (k \.* v) <-> u _|_ v).
  Proof. intros. apply vorth_vcmul_r; auto. Qed.

  (* ======================================================================= *)
  (** ** Projection component of a vector onto another *)
  
  (** The projection component of a onto b *)
  Definition vproj {n} (u v : vec n) : vec n := @vproj _ Aadd 0 Amul Ainv _ u v.

  (** vunit v -> vproj u v = <u, v> \.* v *)
  Lemma vproj_vunit : forall {n} (u v : vec n), vunit v -> vproj u v = <u, v> \.* v.
  Proof. intros. apply vproj_vunit; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Perpendicular component of a vector respect to another *)
  
  (** The perpendicular component of u respect to u *)
  Definition vperp {n} (u v : vec n) : vec n :=
    @vperp _ Aadd 0 Aopp Amul Ainv _ u v.

  (** vperp u v = u - vproj u v *)
  Lemma vperp_eq_minus_vproj : forall {n} (u v : vec n), vperp u v = u - vproj u v.
  Proof. intros; apply vperp_eq_minus_vproj. Qed.

  (** vproj u v = u - vperp u v *)
  Lemma vproj_eq_minus_vperp : forall {n} (u v : vec n), vproj u v = u - vperp u v.
  Proof. intros; apply vproj_eq_minus_vperp. Qed.

  (** vproj u v = u - vperp u v *)
  Lemma vproj_plus_vperp : forall {n} (u v : vec n), vproj u v + vperp u v = u.
  Proof. intros; apply vproj_plus_vperp. Qed.

  (** u _|_ v -> vperp u v = u *)
  Lemma vorth_imply_vperp_eq_l : forall {n} (u v : vec n),
      v <> vzero -> u _|_ v -> vperp u v = u.
  Proof. intros. apply vorth_imply_vperp_eq_l; auto. Qed.
  
  (* ======================================================================= *)
  (** ** un-sorted properties about vector *)

  (** The unit vector cannot be zero vector *)
  Lemma vunit_neq0 : forall {n} (v : vec n), vunit v -> v <> vzero.
  Proof. intros. apply vunit_neq0; auto. Qed.

  (** Index of first nonzero element in a vector start from i *)
  Definition vfirstNonZeroFrom {n} (v : vec n) (i : fin n) : option (fin n) :=
    vfirstNonZeroFrom (Azero:=0) v i.
  
  (** Index of first nonzero element in a vector *)
  Definition vfirstNonZero {n} (v : vec n) : option (fin n) :=
    vfirstNonZero v (Azero:=0).

  Open Scope mat_scope.
  
  (* ======================================================================= *)
  (** ** Properties about zero or non-zero matrices *)

  (** k * M = 0 -> (k = 0) \/ (M = 0) *)
  Lemma mcmul_eq0_imply_m0_or_k0 : forall {r c} (M : mat r c) k,
      k \.* M = mat0 -> k = 0 \/ (M = mat0).
  Proof. intros. apply mcmul_eq0_imply_m0_or_k0; auto. Qed.

  (** (M <> 0 /\ k * M = 0) -> M = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (M : mat r c) k,
      M <> mat0 -> k \.* M = mat0 -> k = 0.
  Proof. intros. apply mcmul_mnonzero_eq0_imply_k0 with (M:=M); auto. Qed.

  (** k * M = M -> k = 1 \/ M = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} k (M : mat r c),
      k \.* M = M -> k = 1 \/ (M = mat0).
  Proof. intros. apply mcmul_same_imply_coef1_or_mzero; auto. Qed.

  (* ======================================================================= *)
  (** ** Gauss Elimination *)

  (** Elementary row operation *)
  Definition RowOp {r} := @RowOp A r.

  (** Convert row operation to matrix *)
  Definition rowOp2mat {r} (x : @RowOp r) : smat r :=
    @rowOp2mat _ Aadd 0 Amul 1 _ x.
  
  (** Convert list of row operation to matrix *)
  Definition rowOpList2mat {r} (l : list (@RowOp r)) : smat r :=
    @rowOpList2mat _ Aadd 0 Amul 1 _ l.

  (** Convert to echelon matrix *)
  Definition echelon {r c} (M : mat r c) : list (@RowOp r) * mat r c :=
    @echelon _ Aadd Azero Aopp Amul Ainv AeqDec _ _ M.
  
  (** Convert to simplest row echelon matrix *)
  Definition minEchelon {r c} (M : mat r c) : list (@RowOp r) * mat r c :=
    @minEchelon _ Aadd Azero Aopp Amul Aone Ainv AeqDec _ _ M.

  (** inverse matrix by gauss elimination (option version) *)
  Definition minvGEo {n} (M : smat n) : option (smat n) :=
    @minvGEo _ Aadd 0 Aopp Amul 1 Ainv _ _ M.
    
  (** inverse matrix by gauss elimination (if input a non-invertible matrix, 
      return identity matrix) *)
  Definition minvGE {n} (M : smat n) : smat n :=
    @minvGE _ Aadd 0 Aopp Amul 1 Ainv _ _ M.
  
  (* ======================================================================= *)
  (** ** Cramer rule *)
  
  (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid only when D is not zero *)
  Definition cramerRule {n} (A : smat n) (b : vec n) : vec n :=
    @cramerRule _ Aadd 0 Aopp Amul 1 Ainv _ A b.

  (* ======================================================================= *)
  (** ** Matrix Inversion by AM *)

  (** inverse matrix by adjoint matrix *)
  Definition minvAM {n} (M : smat n) : smat n :=
    @minvAM _ Aadd 0 Aopp Amul 1 Ainv _ M.
  
  (** inverse matrix (default method) *)
  Definition minv {n} (M : smat n) := minvAM M.
  Notation "M \-1" := (minv M) : mat_scope.

  (** M * N = mat1 <-> M \-1 = N *)
  Lemma mmul_eq1_iff_minv_l : forall {n} (M N : smat n),
      M * N = mat1 <-> minv M = N.
  Proof. intros. apply AM_mmul_eq1_iff_minv_l; auto. Qed.

  (** M * N = mat1 <-> M \-1 = M *)
  Lemma mmul_eq1_iff_minv_r : forall {n} (M N : smat n),
      M * N = mat1 <-> minv N = M.
  Proof. intros. apply AM_mmul_eq1_iff_minv_r; auto. Qed.

  (** invertible M -> invertible (M \-1) *)
  Lemma minvertible_inv : forall {n} (M : smat n),
      minvertible M -> minvertible (M \-1).
  Proof. intros. apply AM_minv_invertible; auto. Qed.

  (** M \-1 * M = mat1 *)
  Lemma mmul_minv_l : forall n (M : smat n), minvertible M -> (minv M) * M = mat1.
  Proof. intros. apply AM_mmul_minv_l; auto. Qed.
  
  (** M * M \-1 = mat1 *)
  Lemma mmul_minv_r : forall n (M : smat n), minvertible M -> M * M \-1 = mat1.
  Proof. intros. apply AM_mmul_minv_r; auto. Qed.

  (** mat1 \-1 = mat1 *)
  Lemma minv_1 : forall n, @minv n mat1 = mat1.
  Proof. intros. apply AM_minv_mat1. Qed.

  (** M \-1 \-1 = M *)
  Lemma minv_minv : forall n (M : smat n), minvertible M -> M \-1 \-1 = M.
  Proof. intros. apply AM_minv_minv; auto. Qed.

  (** (M * N) \-1 = N \-1 * M \-1 *)
  Lemma minv_mmul : forall n (M N : smat n),
      minvertible M -> minvertible N -> (M * N) \-1 = N \-1 * M \-1.
  Proof. intros. apply AM_minv_mmul; auto. Qed.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma minv_mtrans : forall n (M : smat n), minvertible M -> (M \T) \-1 = (M \-1) \T.
  Proof. intros. apply AM_minv_mtrans; auto. Qed.
  
  (** mdet (M \-1) = 1 / (|M|) *)
  Lemma mdet_minv : forall {n} (M : smat n), mdet (M \-1) = 1 / (mdet M).
  Proof. intros. apply AM_mdet_minv; auto. Qed.

  (** minvertible M -> M * N = M * O -> N = O *)
  Lemma mmul_cancel_l : forall {r c} (M : smat r) (N O : mat r c),
      minvertible M -> M * N = M * O -> N = O.
  Proof. intros. apply mmul_cancel_l in H0; auto. Qed.

  (** minvertible M -> N * M = O * M -> N = O *)
  Lemma mmul_cancel_r : forall {r c} (M : smat c) (N O : mat r c),
      minvertible M -> N * M = O * M -> N = O.
  Proof. intros. apply mmul_cancel_r in H0; auto. Qed.
  
  (** minvertible M -> M * u = M * v -> u = v *)
  Lemma mmulv_cancel_l : forall {n} (M : smat n) (u v : vec n),
      minvertible M -> (M * u = M * v)%V -> u = v.
  Proof. intros. apply mmulv_cancel_l in H0; auto. Qed.
  

  (* ======================================================================= *)
  (** ** Inversion matrix of common finite dimension *)
  
  (** Inversion matrix of dimension-1 *)
  Definition minv1 (M : smat 1) : smat 1 := @minv1AM _ 0 Amul 1 Ainv M.

  (** |M| <> 0 -> minv1 M = inv M *)
  Lemma minv1_eq_inv : forall M, mdet M <> 0 -> minv1 M = minv M.
  Proof. intros. apply AM_minv1_eq_inv; auto. Qed.
  
  (** Inversion matrix of dimension-2 *)
  Definition minv2 (M : smat 2) : smat 2 := @minv2AM _ Aadd 0 Aopp Amul Ainv M.

  (** |M| <> 0 -> minv2 M = inv M *)
  Lemma minv2_eq_inv : forall M, mdet M <> 0 -> minv2 M = minv M.
  Proof. intros. apply AM_minv2_eq_inv; auto. Qed.
  
  (** Inversion matrix of dimension-3 *)
  Definition minv3 (M : smat 3) : smat 3 := @minv3AM _ Aadd 0 Aopp Amul Ainv M.
  
  (** |M| <> 0 -> minv3 M = inv M *)
  Lemma minv3_eq_inv : forall M, mdet M <> 0 -> minv3 M = minv M.
  Proof. intros. apply AM_minv3_eq_inv; auto. Qed.

  (** Inversion matrix of dimension-4 *)
  Definition minv4 (M : smat 4) : smat 4 := @minv4AM _ Aadd 0 Aopp Amul Ainv M.
  
  (** |M| <> 0 -> minv4 M = inv M *)
  Lemma minv4_eq_inv : forall M, mdet M <> 0 -> minv4 M = minv M.
  Proof. intros. apply AM_minv4_eq_inv; auto. Qed.

  (* ======================================================================= *)
  (** ** Orthonormal vectors 标准正交的向量组 *)
  
  (** All (different) column-vectors of a matrix are orthogonal each other.
      For example: [v1;v2;v3] => u_|_v2 && u_|_v3 && v_|_v3. *)
  Definition mcolsOrth {r c} (M : mat r c) : Prop :=
    @mcolsOrth _ Aadd 0 Amul _ _ M.

  (** All column-vectors of a matrix are unit vector.
      For example: [v1;v2;v3] => unit u && unit v && unit v3 *)
  Definition mcolsUnit {r c} (M : mat r c) : Prop :=
    @mcolsUnit _ Aadd 0 Amul 1 _ _ M.

  (** The columns of a matrix is orthogomal *)
  Definition mcolsOrthonormal {r c} (M : mat r c) : Prop :=
    @mcolsOrthonormal _ Aadd 0 Amul 1 _ _ M.
  
  
  (* ======================================================================= *)
  (** ** Orthogonal matrix *)

  (** An orthogonal matrix *)
  Definition morth {n} (M : smat n) : Prop := @morth _ Aadd 0 Amul 1 _ M.
  
  (** matrix M is orthogonal <-> columns of M are orthogomal *)
  Lemma morth_iff_mcolsOrthonormal : forall {n} (M : smat n),
      morth M <-> mcolsOrthonormal M.
  Proof. intros. apply morth_iff_mcolsOrthonormal. Qed.

  (** orthogonal M -> invertible M *)
  Lemma morth_invertible : forall {n} (M : smat n), morth M -> minvertible M.
  Proof. intros. apply morth_invertible; auto. Qed.

  (** orthogonal M -> M \-1 = M \T *)
  Lemma morth_imply_inv_eq_trans : forall {n} (M : smat n), morth M -> M \-1 = M \T.
  Proof. intros. apply morth_imply_inv_eq_trans; auto. Qed.

  (** M \-1 = M \T -> orthogonal M *)
  Lemma minv_eq_trans_imply_morth : forall {n} (M : smat n), M \-1 = M \T -> morth M.
  Proof. intros. apply minv_eq_trans_imply_morth; auto. Qed.

  (** orthogonal M <-> M \T * M = mat1 *)
  Lemma morth_iff_mul_trans_l : forall {n} (M : smat n), morth M <-> M \T * M = mat1.
  Proof. intros. apply morth_iff_mul_trans_l; auto. Qed.

  (** orthogonal M <-> M * M \T = mat1 *)
  Lemma morth_iff_mul_trans_r : forall {n} (M : smat n), morth M <-> M * M \T = mat1.
  Proof. intros. apply morth_iff_mul_trans_r; auto. Qed.

  (** orthogonal mat1 *)
  Lemma morth_mat1 : forall {n}, morth (@mat1 n).
  Proof. intros. apply morth_mat1; auto. Qed.

  (** orthogonal M -> orthogonal N -> orthogonal (M * N) *)
  Lemma morth_mul : forall {n} (M N : smat n), morth M -> morth N -> morth (M * N).
  Proof. intros. apply morth_mul; auto. Qed.

  (** orthogonal M -> orthogonal M \T *)
  Lemma morth_mtrans : forall {n} (M : smat n), morth M -> morth (M \T).
  Proof. intros. apply morth_mtrans; auto. Qed.

  (** orthogonal M -> orthogonal M \-1 *)
  Lemma morth_minv : forall {n} (M : smat n), morth M -> morth (M \-1).
  Proof. intros. apply morth_minv; auto. Qed.

  (** orthogonal M -> |M| = ± 1 *)
  Lemma morth_mdet : forall {n} (M : smat n), morth M -> mdet M = 1 \/ mdet M = (- (1))%A.
  Proof. intros. apply morth_mdet; auto. Qed.

  (** Transformation by orthogonal matrix will keep inner-product *)
  Lemma morth_keep_dot : forall {n} (M : smat n) (u v : vec n),
      morth M -> <M * u, M * v>%V = <u, v>.
  Proof. intros. apply morth_keep_dot; auto. Qed.

  (* ======================================================================= *)
  (** ** O(n): General Orthogonal Group, General Linear Group *)
  
  (** The set of GOn *)
  Definition GOn {n : nat} := (@GOn _ Aadd 0 Amul 1 n).

  (** Additional coercion, hence the re-definition of `mat` and `GOn` *)
  Definition GOn_mat {n} (x : @GOn n) : mat n n := GOn_mat x.
  Coercion GOn_mat : GOn >-> mat.

  (** The condition to form a GOn from a matrix *)
  Definition GOnP {n} (m : smat n) : Prop := @GOnP _ Aadd 0 Amul 1 _ m.

  Lemma GOnP_spec : forall {n} (x : @GOn n), GOnP x.
  Proof. intros. apply GOnP_spec. Qed.

  (** Create a GOn from a matrix satisfing `GOnP` *)
  Definition mkGOn {n} (m : smat n) (H : GOnP m) : @GOn n := mkGOn m H.

  (** Multiplication of elements in GOn *)
  Definition GOn_mul {n} (x1 x2 : @GOn n) : @GOn n := GOn_mul x1 x2.

  (** Identity element in GOn *)
  Definition GOn_1 {n} : @GOn n :=  GOn_1.

  (** Inverse operation of multiplication in GOn *)
  Definition GOn_inv {n} (x : @GOn n) : @GOn n := GOn_inv x.

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
  Lemma Group_GOn : forall n, Group (@GOn_mul n) GOn_1 GOn_inv.
  Proof. intros. apply Group_GOn. Qed.

  (** M \-1 = M \T *)
  Lemma GOn_imply_inv_eq_trans : forall {n} (M : @GOn n), M \-1 = M \T.
  Proof. intros. apply GOn_imply_inv_eq_trans. Qed.
  
  (* ======================================================================= *)
  (** ** SO(n): Special Orthogonal Group, Rotation Group *)

  (** The set of SOn *)
  Definition SOn {n: nat} := (@SOn _ Aadd 0 Aopp Amul 1 n).

  (** Additional coercion, hence the re-definition of `mat` and `SOn` *)
  Definition SOn_GOn {n} (x : @SOn n) : @GOn n := SOn_GOn x.
  Coercion SOn_GOn : SOn >-> GOn.

  (** The condition to form a SOn from a matrix *)
  Definition SOnP {n} (m : smat n) : Prop := @SOnP _ Aadd 0 Aopp Amul 1 _ m.

  Lemma SOnP_spec : forall {n} (x : @SOn n), SOnP x.
  Proof. intros. apply SOnP_spec. Qed.

  (** Create a SOn from a matrix satisfing `SOnP` *)
  Definition mkSOn {n} (m : smat n) (H : SOnP m) : @SOn n := mkSOn m H.

  (** Multiplication of elements in SOn *)
  Definition SOn_mul {n} (x1 x2 : @SOn n) : @SOn n := SOn_mul x1 x2.
  
  (** Identity element in SOn *)
  Definition SOn_1 {n} : @SOn n := SOn_1.

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

  (** Inverse operation of multiplication in GOn *)
  Definition SOn_inv {n} (x : @SOn n) : @SOn n := SOn_inv x.

  (** SOn_inv is left-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_l : forall n, InverseLeft SOn_mul SOn_1 (@SOn_inv n).
  Proof. intros. apply SOn_mul_inv_l. Qed.

  (** SOn_inv is right-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_r : forall n, InverseRight SOn_mul SOn_1 (@SOn_inv n).
  Proof. intros. apply SOn_mul_inv_r. Qed.

  (** <SOn, +, 1, /x> is a group *)
  Lemma Group_SOn : forall n, Group (@SOn_mul n) SOn_1 SOn_inv.
  Proof. intros. apply Group_SOn. Qed.

  (** M \-1 = M \T *)
  Lemma SOn_inv_eq_trans : forall {n} (M : @SOn n), M \-1 = M \T.
  Proof. intros. apply SOn_inv_eq_trans. Qed.

  (** M\T * M = mat1 *)
  Lemma SOn_mul_trans_l_eq1 : forall {n} (M : @SOn n), M\T * M = mat1.
  Proof. intros. apply SOn_mul_trans_l_eq1. Qed.

  (** M * M\T = mat1 *)
  Lemma SOn_mul_trans_r_eq1 : forall {n} (M : @SOn n), M * M\T = mat1.
  Proof. intros. apply SOn_mul_trans_r_eq1. Qed.
  
End FieldMatrixTheory.


(* ######################################################################### *)
(** * Ordered field matrix theory *)
Module OrderedFieldMatrixTheory (E : OrderedFieldElementType).

  Include (FieldMatrixTheory E).

  Open Scope vec_scope.

  Section THESE_CODE_ARE_COPIED_FROM_OrderedRingMatrixTheroy.
    
    (** 0 <= <v, v> *)
    Lemma vdot_ge0 : forall {n} (v : vec n), 0 <= (<v, v>).
    Proof. intros. apply vdot_ge0. Qed.
    
    (** <u, v> ² <= <u, u> * <v, v> *)
    Lemma vdot_sqr_le : forall {n} (u v : vec n), (<u, v> ²) <= (<u, u> * <v, v>)%A.
    Proof. intros. apply vdot_sqr_le. Qed.

    (** (v i)² <= <v, v> *)
    Lemma vnth_sqr_le_vdot : forall {n} (v : vec n) (i : fin n), (v i) ² <= <v, v>.
    Proof. intros. apply vnth_sqr_le_vdot. Qed.

    (** (∀ i, 0 <= v.i) -> v.i <= ∑v *)
    Lemma vsum_ge_any : forall {n} (v : vec n) i, (forall i, 0 <= v $ i) -> v $ i <= vsum v.
    Proof. intros. apply vsum_ge_any; auto. Qed.
    
    (** (∀ i, 0 <= v.i) -> 0 <= ∑v *)
    Lemma vsum_ge0 : forall {n} (v : vec n), (forall i, 0 <= v $ i) -> 0 <= vsum v.
    Proof. intros. apply vsum_ge0; auto. Qed.
    
    (** (∀ i, 0 <= v.i) -> (∃ i, v.i <> 0) -> 0 < ∑v *)
    Lemma vsum_gt0 : forall {n} (v : vec n),
        (forall i, 0 <= v $ i) -> (exists i, v $ i <> 0) -> 0 < vsum v.
    Proof. intros. apply vsum_gt0; auto. Qed.
    
  End THESE_CODE_ARE_COPIED_FROM_OrderedRingMatrixTheroy.

  (** v = 0 -> <v, v> = 0 *)
  Lemma vdot_same_eq0_if_vzero : forall {n} (v : vec n), v = vzero -> <v, v> = 0.
  Proof. intros. apply vdot_same_eq0_if_vzero; auto. Qed.
  
  (** <v, v> = 0 -> v = 0 *)
  Lemma vdot_same_eq0_then_vzero : forall {n} (v : vec n), <v, v> = 0 -> v = vzero.
  Proof. intros. apply vdot_same_eq0_then_vzero; auto. Qed.

  (** v <> vzero -> <v, v> <> 0 *)
  Lemma vdot_same_neq0_if_vnonzero : forall {n} (v : vec n), v <> vzero -> <v, v> <> 0.
  Proof. intros. apply vdot_same_neq0_if_vnonzero; auto. Qed.
  
  (** <v, v> <> 0 -> v <> vzero *)
  Lemma vdot_same_neq0_then_vnonzero : forall {n} (v : vec n), <v, v> <> 0 -> v <> vzero.
  Proof. intros. apply vdot_same_neq0_then_vnonzero; auto. Qed.

  (** 0 < <v, v> *)
  Lemma vdot_gt0 : forall {n} (v : vec n), v <> vzero -> 0 < (<v, v>).
  Proof. intros. apply vdot_gt0; auto. Qed.
  
  (** <u, v>² / (<u, u> * <v, v>) <= 1. *)
  Lemma vdot_sqr_le_form2 : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> <u, v>² / (<u, u> * <v, v>)%A <= 1.
  Proof. intros. apply vdot_sqr_le_form2; auto. Qed.

  (** vproj (u + v) w = vproj u w + vproj v w *)
  Lemma vproj_vadd : forall {n} (u v w : vec n),
      w <> vzero -> vproj (u + v) w = vproj u w + vproj v w.
  Proof. intros. apply vproj_vadd; auto. Qed.
  
  (** vproj (k \.* u) v = k * (vproj u v) *)
  Lemma vproj_vcmul : forall {n} (u v : vec n) k,
      v <> vzero -> vproj (k \.* u) v = k \.* (vproj u v).
  Proof. intros. apply vproj_vcmul; auto. Qed.

  (** vproj v v = v *)
  Lemma vproj_same : forall {n} (v : vec n), v <> vzero -> vproj v v = v.
  Proof. intros. apply vproj_same; auto. Qed.

  (** vproj _|_ vperp *)
  Lemma vorth_vproj_vperp : forall {n} (u v : vec n), v <> vzero -> vproj u v _|_ vperp u v.
  Proof. intros. apply vorth_vproj_vperp; auto. Qed.

  (** vperp (u + v) w = vperp u w + vperp v w *)
  Lemma vperp_vadd : forall {n} (u v w : vec n),
      w <> vzero -> vperp (u + v) w = vperp u w + vperp v w.
  Proof. intros. apply vperp_vadd; auto. Qed.

  (** vperp (k * u) v = k * (vperp u v) *)
  Lemma vperp_vcmul : forall {n} (k : A) (u v : vec n),
      v <> vzero -> vperp (k \.* u) v = k \.* (vperp u v).
  Proof. intros. apply vperp_vcmul; auto. Qed.

  (** vperp v v = vzero *)
  Lemma vperp_same : forall {n} (v : vec n), v <> vzero -> vperp v v = vzero.
  Proof. intros. apply vperp_same; auto. Qed.

  (* ======================================================================= *)
  (** ** Two vectors are collinear *)

  (** Two non-zero vectors are collinear, if the components are proportional *)
  Definition vcoll {n} (u v : vec n) : Prop := @vcoll _ 0 Amul _ u v.
  Infix "//" := vcoll : vec_scope.

  (** v // v *)
  Lemma vcoll_refl : forall {n} (v : vec n), v <> vzero -> v // v.
  Proof. intros; apply vcoll_refl; auto. Qed.
  
  (** u // v -> v // u *)
  Lemma vcoll_sym : forall {n} (u v : vec n), u // v -> v // u.
  Proof. intros; apply vcoll_sym; auto. Qed.

  (** u // v -> v // w -> u // w *)
  Lemma vcoll_trans : forall {n} (u v w: vec n), u // v -> v // w -> u // w.
  Proof. intros; apply vcoll_trans with v; auto. Qed.

  (** u // v => ∃! k, k <> 0 /\ k * u = v *)
  Lemma vcoll_imply_uniqueK : forall {n} (u v : vec n),
      u // v -> (exists ! k, k <> 0 /\ k \.* u = v).
  Proof. intros; apply vcoll_imply_uniqueK; auto. Qed.

  (** u // v -> (k \.* u) // v *)
  Lemma vcoll_vcmul_l : forall {n} k (u v : vec n), k <> 0 -> u // v -> k \.* u // v.
  Proof. intros; apply vcoll_vcmul_l; auto. Qed.

  (** u // v -> u // (k \.* v) *)
  Lemma vcoll_vcmul_r : forall {n} k (u v : vec n), k <> 0 -> u // v -> u // (k \.* v).
  Proof. intros; apply vcoll_vcmul_r; auto. Qed.

  (* ======================================================================= *)
  (** ** Two vectors are parallel (i.e., collinear with same direction) *)

  (** Two non-zero vectors are parallel, if positive proportional *)
  Definition vpara {n} (u v : vec n) : Prop := @vpara _ 0 Amul Alt _ u v.
  Infix "//+" := vpara : vec_scope.

  (** v //+ v *)
  Lemma vpara_refl : forall {n} (v : vec n), v <> vzero -> v //+ v.
  Proof. intros. apply vpara_refl; auto. Qed.
  
  (** u //+ v -> v //+ u *)
  Lemma vpara_sym : forall {n} (u v : vec n), u //+ v -> v //+ u.
  Proof. intros. apply vpara_sym; auto. Qed.

  (** u //+ v -> v //+ w -> u //+ w *)
  Lemma vpara_trans : forall {n} (u v w: vec n), u //+ v -> v //+ w -> u //+ w.
  Proof. intros. apply vpara_trans with v; auto. Qed.

  (** u //+ v => ∃! k, 0 < k /\ k * u = v *)
  Lemma vpara_imply_uniqueK : forall {n} (u v : vec n),
      u //+ v -> (exists ! k, 0 < k /\ k \.* u = v).
  Proof. intros. apply vpara_imply_uniqueK; auto. Qed.

  (** u //+ v -> (k \.* u) //+ v *)
  Lemma vpara_vcmul_l : forall {n} k (u v : vec n),
      0 < k -> u //+ v -> k \.* u //+ v.
  Proof. intros. apply vpara_vcmul_l; auto. Qed.

  (** u //+ v -> u //+ (k \.* v) *)
  Lemma vpara_vcmul_r : forall {n} k (u v : vec n),
      0 < k -> u //+ v -> u //+ (k \.* v).
  Proof. intros. apply vpara_vcmul_r; auto. Qed.

  (* ======================================================================= *)
  (** ** Two vectors are antiparallel (i.e., collinear with opposite direction) *)
  
  (** Two non-zero vectors are antiparallel, if negative proportional *)
  Definition vantipara {n} (u v : vec n) : Prop := @vantipara _ 0 Amul Alt _ u v.
  Infix "//-" := vantipara : vec_scope.

  (** u //- v -> v //- u *)
  Lemma vantipara_sym : forall {n} (u v : vec n),  u //- v -> v //- u.
  Proof. intros. apply vantipara_sym; auto. Qed.

  (** u //- v => ∃! k, k < 0 /\ k * u = v *)
  Lemma vantipara_imply_uniqueK : forall {n} (u v : vec n),
      u //- v -> (exists ! k, k < 0 /\ k \.* u = v).
  Proof. intros. apply vantipara_imply_uniqueK; auto. Qed.

  (** u //- v -> (k \.* u) //- v *)
  Lemma vantipara_vcmul_l : forall {n} k (u v : vec n),
      0 < k -> u //- v -> k \.* u //- v.
  Proof. intros. apply vantipara_vcmul_l; auto. Qed.

  (** u //- v -> u //- (k \.* v) *)
  Lemma vantipara_vcmul_r : forall {n} k (u v : vec n),
      0 < k -> u //- v -> u //- (k \.* v).
  Proof. intros. apply vantipara_vcmul_r; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Convert between //, //+, and //-  *)
  
  (** u //+ v -> u // v *)
  Lemma vpara_imply_vcoll : forall {n} (u v : vec n), u //+ v -> u // v.
  Proof. intros. apply vpara_imply_vcoll; auto. Qed.
  
  (** u //- v -> u // v *)
  Lemma vantipara_imply_vcoll : forall {n} (u v : vec n), u //- v -> u // v.
  Proof. intros. apply vantipara_imply_vcoll; auto. Qed.
  
  (** u //+ v -> (-u) //- v *)
  Lemma vpara_imply_vantipara_opp_l : forall {n} (u v : vec n), u //+ v -> (-u) //- v.
  Proof. intros. apply vpara_imply_vantipara_opp_l; auto. Qed.
  
  (** u //+ v -> u //- (-v)*)
  Lemma vpara_imply_vantipara_opp_r : forall {n} (u v : vec n), u //+ v -> u //- (-v).
  Proof. intros. apply vpara_imply_vantipara_opp_r; auto. Qed.
  
  (** u // v -> (u //+ v) \/ (u //- v) *)
  Lemma vcoll_imply_vpara_or_vantipara : forall {n} (u v : vec n),
      u // v -> u //+ v \/ u //- v.
  Proof. intros. apply vpara_imply_vpara_or_vantipara; auto. Qed.
  
End OrderedFieldMatrixTheory.


(* ######################################################################### *)
(** * Normed ordered field matrix theory *)
Module NormedOrderedFieldMatrixTheory (E : NormedOrderedFieldElementType).
  
  Include (OrderedFieldMatrixTheory E).

  Open Scope vec_scope.
  
  (** Length of a vector *)
  Definition vlen {n} (v : vec n) : R := @vlen _ Aadd 0 Amul a2r _ v.
  Notation "|| v ||" := (vlen v) : vec_scope.

  (** ||vzero|| = 0 *)
  Lemma vlen_vzero : forall {n:nat}, || @vzero n || = 0%R.
  Proof. intros. apply vlen_vzero. Qed.

  (** 0 <= ||v|| *)
  Lemma vlen_ge0 : forall {n} (v : vec n), (0 <= || v ||)%R.
  Proof. intros. apply vlen_ge0. Qed.
  
  (** ||u|| = ||v|| <-> <u, u> = <v, v> *)
  Lemma vlen_eq_iff_dot_eq : forall {n} (u v : vec n), ||u|| = ||v|| <-> <u, u> = <v, v>.
  Proof. intros. apply vlen_eq_iff_dot_eq. Qed.

  (** <v, v> = ||v||² *)
  Lemma vdot_same : forall {n} (v : vec n), a2r (<v, v>) = (||v||²)%R.
  Proof. intros. apply vdot_same. Qed.

  (** |v i| <= ||v|| *)
  Lemma vnth_le_vlen : forall {n} (v : vec n) (i : fin n),
      v <> vzero -> (a2r (|v i|%A) <= ||v||)%R.
  Proof. intros. apply vnth_le_vlen; auto. Qed.

  (** || v || = 1 <-> <v, v> = 1 *)
  Lemma vlen_eq1_iff_vdot1 : forall {n} (v : vec n), ||v|| = 1%R <-> <v, v> = 1.
  Proof. intros. apply vlen_eq1_iff_vdot1. Qed.

  (** || - v|| = || v || *)
  Lemma vlen_vopp : forall n (v : vec n), || - v || = || v ||.
  Proof. intros. apply vlen_vopp. Qed.

  (** ||k \.* v|| = |k| * ||v|| *)
  Lemma vlen_vcmul : forall n k (v : vec n), || k \.* v || = ((a2r (|k|))%A * ||v||)%R.
  Proof. intros. apply vlen_vcmul. Qed.

  (** ||u + v||² = ||u||² + ||v||² + 2 * <u, v> *)
  Lemma vlen_sqr_vadd : forall {n} (u v : vec n),
      (||(u + v)%V||² = ||u||² + ||v||² + 2 * a2r (<u,v>))%R.
  Proof. intros. apply vlen_sqr_vadd. Qed.

  (** ||u - v||² = ||u||² + ||v||² - 2 * <u, v> *)
  Lemma vlen_sqr_vsub : forall {n} (u v : vec n),
      (||(u - v)%V||² = ||u||² + ||v||² - 2 * a2r (<u, v>))%R.
  Proof. intros. apply vlen_sqr_vsub. Qed.

  (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
  (** |<u, v>| <= ||u|| * ||v|| *)
  Lemma vdot_abs_le : forall {n} (u v : vec n), (|a2r (<u, v>)| <= ||u|| * ||v||)%R.
  Proof. intros. apply vdot_abs_le. Qed.

  (** <u, v> <= ||u|| * ||v|| *)
  Lemma vdot_le_mul_vlen : forall {n} (u v : vec n), (a2r (<u, v>) <= ||u|| * ||v||)%R.
  Proof. intros. apply vdot_le_mul_vlen. Qed.

  (** - ||u|| * ||v|| <= <u, v> *)
  Lemma vdot_ge_mul_vlen_neg : forall {n} (u v : vec n), (- (||u|| * ||v||) <= a2r (<u, v>))%R.
  Proof. intros. apply vdot_ge_mul_vlen_neg. Qed.

  (* 任意维度“三角形”两边长度之和大于第三边长度 *)
  (** ||u + v|| <= ||u|| + ||v|| *)
  Lemma vlen_vadd_le : forall {n} (u v : vec n), (||(u + v)%V|| <= ||u|| + ||v||)%R.
  Proof. intros. apply vlen_vadd_le. Qed.

  (** ||v|| = 0 <-> v = 0 *)
  Lemma vlen_eq0_iff_eq0 : forall {n} (v : vec n), ||v|| = 0%R <-> v = vzero.
  Proof. intros. apply vlen_eq0_iff_eq0. Qed.

  (** ||v|| <> 0 <-> v <> 0 *)
  Lemma vlen_neq0_iff_neq0 : forall {n} (v : vec n), ||v|| <> 0%R <-> v <> vzero.
  Proof. intros. apply vlen_neq0_iff_neq0. Qed.

  (** v <> vzero -> 0 < ||v|| *)
  Lemma vlen_gt0 : forall {n} (v : vec n), v <> vzero -> (0 < ||v||)%R.
  Proof. intros. apply vlen_gt0; auto. Qed.
      
  (** 0 <= <v, v> *)
  Lemma vdot_same_ge0 : forall {n} (v : vec n), 0 <= <v, v>.
  Proof. intros. apply vdot_same_ge0. Qed.

  (** Verify the definition is reasonable *)
  Lemma vunit_spec : forall {n} (v : vec n), vunit v <-> ||v|| = 1%R.
  Proof. intros. apply vunit_spec. Qed.

  (* Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv}. *)
  (* Context `{HConvertToR *)
  (*     : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb a2r}. *)
  (* Notation vlen := (@vlen _ Aadd Azero Amul a2r). *)
  (* Notation "|| v ||" := (vlen v) : vec_scope. *)

  (** Transformation by orthogonal matrix will keep length. *)
  Lemma morth_keep_length : forall {n} (M : smat n) (v : vec n),
      morth M -> ||(M * v)%V|| = ||v||.
  Proof. intros. apply morth_keep_length. auto. Qed.
  
  (** Transformation by orthogonal matrix will keep zero. *)
  Lemma morth_keep_nonzero : forall {n} (M : smat n) (v : vec n),
      v <> vzero -> morth M -> (M * v)%V <> vzero.
  Proof. intros. apply morth_keep_nonzero; auto. Qed.

End NormedOrderedFieldMatrixTheory.

