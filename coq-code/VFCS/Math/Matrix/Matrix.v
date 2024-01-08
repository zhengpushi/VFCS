(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Record-List model
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
 *)


Require Export TupleExt Hierarchy.
Require Export ListExt.
Require Export vec.
Require Reals.
Require Import Extraction.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** ** Matrix type *)

Notation mat A r c := (@vec (@vec A c) r).

(** square matrix type *)
Notation smat A n := (mat A n n).

(** Row / Column vector type *)
Notation rvec A n := (mat A 1 n).
Notation cvec A n := (mat A n 1).

(* Notation "M .11" := (M $ 0 $ 0) : mat_scope. *)
(* Notation "M .12" := (M $ 0 $ 1) : mat_scope. *)
(* Notation "M .13" := (M $ 0 $ 2) : mat_scope. *)
(* Notation "M .14" := (M $ 0 $ 3) : mat_scope. *)
(* Notation "M .21" := (M $ 1 $ 0) : mat_scope. *)
(* Notation "M .22" := (M $ 1 $ 1) : mat_scope. *)
(* Notation "M .23" := (M $ 1 $ 2) : mat_scope. *)
(* Notation "M .24" := (M $ 1 $ 3) : mat_scope. *)
(* Notation "M .31" := (M $ 2 $ 0) : mat_scope. *)
(* Notation "M .32" := (M $ 2 $ 1) : mat_scope. *)
(* Notation "M .33" := (M $ 2 $ 2) : mat_scope. *)
(* Notation "M .34" := (M $ 2 $ 3) : mat_scope. *)
(* Notation "M .41" := (M $ 3 $ 0) : mat_scope. *)
(* Notation "M .42" := (M $ 3 $ 1) : mat_scope. *)
(* Notation "M .43" := (M $ 3 $ 2) : mat_scope. *)
(* Notation "M .44" := (M $ 3 $ 3) : mat_scope. *)

Lemma meq_iff_mnth : forall {A r c} (M1 M2 : mat A r c),
    M1 = M2 <-> (forall i j, M1$i$j = M2$i$j).
Proof.
  intros. split; intros; subst; auto.
  apply veq_iff_vnth. intros i.
  apply veq_iff_vnth. intros j. auto.
Qed.


(** ** Convert between nat-indexing-Function (f) and matrix *)
Section f2m_m2f.
  Context {A} (Azero : A).

  Definition f2m {r c} (f : nat -> nat -> A) : mat A r c :=
    @f2v _ r (fun i => @f2v A c (f i)).
    
  Definition m2f {r c} (M : mat A r c) : (nat -> nat -> A) :=
    fun i => @v2f _ Azero c (@v2f _ (vzero Azero) r M i).

End f2m_m2f.


(** ** Convert between dlist and mat *)
Section l2m_m2l.
  Context {A} (Azero : A).

  (** mat to dlist *)
  Definition m2l {r c} (M : mat A r c) : dlist A := map v2l (v2l M).

  Lemma m2l_length : forall {r c} (M : mat A r c), length (m2l M) = r.
  Proof. intros. unfold m2l. rewrite map_length. rewrite v2l_length; auto. Qed.

  Lemma m2l_width : forall {r c} (M : mat A r c), width (m2l M) c.
  Proof.
    intros. unfold width,m2l. apply Forall_map_forall.
    intros. apply v2l_length.
  Qed.

  Lemma m2l_width_form2 : forall {r c} (M : mat A r c) i,
      i < r -> length (nth i (m2l M) []) = c.
  Proof.
    intros. unfold m2l.
    rewrite nth_map with (n:=r)(Azero:=vzero Azero); auto; rewrite v2l_length; auto.
  Qed.

  Lemma m2l_inj : forall {r c} (M1 M2 : mat A r c), m2l M1 = m2l M2 -> M1 = M2.
  Proof.
    intros. unfold m2l in H.  apply map_inj in H; auto. apply v2l_inj; auto.
    intros. apply v2l_inj; auto.
  Qed.

  Lemma m2l_surj : forall {r c} (d : dlist A),
      length d = r -> width d c -> (exists M : mat A r c, m2l M = d).
  Proof.
    intros. unfold m2l.
    pose proof (map_surj (@v2l A c) d).
    assert (forall b : list A, In b d -> exists a : vec c, v2l a = b).
    { intros. exists (l2v Azero c b). apply v2l_l2v_id.
      apply (width_imply_in_length b d); auto. }
    specialize (H1 H2). destruct H1. destruct H1.
    exists (l2v (vzero Azero) _ x). rewrite v2l_l2v_id; auto. lia.
  Qed.

  Definition l2m {r c} (dl : dlist A) : mat A r c :=
    l2v (vzero Azero) r (map (l2v Azero c) dl).

  Lemma l2m_inj : forall {r c} (d1 d2 : dlist A),
      length d1 = r -> width d1 c ->
      length d2 = r -> width d2 c ->
      @l2m r c d1 = @l2m r c d2 -> d1 = d2.
  Proof.
    intros. unfold l2m in H3. apply l2v_inj in H3; try rewrite map_length; auto.
    apply map_inj in H3; auto.
    intros. apply l2v_inj in H6; auto.
    apply (width_imply_in_length a d1); auto.
    apply (width_imply_in_length b d2); auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (M : mat A r c), (exists d, @l2m r c d = M).
  Proof.
    intros. unfold l2m. destruct (@l2v_surj _ (vzero Azero) r M).
    exists (map v2l x). rewrite <- H. f_equal.
    rewrite map_map. apply map_id. intros. apply l2v_v2l_id.
  Qed.

  Lemma l2m_m2l_id : forall {r c} (M : mat A r c), (@l2m r c (m2l M)) = M.
  Proof.
    intros. unfold l2m,m2l.
    apply veq_iff_vnth; intros i. apply veq_iff_vnth; intros j.
    rewrite !vnth_l2v.
    rewrite nth_map with (n:=r)(Azero:=[]); auto;
      try rewrite map_length; try apply v2l_length; try apply fin2nat_lt.
    rewrite nth_map with (n:=r)(Azero:=vzero Azero);
      try apply v2l_length; try apply fin2nat_lt.
    rewrite l2v_v2l_id.
    rewrite nth_v2l with (H:=fin2nat_lt _); try apply fin2nat_lt.
    f_equal. apply nat2fin_fin2nat_id.
  Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : dlist A),
      length dl = r -> width dl c -> m2l (@l2m r c dl) = dl.
  Proof.
    intros. unfold l2m,m2l; simpl. rewrite v2l_l2v_id.
    - rewrite map_map. apply map_id_In; intros. apply v2l_l2v_id.
      apply (width_imply_in_length a dl); auto.
    - rewrite map_length; auto.
  Qed.

End l2m_m2l.


(** ** matrix with specific size *)

Section mat_specific.
  Context {A} {Azero : A}.
  Notation l2m := (l2m Azero).
  Variable r c : nat.
  Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : A.

  (** *** Create matrix *)
  Definition mkmat_0_c : mat A 0 c := vzero (vzero Azero). (* anything is ok *)
  Definition mkmat_r_0 : mat A r 0 := vzero (vzero Azero). (* anything is ok *)

  Definition mkmat_1_c (f : @vec A c) : mat A 1 c := fun i j => f j.
  Definition mkmat_r_1 (f : @vec A r) : mat A r 1 := fun i j => f i.

  Definition mkmat_1_1 : mat A 1 1 := l2m [[a11]].
  Definition mkmat_1_2 : mat A 1 2 := l2m [[a11;a12]].
  Definition mkmat_2_1 : mat A 2 1 := l2m [[a11];[a21]].
  Definition mkmat_2_2 : mat A 2 2 := l2m [[a11;a12];[a21;a22]].
  Definition mkmat_1_3 : mat A 1 3 := l2m [[a11;a12;a13]].
  Definition mkmat_2_3 : mat A 2 3 := l2m [[a11;a12;a13];[a21;a22;a23]].
  Definition mkmat_3_1 : mat A 3 1 := l2m [[a11];[a21];[a31]].
  Definition mkmat_3_2 : mat A 3 2 := l2m [[a11;a12];[a21;a22];[a31;a32]].
  Definition mkmat_3_3 : mat A 3 3 := l2m [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  Definition mkmat_1_4 : mat A 1 4 := l2m [[a11;a12;a13;a14]].
  Definition mkmat_4_1 : mat A 4 1 := l2m [[a11];[a21];[a31];[a41]].
  Definition mkmat_4_4 : mat A 4 4 :=
    l2m [[a11;a12;a13;a14];[a21;a22;a23;a24];[a31;a32;a33;a34];[a41;a42;a43;a44]].
  
End mat_specific.


(** ** Matrix map *)
Notation mmap f M := (vmap (vmap f) M).

Lemma mnth_mmap : forall {A B} {r c} (M : mat A r c) (f:A->B) i j,
    (mmap f M)$i$j = f (M$i$j).
Proof. intros. unfold mmap. auto. Qed.


(** ** Matrix map2 *)
Notation mmap2 f M1 M2 := (vmap2 (vmap2 f) M1 M2).

Lemma mnth_mmap2 : forall {A B C} {r c} (M1:mat A r c) (M2:mat B r c) (f:A->B->C) i j,
    (mmap2 f M1 M2)$i$j = f (M1$i$j) (M2$i$j).
Proof. intros. unfold mmap2. auto. Qed.

Lemma mmap2_comm `{Commutative A Aadd} : forall {r c} (M1 M2 : mat A r c),
    mmap2 Aadd M1 M2 = mmap2 Aadd M2 M1.
Proof. intros. apply meq_iff_mnth; intros. unfold mmap2. apply commutative. Qed.

Lemma mmap2_assoc `{Associative A Aadd} : forall {r c} (M1 M2 M3 : mat A r c),
    mmap2 Aadd (mmap2 Aadd M1 M2) M3 = mmap2 Aadd M1 (mmap2 Aadd M2 M3).
Proof. intros. apply meq_iff_mnth; intros. unfold mmap2. apply associative. Qed.


(** ** Get row and column of a matrix *)
Section mrow_mcol.
  Context {A} {Azero : A} {r c : nat}.
  Notation vzero := (vzero Azero).

  Definition mrow (M : mat A r c) (i : fin r) : @vec A c := M i.

  Lemma vnth_mrow : forall (M : mat A r c) (i : fin r) (j : fin c),
      (mrow M i) $ j = M $ i $ j.
  Proof. intros. auto. Qed.
  
  Definition mcol (M : mat A r c) (j : fin c) : @vec A r := fun i => M i j.

  Lemma vnth_mcol : forall (M : mat A r c) (i : fin r) (j : fin c),
      (mcol M j) $ i = M $ i $ j.
  Proof. intros. auto. Qed.

End mrow_mcol.

  
(** ** Construct matrix with two matrices *)
Section mapp.
  Context {A} {Azero : A}.
  Notation m2f := (m2f Azero).
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (M1 : mat A r1 c) (M2 : mat A r2 c)
    : mat A (r1 + r2) c :=
    f2m (fun i j => if i ??< r1 then m2f M1 i j else m2f M2 (i - r1) j).

  (** Append matrix by column *)
  Definition mappc {r c1 c2} (M1 : mat A r c1) (M2 : mat A r c2)
    : mat A r (c1 + c2) :=
    f2m (fun i j => if j ??< c1 then m2f M1 i j else m2f M2 i (j - c1)).
  
End mapp.

Section test.
  Let M1 := @l2m _ 9 2 2 [[1;2];[3;4]].
  Let M2 :=  @l2m _ 9 2 2 [[11;12];[13;14]].
  (* Compute m2l (mappr M1 M2). *)
  (* Compute m2l (mappc M1 M2). *)
End test.


(** ** Elementary Row Transform *)

Section RowTrans.
  Context `{ARing}.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.

  (** 第 i1 行乘以 k *)
  Definition mrowK {r c} (M : mat A r c) (i1 : fin r) (k : A) : mat A r c :=
    fun i j => if finEqdec i i1
             then k * M i j
             else M i j.
  
  (** 交换 i1,i2 两行 *)
  Definition mrowSwap {r c} (M : mat A r c) (i1 i2 : fin r) : mat A r c :=
    fun i j => if finEqdec i i1
             then M i2 j
             else if finEqdec i i2
                  then M i1 j
                  else M i j.

  (** 第 i1 行的 k 倍 加到第 i2 行 *)
  Definition mrowKAdd {r c} (M : mat A r c) (i1 i2 : fin r) (k : A) : mat A r c :=
    fun i j => if finEqdec i i2 then (k * M i1 j + M i2 j) else M i j.
End RowTrans.

Section test.
  Import Reals.
  Open Scope R.

  Notation mrowK := (mrowK (Amul:=Rmult)).
  Notation mrowKAdd := (mrowKAdd (Aadd:=Rplus)(Amul:=Rmult)).
  
  Let M1 : smat R 2 := @l2m _ 0 2 2 ([[1;2];[3;4]]).

  Let i0 : fin 2 := nat2finS 0.
  Let i1 : fin 2 := nat2finS 1.

  Goal m2l (mrowK M1 i0 2) = [[2;4];[3;4]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowK M1 i1 2) = [[1;2];[6;8]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowSwap M1 i0 i0) = m2l M1. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowSwap M1 i0 i1) = [[3;4];[1;2]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowKAdd M1 i0 i1 2) = [[1;2];[5;8]]. Proof. cbv. list_eq ;ring. Qed.
  Goal m2l (mrowKAdd M1 i1 i0 2) = [[7;10];[3;4]]. Proof. cbv. list_eq; ring. Qed.
End test.


(* ======================================================================= *)
(** ** Construct matrix from vector and matrix *)
Section mcons.
  Context {A} (Azero:A).

  (** Construct a matrix by row with a vector and a matrix *)
  Definition mconsr {r c} (V : @vec A c) (M : mat A r c) : mat A (S r) c :=
    vconsH (Azero:=vzero Azero) V M.
  
  (** Construct a matrix by column with a d vector and a matrix *)
  Definition mconsc {r c} (V : @vec A r) (M : mat A r c) : mat A r (S c) :=
    @vmap2 A (vec c) (vec (S c)) (vconsH (Azero:=Azero)) r V M.

End mcons.


(* ==================================== *)
(** ** matrix column shift *)
Section mcsh.
  Context {A} (Azero : A).

  (** left shift column. *)
  (* [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *)
  Definition mcshl {r c} (M : mat A r c) (k : fin c) : mat A r c :=
    fun i j =>
      if fin2nat j + fin2nat k ??< c
      then M $ i $ (fin2SameRangeAdd j k)
      else Azero.

  (** right shift column. *)
  (* [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *)
  Definition mcshr {r c} (M : mat A r c) (k : fin c) : mat A r c :=
    fun i j =>
      if fin2nat k ??<= fin2nat j
      then M $ i $ (fin2SameRangeSub j k)
      else Azero.

  (** loop shift left of column. *)
  (* [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *)
  Definition mclsl {r c} (M : @mat A r c) (k : fin c) : @mat A r c :=
    fun i j => M $ i $ (fin2SameRangeLSL j k).

  (** loop shift right of column *)
  (* [[1;2;3];[4;5;6];[7;8;9] ==1==> [[3;1;2];[6;4;5];[9;7;8] *)
  Definition mclsr {r c} (M : @mat A r c) (k : fin c) : @mat A r c :=
    fun i j => M $ i $ (fin2SameRangeLSR j k).

End mcsh.

Section test.
  Let M1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute @nat2finS 2 3. *)
  (* Compute m2l (mcshl 0 M1 (nat2finS 0)). *)
  (* Compute m2l (mcshl 0 M1 (nat2finS 1)). *)
  (* 移动次数最大是 c - 1 次，若需要更多，则可以多次进行 *)
  (* Compute m2l (mcshl 0 (mcshl 0 M1 (nat2finS 2)) (nat2finS 1)). *)
  
  (* Compute m2l (mcshr 0 M1 (nat2finS 1)). *)
  
  (* Compute m2l (mclsl M1 (nat2finS 1)). *)
  (* Compute m2l (mclsr M1 (nat2finS 1)). *)
End test.


(** ** matrix transpose *)
Section mtrans.
  Context {A} (Azero : A).

  (* Definition mtrans_old {r c} (M : mat A r c) : mat A c r := *)
  (*   vmap (fun j => mcol M j) (vfinseq c). *)
  
  Definition mtrans {r c} (M : mat A r c) : mat A c r := fun i j => M j i.

  (** (M\T)[i,*] = M[*,i] *)
  Lemma vnth_mtrans : forall {r c} (M : mat A r c) i, (mtrans M)$i = fun j => M$j$i.
  Proof. intros. auto. Qed.

  (** (M\T)[i,j] = M[j,i] *)
  Lemma mnth_mtrans : forall {r c} (M : mat A r c) i j, (mtrans M)$i$j = M$j$i.
  Proof. intros. auto. Qed.

  (** Transpose twice return back *)
  Lemma mtrans_mtrans : forall {r c} (M : mat A r c), mtrans (mtrans M) = M.
  Proof. intros. auto. Qed.

End mtrans.

Notation "M \T" := (mtrans M) : mat_scope.


(** ** Diagonal matrix *)
Section mdiag.
  Context {A} (Azero:A).

  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (M : smat A n) : Prop :=
    forall i j, i <> j -> M$i$j = Azero.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (M : smat A n), mdiag M -> M\T = M.
  Proof.
    intros. unfold mdiag in H. apply meq_iff_mnth; intros i j.
    rewrite mnth_mtrans. destruct (finEqdec i j).
    subst; auto. rewrite !H; auto.
  Qed.

  (** Construct a diagonal matrix *)
  Definition mdiagMk {n} (V : @vec A n) : @smat A n :=
    fun i j => if (finEqdec i j) then V$i else Azero.

  (** mdiagMk is correct *)
  Lemma mdiagMk_spec : forall {n} (V : @vec A n), mdiag (mdiagMk V).
  Proof.
    intros. hnf. intros. unfold mdiagMk. destruct (finEqdec i j); auto. easy.
  Qed.

  (** (mdiagMk l)[i,i] = l[i] *)
  Lemma mnth_mdiagMk_same : forall {n} (V : @vec A n) i, (mdiagMk V)$i$i = V$i.
  Proof. intros. unfold mdiagMk. destruct finEqdec; auto. easy. Qed.

  (** (mdiagMk l)[i,j] = 0 *)
  Lemma mnth_mdiagMk_diff : forall {n} (v : @vec A n) i j,
      i <> j -> (mdiagMk v)$i$j = Azero.
  Proof. intros. unfold mdiagMk. destruct finEqdec; auto. easy. Qed.

End mdiag.



(** ** matrix algebra *)
(* addition,opposition,subtraction, trace, scalar multiplication, multiplication *)
Section malg.

  Context `{AGroup} {Aone : A}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b)).
  Infix "-" := Asub : A_scope.
  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation vsum := (@vsum _ Aadd Azero).


  (** *** Zero matrix *)
  Definition mat0 {r c} : mat r c := fun _ _ => Azero.

  (** mat0\T = mat0 *)
  Lemma mtrans_mat0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. auto. Qed.

  (** mat0[i,j] = 0 *)
  Lemma mnth_mat0 : forall {r c} i j, @mat0 r c $ i $ j = Azero.
  Proof. intros. auto. Qed.

  (* row mat0 i = vzero *)
  Lemma mrow_mat0 : forall {r c} i, @mat0 r c $ i = vzero Azero.
  Proof. intros. auto. Qed.

  (* col mat0 i = vzero *)
  Lemma mcol_mat0 : forall {r c} j, (fun k => @mat0 r c $ k $ j) = vzero Azero.
  Proof. intros. auto. Qed.

  
  (** *** Unit matrix *)
  Definition mat1 {n} : smat n :=
    fun i j => if finEqdec i j then Aone else Azero.
      
  (** mat1\T = mat1 *)
  Lemma mtrans_mat1 : forall {n : nat}, (@mat1 n)\T = mat1.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold mtrans,mat1.
    destruct finEqdec,finEqdec; auto; subst; easy.
  Qed.

  (** mat1[i,i] = 1 *)
  Lemma mnth_mat1_same : forall {n} i, (@mat1 n) $ i $ i = Aone.
  Proof. intros. unfold mat1. destruct finEqdec; easy. Qed.

  (** i <> j -> mat1[i,j] = 0 *)
  Lemma mnth_mat1_diff : forall {n} i j, i <> j -> @mat1 n $ i $ j = Azero.
  Proof. intros. unfold mat1. destruct finEqdec; easy. Qed.

  (** mat1 is diagonal matrix *)
  Lemma mat1_diag : forall {n : nat}, mdiag Azero (@mat1 n).
  Proof. intros. hnf. intros. rewrite mnth_mat1_diff; auto. Qed.


  (** *** Matrix Trace *)

  Definition mtrace {n : nat} (M : smat n) : A := vsum (fun i => M$i$i).
  Notation "'tr' M" := (mtrace M).

  (** tr(M\T) = tr(M) *)
  Lemma mtrace_mtrans : forall {n} (M : smat n), tr (M\T) = tr M.
  Proof. intros. apply vsum_eq; intros. apply mnth_mtrans. Qed.
  
  
  (** *** Matrix Addition *)
  Definition madd {r c} (M1 M2 : mat r c) : mat r c := mmap2 Aadd M1 M2.
  Infix "+" := madd : mat_scope.
  
  (** (M1+M2)[i,j] = M1[i,j] + M2[i,j] *)
  Lemma mnth_madd : forall {r c} (M1 M2 : mat r c) i j,
      (M1 + M2) $ i $ j = (M1$i$j + M2$i$j)%A.
  Proof. intros. unfold madd. rewrite !vnth_vmap2. auto. Qed.

  Lemma madd_comm : forall {r c} (M1 M2 : mat r c), M1 + M2 = M2 + M1.
  Proof. intros. apply mmap2_comm. Qed.
  
  Lemma madd_assoc : forall {r c} (M1 M2 M3 : mat r c),
      (M1 + M2) + M3 = M1 + (M2 + M3).
  Proof. intros. apply mmap2_assoc. Qed.
  
  (** 0 + M = M *)
  Lemma madd_0_l : forall {r c} (M : mat r c), mat0 + M = M.
  Proof.
    intros. unfold madd. apply meq_iff_mnth; intros.
    rewrite mnth_mmap2. rewrite mnth_mat0. monoid.
  Qed.

  (** M + 0 = M *)
  Lemma madd_0_r : forall {r c} (M : mat r c), M + mat0 = M.
  Proof. intros. rewrite madd_comm, madd_0_l; auto. Qed.
  
  Instance Associative_madd : forall r c, @Associative (mat r c) madd.
  Proof. intros. constructor. apply madd_assoc. Qed.

  Instance Commutative_madd : forall r c, @Commutative (mat r c) madd.
  Proof. intros. constructor. apply madd_comm. Qed.

  Instance IdentityLeft_madd : forall r c, @IdentityLeft (mat r c) madd mat0.
  Proof. intros. constructor. apply madd_0_l. Qed.

  Instance IdentityRight_madd : forall r c, @IdentityRight (mat r c) madd mat0.
  Proof. intros. constructor. apply madd_0_r. Qed.

  Instance Monoid_madd : forall r c, Monoid (@madd r c) mat0.
  Proof.
    intros. repeat constructor; intros;
      try apply associative;
      try apply identityLeft;
      try apply identityRight.
  Qed.

  (** (M1 + M2)\T = M1\T + M2\T *)
  Lemma mtrans_madd : forall {r c} (M1 M2 : mat r c), (M1 + M2)\T = M1\T + M2\T.
  Proof.
    intros. unfold madd. apply meq_iff_mnth; intros.
    rewrite ?mnth_mtrans, ?mnth_mmap2, ?mnth_mtrans. auto.
  Qed.

  (** tr(M1 + M2) = tr(M1) + tr(M2) *)
  Lemma mtrace_madd : forall {n} (M1 M2 : smat n), tr (M1 + M2) = (tr M1 + tr M2)%A.
  Proof.
    intros. unfold madd, mtrace. apply vsum_add; intros. rewrite mnth_mmap2. auto.
  Qed.


  (** *** Matrix Opposition *)
  Definition mopp {r c} (M : mat r c) : mat r c := mmap Aopp M.
  Notation "- M" := (mopp M) : mat_scope.
  
  (** (-M)[i,j] = - M[i,j] *)
  Lemma mnth_mopp : forall {r c} (M : mat r c) i j, (- M) $ i $ j = (- M$i$j)%A.
  Proof. intros. unfold mopp. rewrite !vnth_vmap. auto. Qed.
  
  Lemma madd_opp_l : forall {r c} (M : mat r c), (-M) + M = mat0.
  Proof.
    intros. unfold madd,mopp,mat0,mmap2,mmap. apply meq_iff_mnth; intros. group.
  Qed.
    
  Lemma madd_opp_r : forall {r c} (M : mat r c), M + (-M) = mat0.
  Proof. intros. rewrite madd_comm. apply madd_opp_l. Qed.

  Instance InverseLeft_madd : forall r c, @InverseLeft (mat r c) madd mat0 mopp.
  Proof. intros. constructor. apply madd_opp_l. Qed.

  Instance InverseRight_madd : forall r c, @InverseRight (mat r c) madd mat0 mopp.
  Proof. intros. constructor. apply madd_opp_r. Qed.

  Instance AGroup_madd : forall r c, @AGroup (mat r c) madd mat0 mopp.
  Proof.
    intros. repeat constructor;
      try apply associative;
      try apply identityLeft;
      try apply identityRight;
      try apply inverseLeft;
      try apply inverseRight;
      try apply commutative.
  Qed.

  (* Now, we ca use group theory on <madd, mat0, mopp, msub> *)

  (** (M1 + M2) + M3 = (M1 + M3) + M2 *)
  Lemma madd_perm : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) + M3 = (M1 + M3) + M2.
  Proof. intros. rewrite !associative. f_equal. apply commutative. Qed.
  
  (** - (- M) = M *)
  Lemma mopp_mopp : forall {r c} (M : mat r c), - (- M) = M.
  Proof. intros. apply group_inv_inv. Qed.

  (** -M1 = M2 <-> M1 = -M2 *)
  Lemma mopp_exchange : forall {r c} (M1 M2 : mat r c), -M1 = M2 <-> M1 = -M2.
  Proof. intros. split; intros; subst; rewrite group_inv_inv; auto. Qed.

  (** - (mat0) = mat0 *)
  Lemma mopp_mat0 : forall {r c:nat}, - (@mat0 r c) = mat0.
  Proof. intros. apply group_inv_id. Qed.

  (** - (m1 + m2) = (-m1) + (-m2) *)
  Lemma mopp_madd : forall {r c : nat} (M1 M2 : mat r c), - (M1 + M2) = (-M1) + (-M2).
  Proof. intros. rewrite group_inv_distr. apply commutative. Qed.

  (** (- M)\T = - (M\T) *)
  Lemma mtrans_mopp : forall {r c} (M : mat r c), (- M)\T = - (M\T).
  Proof.
    intros. apply meq_iff_mnth; intros.
    rewrite ?mnth_mtrans, ? mnth_mopp, ?mnth_mtrans. auto.
  Qed.

  (** tr(- M) = - (tr(m)) *)
  Lemma mtrace_mopp : forall {n} (M : smat n), tr (-M) = (- (tr M))%A.
  Proof.
    intros. unfold mopp, mtrace. apply vsum_opp; intros. rewrite !vnth_vmap; auto.
  Qed.
  
  
  (** *** Matrix Subtraction *)
  Definition msub {r c} (M1 M2 : mat r c) : mat r c := M1 + (-M2).
  Infix "-" := msub : mat_scope.

  (** M1 - M2 = - (M2 - M1) *)
  Lemma msub_comm : forall {r c} (M1 M2 : mat r c), M1 - M2 = - (M2 - M1).
  Proof.
    intros. unfold msub. rewrite group_inv_distr. rewrite group_inv_inv; auto.
  Qed.

  (** (M1 - M2) - M3 = M1 - (M2 + M3) *)
  Lemma msub_assoc : forall {r c} (M1 M2 M3 : mat r c),
      (M1 - M2) - M3 = M1 - (M2 + M3).
  Proof. intros. unfold msub. rewrite group_inv_distr. asemigroup. Qed.

  (** (M1 + M2) - M3 = M1 + (M2 - M3) *)
  Lemma msub_assoc1 : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) - M3 = M1 + (M2 - M3).
  Proof. intros. unfold msub. asemigroup. Qed.

  (** (M1 - M2) - M3 = M1 - (M3 - M2) *)
  Lemma msub_assoc2 : forall {r c} (M1 M2 M3 : mat r c), (M1 - M2) - M3 = (M1 - M3) - M2.
  Proof. intros. unfold msub. asemigroup. Qed.
  
  (** 0 - M = - M *)
  Lemma msub_0_l : forall {r c} (M : mat r c), mat0 - M = - M.
  Proof. intros. unfold msub. monoid. Qed.
  
  (** M - 0 = M *)
  Lemma msub_0_r : forall {r c} (M : mat r c), M - mat0 = M.
  Proof.
    intros. unfold msub. rewrite (@group_inv_id _ madd mat0); auto. monoid.
    apply AGroup_madd.
  Qed.
  
  (** M - M = 0 *)
  Lemma msub_self : forall {r c} (M : mat r c), M - M = mat0.
  Proof. intros. unfold msub. group. Qed.

  (** (M1 - M2)\T = M1\T - M2\T *)
  Lemma mtrans_msub : forall {r c} (M1 M2 : mat r c), (M1 - M2)\T = M1\T - M2\T.
  Proof. intros. unfold msub. rewrite mtrans_madd, mtrans_mopp; auto. Qed.

  (** tr(M1 - M2) = tr(M1) - tr(M2) *)
  Lemma mtrace_msub : forall {n} (M1 M2 : smat n), tr (M1 - M2) = (tr M1 - tr M2)%A.
  Proof. intros. unfold msub. rewrite mtrace_madd, mtrace_mopp; auto. Qed.

  
  Context `{AR : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : make_ring_theory.

  Notation vcmul := (@vcmul _ Amul).
  Notation vdot v1 v2 := (@vdot _ Aadd Azero Amul _ v1 v2).
  Notation "< v1 , v2 >" := (vdot v1 v2) : vec_scope.

  (** *** Matrix Scalar Multiplication *)
  Definition mcmul {r c : nat} (a : A) (M : mat r c) : mat r c := mmap (Amul a) M.
  Infix "c*" := mcmul : mat_scope.

  (** (a * M)[i,j] = a * M[i,j] *)
  Lemma mnth_mcmul : forall {r c} (M : mat r c) a i j, (a c* M)$i$j = a * (M$i$j).
  Proof. intros. unfold mcmul. rewrite !vnth_vmap. auto. Qed.

  (** row (a * M) i = a * row M i *)
  Lemma mrow_mcmul : forall {r c} (M : mat r c) a i, (a c* M)$i = vcmul a (M$i).
  Proof. intros. unfold mcmul,vcmul,mmap. auto. Qed.

  (** col (a * M) i = a * col M i *)
  Lemma mcol_mcmul : forall {r c} (M : mat r c) a j,
      (fun i => (a c* M)$i$j) = vcmul a (fun i => M$i$j).
  Proof. intros. unfold mcmul,vcmul,mmap. auto. Qed.

  (** a1 * (a2 * M) = (a1 * a2) * M *)
  Lemma mcmul_assoc : forall {r c} (M : mat r c) a1 a2,
      a1 c* (a2 c* M) = (a1 * a2)%A c* M.
  Proof. intros. apply meq_iff_mnth; intros. rewrite !mnth_mcmul. monoid. Qed.
  
  (** a1 * (a2 * M) = a2 * (a1 * M) *)
  Lemma mcmul_perm : forall {r c} (M : mat r c) a1 a2,
      a1 c* (a2 c* M) = a2 c* (a1 c* M).
  Proof. intros. rewrite !mcmul_assoc. f_equal. asemigroup. Qed.

  (** a * (M1 + M2) = (a * M1) + (a * M2) *)
  Lemma mcmul_madd_distr : forall {r c} a (M1 M2 : mat r c),
      a c* (M1 + M2) = (a c* M1) + (a c* M2).
  Proof.
    intros. apply meq_iff_mnth; intros.
    rewrite !mnth_mcmul, !mnth_madd, !mnth_mcmul. ring.
  Qed.
  
  (** (a1 + a2) * M = (a1 * M) + (a2 * M) *)
  Lemma mcmul_add_distr : forall {r c} a1 a2 (M : mat r c),
      (a1 + a2)%A c* M = (a1 c* M) + (a2 c* M).
  Proof.
    intros. apply meq_iff_mnth; intros.
    rewrite !mnth_mcmul, !mnth_madd, !mnth_mcmul. ring.
  Qed.

  (* 0 c* M = mat0 *)
  Lemma mcmul_0_l : forall {r c} (M : mat r c), Azero c* M = mat0.
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite !mnth_mcmul, !mnth_mat0. ring.
  Qed.

  (** a c* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a c* (@mat0 r c) = mat0.
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite !mnth_mcmul, !mnth_mat0. ring.
  Qed.
  
  (** 1 c* M = M *)
  Lemma mcmul_1_l : forall {r c} (M : mat r c), Aone c* M = M.
  Proof. intros. apply meq_iff_mnth; intros. rewrite !mnth_mcmul. ring. Qed.

  (** a c* mat1 = mdiag([a,a,...]) *)
  Lemma mcmul_1_r : forall {n} a, a c* (@mat1 n) = mdiagMk Azero (vrepeat a).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_mcmul.
    destruct (finEqdec i j).
    - subst. rewrite mnth_mdiagMk_same.
      rewrite mnth_mat1_same, vnth_vrepeat. ring.
    - rewrite mnth_mat1_diff, mnth_mdiagMk_diff; auto. ring.
  Qed.
  
  (* (-a) * M = - (a * M) *)
  Lemma mcmul_opp : forall {r c} a (M : mat r c), (- a)%A c* M = - (a c* M).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_mopp,!mnth_mcmul. ring.
  Qed.
  
  (* a * (-M) = - (a * M) *)
  Lemma mcmul_mopp : forall {r c} a (M : mat r c), a c* (-M) = - (a c* M).
  Proof.
    intros. apply meq_iff_mnth; intros.
    rewrite !mnth_mopp,!mnth_mcmul,mnth_mopp. ring.
  Qed.
  
  (* (-a) * (- M) = a * M *)
  Lemma mcmul_opp_mopp : forall {r c} a (M : mat r c),
      (- a)%A c* (- M) = a c* M.
  Proof. intros. rewrite mcmul_mopp, mcmul_opp. apply group_inv_inv. Qed.

  (** a c* (M1 - M2) = (a c* M1) - (a c* M2) *)
  Lemma mcmul_msub : forall {r c} a (M1 M2 : mat r c),
      a c* (M1 - M2) = (a c* M1) - (a c* M2).
  Proof.
    intros. unfold msub. rewrite mcmul_madd_distr. rewrite mcmul_mopp. auto.
  Qed.

  (** (a c* M)\T = a c* (m\T) *)
  Lemma mtrans_mcmul : forall {r c} (a : A) (M : mat r c), (a c* M)\T = a c* (M\T).
  Proof.
    intros. apply meq_iff_mnth; intros.
    rewrite mnth_mtrans, !mnth_mcmul, mnth_mtrans. auto.
  Qed.

  (** tr (a c* M) = a * tr (m) *)
  Lemma mtrace_mcmul : forall {n} (a : A) (M : smat n), tr (a c* M) = (a * tr M)%A.
  Proof.
    intros. unfold mcmul, mtrace. apply vsum_cmul; intros.
    rewrite mnth_mmap. auto.
  Qed.

  
  (** *** Matrix Multiplication *)

  (* structural-style *)
  Definition mmul_old {r c t : nat} (M1 : mat r c) (M2 : mat c t) : mat r t :=
    vmap (fun v1 => vmap (fun v2 => <v1,v2>) (mtrans M2)) M1.
  
  (* functional-style *)
  Definition mmul {r c t : nat} (M1 : mat r c) (M2 : mat c t) : mat r t :=
    fun i j => <M1$i, (fun k=>M2$k$j)>.

  Infix "*" := mmul : mat_scope.

  (* (M1 * M2)[i,j] = <row M1 i, col M2 j> *)
  Lemma mnth_mmul : forall {r c t} (M1 : mat r c) (M2 : mat c t) i j,
      (M1 * M2)$i$j = <M1$i, (fun k=>M2$k$j)>.
  Proof. intros. auto. Qed.

  (* (M1 * M2)[i] = <row M1 i, col M2 j> *)
  Lemma vnth_mmul : forall {r c t} (M1 : mat r c) (M2 : mat c t) i,
      (M1 * M2)$i = vmap (fun v => <M1$i,v>) (M2\T).
  Proof. intros. auto. Qed.

  (** (M1 * M2) * M3 = M1 * (M2 * M3) *)
  Lemma mmul_assoc : forall {m n r s} (M1 : mat m n) (M2 : mat n r) (M3 : mat r s),
      (M1 * M2) * M3 = M1 * (M2 * M3).
  Proof.
    intros. unfold mmul,vdot,vsum,vmap2. apply meq_iff_mnth; intros.
    pose proof (fseqsum_fseqsum_exchg r n
                  (fun i0 j0 => M1 i j0 * M2 j0 i0 * M3 i0 j)%A).
    match goal with
    | H: ?a1 = ?b1 |- ?a2 = ?b2 => replace a2 with a1;[replace b2 with b1|]; auto
    end.
    - f_equal. extensionality j0. apply fseqsum_cmul; intros. ring.
    - f_equal. extensionality j0. rewrite commutative.
      apply fseqsum_cmul; intros. ring.
  Qed.

  (** M1 * (M2 + M3) = M1 * M2 + M1 * M3 *)
  Lemma mmul_madd_distr_l : forall {r c t} (M1 : mat r c) (M2 M3 : mat c t),
      M1 * (M2 + M3) = (M1 * M2) + (M1 * M3).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_madd, !mnth_mmul.
    unfold vdot. apply vsum_add; intros k. rewrite !vnth_vmap2, mnth_madd. ring.
  Qed.
  
  (** (M1 + M2) * M3 = M1 * M3 + M2 * M3 *)
  Lemma mmul_madd_distr_r : forall {r c t} (M1 M2 : mat r c) (M3 : mat c t),
      (M1 + M2) * M3 = (M1 * M3) + (M2 * M3).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_madd,!mnth_mmul.
    unfold vdot. apply vsum_add; intros k. rewrite !vnth_vmap2, mnth_madd. ring.
  Qed.

  (** (-M1) * M2 = - (M1 * M2) *)
  Lemma mmul_mopp_l : forall {r c t} (M1 : mat r c) (M2 : mat c t),
      (-M1) * M2 = -(M1 * M2).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_mopp, !mnth_mmul.
    unfold vdot. apply vsum_opp; intros k. rewrite !vnth_vmap2, mnth_mopp. ring.
  Qed.

  (** M1 * (-M2) = - (M1 * M2) *)
  Lemma mmul_mopp_r : forall {r c t} (M1 : mat r c) (M2 : mat c t),
      M1 * (-M2) = -(M1 * M2).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_mopp, !mnth_mmul.
    unfold vdot. apply vsum_opp; intros k. rewrite !vnth_vmap2, mnth_mopp. ring.
  Qed.

  (** M1 * (M2 - M3) = M1 * M2 - M1 * M3 *)
  Lemma mmul_msub_distr_l : forall {r c t} (M1 : mat r c) (M2 M3 : mat c t),
      M1 * (M2 - M3) = (M1 * M2) - (M1 * M3).
  Proof.
    intros. unfold msub. rewrite mmul_madd_distr_l. rewrite mmul_mopp_r. auto.
  Qed.
  
  (** (M1 - M2) * M3 = M1 * M3 - M2 * M3 *)
  Lemma mmul_msub_distr_r : forall {r c t} (M1 M2 : mat r c) (M3 : mat c t),
      (M1 - M2) * M3 = (M1 * M3) - (M2 * M3).
  Proof.
    intros. unfold msub. rewrite mmul_madd_distr_r. rewrite mmul_mopp_l. auto.
  Qed.
  
  (** 0 * M = 0 *)
  Lemma mmul_0_l : forall {r c t} (M : mat c t), mat0 * M = @mat0 r t.
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite !mnth_mmul, mnth_mat0.
    rewrite mrow_mat0. apply vdot_0_l.
  Qed.
  
  (** M * 0 = 0 *)
  Lemma mmul_0_r : forall {r c t} (M : mat r c), M * mat0 = @mat0 r t.
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite !mnth_mmul, mnth_mat0.
    rewrite mcol_mat0. apply vdot_0_r.
  Qed.
  
  (** 1 * M = M *)
  Lemma mmul_1_l : forall {r c} (M : mat r c), mat1 * M = M.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold mmul,vdot,mat1,vmap2,vsum.
    apply fseqsum_unique with (i:=i).
    - destruct finEqdec; subst. monoid. easy.
    - intros. destruct finEqdec; subst. easy. ring.
  Qed.
  
  (** M * 1 = M *)
  Lemma mmul_1_r : forall {r c} (M : mat r c), M * mat1 = M.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold mmul,vdot,mat1,vmap2,vsum.
    apply fseqsum_unique with (i:=j).
    - destruct finEqdec; subst. monoid. easy.
    - intros. destruct finEqdec; subst. easy. ring.
  Qed.

  (** (a c* M1) * M2 = a c* (M1 * M2) *)
  Lemma mmul_mcmul_l : forall {r c s} (a : A) (M1 : mat r c) (M2 : mat c s), 
      (a c* M1) * M2 = a c* (M1 * M2).
  Proof.
    intros. apply meq_iff_mnth; intros.
    repeat rewrite ?mnth_mmul, ?mnth_mcmul.
    rewrite mrow_mcmul. rewrite vdot_assoc_cmul_l. auto.
  Qed.
  
  (** M1 * (a c* M2) = a c* (M1 * M2) *)
  Lemma mmul_mcmul_r : forall {r c s} (a : A) (M1 : mat r c) (M2 : mat c s), 
      M1 * (a c* M2) = a c* (M1 * M2).
  Proof.
    intros. apply meq_iff_mnth; intros.
    repeat rewrite ?mnth_mmul, ?mnth_mcmul.
    rewrite mcol_mcmul. rewrite vdot_assoc_cmul_r. auto.
  Qed.

  (** (M1 * M2)\T = M2\T * M1\T *)
  Lemma mtrans_mmul : forall {r c s} (M1 : mat r c) (M2 : mat c s),
      (M1 * M2)\T = M2\T * M1\T.
  Proof.
    intros. apply meq_iff_mnth; intros.
    rewrite !mnth_mtrans,!mnth_mmul. rewrite vdot_comm. f_equal.
  Qed.

  (** tr (M1 * M2) = tr (M2 * M1) *)
  Lemma mtrace_mmul : forall {r c} (M1 : mat r c) (M2 : mat c r),
      tr (M1 * M2) = tr (M2 * M1).
  Proof.
    (* from: https://en.wikipedia.org/wiki/Trace_(linear_algebra)
       tr(A*B) = Σ(A*B)_{ii}
       = ΣΣ(A_{ij} B_{ji}) = ΣΣ(B_{ji} A_{ij}) 
       = Σ(BA)_{jj} = tr(B*A) *)
    intros. unfold mtrace. unfold mmul,vdot,vmap2,vsum.
    rewrite fseqsum_fseqsum_exchg.
    apply fseqsum_eq; intros. apply fseqsum_eq; intros. ring.
  Qed.

  (* tr(ABCD) = tr(BCDA) = tr(CDAB) = tr(DABC) *)
  Lemma mtrace_cyclic4_BCDA :
    forall {r c s t} (A:mat r c)(B:mat c s)(C:mat s t)(D:mat t r),
      tr(A*B*C*D) = tr(B*C*D*A).
  Proof.
    intros. replace (A0*B*C*D) with (A0*(B*C*D)). apply mtrace_mmul.
    rewrite <- !mmul_assoc. auto.
  Qed.
  
  Lemma mtrace_cyclic4_CDAB :
    forall {r c s t} (A:mat r c)(B:mat c s)(C:mat s t)(D:mat t r),
      tr(A*B*C*D) = tr(C*D*A*B).
  Proof. intros. do 2 rewrite mtrace_cyclic4_BCDA. auto. Qed.
  
  Lemma mtrace_cyclic4_DABC :
    forall {r c s t} (A:mat r c)(B:mat c s)(C:mat s t)(D:mat t r),
      tr(A*B*C*D) = tr(D*A*B*C).
  Proof. intros. do 3 rewrite mtrace_cyclic4_BCDA. auto. Qed.

  (* tr(ABC) = tr(BCA) = tr(CAB) *)
  Lemma mtrace_cyclic3_BCA : forall {n} (A B C:smat n), tr(A*B*C) = tr(B*C*A).
  Proof.
    (* tr(ABC)=tr((ABC)\T))=tr((BC)\T A\T)=tr(A\T (BC)\T)=tr(BCA) *)
    intros. rewrite <- mtrace_mtrans. rewrite mmul_assoc. rewrite mtrans_mmul.
    rewrite mtrace_mmul. rewrite <- mtrans_mmul. apply mtrace_mtrans.
  Qed.

  Lemma mtrace_cyclic3_CAB : forall {n} (A B C:smat n), tr(A*B*C) = tr(C*A*B).
  Proof.
    (* tr(ABC)=tr((ABC)\T))=tr(C\T (AB)\T)=tr((AB)\T C\T)=tr(CAB) *)
    intros. rewrite <- mtrace_mtrans. rewrite mtrans_mmul. rewrite mtrace_mmul.
    rewrite <- mtrans_mmul. rewrite mtrace_mtrans. rewrite mmul_assoc. auto.
  Qed.


  Context `{ADec : Dec A}.

  
  (** (M1 <> 0 /\ M2 <> 0 /\ k * M1 = M2) -> k <> 0 *)
  Lemma mcmul_eq_implfy_not_k0 : forall {r c} (M1 M2 : mat r c) k,
      M1 <> mat0 -> M2 <> mat0 -> k c* M1 = M2 -> k <> Azero.
  Proof.
    intros. destruct (dec k Azero); auto. exfalso. subst.
    rewrite mcmul_0_l in H1. easy.
  Qed.

  
  (** Properties below, need a field structure *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.

  
  (** k * M = 0 -> (k = 0) \/ (M = 0) *)
  Lemma mcmul_eq0_imply_m0_or_k0 : forall {r c} (M : mat r c) k,
      k c* M = mat0 -> (k = Azero)%A \/ (M = mat0).
  Proof.
    intros. destruct (dec k Azero); auto. right.
    apply meq_iff_mnth; intros. rewrite meq_iff_mnth in H0. specialize (H0 i j).
    cbv in H0. cbv. apply field_mul_eq0_imply_a0_or_b0 in H0; auto. tauto.
  Qed.

  (** (M <> 0 /\ k * M = 0) -> M = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (M : mat r c) k,
      M <> mat0 -> k c* M = mat0 -> (k = Azero)%A.
  Proof. intros. apply mcmul_eq0_imply_m0_or_k0 in H1; auto. tauto. Qed.

  (** k * M = M -> k = 1 \/ M = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} k (M : mat r c),
      k c* M = M -> (k = Aone)%A \/ (M = mat0).
  Proof.
    intros. destruct (dec k Aone); auto. right.
    apply meq_iff_mnth; intros. rewrite meq_iff_mnth in H0. specialize (H0 i j).
    cbv in H0. cbv. apply field_mul_eq_imply_a1_or_b0 in H0; auto. tauto.
  Qed.

  Section Extra.
    
    (* Notation "M $ i $ j " := (mnth Azero M i j) : mat_scope. *)
    (* Notation "M .11" := (M $ 0 $ 0) : mat_scope. *)
    (* Notation "M .12" := (M $ 0 $ 1) : mat_scope. *)
    (* Notation "M .13" := (M $ 0 $ 2) : mat_scope. *)
    (* Notation "M .14" := (M $ 0 $ 3) : mat_scope. *)
    (* Notation "M .21" := (M $ 1 $ 0) : mat_scope. *)
    (* Notation "M .22" := (M $ 1 $ 1) : mat_scope. *)
    (* Notation "M .23" := (M $ 1 $ 2) : mat_scope. *)
    (* Notation "M .24" := (M $ 1 $ 3) : mat_scope. *)
    (* Notation "M .31" := (M $ 2 $ 0) : mat_scope. *)
    (* Notation "M .32" := (M $ 2 $ 1) : mat_scope. *)
    (* Notation "M .33" := (M $ 2 $ 2) : mat_scope. *)
    (* Notation "M .34" := (M $ 2 $ 3) : mat_scope. *)
    (* Notation "M .41" := (M $ 3 $ 0) : mat_scope. *)
    (* Notation "M .42" := (M $ 3 $ 1) : mat_scope. *)
    (* Notation "M .43" := (M $ 3 $ 2) : mat_scope. *)
    (* Notation "M .44" := (M $ 3 $ 3) : mat_scope. *)
    
    (* Definition det_of_mat_3_3 (M : mat A 3 3) : A := *)
    (*   let b1 := (M.11 * M.22 * M.33)%A in *)
    (*   let b2 := (M.12 * M.23 * M.31)%A in *)
    (*   let b3 := (M.13 * M.21 * M.32)%A in *)
    (*   let c1 := (M.11 * M.23 * M.32)%A in *)
    (*   let c2 := (M.12 * M.21 * M.33)%A in *)
    (*   let c3 := (M.13 * M.22 * M.31)%A in *)
    (*   let b := (b1 + b2 + b3)%A in *)
    (*   let c := (c1 + c2 + c3)%A in *)
    (*   (b - c)%A. *)

    (* Definition skew_sym_mat_of_v3 (V : @cvec A 3) : mat A 3 3. *)
    (* Proof. *)
    (*   refine (mk_mat_3_3 *)
    (*             Azero    (-V.z)    y *)
    (*             z     Azero     (-x) *)
    (*             (-y)  x       Azero)%A. *)
    (* Defined. *)
    
    (* Definition v3cross (v1 v2 : V3) : vec 3 := (skew_sym_mat_of_v3 v1) * v2. *)
    
    (* Definition so3 (M : mat 3 3) : Prop :=  *)
    (*   let so3_mul_unit : Prop := (m \T) * m = mat1 3 in *)
    (*   let so3_det : Prop := (det_of_mat_3_3 M) = Aone in *)
    (*     so3_mul_unit /\ so3_det. *)

  End Extra.

End malg.


Section test.
  Let M0 := @l2m _ 9 2 2 [].
  Let M1 := @l2m _ 9 2 2 [[1;2];[3;4]].
  Let M2 := @l2m _ 9 2 2 [[1];[3;4]].
  Let M3 := @l2m _ 9 2 2 [[1;2];[3]].
  Let M4 := @l2m _ 9 2 2 [[1;2;3];[3;4]].
  Let M5 := @l2m _ 9 2 2 [[1;2];[3;4;5]].
  (* Compute m2l M0. *)
  (* Compute m2l M1. *)
  (* Compute m2l M2. *)
  (* Compute m2l M3. *)
  (* Compute m2l M4. *)
  (* Compute m2l M5. *)
End test.


Module coordinate_transform_test.
  Import Reals.
  Open Scope R.
  
  (* https://en.wikipedia.org/wiki/Matrix_(mathematics)#Basic_operations *)

  Infix "*" := Rmult.
  Infix "+" := Rplus.
  Notation mat r c := (mat R r c).
  Notation l2m := (l2m 0).
  Infix "+" := (madd (Aadd:=Rplus)) : mat_scope.
  Infix "*" := (mmul (Aadd:=Rplus) (Amul:=Rmult) (Azero:=R0)) : mat_scope.
  Infix "c*" := (mcmul (Amul:=Rmult)) : mat_scope.

  Open Scope mat_scope.

  Definition M1 : mat 2 3 := l2m [[1;3;1];[1;0;0]].
  Definition M2 : mat 2 3 := l2m [[0;0;5];[7;5;0]].
  Definition M3 : mat 2 3 := l2m [[1;3;6];[8;5;0]].

  (** There are many wasy to finish the proof *)
  
  (* 1. use `m2l_inj` to convert the equation to `list` domain *)
  Example madd_m1_m2_eq_m3 : M1 + M2 = M3.
  Proof. apply m2l_inj. cbv. list_eq; ring. Qed.
  
  (* 2. use `mnth` to compare elements. It is a bit complex *)
  Example madd_m1_m2_eq_m3' : M1 + M2 = M3.
  Proof.
    apply meq_iff_mnth; intros. rewrite mnth_madd. unfold M1,M2,M3. destruct i,j.
    repeat (try destruct x; try destruct x0; try lia; try (cbn; ring)).
  Qed.
  
  Definition M4 : mat 2 3 := l2m [[1; 8;-3];[4;-2; 5]].
  Definition M5 : mat 2 3 := l2m [[2;16;-6];[8;-4;10]].
  Example mscale_2_m4_eq_m5 : 2 c* M4 = M5.
  Proof. apply m2l_inj. cbv. list_eq; ring. Qed.
  
  Definition M6 : mat 2 3 := l2m [[1;2;3];[0;-6;7]].
  Definition M7 : mat 3 2 := l2m [[1;0];[2;-6];[3;7]].
  Example mtrans_m6_eq_m7 : M6\T = M7.
  Proof. apply m2l_inj. cbv. list_eq; ring. Qed.
  
  Variable θ ψ φ : R.
  Definition Rx (α : R) : mat 3 3 :=
    @mkmat_3_3 _ 0
      1         0           0
      0         (cos α)     (sin α)
      0         (-sin α)%R    (cos α).

  Definition Ry (β : R) : mat 3 3 :=
    @mkmat_3_3 _ 0
      (cos β)   0           (-sin β)%R
      0         1           0
      (sin β)   0           (cos β).

  Definition Rz (γ : R) : mat 3 3 :=
    @mkmat_3_3 _ 0
      (cos γ)   (sin γ)   0
      (-sin γ)  (cos γ)   0
      0         0         1.

  Definition R_b_e_direct : mat 3 3 :=
    (@mkmat_3_3 _ 0
       (cos θ * cos ψ)
       (cos ψ * sin θ * sin φ - sin ψ * cos φ)
       (cos ψ * sin θ * cos φ + sin φ * sin ψ)
       
       (cos θ * sin ψ)
       (sin ψ * sin θ * sin φ + cos ψ * cos φ)
       (sin ψ * sin θ * cos φ - cos ψ * sin φ)
       
       (-sin θ)
       (sin φ * cos θ)
       (cos φ * cos θ))%R.
  
  Opaque cos sin.

  Lemma Rx_Ry_Rz_eq_Rbe : (Rz ψ)\T * (Ry θ)\T * (Rx φ)\T = R_b_e_direct.
  Proof. apply m2l_inj. cbv. list_eq; ring. Qed.
  
End coordinate_transform_test.
