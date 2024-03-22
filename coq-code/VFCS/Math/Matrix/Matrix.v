(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Record-List model
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. 变换矩阵，基变换，
     https://en.wikipedia.org/wiki/Change_of_basis
     change-of-basis matrix (also called transition matrix)
  2. 
 *)


Require Export TupleExt Hierarchy.
Require Export ListExt.
Require Export Vector.
Require Reals.
Require Import Extraction.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.

(** Control the scope *)
(* Open Scope nat_scope. *)
(* Open Scope fin_scope. *)
(* Open Scope A_scope. *)
(* Open Scope vec_scope. *)
Open Scope mat_scope.


(* ======================================================================= *)
(** ** Matrix type *)

Notation mat A r c := (@vec (@vec A c) r).

(** square matrix type *)
Notation smat A n := (mat A n n).

(* Actually, mat A r c = forall A r c, fin r -> fin c -> A  *)
(* Eval cbv in forall A r c, mat A r c. *)


(* Note that: these notatiosn are dangerous.
   The reason can be found in the definition of `V.1` in file `Vector.v`
 *)
Notation "M .11" := (M.1.1) : mat_scope.
Notation "M .12" := (M.1.2) : mat_scope.
Notation "M .13" := (M.1.3) : mat_scope.
Notation "M .14" := (M.1.4) : mat_scope.
Notation "M .21" := (M.2.1) : mat_scope.
Notation "M .22" := (M.2.2) : mat_scope.
Notation "M .23" := (M.2.3) : mat_scope.
Notation "M .24" := (M.2.4) : mat_scope.
Notation "M .31" := (M.3.1) : mat_scope.
Notation "M .32" := (M.3.2) : mat_scope.
Notation "M .33" := (M.3.3) : mat_scope.
Notation "M .34" := (M.3.4) : mat_scope.
Notation "M .41" := (M.4.1) : mat_scope.
Notation "M .42" := (M.4.2) : mat_scope.
Notation "M .43" := (M.4.3) : mat_scope.
Notation "M .44" := (M.4.4) : mat_scope.

Lemma meq_iff_mnth : forall {A r c} (M N : mat A r c),
    M = N <-> (forall i j, M $ i $ j = N $ i $ j).
Proof.
  intros. split; intros; subst; auto.
  apply veq_iff_vnth. intros i.
  apply veq_iff_vnth. intros j. auto.
Qed.

Lemma mneq_iff_exist_mnth_neq : forall {A r c} (M N : mat A r c),
    M <> N <-> (exists i j, M $ i $ j <> N $ i $ j).
Proof.
  intros. rewrite meq_iff_mnth. split; intros.
  - apply not_all_ex_not in H. destruct H as [i H].
    apply not_all_ex_not in H. destruct H as [j H]. exists i, j; auto.
  - destruct H as [i [j H]].
    apply ex_not_not_all; auto. exists i.
    apply ex_not_not_all; auto. exists j. auto.
Qed.


(* ======================================================================= *)
(** ** Zero matrix *)
Section mat0.
  Context {A} {Azero : A}.
  Definition mat0 {r c} : mat A r c := fun _ _ => Azero.

  (** mat0[i,j] = 0 *)
  Lemma mnth_mat0 : forall {r c} i j, @mat0 r c $ i $ j = Azero.
  Proof. intros. auto. Qed.

  (* row mat0 i = vzero *)
  Lemma mrow_mat0 : forall {r c} i, @mat0 r c $ i = vzero Azero.
  Proof. intros. auto. Qed.

  (* col mat0 i = vzero *)
  Lemma mcol_mat0 : forall {r c} j, (fun k => @mat0 r c $ k $ j) = vzero Azero.
  Proof. intros. auto. Qed.
End mat0.


(* ======================================================================= *)
(** ** Row vector and column vector *)
  
(** Row/column vector type *)
Notation rvec A n := (mat A 1 n).
Notation cvec A n := (mat A n 1).

(** *** Convert between `cvec` and `vec *)
Section cvec_vec.
  Context {A : Type}.
  Notation cvec n := (cvec A n).
  
  Definition cv2v {n} (M : cvec n) : vec n := fun i => M $ i $ fin0.
  Definition v2cv {n} (a : vec n) : cvec n := fun i j => a $ i.
  
  Lemma cv2v_spec : forall {n} (M : cvec n) i, M $ i $ fin0 = (cv2v M) $ i.
  Proof. auto. Qed.
  Lemma v2cv_spec : forall {n} (a : vec n) i, a $ i = (v2cv a) $ i $ fin0.
  Proof. auto. Qed.

  Lemma cv2v_v2cv : forall {n} (a : vec n), cv2v (v2cv a) = a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. auto. Qed.
  
  Lemma v2cv_cv2v : forall {n} (M : cvec n), v2cv (cv2v M) = M.
  Proof.
    intros. apply meq_iff_mnth; intros. cbv. f_equal.
    rewrite (fin1_uniq j). apply Fin_eq_iff; auto.
  Qed.

  Lemma cv2v_inj : forall {n} (M N : cvec n), cv2v M = cv2v N -> M = N.
  Proof.
    intros. rewrite veq_iff_vnth in H. rewrite meq_iff_mnth.
    unfold cv2v in H. intros. rewrite (fin1_uniq j). auto.
  Qed.
  
  Lemma v2cv_inj : forall {n} (a b : vec n), v2cv a = v2cv b -> a = b.
  Proof.
    intros. rewrite meq_iff_mnth in H. rewrite veq_iff_vnth.
    unfold v2cv in H. intros. apply (H i fin0).
  Qed.
  
  Lemma vnth_v2cv : forall {n} (a : vec n) i j, (v2cv a) $ i $ j = a $ i.
  Proof. intros. unfold v2cv. auto. Qed.

  Lemma vnth_cv2v : forall {n} (M : cvec n) i j, (cv2v M) $ i = M $ i $ j.
  Proof. intros. unfold cv2v. f_equal. rewrite (fin1_uniq j); auto. Qed.
  
End cvec_vec.


(** *** Convert between `rvec` and `vec *)
Section rvec_vec.
  Context {A : Type}.
  Notation rvec n := (rvec A n).
  
  Definition rv2v {n} (M : rvec n) : vec n := fun i => M $ fin0 $ i.
  Definition v2rv {n} (a : vec n) : rvec n := fun i j => a $ j.
  
  Lemma rv2v_spec : forall {n} (M : rvec n) i, M $ fin0 $ i = (rv2v M) $ i.
  Proof. auto. Qed.
  Lemma v2rv_spec : forall {n} (a : vec n) i, a $ i = (v2rv a) $ fin0 $ i.
  Proof. auto. Qed.

  Lemma rv2v_v2rv : forall {n} (a : vec n), rv2v (v2rv a) = a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. auto. Qed.

  Lemma v2rv_rv2v : forall {n} (M : rvec n), v2rv (rv2v M) = M.
  Proof.
    intros. apply meq_iff_mnth; intros. cbv. f_equal. rewrite (fin1_uniq i).
    apply Fin_eq_iff; auto.
  Qed.
  
  Lemma vnth_v2rv : forall {n} (a : vec n) i, (v2rv a) $ i  = a.
  Proof. intros. unfold v2rv. auto. Qed.
  
End rvec_vec.


(** *** Convert between `cvec` and `rvec *)
Lemma v2rv_cv2v : forall {A n} (M : cvec A n), v2rv (cv2v M) = fun i j => M $ j $ i.
Proof.
  intros. apply meq_iff_mnth; intros. cbv. f_equal.
  rewrite (fin1_uniq i). apply Fin_eq_iff; auto.
Qed.


(* ======================================================================= *)
(** ** Convert between `list of vectors` and mat *)
Section vl2m_m2vl.
  Context {A} (Azero : A).
  Notation mat r c := (mat A r c).

  (** mat to `list of row vectors` *)
  Definition m2rvl {r c} (M : mat r c) : list (@vec A c) :=
    map (fun i => M $ i) (finseq r).

  (** `list of row vectors` to mat *)
  Definition rvl2m {r c} (l : list (@vec A c)) : mat r c :=
    fun i => nth (fin2nat i) l (vzero Azero).

  Lemma m2rvl_rvl2m : forall {r c} (l : list (@vec A c)),
      length l = r -> @m2rvl r c (rvl2m l) = l.
  Proof.
    intros. unfold m2rvl, rvl2m.
    rewrite (list_eq_iff_nth (vzero Azero) r); auto.
    - intros. rewrite nth_map_finseq with (H:=H0). f_equal.
    - rewrite map_length, finseq_length. auto.
  Qed.
  
  Lemma rvl2m_m2rvl : forall {r c} (M : mat r c), rvl2m (m2rvl M) = M.
  Proof.
    intros. unfold rvl2m, m2rvl. apply meq_iff_mnth; intros.
    rewrite nth_map_finseq with (H:=fin2nat_lt _). f_equal. apply fin_fin2nat.
  Qed.

  (** mat to `list of column vectors` *)
  Definition m2cvl {r c} (M : mat r c) : list (@vec A r) :=
    map (fun i j => M j i) (finseq c).
  
  (** `list of column vectors` to mat *)
  Definition cvl2m {r c} (l : list (@vec A r)) : mat r c :=
    fun i j  => (nth (fin2nat j) l (vzero Azero)) $ i.
  
  Lemma m2cvl_cvl2m : forall {r c} (l : list (@vec A r)),
      length l = c -> @m2cvl r c (cvl2m l) = l.
  Proof.
    intros. unfold m2cvl, cvl2m.
    rewrite (list_eq_iff_nth (vzero Azero) c); auto.
    - intros. rewrite nth_map_finseq with (H:=H0).
      apply veq_iff_vnth; intros j. f_equal.
    - rewrite map_length, finseq_length. auto.
  Qed.
  
  Lemma cvl2m_m2cvl : forall {r c} (M : mat r c), cvl2m (m2cvl M) = M.
  Proof.
    intros. unfold cvl2m, m2cvl. apply meq_iff_mnth; intros.
    rewrite nth_map_finseq with (H:=fin2nat_lt _). f_equal. apply fin_fin2nat.
  Qed.

End vl2m_m2vl.


  
(* ======================================================================= *)
(** ** Convert between nat-indexing-Function (f) and matrix *)
Section f2m_m2f.
  Context {A} (Azero : A).

  Definition f2m {r c} (f : nat -> nat -> A) : mat A r c :=
    @f2v _ r (fun i => @f2v A c (f i)).
    
  Definition m2f {r c} (M : mat A r c) : (nat -> nat -> A) :=
    fun i => @v2f _ Azero c (@v2f _ (vzero Azero) r M i).
  
  (* M[i,j] = m2f M i j *)
  Lemma mnth_eq_nth_m2f : forall {r c} (M : @mat A r c) (i j : nat) (Hi:i < r)(Hj:j < c),
      M (Fin i Hi) (Fin j Hj) = m2f M i j.
  Proof.
    intros. unfold m2f,v2f,ff2f.
    destruct (_??<_)%nat; try lia.
    destruct (_??<_)%nat; try lia. f_equal; apply Fin_eq_iff; auto.
  Qed.

  Lemma meq_iff_nth_m2f : forall {r c} (M N : mat A r c),
      M = N <-> (forall i j, i < r -> j < c -> (m2f M) i j = (m2f N) i j).
  Proof.
    intros. rewrite meq_iff_mnth. split; intros.
    - specialize (H (Fin i H0) (Fin j H1)).
      rewrite !mnth_eq_nth_m2f in H. auto.
    - destruct i, j. rewrite !mnth_eq_nth_m2f. auto.
  Qed.

End f2m_m2f.


(* ======================================================================= *)
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

  Lemma m2l_inj : forall {r c} (M N : mat A r c), m2l M = m2l N -> M = N.
  Proof.
    intros. unfold m2l in H.  apply map_inj in H; auto. apply v2l_inj; auto.
    intros. apply v2l_inj; auto.
  Qed.

  Lemma m2l_surj : forall {r c} (d : dlist A),
      length d = r -> width d c -> (exists M : mat A r c, m2l M = d).
  Proof.
    intros. unfold m2l.
    pose proof (map_surj (@v2l A c) d).
    assert (forall l : list A, In l d -> exists a : vec c, v2l a = l).
    { intros. exists (l2v Azero l). apply v2l_l2v.
      apply (width_imply_in_length l d); auto. }
    specialize (H1 H2). destruct H1. destruct H1.
    exists (l2v (vzero Azero) x). rewrite v2l_l2v; auto. lia.
  Qed.

  Definition l2m {r c} (d : dlist A) : mat A r c :=
    l2v (vzero Azero) (map (l2v Azero) d).

  Lemma mnth_l2m : forall {r c} (d : dlist A) i j,
      (* length d = r -> *)
      (@l2m r c d) i j = nth (fin2nat i) (nth (fin2nat i) d []) Azero.
  Proof.
    intros r c d. revert r c. induction d; intros.
    - simpl.
      unfold l2m.
  Abort.

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
    rewrite map_map. apply ListExt.map_id. intros. apply l2v_v2l.
  Qed.

  Lemma l2m_m2l : forall {r c} (M : mat A r c), (@l2m r c (m2l M)) = M.
  Proof.
    intros. unfold l2m,m2l.
    apply veq_iff_vnth; intros i. apply veq_iff_vnth; intros j.
    rewrite !vnth_l2v.
    rewrite nth_map with (n:=r)(Azero:=[]); auto;
      try rewrite map_length; try apply v2l_length; try apply fin2nat_lt.
    rewrite nth_map with (n:=r)(Azero:=vzero Azero);
      try apply v2l_length; try apply fin2nat_lt.
    rewrite l2v_v2l.
    rewrite nth_v2l with (H:=fin2nat_lt _); try apply fin2nat_lt.
    f_equal. apply nat2fin_fin2nat.
  Qed.

  Lemma m2l_l2m : forall {r c} (d : dlist A),
      length d = r -> width d c -> m2l (@l2m r c d) = d.
  Proof.
    intros. unfold l2m,m2l; simpl. rewrite v2l_l2v.
    - rewrite map_map. apply map_id_In; intros. apply v2l_l2v.
      apply (width_imply_in_length a d); auto.
    - rewrite map_length; auto.
  Qed.

End l2m_m2l.


(* ======================================================================= *)
(** ** matrix transpose *)
Section mtrans.
  Context {A} (Azero : A).

  Notation mat0 := (@mat0 _ Azero).

  (* Definition mtrans_old {r c} (M : mat A r c) : mat A c r := *)
  (*   vmap (fun j => mcol M j) (vfinseq c). *)
  
  Definition mtrans {r c} (M : mat A r c) : mat A c r := fun i j => M j i.
  Notation "M \T" := (mtrans M) : mat_scope.

  (** (M\T)[i,*] = M[*,i] *)
  Lemma vnth_mtrans : forall {r c} (M : mat A r c) i, (M\T) $ i = fun j => M $ j $ i.
  Proof. intros. auto. Qed.

  (** (M\T)[i,j] = M[j,i] *)
  Lemma mnth_mtrans : forall {r c} (M : mat A r c) i j, (M\T) $ i $ j = M $ j $ i.
  Proof. intros. auto. Qed.

  (** Transpose twice return back *)
  Lemma mtrans_mtrans : forall {r c} (M : mat A r c), (M\T)\T = M.
  Proof. intros. auto. Qed.
  
  (** mat0\T = mat0 *)
  Lemma mtrans_mat0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. auto. Qed.

End mtrans.

Notation "M \T" := (mtrans M) : mat_scope.


(* ======================================================================= *)
(** ** Get row and column of a matrix *)
Section mrow_mcol.
  Context {A} {Azero : A}.
  Notation vzero := (vzero Azero).

  Definition mrow {r c} (M : mat A r c) (i : fin r) : @vec A c := M i.

  Lemma vnth_mrow : forall {r c} (M : mat A r c) (i : fin r) (j : fin c),
      (mrow M i) $ j = M $ i $ j.
  Proof. intros. auto. Qed.
  
  Definition mcol {r c} (M : mat A r c) (j : fin c) : @vec A r := fun i => M i j.

  Lemma vnth_mcol : forall {r c} (M : mat A r c) (i : fin r) (j : fin c),
      (mcol M j) $ i = M $ i $ j.
  Proof. intros. auto. Qed.

End mrow_mcol.

  
(* ======================================================================= *)
(** ** Construct matrix with two matrices *)
Section mapp.
  Context {A} {Azero : A}.
  Notation m2f := (m2f Azero).
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (M : mat A r1 c) (N : mat A r2 c)
    : mat A (r1 + r2) c :=
    f2m (fun i j => if i ??< r1 then m2f M i j else m2f N (i - r1) j).

  (** Append matrix by column *)
  Definition mappc {r c1 c2} (M : mat A r c1) (N : mat A r c2)
    : mat A r (c1 + c2) :=
    f2m (fun i j => if j ??< c1 then m2f M i j else m2f N i (j - c1)).
  
End mapp.

Section test.
  Let M := @l2m _ 9 2 2 [[1;2];[3;4]].
  Let N :=  @l2m _ 9 2 2 [[11;12];[13;14]].
  (* Compute m2l (mappr M N). *)
  (* Compute m2l (mappc M N). *)
End test.


(* ======================================================================= *)
(** ** matrix with specific size *)

Section mat_specific.
  Context {A} {Azero : A}.
  Notation l2m := (l2m Azero).
  Variable r c : nat.
  Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : A.

  (** *** Create matrix *)
  Definition mkmat_0_c : mat A 0 c := vzero (vzero Azero). (* anything is ok *)
  Definition mkmat_r_0 : mat A r 0 := vzero (vzero Azero). (* anything is ok *)

  Definition mkmat_1_c (a : @vec A c) : mat A 1 c := fun i j => a j.
  Definition mkmat_r_1 (a : @vec A r) : mat A r 1 := fun i j => a i.

  Definition mkmat_1_1 : mat A 1 1 := l2m [[a11]].
  Definition mkmat_1_2 : mat A 1 2 := l2m [[a11;a12]].
  Definition mkmat_2_1 : mat A 2 1 := l2m [[a11];[a21]].
  Definition mkmat_2_2 : mat A 2 2 := l2m [[a11;a12];[a21;a22]].
  Definition mkmat_1_3 : mat A 1 3 := l2m [[a11;a12;a13]].
  Definition mkmat_2_3 : mat A 2 3 := l2m [[a11;a12;a13];[a21;a22;a23]].
  Definition mkmat_3_1 : mat A 3 1 := l2m [[a11];[a21];[a31]].
  Definition mkmat_3_2 : mat A 3 2 := l2m [[a11;a12];[a21;a22];[a31;a32]].
  Definition mkmat_3_3 : mat A 3 3 :=
    l2m [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  Definition mkmat_1_4 : mat A 1 4 := l2m [[a11;a12;a13;a14]].
  Definition mkmat_4_1 : mat A 4 1 := l2m [[a11];[a21];[a31];[a41]].
  Definition mkmat_4_4 : mat A 4 4 :=
    l2m [[a11;a12;a13;a14];[a21;a22;a23;a24];[a31;a32;a33;a34];[a41;a42;a43;a44]].
  
End mat_specific.


(* ======================================================================= *)
(** ** Matrix map *)
Notation mmap f M := (vmap (vmap f) M).

Lemma mnth_mmap : forall {A B} {r c} (M : mat A r c) (f:A -> B) i j,
    (mmap f M) $ i $ j = f (M $ i $ j).
Proof. intros. unfold mmap. auto. Qed.


(* ======================================================================= *)
(** ** Matrix map2 *)
Notation mmap2 f M N := (vmap2 (vmap2 f) M N).

Lemma mnth_mmap2 : forall {A B C} {r c} (M : mat A r c) (N : mat B r c)
                     (f : A -> B -> C) i j,
    (mmap2 f M N) $ i $ j = f (M $ i $ j) (N $ i $ j).
Proof. intros. unfold mmap2. auto. Qed.

Lemma mmap2_comm `{Commutative A Aadd} : forall {r c} (M N : mat A r c),
    mmap2 Aadd M N = mmap2 Aadd N M.
Proof. intros. apply meq_iff_mnth; intros. unfold mmap2. apply commutative. Qed.

Lemma mmap2_assoc `{Associative A Aadd} : forall {r c} (M N O : mat A r c),
    mmap2 Aadd (mmap2 Aadd M N) O = mmap2 Aadd M (mmap2 Aadd N O).
Proof. intros. apply meq_iff_mnth; intros. unfold mmap2. apply associative. Qed.


(* ======================================================================= *)
(** ** Get head or tail column *)
Section mheadc_mtailc.
  Context {A} {Azero : A}.

  (** Get head column *)
  Definition mheadc {r c} (M : @mat A r (S c)) : @vec A r := fun i => vhead (M$i).

  (** (mheadc M).i = M.i.0 *)
  Lemma vnth_mheadc : forall {r c} (M : @mat A r (S c)) i, (mheadc M) $ i = M $ i $ fin0.
  Proof. auto. Qed.

  
  (** Get tail column *)
  Definition mtailc {r c} (M : @mat A r (S c)) : @vec A r := fun i => vtail (M$i).

  (** (mtailc M).i = M.i.(n-1) *)
  Lemma vnth_mtailc : forall {r c} (M : @mat A r (S c)) i,
      (mtailc M) $ i = M $ i $ (nat2finS c).
  Proof. intros. auto. Qed.

End mheadc_mtailc.


(* ======================================================================= *)
(** ** Remove exact one column at head or tail *)
Section mremovecH_mremovecT.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  (** *** mremovecH *)
  
  (** Remove head column *)
  Definition mremovecH {r c} (M : @mat A r (S c)) : @mat A r c :=
    fun i => vremoveH (M $ i).
  
  (** (mremovecH M).i.j = M.i.(S j) *)
  Lemma mnth_mremovecH : forall {r c} (M : @mat A r (S c)) i j,
      (mremovecH M) $ i $ j = M $ i $ (fin2SuccRangeSucc j).
  Proof. intros. auto. Qed.

  
  (** *** mremovecT *)

  (** Remove tail column *)
  Definition mremovecT {r c} (M : @mat A r (S c)) : @mat A r c :=
    fun i => vremoveT (M $ i).
  
  (** (mremovecT M).i.j = M.i.j *)
  Lemma mnth_mremovecT : forall {r c} (M : @mat A r (S c)) i j,
      (mremovecT M) $ i $ j = M $ i $ (fin2SuccRange j).
  Proof. intros. auto. Qed.

End mremovecH_mremovecT.


(* ======================================================================= *)
(** ** Construct matrix from vector and matrix *)
Section mcons.
  Context {A} (Azero:A).

  (** Construct a matrix with a row vector and a matrix *)
  Definition mconsrH {r c} (a : @vec A c) (M : mat A r c) : mat A (S r) c :=
    vconsH a M.

  Lemma mnth_mconsrH_0 : forall {r c} (a : @vec A c) (M : mat A r c) j,
      (mconsrH a M) $ fin0 $ j = a $ j.
  Proof. intros. unfold mconsrH. rewrite vnth_vconsH_0; auto. Qed.

  Lemma mnth_mconsrH_gt0 :
    forall {r c} (a : @vec A c) (M : mat A r c) i j (H : 0 < fin2nat i),
      (mconsrH a M) $ i $ j = M $ (fin2PredRangePred i H) $ j.
  Proof.
    intros. unfold mconsrH. erewrite vnth_vconsH_gt0. f_equal.
  Qed.

  Lemma mconsrH_spec : forall {r c} (a : @vec A c) (M : mat A r c),
      let fa := v2f Azero a in
      let fM := m2f Azero M in
      let faM := m2f Azero (mconsrH a M) in
      (forall j, j < c -> faM 0 j = fa j) /\
        (forall i j, 0 < i < r -> j < c -> faM i j = fM (i - 1) j).
  Proof.
    intros. unfold fa,fM,faM. split; intros; auto.
    unfold mconsrH, m2f, v2f. f_equal.
    rewrite vconsH_spec_gt0; try lia.
    erewrite !nth_ff2f. f_equal. apply Fin_eq_iff. lia.
    Unshelve. lia. lia.
  Qed.

  
  (** Construct a matrix with a matrix and a row vector *)
  Definition mconsrT {r c} (M : mat A r c) (a : @vec A c) : mat A (S r) c :=
    vconsT M a.

  Lemma mnth_mconsrT_n : forall {r c} (M : mat A r c) (a : @vec A c) i j,
      i = nat2finS r -> (mconsrT M a) $ i $ j = a $ j.
  Proof.
    intros. rewrite H. unfold mconsrT. rewrite vnth_vconsT_n; auto.
    rewrite fin2nat_nat2finS; auto.
  Qed.

  Lemma mnth_mconsrT_lt :
    forall {r c} (M : mat A r c) (a : @vec A c) i j (H : fin2nat i < r),
      (mconsrT M a) $ i $ j = M $ (fin2PredRange i H) $ j.
  Proof.
    intros. unfold mconsrT. erewrite vnth_vconsT_lt. f_equal.
  Qed.

  
  (** Construct a matrix with a column vector and a matrix *)
  Definition mconscH {r c} (a : @vec A r) (M : mat A r c) : mat A r (S c) :=
    @vmap2 A (vec c) (vec (S c)) vconsH r a M.

  Lemma vnth_mconscH : forall {r c} (M : mat A (S r) c) (a : vec (S r)) (i : fin (S r)),
      (mconscH a M) $ i = vconsH (a $ i) (M $ i).
  Proof. intros. auto. Qed.
  
  Lemma mnth_mconscH_0 : forall {r c} (a : @vec A r) (M : mat A r c) i,
      (mconscH a M) $ i $ fin0 = a $ i.
  Proof.
    intros. unfold mconscH. rewrite vnth_vmap2. rewrite vnth_vconsH_0; auto.
  Qed.

  Lemma mnth_mconscH_gt0 :
    forall {r c} (M : mat A r c) (a : @vec A r) i j (H : 0 < fin2nat j),
      (mconscH a M) $ i $ j = M $ i $ (fin2PredRangePred j H).
  Proof.
    intros. unfold mconscH. rewrite vnth_vmap2. erewrite vnth_vconsH_gt0. f_equal.
  Qed.

  (** mconscH (mheadc M) (mremovecH M) = M *)
  Lemma mconscH_mheadc_mremovecH : forall {r c} (M : @mat A r (S c)),
      mconscH (mheadc M) (mremovecH M) = M.
  Proof.
    intros. apply meq_iff_mnth; intros i j. destruct (j ??= fin0) as [H|H].
    - subst. rewrite mnth_mconscH_0; auto.
    - apply fin2nat_neq0_imply_gt0 in H. rewrite mnth_mconscH_gt0 with (H:=H).
      rewrite mnth_mremovecH. f_equal. apply fin2SuccRangeSucc_fin2PredRangePred.
  Qed.

  (** mconscH (vconsT a x) (vconsT M b) = vconsT (mconscH a M) (vconsH x b) *)
  Lemma mconscH_vconsT_vconsT_eq_vconsT_mconscH_vconsH :
    forall {r c} (a : vec r) (x : A) (M : mat A r c) (b : vec c),
      mconscH (vconsT a x) (vconsT M b) = vconsT (mconscH a M) (vconsH x b).
  Proof with try apply fin2nat_nat2finS; auto.
    intros. apply meq_iff_mnth; intros.
    destruct (i ??= nat2finS r) as [Hi|Hi], (j ??= fin0) as [Hj|Hj]; subst.
    - rewrite mnth_mconscH_0.
      rewrite !vnth_vconsT_n...
    - apply fin2nat_neq0_imply_gt0 in Hj.
      rewrite mnth_mconscH_gt0 with (H:=Hj).
      rewrite !vnth_vconsT_n...
      rewrite vnth_vconsH_gt0 with (H:=Hj)...
    - apply nat2finS_neq_imply_lt in Hi.
      rewrite mnth_mconscH_0.
      rewrite !vnth_vconsT_lt with (H:=Hi).
      rewrite mnth_mconscH_0; auto.
    - apply nat2finS_neq_imply_lt in Hi.
      apply fin2nat_neq0_imply_gt0 in Hj.
      rewrite mnth_mconscH_gt0 with (H:=Hj).
      rewrite !vnth_vconsT_lt with (H:=Hi).
      rewrite mnth_mconscH_gt0 with (H:=Hj); auto.
  Qed.
  
  
  (** Construct a matrix with a matrix and a column vector *)
  Definition mconscT {r c} (M : mat A r c) (a : @vec A r) : mat A r (S c) :=
    @vmap2 (vec c) A (vec (S c)) vconsT r M a.
  
  Lemma mnth_mconscT_n : forall {r c} (M : mat A r c) (a : @vec A r) i j,
      j = nat2finS c -> (mconscT M a) $ i $ j = a $ i.
  Proof.
    intros. rewrite H. unfold mconscT. rewrite vnth_vmap2.
    rewrite vnth_vconsT_n; auto. rewrite fin2nat_nat2finS; auto.
  Qed.

  Lemma mnth_mconscT_lt :
    forall {r c} (M : mat A r c) (a : @vec A r) i j (H : fin2nat j < c),
      (mconscT M a) $ i $ j = M $ i $ (fin2PredRange j H).
  Proof.
    intros. unfold mconscT. rewrite vnth_vmap2. erewrite vnth_vconsT_lt. f_equal.
  Qed.

  Lemma vnth_mconscT : forall {r c} (M : mat A r c) (a : @vec A r) i,
      (mconscT M a) $ i = vconsT (M$i) (a$i).
  Proof.
    intros. apply veq_iff_vnth; intros j. destruct (j ??= nat2finS c).
    - subst. rewrite mnth_mconscT_n, vnth_vconsT_n; auto.
      apply fin2nat_nat2finS; auto.
    - rewrite mnth_mconscT_lt with (H:=nat2finS_neq_imply_lt j n).
      rewrite vnth_vconsT_lt with (H:=nat2finS_neq_imply_lt j n). auto.
  Qed.

  (** mconscT (mremovecT M) (mtailc M) = M *)
  Lemma mconsT_mremoveT_mtailc : forall {r c} (M : @mat A r (S c)),
      mconscT (mremovecT M) (mtailc M) = M.
  Proof.
    intros. apply meq_iff_mnth; intros i j. destruct (j ??= nat2finS c) as [H|H].
    - subst. rewrite mnth_mconscT_n; auto.
    - apply nat2finS_neq_imply_lt in H. rewrite mnth_mconscT_lt with (H:=H).
      rewrite mnth_mremovecT. f_equal. apply fin2SuccRange_fin2PredRange.
  Qed.

End mcons.

Section test.

  Let a : @vec nat 2 := l2v 9 [1;2].
  Let M : @mat nat 2 2 := l2m 9 [[3;4];[5;6]].
  (* Compute m2l (mconsrH a M). *)
  (* Compute m2l (mconsrT M a). *)
  (* Compute m2l (mconscH a M). *)
  (* Compute m2l (mconscT M a). *)

End test.


(* ======================================================================= *)
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
  Let M := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute @nat2finS 2 3. *)
  (* Compute m2l (mcshl 0 M (nat2finS 0)). *)
  (* Compute m2l (mcshl 0 M (nat2finS 1)). *)
  (* 移动次数最大是 c - 1 次，若需要更多，则可以多次进行 *)
  (* Compute m2l (mcshl 0 (mcshl 0 M (nat2finS 2)) (nat2finS 1)). *)
  
  (* Compute m2l (mcshr 0 M (nat2finS 1)). *)
  
  (* Compute m2l (mclsl M (nat2finS 1)). *)
  (* Compute m2l (mclsr M (nat2finS 1)). *)
End test.


(* ======================================================================= *)
(** ** matrix set row / column *)
Section mset.
  Context {A} (Azero : A).

  (** set row *)
  Definition msetr {r c} (M : mat A r c) (a : @vec A c) (i0 : fin r) : mat A r c :=
    fun i j => if i ??= i0 then a $ j else M $ i $ j.

  Lemma mnth_msetr_same : forall {r c} (M : mat A r c) (a : @vec A c) (i0 : fin r) i j,
      i = i0 -> (msetr M a i0) $ i $ j = a $ j.
  Proof. intros. unfold msetr. destruct (_??=_); auto. easy. Qed.

  Lemma mnth_msetr_diff : forall {r c} (M : mat A r c) (a : @vec A c) (i0 : fin r) i j,
      i <> i0 -> (msetr M a i0) $ i $ j = M $ i $ j.
  Proof. intros. unfold msetr. destruct (_??=_); auto. easy. Qed.

  (** set column *)
  Definition msetc {r c} (M : mat A r c) (a : @vec A r) (j0 : fin c) : mat A r c :=
    fun i j => if j ??= j0 then a $ i else M $ i $ j.

  Lemma mnth_msetc_same : forall {r c} (M : mat A r c) (a : @vec A r) (j0:fin c) i j,
      j = j0 -> (msetc M a j0) $ i $ j = a $ i.
  Proof. intros. unfold msetc. destruct (_??=_); auto. easy. Qed.

  Lemma mnth_msetc_diff : forall {r c} (M : mat A r c) (a : @vec A r) (j0:fin c) i j,
      j <> j0 -> (msetc M a j0) $ i $ j = M $ i $ j.
  Proof. intros. unfold msetc. destruct (_??=_); auto. easy. Qed.

End mset.


(* ======================================================================= *)
(** ** Diagonal matrix *)
Section mdiag.
  Context {A} (Azero:A).

  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (M : smat A n) : Prop :=
    forall i j, i <> j -> M $ i $ j = Azero.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (M : smat A n), mdiag M -> M\T = M.
  Proof.
    intros. unfold mdiag in H. apply meq_iff_mnth; intros i j.
    rewrite mnth_mtrans. destruct (i ??= j).
    subst; auto. rewrite !H; auto.
  Qed.

  (** Construct a diagonal matrix *)
  Definition mdiagMk {n} (a : @vec A n) : @smat A n :=
    fun i j => if i ??= j then a $ i else Azero.

  (** mdiagMk is correct *)
  Lemma mdiagMk_spec : forall {n} (a : @vec A n), mdiag (mdiagMk a).
  Proof.
    intros. hnf. intros. unfold mdiagMk. destruct (_??=_); auto. easy.
  Qed.

  (** (mdiagMk l)[i,i] = l[i] *)
  Lemma mnth_mdiagMk_same : forall {n} (a : @vec A n) i, (mdiagMk a) $ i $ i = a $ i.
  Proof. intros. unfold mdiagMk. destruct (_??=_); auto. easy. Qed.

  (** (mdiagMk l)[i,j] = 0 *)
  Lemma mnth_mdiagMk_diff : forall {n} (a : @vec A n) i j,
      i <> j -> (mdiagMk a) $ i $ j = Azero.
  Proof. intros. unfold mdiagMk. destruct (_??=_); auto. easy. Qed.

End mdiag.


(* ======================================================================= *)
(** ** Matrix Addition *)
Section madd.
  Context `{AMonoid}.
  Notation mat r c := (mat A r c).
  Infix "+" := Aadd : A_scope.
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation mat0 := (@mat0 _ Azero).
  
  Definition madd {r c} (M N : mat r c) : mat r c := mmap2 Aadd M N.
  Infix "+" := madd : mat_scope.
  
  (** (M+N)[i,j] = M[i,j] + N[i,j] *)
  Lemma mnth_madd : forall {r c} (M N : mat r c) i j,
      (M + N) $ i $ j = (M $ i $ j + N $ i $ j)%A.
  Proof. intros. auto. Qed.
  
  (** (M+N)[i] = M[i] + N[i] *)
  Lemma vnth_madd : forall {r c} (M N : mat r c) i,
      (M + N) $ i = (M $ i + N $ i)%V.
  Proof. intros. auto. Qed.

  Lemma cv2v_madd : forall {n} (a b : cvec A n),
      cv2v (a + b) = (cv2v a + cv2v b)%V.
  Proof. intros. apply veq_iff_vnth; intros. cbv. auto. Qed.

  Lemma madd_comm : forall {r c} (M N : mat r c), M + N = N + M.
  Proof. intros. apply mmap2_comm. Qed.
  
  Lemma madd_assoc : forall {r c} (M N O : mat r c),
      (M + N) + O = M + (N + O).
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

  (** (M + N) + O = (M + O) + N *)
  Lemma madd_perm : forall {r c} (M N O : mat r c), (M + N) + O = (M + O) + N.
  Proof. intros. rewrite !associative. f_equal. apply commutative. Qed.
  
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

  Example madd_monoid_example1 : forall r c (M N : mat r c),
      mat0 + M + N + mat0 = M + mat0 + N.
  Proof. monoid. Qed.
  

  (** (M + N)\T = M\T + N\T *)
  Lemma mtrans_madd : forall {r c} (M N : mat r c), (M + N)\T = M\T + N\T.
  Proof.
    intros. unfold madd. apply meq_iff_mnth; intros.
    rewrite ?mnth_mtrans, ?mnth_mmap2, ?mnth_mtrans. auto.
  Qed.
End madd.


(* ======================================================================= *)
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
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation mat0 := (@mat0 _ Azero).
  Notation madd := (@madd _ Aadd).
  Infix "+" := madd : mat_scope.
  
  
  (** *** Unit matrix *)
  Section mat1.
    Definition mat1 {n} : smat n :=
      fun i j => if i ??= j then Aone else Azero.
    
    (** mat1\T = mat1 *)
    Lemma mtrans_mat1 : forall {n : nat}, (@mat1 n)\T = mat1.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold mtrans,mat1.
      destruct (_??=_),(_??=_); auto; subst; easy.
    Qed.

    (** mat1[i,i] = 1 *)
    Lemma mnth_mat1_same : forall {n} i, (@mat1 n) $ i $ i = Aone.
    Proof. intros. unfold mat1. destruct (_??=_); easy. Qed.

    (** i <> j -> mat1[i,j] = 0 *)
    Lemma mnth_mat1_diff : forall {n} i j, i <> j -> @mat1 n $ i $ j = Azero.
    Proof. intros. unfold mat1. destruct (_??=_); easy. Qed.

    (** mat1 is diagonal matrix *)
    Lemma mat1_diag : forall {n : nat}, mdiag Azero (@mat1 n).
    Proof. intros. hnf. intros. rewrite mnth_mat1_diff; auto. Qed.
  End mat1.


  (** *** Matrix Trace *)
  Section mtrace.
    Definition mtrace {n : nat} (M : smat n) : A := vsum (fun i => M $ i $ i).
    Notation "'tr' M" := (mtrace M).

    (** tr(M\T) = tr(M) *)
    Lemma mtrace_mtrans : forall {n} (M : smat n), tr (M\T) = tr M.
    Proof. intros. apply vsum_eq; intros. apply mnth_mtrans. Qed.

    (** tr(M + N) = tr(M) + tr(N) *)
    Lemma mtrace_madd : forall {n} (M N : smat n), tr (M + N) = (tr M + tr N)%A.
    Proof.
      intros. unfold madd, mtrace. apply vsum_add; intros. rewrite mnth_mmap2. auto.
    Qed.
  End mtrace.
  Notation "'tr' M" := (mtrace M).


  (** *** Matrix Opposition *)
  Section mopp.
    Notation vopp := (@vopp _ Aopp).
    Notation "- v" := (vopp v) : vec_scope.
    
    Definition mopp {r c} (M : mat r c) : mat r c := mmap Aopp M.
    Notation "- M" := (mopp M) : mat_scope.
    
    (** (- M)[i] = - M[i] *)
    Lemma vnth_mopp : forall {r c} (M : mat r c) i, (- M) $ i = (- (M $ i))%V.
    Proof. intros. unfold mopp,vopp. rewrite !vnth_vmap. auto. Qed.
    
    (** (- M)[i, j] = - M[i, j] *)
    Lemma mnth_mopp : forall {r c} (M : mat r c) i j, (- M) $ i $ j = (- M $ i $ j)%A.
    Proof. intros. unfold mopp. rewrite !vnth_vmap. auto. Qed.
    
    Lemma madd_opp_l : forall {r c} (M : mat r c), (- M) + M = mat0.
    Proof.
      intros. unfold madd,mopp,mat0,mmap2,mmap. apply meq_iff_mnth; intros. group.
    Qed.
    
    Lemma madd_opp_r : forall {r c} (M : mat r c), M + (- M) = mat0.
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

    Example madd_agroup_example1 : forall r c (M N : mat r c), mat0 + M + (- N) + N = M.
    Proof.
      intros.
      (* rewrite associative. *)
      (* rewrite inverseLeft. *)
      (* rewrite identityRight. *)
      (* rewrite identityLeft. *)
      group.
    Qed.

    (* Now, we ca use group theory on <madd, mat0, mopp, msub> *)
    
    (** - (- M) = M *)
    Lemma mopp_mopp : forall {r c} (M : mat r c), - (- M) = M.
    Proof. intros. apply group_opp_opp. Qed.

    (** - M = N <-> M = - N *)
    Lemma mopp_exchange : forall {r c} (M N : mat r c), - M = N <-> M = - N.
    Proof. intros. split; intros; subst; rewrite group_opp_opp; auto. Qed.

    (** - (mat0) = mat0 *)
    Lemma mopp_mat0 : forall {r c:nat}, - (@Matrix.mat0 _ Azero r c) = mat0.
    Proof. intros. apply group_opp_0. Qed.

    (** - (m1 + m2) = (-m1) + (-m2) *)
    Lemma mopp_madd : forall {r c : nat} (M N : mat r c), - (M + N) = (- M) + (- N).
    Proof. intros. rewrite group_opp_distr. apply commutative. Qed.

    (** (- M)\T = - (M\T) *)
    Lemma mtrans_mopp : forall {r c} (M : mat r c), (- M)\T = - (M\T).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite ?mnth_mtrans, ? mnth_mopp, ?mnth_mtrans. auto.
    Qed.

    (** tr(- M) = - (tr(m)) *)
    Lemma mtrace_mopp : forall {n} (M : smat n), tr (- M) = (- (tr M))%A.
    Proof.
      intros. unfold mopp, mtrace. apply vsum_opp; intros. rewrite !vnth_vmap; auto.
    Qed.
  End mopp.
  Notation "- M" := (mopp M) : mat_scope.
  
  
  (** *** Matrix Subtraction *)
  Section msub.
    Definition msub {r c} (M N : mat r c) : mat r c := M + (- N).
    Infix "-" := msub : mat_scope.

    (** M - N = - (N - M) *)
    Lemma msub_comm : forall {r c} (M N : mat r c), M - N = - (N - M).
    Proof.
      intros. unfold msub. rewrite group_opp_distr. rewrite group_opp_opp; auto.
    Qed.

    (** (M - N) - O = M - (N + O) *)
    Lemma msub_assoc : forall {r c} (M N O : mat r c),
        (M - N) - O = M - (N + O).
    Proof. intros. unfold msub. rewrite group_opp_distr. asemigroup. Qed.

    (** (M + N) - O = M + (N - O) *)
    Lemma msub_assoc1 : forall {r c} (M N O : mat r c), (M + N) - O = M + (N - O).
    Proof. intros. unfold msub. asemigroup. Qed.

    (** (M - N) - O = M - (O - N) *)
    Lemma msub_assoc2 : forall {r c} (M N O : mat r c), (M - N) - O = (M - O) - N.
    Proof. intros. unfold msub. asemigroup. Qed.
    
    (** 0 - M = - M *)
    Lemma msub_0_l : forall {r c} (M : mat r c), mat0 - M = - M.
    Proof. intros. unfold msub. monoid. Qed.
    
    (** M - 0 = M *)
    Lemma msub_0_r : forall {r c} (M : mat r c), M - mat0 = M.
    Proof. intros. unfold msub. rewrite group_opp_0 at 1. monoid. Qed.
    
    (** M - M = 0 *)
    Lemma msub_self : forall {r c} (M : mat r c), M - M = mat0.
    Proof. intros. unfold msub. group. Qed.

    (** (M - N)\T = M\T - N\T *)
    Lemma mtrans_msub : forall {r c} (M N : mat r c), (M - N)\T = M\T - N\T.
    Proof. intros. unfold msub. rewrite mtrans_madd, mtrans_mopp; auto. Qed.

    (** tr(M - N) = tr(M) - tr(N) *)
    Lemma mtrace_msub : forall {n} (M N : smat n), tr (M - N) = (tr M - tr N)%A.
    Proof. intros. unfold msub. rewrite mtrace_madd, mtrace_mopp; auto. Qed.
  End msub.
  Infix "-" := msub : mat_scope.

  
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation vcmul := (@vcmul _ Amul).
  Infix "\.*" := vcmul : vec_scope.
  Notation vdot v1 v2 := (@vdot _ Aadd Azero Amul _ v1 v2).
  Notation "< v1 , v2 >" := (vdot v1 v2) : vec_scope.

  
  (** *** Matrix Scalar Multiplication *)
  Section mcmul.
    Definition mcmul {r c : nat} (a : A) (M : mat r c) : mat r c := mmap (Amul a) M.
    Infix "\.*" := mcmul : mat_scope.

    (** (a * M)[i] = a * M[i] *)
    Lemma vnth_mcmul : forall {r c} (M : mat r c) a i,
        (a \.* M) $ i = (a \.* (M $ i))%V.
    Proof. intros. auto. Qed.

    (** (a * M)[i,j] = a * M[i,j] *)
    Lemma mnth_mcmul : forall {r c} (M : mat r c) a i j,
        (a \.* M) $ i $ j = a * (M $ i $ j).
    Proof. intros. unfold mcmul. rewrite !vnth_vmap. auto. Qed.

    Lemma cv2v_mcmul : forall {n} (x : A) (a : cvec A n),
        cv2v (x \.* a) = (x \.* (cv2v a))%V.
    Proof. intros. apply veq_iff_vnth; intros. cbv. auto. Qed.

    (** row (a * M) i = a * row M i *)
    Lemma mrow_mcmul : forall {r c} (M : mat r c) a i, (a \.* M) $ i = vcmul a (M $ i).
    Proof. intros. unfold mcmul,vcmul,mmap. auto. Qed.

    (** col (a * M) i = a * col M i *)
    Lemma mcol_mcmul : forall {r c} (M : mat r c) a j,
        (fun i => (a \.* M) $ i $ j) = vcmul a (fun i => M $ i $ j).
    Proof. intros. unfold mcmul,vcmul,mmap. auto. Qed.

    (** a * (b * M) = (a * b) * M *)
    Lemma mcmul_assoc : forall {r c} (M : mat r c) a b,
        a \.* (b \.* M) = (a * b)%A \.* M.
    Proof. intros. apply meq_iff_mnth; intros. rewrite !mnth_mcmul. monoid. Qed.
    
    (** a * (b * M) = b * (a * M) *)
    Lemma mcmul_perm : forall {r c} (M : mat r c) a b,
        a \.* (b \.* M) = b \.* (a \.* M).
    Proof. intros. rewrite !mcmul_assoc. f_equal. asemigroup. Qed.

    (** a * (M + N) = (a * M) + (a * N) *)
    Lemma mcmul_madd_distr : forall {r c} a (M N : mat r c),
        a \.* (M + N) = (a \.* M) + (a \.* N).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite !mnth_mcmul, !mnth_madd, !mnth_mcmul. ring.
    Qed.
    
    (** (a + b) * M = (a * M) + (b * M) *)
    Lemma mcmul_add_distr : forall {r c} a b (M : mat r c),
        (a + b)%A \.* M = (a \.* M) + (b \.* M).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite !mnth_mcmul, !mnth_madd, !mnth_mcmul. ring.
    Qed.

    (* 0 \.* M = mat0 *)
    Lemma mcmul_0_l : forall {r c} (M : mat r c), Azero \.* M = mat0.
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite !mnth_mcmul, !mnth_mat0. ring.
    Qed.

    (** a \.* mat0 = mat0 *)
    Lemma mcmul_0_r : forall {r c} a, a \.* (@Matrix.mat0 _ Azero r c) = mat0.
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite !mnth_mcmul, !mnth_mat0. ring.
    Qed.
    
    (** 1 \.* M = M *)
    Lemma mcmul_1_l : forall {r c} (M : mat r c), Aone \.* M = M.
    Proof. intros. apply meq_iff_mnth; intros. rewrite !mnth_mcmul. ring. Qed.

    (** a \.* mat1 = mdiag([a,a,...]) *)
    Lemma mcmul_1_r : forall {n} a, a \.* (@mat1 n) = mdiagMk Azero (vrepeat a).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_mcmul.
      destruct (i ??= j).
      - subst. rewrite mnth_mdiagMk_same.
        rewrite mnth_mat1_same, vnth_vrepeat. ring.
      - rewrite mnth_mat1_diff, mnth_mdiagMk_diff; auto. ring.
    Qed.
    
    (* (-a) * M = - (a * M) *)
    Lemma mcmul_opp : forall {r c} a (M : mat r c), (- a)%A \.* M = - (a \.* M).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_mopp,!mnth_mcmul. ring.
    Qed.
    
    (* a * (- M) = - (a * M) *)
    Lemma mcmul_mopp : forall {r c} a (M : mat r c), a \.* (- M) = - (a \.* M).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite !mnth_mopp,!mnth_mcmul,mnth_mopp. ring.
    Qed.
    
    (* (-a) * (- M) = a * M *)
    Lemma mcmul_opp_mopp : forall {r c} a (M : mat r c),
        (- a)%A \.* (- M) = a \.* M.
    Proof. intros. rewrite mcmul_mopp, mcmul_opp. apply group_opp_opp. Qed.

    (** a \.* (M - N) = (a \.* M) - (a \.* N) *)
    Lemma mcmul_msub : forall {r c} a (M N : mat r c),
        a \.* (M - N) = (a \.* M) - (a \.* N).
    Proof.
      intros. unfold msub. rewrite mcmul_madd_distr. rewrite mcmul_mopp. auto.
    Qed.

    (** (a \.* M)\T = a \.* (m\T) *)
    Lemma mtrans_mcmul : forall {r c} (a : A) (M : mat r c), (a \.* M)\T = a \.* (M\T).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite mnth_mtrans, !mnth_mcmul, mnth_mtrans. auto.
    Qed.

    (** tr (a \.* M) = a * tr (m) *)
    Lemma mtrace_mcmul : forall {n} (a : A) (M : smat n), tr (a \.* M) = (a * tr M)%A.
    Proof.
      intros. unfold mcmul, mtrace. apply vsum_cmul; intros.
      rewrite mnth_mmap. auto.
    Qed.
  End mcmul.
  Infix "\.*" := mcmul : mat_scope.

  
  (** *** Matrix Multiplication *)
  Section mmul.
    (* structural-style *)
    Definition mmul_old {r c t : nat} (M : mat r c) (N : mat c t) : mat r t :=
      vmap (fun v1 => vmap (fun v2 => <v1,v2>) (mtrans N)) M.
    
    (* functional-style *)
    Definition mmul {r c t : nat} (M : mat r c) (N : mat c t) : mat r t :=
      fun i j => <M $ i, (fun k => N $ k $ j)>.
    Infix "*" := mmul : mat_scope.

    (** (M * N)[i,j] = <row M i, col N j> *)
    Lemma mnth_mmul : forall {r c t} (M : mat r c) (N : mat c t) i j,
        (M * N) $ i $ j = <M $ i, (fun k => N $ k $ j)>.
    Proof. intros. auto. Qed.

    (** (M * N)[i] = <row M i, col N j> *)
    Lemma vnth_mmul : forall {r c t} (M : mat r c) (N : mat c t) i,
        (M * N) $ i = vmap (fun v => <M $ i,v>) (N\T).
    Proof. intros. auto. Qed.

    (** N is cvec -> M * N = fun i => (vdot N) (M $ i) *)
    Lemma mmul_cvec : forall {r c} (M : mat r c) (N : cvec A c),
        M * N = fun i j => <cv2v N, M $ i>.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold cv2v.
      unfold mmul. rewrite vdot_comm. rewrite (fin1_uniq j). auto.
    Qed.

    (** M is rvec -> M * N = fun i j => (vdot M) (mcol N j) *)
    Lemma mmul_rvec : forall {r c} (M : rvec A r) (N : mat r c),
        M * N = fun i j => <rv2v M, mcol N j>.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold rv2v, mcol.
      unfold mmul. rewrite (fin1_uniq i). auto.
    Qed.

    (** <row(M,i), col(N,j)> = [M * N].ij *)
    Lemma vdot_row_col : forall {r c s} (M : mat r c) (N : mat c s) i j,
        <mrow M i, mcol N j> = (M * N) $ i $ j.
    Proof. intros. apply vsum_eq; intros; auto. Qed.

    (** <col(M,i), col(N,j)> = (M\T * N)[i,j] *)
    Lemma vdot_col_col : forall {n} (M N : smat n) i j,
        <mcol M i, mcol N j> = (M\T * N) $ i $ j.
    Proof. intros. apply vsum_eq. intros; auto. Qed.

    (** <row(M,i), row(N,j)> = (M * N\T)[i,j] *)
    Lemma vdot_row_row : forall {n} (M N : smat n) i j,
        <mrow M i, mrow N j> = (M * N\T) $ i $ j.
    Proof. intros. apply vsum_eq. intros; auto. Qed.

    (** <a, b> = (a\T * b).11 *)
    Lemma vdot_eq_mmul : forall {n} (a b : vec n), <a, b> = (v2rv a * v2cv b).11.
    Proof. intros. apply vsum_eq; intros; auto. Qed.

    (** (M * N) * O = M * (N * O) *)
    Lemma mmul_assoc : forall {m n r s} (M : mat m n) (N : mat n r) (O : mat r s),
        (M * N) * O = M * (N * O).
    Proof. intros. unfold mmul. apply meq_iff_mnth; intros. apply vdot_assoc. Qed.

    (** M * (N + O) = M * N + M * O *)
    Lemma mmul_madd_distr_l : forall {r c t} (M : mat r c) (N O : mat c t),
        M * (N + O) = (M * N) + (M * O).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_madd, !mnth_mmul.
      unfold vdot. apply vsum_add; intros k. rewrite !vnth_vmap2, mnth_madd. ring.
    Qed.
    
    (** (M + N) * O = M * O + N * O *)
    Lemma mmul_madd_distr_r : forall {r c t} (M N : mat r c) (O : mat c t),
        (M + N) * O = (M * O) + (N * O).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_madd,!mnth_mmul.
      unfold vdot. apply vsum_add; intros k. rewrite !vnth_vmap2, mnth_madd. ring.
    Qed.

    (** (- M) * N = - (M * N) *)
    Lemma mmul_mopp_l : forall {r c t} (M : mat r c) (N : mat c t),
        (- M) * N = - (M * N).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_mopp, !mnth_mmul.
      unfold vdot. apply vsum_opp; intros k. rewrite !vnth_vmap2, mnth_mopp. ring.
    Qed.

    (** M * (- N) = - (M * N) *)
    Lemma mmul_mopp_r : forall {r c t} (M : mat r c) (N : mat c t),
        M * (- N) = - (M * N).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_mopp, !mnth_mmul.
      unfold vdot. apply vsum_opp; intros k. rewrite !vnth_vmap2, mnth_mopp. ring.
    Qed.

    (** M * (N - O) = M * N - M * O *)
    Lemma mmul_msub_distr_l : forall {r c t} (M : mat r c) (N O : mat c t),
        M * (N - O) = (M * N) - (M * O).
    Proof.
      intros. unfold msub. rewrite mmul_madd_distr_l. rewrite mmul_mopp_r. auto.
    Qed.
    
    (** (M - N) * O = M * O - N * O *)
    Lemma mmul_msub_distr_r : forall {r c t} (M N : mat r c) (O : mat c t),
        (M - N) * O = (M * O) - (N * O).
    Proof.
      intros. unfold msub. rewrite mmul_madd_distr_r. rewrite mmul_mopp_l. auto.
    Qed.
    
    (** 0 * M = 0 *)
    Lemma mmul_0_l : forall {r c t} (M : mat c t), mat0 * M = @Matrix.mat0 _ Azero r t.
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite !mnth_mmul, mnth_mat0.
      rewrite mrow_mat0. apply vdot_0_l.
    Qed.
    
    (** M * 0 = 0 *)
    Lemma mmul_0_r : forall {r c t} (M : mat r c), M * mat0 = @Matrix.mat0 _ Azero r t.
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite !mnth_mmul, mnth_mat0.
      rewrite mcol_mat0. apply vdot_0_r.
    Qed.
    
    (** 1 * M = M *)
    Lemma mmul_1_l : forall {r c} (M : mat r c), mat1 * M = M.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold mmul,vdot,mat1,vmap2,vsum.
      apply fseqsum_unique with (i:=i).
      - destruct (_??=_); subst. monoid. easy.
      - intros. destruct (_??=_); subst. easy. ring.
    Qed.
    
    (** M * 1 = M *)
    Lemma mmul_1_r : forall {r c} (M : mat r c), M * mat1 = M.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold mmul,vdot,mat1,vmap2,vsum.
      apply fseqsum_unique with (i:=j).
      - destruct (_??=_); subst. monoid. easy.
      - intros. destruct (_??=_); subst. easy. ring.
    Qed.

    (** (a \.* M) * N = a \.* (M * N) *)
    Lemma mmul_mcmul_l : forall {r c s} (a : A) (M : mat r c) (N : mat c s), 
        (a \.* M) * N = a \.* (M * N).
    Proof.
      intros. apply meq_iff_mnth; intros.
      repeat rewrite ?mnth_mmul, ?mnth_mcmul.
      rewrite mrow_mcmul. rewrite vdot_vcmul_l. auto.
    Qed.
    
    (** M * (a \.* N) = a \.* (M * N) *)
    Lemma mmul_mcmul_r : forall {r c s} (a : A) (M : mat r c) (N : mat c s), 
        M * (a \.* N) = a \.* (M * N).
    Proof.
      intros. apply meq_iff_mnth; intros.
      repeat rewrite ?mnth_mmul, ?mnth_mcmul.
      rewrite mcol_mcmul. rewrite vdot_vcmul_r. auto.
    Qed.

    (** (M * N)\T = N\T * M\T *)
    Lemma mtrans_mmul : forall {r c s} (M : mat r c) (N : mat c s),
        (M * N)\T = N\T * M\T.
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite !mnth_mtrans,!mnth_mmul. rewrite vdot_comm. f_equal.
    Qed.

    (** tr (M * N) = tr (N * M) *)
    Lemma mtrace_mmul : forall {r c} (M : mat r c) (N : mat c r),
        tr (M * N) = tr (N * M).
    Proof.
      (* from: https://en.wikipedia.org/wiki/Trace_(linear_algebra)
       tr(A*B) = Σ(A*B)_{ii}
       = ΣΣ(A_{ij} B_{ji}) = ΣΣ(B_{ji} A_{ij}) 
       = Σ(BA)_{jj} = tr(B*A) *)
      intros. unfold mtrace. unfold mmul,vdot,vmap2,vsum.
      rewrite fseqsum_fseqsum_exchg.
      apply fseqsum_eq; intros. apply fseqsum_eq; intros. ring.
    Qed.

    (* tr(MNOP) = tr(NOPM) = tr(OPMN) = tr(PMNO) *)
    Lemma mtrace_cyclic4_NOPM :
      forall {r c s t} (M : mat r c) (N : mat c s) (O : mat s t) (P : mat t r),
        tr(M * N * O * P) = tr(N * O * P * M).
    Proof.
      intros. replace (M * N * O * P) with (M * (N * O * P)). apply mtrace_mmul.
      rewrite <- !mmul_assoc. auto.
    Qed.
    
    Lemma mtrace_cyclic4_OPMN :
      forall {r c s t} (M : mat r c) (N : mat c s) (O : mat s t) (P : mat t r),
        tr(M * N * O * P) = tr(O * P * M * N).
    Proof. intros. do 2 rewrite mtrace_cyclic4_NOPM. auto. Qed.
    
    Lemma mtrace_cyclic4_PMNO :
      forall {r c s t} (M : mat r c) (N : mat c s) (O : mat s t) (P : mat t r),
        tr(M * N * O * P) = tr(P * M * N * O).
    Proof. intros. do 3 rewrite mtrace_cyclic4_NOPM. auto. Qed.

    (* tr(MNO) = tr(NOM) = tr(OMN) *)
    Lemma mtrace_cyclic3_NOM : forall {n} (M N O : smat n), tr(M * N * O) = tr(N * O * M).
    Proof.
      (* tr(MNO)=tr((MNO)\T))=tr((NO)\T M\T)=tr(M\T (NO)\T)=tr(NOM) *)
      intros. rewrite <- mtrace_mtrans. rewrite mmul_assoc. rewrite mtrans_mmul.
      rewrite mtrace_mmul. rewrite <- mtrans_mmul. apply mtrace_mtrans.
    Qed.

    Lemma mtrace_cyclic3_OMN : forall {n} (M N O : smat n), tr(M * N * O) = tr(O * M * N).
    Proof.
      (* tr(MNO)=tr((MNO)\T))=tr(O\T (MN)\T)=tr((MN)\T O\T)=tr(OMN) *)
      intros. rewrite <- mtrace_mtrans. rewrite mtrans_mmul. rewrite mtrace_mmul.
      rewrite <- mtrans_mmul. rewrite mtrace_mtrans. rewrite mmul_assoc. auto.
    Qed.
  End mmul.
  Infix "*" := mmul : mat_scope.
  
  (** *** Matrix multiply vector (treat vector as column vector) *)
  Section mmulv.
    Open Scope vec_scope.
    
    Notation vec := (@vec A).
    Notation vzero := (vzero Azero).
    Notation vopp := (@vopp _ Aopp).
    Notation "- a" := (vopp a) : vec_scope.
    Notation vsub := (@vsub _ Aadd Aopp).
    Infix "-" := vsub : vec_scope.
   
    Definition mmulv {r c : nat} (M : mat r c) (a : vec c) : vec r :=
      fun i => <M $ i, a>.
    Infix "*" := mmulv : vec_scope.

    (** (M * a)[i] = <row M i, a> *)
    Lemma vnth_mmulv : forall {r c} (M : mat r c) (a : vec c) i,
        (M * a) $ i = <M $ i, a>.
    Proof. intros. auto. Qed.

    (** (M * N) * a = M * (N * a) *)
    Lemma mmulv_assoc : forall {m n r} (M : mat m n) (N : mat n r) (a : vec r),
        (M * N)%M * a = M * (N * a).
    Proof. intros. unfold mmulv. apply veq_iff_vnth; intros. apply vdot_assoc. Qed.

    (** M * (a + b) = M * a + M * b *)
    Lemma mmulv_vadd : forall {r c} (M : mat r c) (a b : vec c),
        M * (a + b) = (M * a) + (M * b).
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite vnth_vadd, vnth_mmulv.
      unfold vdot. apply vsum_add; intros k. rewrite !vnth_vmap2. ring.
    Qed.
    
    (** (M + N) * a = M * a + N * a *)
    Lemma mmulv_madd : forall {r c} (M N : mat r c) (a : vec c),
        (M + N)%M * a = (M * a) + (N * a).
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite vnth_vadd, vnth_mmulv.
      unfold vdot. apply vsum_add; intros k. rewrite !vnth_vmap2, mnth_madd. ring.
    Qed.

    (** (- M) * a = - (M * a) *)
    Lemma mmulv_mopp : forall {r c} (M : mat r c) (a : vec c), (- M)%M * a = - (M * a).
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite ?vnth_vopp, ?vnth_mmulv.
      rewrite vnth_mopp. rewrite vdot_vopp_l. auto.
    Qed.

    (** M * (- a) = - (M * a) *)
    Lemma mmulv_vopp : forall {r c} (M : mat r c) (a : vec c), M * (- a) = - (M * a).
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite ?vnth_vopp, ?vnth_mmulv.
      rewrite vdot_vopp_r. auto.
    Qed.

    (** M * (a - b) = M * a - M * b *)
    Lemma mmulv_vsub : forall {r c} (M : mat r c) (a b : vec c),
        M * (a - b) = (M * a) - (M * b).
    Proof.
      intros. unfold vsub. rewrite mmulv_vadd. rewrite mmulv_vopp. auto.
    Qed.
    
    (** (M - N) * a = M * a - N * a *)
    Lemma mmulv_msub : forall {r c} (M N : mat r c) (a : vec c),
        (M - N)%M * a = (M * a) - (N * a).
    Proof.
      intros. unfold msub. rewrite mmulv_madd. rewrite mmulv_mopp. auto.
    Qed.
    
    (** 0 * a = 0 *)
    Lemma mmulv_0_l : forall {r c} (a : vec c), (@mat0 r c) * a = vzero.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite !vnth_mmulv, vnth_vzero.
      apply vdot_0_l.
    Qed.
    
    (** M * 0 = 0 *)
    Lemma mmulv_0_r : forall {r c} (M : mat r c), M * vzero = vzero.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite !vnth_mmulv, vnth_vzero.
      apply vdot_0_r.
    Qed.
    
    (** 1 * a = a *)
    Lemma mmulv_1_l : forall {n} (a : vec n), mat1 * a = a.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite vnth_mmulv.
      apply vsum_unique with (i:=i).
      - rewrite vnth_vmap2. rewrite mnth_mat1_same. monoid.
      - intros. rewrite vnth_vmap2. rewrite mnth_mat1_diff; auto. ring.
    Qed.

    (** (x .* M) .* a = x .* (M * a) *)
    Lemma mmulv_mcmul : forall {r c} (x : A) (M : mat r c) (a : vec c), 
        (x \.* M)%M * a = x \.* (M * a).
    Proof.
      intros. apply veq_iff_vnth; intros.
      repeat rewrite ?vnth_mmulv, ?vnth_vcmul, ?vnth_mcmul.
      rewrite vdot_vcmul_l. auto.
    Qed.
    
    (** M * (x .* v) = x .* (M * a) *)
    Lemma mmulv_vcmul : forall {r c} (x : A) (M : mat r c) (a : vec c), 
        M * (x \.* a) = x \.* (M * a).
    Proof.
      intros. apply veq_iff_vnth; intros.
      repeat rewrite ?vnth_mmulv, ?vnth_vcmul, ?vnth_mcmul.
      rewrite vdot_vcmul_r. auto.
    Qed.

    (** <a, b> = (a\T * b).1 *)
    Lemma vdot_eq_mmulv : forall {n} (a b : vec n), <a, b> = (v2rv a * b).1.
    Proof. intros. apply vsum_eq; intros; auto. Qed.

    (** v2cv (M * a) = M * v2cv a *)
    Lemma v2cv_mmulv : forall {r c} (M : mat r c) (a : vec c),
        v2cv (M * a) = (M * v2cv a)%M.
    Proof. intros. auto. Qed.

    (** v2rv (M * a) = (v2rv a) * M\T *)
    Lemma v2rv_mmulv : forall {r c} (M : mat r c) (a : vec c),
        v2rv (M * a) = (v2rv a * M\T)%M.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold v2rv.
      rewrite vnth_mmulv. rewrite mnth_mmul. rewrite vdot_comm. auto.
    Qed.
    
  End mmulv.
  Infix "*" := mmulv : vec_scope.
    
  
  (** *** Skew-symmetric matrix *)
  Section skew.
    
    (** Given matrix is skew-symmetric matrices *)
    Definition skewP {n} (M : smat n) : Prop := - M = M\T.

  End skew.
  

  Context {ADec : Dec (@eq A)}.

  (** *** Properties when equipped with `Dec` *)
  Section with_Dec.
    
    (** (M <> 0 /\ N <> 0 /\ x .* M = N) -> x <> 0 *)
    Lemma mcmul_eq_imply_not_x0 : forall {r c} (M N : mat r c) x,
        M <> mat0 -> N <> mat0 -> x \.* M = N -> x <> Azero.
    Proof.
      intros. destruct (Aeqdec x Azero); auto. exfalso. subst.
      rewrite mcmul_0_l in H1. easy.
    Qed.
  End with_Dec.

  
  (** Properties below, need a field structure *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.

  
  (** *** Properties when equipped with `Field` *)
  Section with_Field.
  
    (** x * M = 0 -> (x = 0) \/ (M = 0) *)
    Lemma mcmul_eq0_imply_x0_or_m0 : forall {r c} (M : mat r c) x,
        x \.* M = mat0 -> (x = Azero)%A \/ (M = mat0).
    Proof.
      intros. destruct (Aeqdec x Azero); auto. right.
      apply meq_iff_mnth; intros. rewrite meq_iff_mnth in H0. specialize (H0 i j).
      cbv in H0. cbv. apply field_mul_eq0_iff in H0. tauto.
    Qed.

    (** (M <> 0 /\ x * M = 0) -> M = 0 *)
    Lemma mcmul_mnonzero_eq0_imply_x0 : forall {r c} (M : mat r c) x,
        M <> mat0 -> x \.* M = mat0 -> (x = Azero)%A.
    Proof. intros. apply mcmul_eq0_imply_x0_or_m0 in H1; auto. tauto. Qed.

    (** x * M = M -> x = 1 \/ M = 0 *)
    Lemma mcmul_same_imply_x1_or_m0 : forall {r c} x (M : mat r c),
        x \.* M = M -> (x = Aone)%A \/ (M = mat0).
    Proof.
      intros. destruct (Aeqdec x Aone); auto. right.
      apply meq_iff_mnth; intros. rewrite meq_iff_mnth in H0. specialize (H0 i j).
      cbv in H0. cbv. apply field_mul_eq_imply_a1_or_b0 in H0; auto. tauto.
    Qed.
  End with_Field.

End malg.

Section test.
  Let M0 := @l2m _ 9 2 2 [].
  Let M := @l2m _ 9 2 2 [[1;2];[3;4]].
  Let N := @l2m _ 9 2 2 [[1];[3;4]].
  Let O := @l2m _ 9 2 2 [[1;2];[3]].
  Let M4 := @l2m _ 9 2 2 [[1;2;3];[3;4]].
  Let M5 := @l2m _ 9 2 2 [[1;2];[3;4;5]].
  (* Compute m2l M0. *)
  (* Compute m2l M. *)
  (* Compute m2l N. *)
  (* Compute m2l O. *)
  (* Compute m2l M4. *)
  (* Compute m2l M5. *)
End test.


(* ======================================================================= *)
(** ** Elementary Row Transform *)

Section RowTrans.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "+" := (@madd _ Aadd _ _) : mat_scope.
  Notation mat1 := (@mat1 _ 0 1 _).
  Infix "*" := (@mmul _ Aadd 0 Amul _ _ _) : mat_scope.

  (** *** 单元素矩阵 *)
  
  (** 在 (x,y) 是 a 的单元素阵 *)
  Definition matOneElem {n} (x y : fin n) (a : A) : smat A n :=
    fun i j => if i ??= x then (if j ??= y then a else 0) else 0.


  (** *** 行倍乘矩阵 *)
  
  (** 行倍乘矩阵
      作用：E(x,c) * M 的结果是 M 的第 x 行乘以 c 倍
      形式：第 (x,x) 的元素是 c, 其余是单位阵 *)
  Definition matRowScale {n} (x : fin n) (c : A) : smat A n :=
    fun (i j : fin n) => if i ??= j then (if i ??= x then c else 1) else 0.

  (** 行倍乘：矩阵 M 的第 x 行乘以 c 倍 *)
  Definition mrowScale {n} (x : fin n) (c : A) (M : smat A n) : smat A n :=
    fun i j => if i ??= x then (c * M i j)%A else M i j.

  Lemma mrowScale_eq : forall {n} (x : fin n) (c : A) (M : smat A n),
      mrowScale x c M = (matRowScale x c) * M.
  Proof.
    intros. unfold mrowScale, matRowScale. apply meq_iff_mnth; intros.
    rewrite mnth_mmul. symmetry. elim_fin_eq.
    - apply vsum_unique with (i := x); intros; rewrite vnth_vmap2; elim_fin_eq.
    - apply vsum_unique with (i := i); intros; rewrite vnth_vmap2; elim_fin_eq.
  Qed.


  (** *** 行倍加矩阵 *)
  
  (** 行倍加矩阵
      作用：E(x,y,c) * M 的结果是 M 的第 y 行的 c 倍加到第 x 行
      形式：单位阵 + 第 (x,y) 的元素是 c *)
  Definition matRowAdd {n} (x y : fin n) (c : A) : smat A n :=
    mat1 + matOneElem x y c.

  (** 行倍加：矩阵 M 的第 y 行的 c 倍加到第 x 行 *)
  Definition mrowAdd {n} (x y : fin n) (c : A) (M : smat A n) : smat A n :=
    fun i j => if i ??= x then (M i j + c * M y j)%A else M i j.

  Lemma mnth_mrowAdd : forall {n} (x y : fin n) (c : A) (M : smat A n),
      mrowAdd x y c M = (matRowAdd x y c) * M.
  Proof.
    intros. unfold mrowAdd, matRowAdd, matOneElem. apply meq_iff_mnth; intros.
    rewrite mnth_mmul. symmetry. elim_fin_eq.
    - rewrite vnth_madd. rewrite vdot_vadd_l. f_equal.
      + apply vsum_unique with (i := x); intros; rewrite vnth_vmap2; elim_fin_eq.
        rewrite mnth_mat1_same. ring. rewrite mnth_mat1_diff; auto. ring.
      + apply vsum_unique with (i := y); intros; rewrite vnth_vmap2; elim_fin_eq.
    - rewrite vnth_madd. unfold vadd.
      apply vsum_unique with (i := i); intros; rewrite !vnth_vmap2; elim_fin_eq.
      rewrite mnth_mat1_same. ring. rewrite mnth_mat1_diff; auto. ring.
  Qed.


  (** *** 行交换矩阵 *)
  
  (** 行交换矩阵
      作用：E(x,y) * M 的结果是 M 的第 x 行和第 y 行交换
      形式：在x,y所在行时，(x,y) 和 (y,x) 是 1；其余行时是单位阵 *)
  Definition matRowSwap {n} (x y : fin n) : smat A n :=
    fun i j =>
      if i ??= x
      then (if j ??= y then 1 else 0)
      else (if i ??= y
            then (if j ??= x then 1 else 0)
            else (if i ??= j then 1 else 0)).

  (** 行交换：矩阵 M 的第 x, y 两行互换 *)
  Definition mrowSwap {n} (x y : fin n) (M : smat A n) : smat A n :=
    fun i j => if i ??= x then M y j else (if i ??= y then M x j else M i j).

  Lemma mnth_mrowSwap : forall {n} (x y : fin n) (M : smat A n),
      mrowSwap x y M = (matRowSwap x y) * M.
  Proof.
    intros. unfold mrowSwap, matRowSwap. apply meq_iff_mnth; intros.
    rewrite mnth_mmul. symmetry. elim_fin_eq.
    - apply vsum_unique with (i := y); intros; rewrite vnth_vmap2; elim_fin_eq.
    - apply vsum_unique with (i := x); intros; rewrite vnth_vmap2; elim_fin_eq.
    - apply vsum_unique with (i := i); intros; rewrite vnth_vmap2; elim_fin_eq.
  Qed.

End RowTrans.

Section test.
  Import Reals.
  Open Scope R.

  Notation mrowScale := (mrowScale (Amul:=Rmult)).
  Notation mrowAdd := (mrowAdd (Aadd:=Rplus) (Amul:=Rmult)).
  
  Let M : smat R 2 := @l2m _ 0 2 2 ([[1;2];[3;4]]).

  Let i0 : fin 2 := nat2finS 0.
  Let i1 : fin 2 := nat2finS 1.

  Goal m2l (mrowScale i0 2 M) = [[2;4];[3;4]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowScale i1 2 M) = [[1;2];[6;8]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowSwap i0 i0 M) = m2l M. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowSwap i0 i1 M) = [[3;4];[1;2]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowAdd i1 i0 2 M) = [[1;2];[5;8]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowAdd i0 i1 2 M) = [[7;10];[3;4]]. Proof. cbv. list_eq; ring. Qed.
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
  Infix "\.*" := (mcmul (Amul:=Rmult)) : mat_scope.

  Open Scope mat_scope.

  Definition M : mat 2 3 := l2m [[1;3;1];[1;0;0]].
  Definition N : mat 2 3 := l2m [[0;0;5];[7;5;0]].
  Definition O : mat 2 3 := l2m [[1;3;6];[8;5;0]].

  (** There are many wasy to finish the proof *)
  
  (* 1. use `m2l_inj` to convert the equation to `list` domain *)
  Example madd_m1_m2_eq_m3 : M + N = O.
  Proof. apply m2l_inj. cbv. list_eq; ring. Qed.
  
  (* 2. use `mnth` to compare elements. It is a bit complex *)
  Example madd_m1_m2_eq_m3' : M + N = O.
  Proof.
    apply meq_iff_mnth; intros. rewrite mnth_madd. unfold M,N,O. destruct i,j.
    repeat (try destruct x; try destruct x0; try lia; try (cbn; ring)).
  Qed.
  
  Definition M4 : mat 2 3 := l2m [[1; 8;-3];[4;-2; 5]].
  Definition M5 : mat 2 3 := l2m [[2;16;-6];[8;-4;10]].
  Example mscale_2_m4_eq_m5 : 2 \.* M4 = M5.
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
