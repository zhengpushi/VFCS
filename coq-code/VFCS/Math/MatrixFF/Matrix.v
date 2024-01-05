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
Require Import Extraction.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.
Open Scope mat_scope.

(* Global Hint Rewrite map_length seq_length : list. *)


(* ======================================================================= *)
(** ** Matrix type *)

Notation mat A r c := (@vec (@vec A c) r).

(** square matrix type *)
Notation smat A n := (mat A n n).

(** Row / Column vector type *)
Notation rvec A n := (mat A 1 n).
Notation cvec A n := (mat A n 1).


(** ** Convert between dlist and mat *)
Section l2m_m2l.
  Context {A : Type} (Azero : A).

  (** mat to dlist *)
  Definition m2l {r c} (M : mat A r c) : dlist A := map v2l (v2l M).

  (* Lemma m2l_length : forall {r c} (M : mat A r c), length (m2l M) = r. *)
  (* Proof. intros. unfold m2l. rewrite map_length. rewrite vlength; auto. Qed. *)

  (* Lemma m2l_width : forall {r c} (M : mat A r c), width (m2l M) c. *)
  (* Proof. *)
  (*   intros. unfold width,m2l. apply Forall_map. destruct M; simpl. clear. *)
  (*   induction vdata; auto. constructor; auto. apply vlength. *)
  (* Qed. *)
  
  (* Lemma m2l_inj : forall {r c} (M1 M2 : mat A r c), M1 <> M2 -> m2l M1 <> m2l M2. *)
  (* Proof. *)
  (*   intros. destruct M1,M2. unfold m2l; simpl in *. intro. *)
  (*   destruct H. apply veq_iff; simpl. *)
  (*   apply map_eq_imply_eq in H0; auto. *)
  (*   intros. apply veq_iff; auto. *)
  (* Qed. *)

  (* Lemma m2l_surj : forall {r c} (d : dlist A), *)
  (*     length d = r -> width d c -> (exists M : mat A r c, m2l M = d). *)
  (* Proof. *)
  (*   intros. *)
  (*   remember (map (l2v Azero c) d). *)
  (*   assert (length l = r). *)
  (*   { rewrite Heql. rewrite map_length; auto. } *)
  (*   exists (mkvec l H1). unfold m2l. simpl. rewrite Heql. rewrite map_map. *)
  (*   apply map_id_In; intros; simpl. apply listN_eq; auto. *)
  (*   apply (width_imply_in_length a d); auto. *)
  (* Qed. *)

  Definition l2m r c (dl : dlist A) : mat A r c :=
    l2v (vzero Azero) r (map (l2v Azero c) dl).

  (* Lemma l2m_inj : forall {r c} (d1 d2 : dlist A), *)
  (*     length d1 = r -> width d1 c -> *)
  (*     length d2 = r -> width d2 c -> *)
  (*     d1 <> d2 -> l2m r c d1 <> l2m r c d2. *)
  (* Proof. *)
  (*   intros. unfold l2m. apply l2v_inj; try rewrite map_length; auto. *)
  (*   intro. destruct H3. apply map_eq_imply_eq in H4; auto. *)
  (*   intros. apply l2v_inj_form2 in H6; auto. *)
  (*   apply width_imply_in_length with d1; auto. *)
  (*   apply width_imply_in_length with d2; auto. *)
  (* Qed. *)
  
  (* Lemma l2m_surj : forall {r c} (M : mat A r c), (exists d, l2m r c d = M). *)
  (* Proof. *)
  (*   intros. destruct (@l2v_surj (@vec A c) (vzero Azero) r M). *)
  (*   exists (map v2l x). unfold l2m. rewrite <- H. f_equal. *)
  (*   rewrite map_map. apply map_id. intros. apply l2v_v2l_id. *)
  (* Qed. *)

  (* (* relation between l2m and M2l *) *)
  (* Lemma l2m_m2l_id : forall {r c} (M : mat A r c), (@l2m r c (m2l M)) = M. *)
  (* Proof. *)
  (*   intros. destruct M; simpl. unfold m2l,l2m; simpl. apply veq_iff; simpl. *)
  (*   rewrite map_map. rewrite listN_eq. *)
  (*   - apply map_id. intros. apply l2v_v2l_id. *)
  (*   - rewrite map_length. auto. *)
  (* Qed. *)

  (* Lemma m2l_l2m_id : forall {r c} (dl : dlist A), *)
  (*     length dl = r -> width dl c -> m2l (@l2m r c dl) = dl. *)
  (* Proof. *)
  (*   intros. unfold l2m,m2l; simpl. rewrite listN_eq. *)
  (*   - rewrite map_map. apply map_id_In; intros. unfold l2v; simpl. *)
  (*     apply listN_eq. apply (width_imply_in_length a dl); auto. *)
  (*   - rewrite map_length; auto. *)
  (* Qed. *)

End l2m_m2l.

Section test.
  Let M0 := l2m 9 2 2 [].
  Let M1 := l2m 9 2 2 [[1;2];[3;4]].
  Let M2 := l2m 9 2 2 [[1];[3;4]].
  Let M3 := l2m 9 2 2 [[1;2];[3]].
  Let M4 := l2m 9 2 2 [[1;2;3];[3;4]].
  Let M5 := l2m 9 2 2 [[1;2];[3;4;5]].
  (* Compute m2l M0. *)
  (* Compute m2l M1. *)
  (* Compute m2l M2. *)
  (* Compute m2l M3. *)
  (* Compute m2l M4. *)
  (* Compute m2l M5. *)
End test.


(** ** Get nth element of a matrix *)
Section mnth.
  Context {A} (Azero : A) {r c : nat}.
  
  (* Lemma meq_iff_mnth : forall (M1 M2 : mat A r c), *)
  (*     M1 = M2 <-> forall i j, M1$i$j = M2$i$j. *)
  (* Proof. *)
  (*   intros. split; intros; subst; auto. unfold vnth in *. *)
  (*   destruct M1,M2; simpl in *. apply veq_iff; simpl. *)
  (*   rewrite (list_eq_iff_nth (vzero Azero) r); auto. *)
  (*   intros. specialize (H (nat2fin i)); simpl in H. *)
  (*   apply veq_iff. simpl. *)
  (*   rewrite (list_eq_iff_nth Azero c); auto. *)
  (*   - intros. specialize (H (nat2fin i0)); simpl in H. *)
  (*     simpl in H. *)
  (*     rewrite !fin2nat_nat2fin_id in H; auto. *)
  (*   - clear. apply vlength. *)
  (*   - clear. apply vlength. *)
  (* Qed. *)

End mnth.


(* Global Hint Unfold mnth : core. *)
(* Notation "M $ i $ j " := (mnth _ M i j) : mat_scope. *)
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


(** ** Convert between nat-indexing-Function (f) and matrix *)
(* Section f2m_m2f. *)
(*   Context {A} (Azero : A). *)

(*   Definition f2m {r c} (f : nat -> nat -> A) : mat A r c := *)
(*     @f2v _ r (fun i => @f2v A c (f i)). *)
    
(*   Definition m2f {r c} (M : mat A r c) : (nat -> nat -> A) := *)
(*     fun i => @v2f _ Azero c (@v2f _ (vzero Azero) r M i). *)

(* End f2m_m2f. *)



(** ** Convert between fin-indexing-Function (ff) and matrix *)
(* Section ff2m_m2ff. *)
(*   Context {A} (Azero : A). *)

(*   Definition ff2m {r c} (f : fin r -> fin c -> A) : mat A r c := *)
(*     @ff2v _ r (fun fi => @ff2v _ c (f fi)). *)

(*   Lemma mnth_ff2m : forall {r c} f i j, (@ff2m r c f)$i$j = f i j. *)
(*   Proof. *)
(*     intros. unfold ff2m. rewrite (vnth_ff2v (vzero Azero c)). *)
(*     apply (vnth_ff2v Azero). *)
(*   Qed. *)

(*   Definition m2ff {r c} (M : mat A r c) : (fin r -> fin c -> A) := *)
(*     fun i => @v2ff _ Azero c (@v2ff _ (vzero Azero c) r M i). *)

(* End ff2m_m2ff. *)


(** ** matrix with specific size *)

(* Section mat_specific. *)
(*   Context {A : Type} {Azero : A}. *)
(*   Variable r c : nat. *)
(*   Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : A. *)

(*   (** *** Create matrix *) *)
(*   Definition mkmat_0_c : mat A 0 c := mkvec0. *)
(*   Definition mkmat_r_0 : mat A r 0 := mkvec (repeat vnil r) (repeat_length _ _). *)

(*   Definition mkmat_1_c (l : list A) : mat A 1 (length l) := *)
(*     mkvec1 (l2v Azero (length l) l). *)
  
(*   Definition mkmat_r_1 (l : list A) : mat A (length l) 1 := *)
(*     mkvec (map (fun a => (mkvec [a] eq_refl) : vec 1) l) (map_length _ _). *)

(*   Definition mkmat_1_1 : mat A 1 1 := mkvec1 (mkvec1 a11). *)
(*   Definition mkmat_1_2 : mat A 1 2 := mkvec1 (mkvec2 a11 a12). *)
(*   Definition mkmat_2_1 : mat A 2 1 := mkvec2 (mkvec1 a11) (mkvec1 a21). *)
(*   Definition mkmat_2_2 : mat A 2 2 := mkvec2 (mkvec2 a11 a12) (mkvec2 a21 a22). *)
(*   Definition mkmat_1_3 : mat A 1 3 := mkvec1 (mkvec3 a11 a12 a13). *)
(*   Definition mkmat_2_3 : mat A 2 3 := *)
(*     mkvec2 (mkvec3 a11 a12 a13) (mkvec3 a21 a22 a23). *)
(*   Definition mkmat_3_1 : mat A 3 1 := *)
(*     mkvec3 (mkvec1 a11) (mkvec1 a21) (mkvec1 a31). *)
(*   Definition mkmat_3_2 : mat A 3 2 := *)
(*     mkvec3 (mkvec2 a11 a12) (mkvec2 a21 a22) (mkvec2 a31 a32). *)
(*   Definition mkmat_3_3 : mat A 3 3 := *)
(*     mkvec3 (mkvec3 a11 a12 a13) (mkvec3 a21 a22 a23) (mkvec3 a31 a32 a33). *)

(*   Definition mkmat_1_4 : mat A 1 4 := *)
(*     mkvec1 (mkvec4 a11 a12 a13 a14). *)
(*   Definition mkmat_4_1 : mat A 4 1 := *)
(*     mkvec4 (mkvec1 a11) (mkvec1 a21) (mkvec1 a31) (mkvec1 a41). *)
(*   Definition mkmat_4_4 : mat A 4 4 := *)
(*     mkvec4 (mkvec4 a11 a12 a13 a14) (mkvec4 a21 a22 a23 a24) *)
(*       (mkvec4 a31 a32 a33 a34) (mkvec4 a41 a42 a43 a44). *)
  
(* End mat_specific. *)

  
(** ** Construct matrix with two matrices *)
(* Section mapp. *)
(*   Context {A : Type}. *)
  
(*   (** Append matrix by row *) *)
(*   Definition mappr {r1 r2 c} (M1 : mat A r1 c) (M2 : mat A r2 c) *)
(*     : mat A (r1 + r2) c. *)
(*     refine (mkvec (vdata M1 ++ vdata M2) _). *)
(*     rewrite app_length, !vlength.  auto. *)
(*   Defined. *)

(*   (** Append matrix by column *) *)
(*   Definition mappc {r c1 c2} (M1 : mat A r c1) (M2 : mat A r c2) *)
(*     : mat A r (c1 + c2). *)
(*     refine (mkvec (map2 vapp (vdata M1) (vdata M2)) _). *)
(*     apply map2_length; apply vlength. *)
(*   Defined. *)
  
(* End mapp. *)


(** ** Elementary Row Transform *)

(* Section RowTrans. *)
(*   Context `{HRing : ARing}. *)
(*   Notation vzero n := (vzero Azero n). *)

(*   (** 第 i 行乘以 k *) *)
(*   Definition mrowK {r c} (M : mat A r c) (i : nat) (k : A) : mat A r c. *)
(*     destruct (le_gt_dec r i). *)
(*     - apply M. *)
(*     - pose (nth i (vdata M) (vzero c)) as row_i. *)
(*       pose (@vcmul _ Amul c k row_i) as row_i_K. *)
(*       pose (listSet (vdata M) i row_i_K) as l. *)
(*       refine (mkvec l _). unfold l, row_i_K, row_i. apply listSet_length, vlength. *)
(*   Defined. *)
  
(*   (** 交换 i1,i2 两行 *) *)
(*   Definition mrowSwap {r c} (M : mat A r c) (i1 i2 : nat) : mat A r c. *)
(*     destruct (le_gt_dec r i1). *)
(*     - apply M. *)
(*     - destruct (le_gt_dec r i2). *)
(*       + apply M. *)
(*       + pose (nth i1 (vdata M) (vzero c)) as row_i1. *)
(*         pose (nth i2 (vdata M) (vzero c)) as row_i2. *)
(*         pose (listSet (listSet (vdata M) i1 row_i2) i2 row_i1) as l. *)
(*         refine (mkvec l _). unfold l, row_i1, row_i2. *)
(*         apply listSet_length, listSet_length, vlength. *)
(*   Defined. *)

(*   (** 第 i1 行的 k 倍 加到第 i2 行 *) *)
(*   Definition mrowKAdd {r c} (M : mat A r c) (i1 i2 : nat) (k : A) : mat A r c. *)
(*     destruct (le_gt_dec r i1). *)
(*     - apply M. *)
(*     - destruct (le_gt_dec r i2). *)
(*       + apply M. *)
(*       + pose (nth i1 (vdata M) (vzero c)) as row_i1. *)
(*         pose (nth i2 (vdata M) (vzero c)) as row_i2. *)
(*         pose (@vadd _ Aadd _ (@vcmul _ Amul _ k row_i1) row_i2) as row_i2'. *)
(*         pose (listSet (vdata M) i2 row_i2') as l. *)
(*         refine (mkvec l _). unfold l, row_i2', row_i2, row_i1. *)
(*         apply listSet_length, vlength. *)
(*   Defined. *)

(* End RowTrans. *)

(* Require QcExt. *)
(* Section test. *)
(*   Import QcExt. *)
(*   Notation smat n := (smat Qc n). *)
  
(*   Let m1 : smat 2 := l2m 0 2 2 (Q2Qc_dlist [[1;2];[3;4]]%Q). *)
  
(*   Notation mrowK := (mrowK (Amul:=Qcmult)). *)
(*   Notation mrowKAdd := (mrowKAdd (Aadd:=Qcplus) (Amul:=Qcmult)). *)
  
(*   (* Compute m2l (mrowK m1 0 (Q2Qc 2)). *) *)
(*   (* Compute m2l (mrowK m1 1 (Q2Qc 2)). *) *)
(*   (* Compute m2l (mrowK m1 2 (Q2Qc 2)). *) *)
(*   (* Compute m2l (mrowSwap m1 0 0). *) *)
(*   (* Compute m2l (mrowSwap m1 0 1). *) *)
(*   (* Compute m2l (mrowSwap m1 0 2). *) *)
(*   (* Compute m2l (mrowKAdd m1 0 1 (Q2Qc 2)). *) *)
(*   (* Compute m2l (mrowKAdd m1 1 0 (Q2Qc 2)). *) *)
(* End test. *)


(** ** Matrix map *)
Notation mmap f M := (vmap (vmap f) M).

(* Lemma mnth_mmap : forall {A B} {r c} (M : mat A r c) (f:A->B) i j, *)
(*     (mmap f M)$i$j = f (M$i$j). *)
(* Admitted. *)

(** ** Matrix map2 *)
Notation mmap2 f M1 M2 := (vmap2 (vmap2 f) M1 M2).

(* Lemma mnth_mmap2 : forall {A B C} {r c} (M1:mat A r c) (M2:mat B r c) (f:A->B->C) i j, *)
(*     (mmap2 f M1 M2)$i$j = f (M1$i$j) (M2$i$j). *)
(* Admitted. *)


(** ** Matrix map2 with same base type *)
(* Section mmap2_sametype. *)
(*   Context `{Commutative A Aadd}. *)
  
(*   Lemma mmap2_comm : forall {r c} (M1 M2 : mat A r c), *)
(*       mmap2 Aadd M1 M2 = mmap2 Aadd M2 M1. *)
(*   Proof. *)
(*     intros. apply veq_iff; simpl. apply map2_comm. constructor. *)
(*     intros. apply vmap2_comm. *)
(*   Qed. *)
  
(*   Context `{Associative A Aadd}. *)
(*   Lemma mmap2_assoc : forall {r c} (M1 M2 M3 : mat A r c), *)
(*       mmap2 Aadd (mmap2 Aadd M1 M2) M3 = mmap2 Aadd M1 (mmap2 Aadd M2 M3). *)
(*   Proof. *)
(*     intros. apply veq_iff; simpl. apply map2_assoc. constructor. *)
(*     intros. apply vmap2_assoc. *)
(*   Qed. *)
  
(* End mmap2_sametype. *)



(* ======================================================================= *)
(** ** Get row and column of a matrix *)
(* Section mrow_mcol. *)
(*   Context {A} {r c : nat} (Azero : A). *)
(*   Notation vzero n := (vzero Azero n). *)

(*   Definition mrowNat (M : mat A r c) (i : nat) : option (@vec A c) := *)
(*     nth_error (vdata M) i. *)

(*   Definition mrow (M : mat A r c) (i : fin r) : @vec A c := vnth M i. *)
  
(*   Definition mcolNat (M : mat A r c) (j : nat) : option (@vec A r). *)
(*     destruct (le_gt_dec c j). *)
(*     - apply None. *)
(*     - pose ((exist _ j g) : fin c) as fj. *)
(*       refine (Some (mkvec (map (fun v => vnth v fj) (vdata M)) _)). *)
(*       rewrite map_length,vlength. auto. *)
(*   Defined. *)
  
(*   Definition mcol (M : mat A r c) (j : fin c) : @vec A r := *)
(*     vmap (fun v => vnth v j) M. *)

(*   Lemma vnth_mcol : forall (M : mat A r c) (i : fin r) (j : fin c), *)
(*       (mcol M j) $ i = M $ i $ j. *)
(*   Proof. *)
(*     intros. destruct M. unfold mcol,vnth; simpl. *)
(*     rewrite !nthFull_eq_nth with (Azero:=Azero). *)
(*     rewrite nth_map with (n:=r) (Azero:=vzero c); auto. *)
(*     - rewrite !nthFull_eq_nth with (Azero:=Azero); auto. *)
(*       rewrite nthFull_eq_nth with (Azero:=vzero c); auto. *)
(*     - subst. apply fin2nat_lt. *)
(*   Qed. *)

(*   Lemma mcol_ff2m : forall (ff : fin r -> fin c -> A) j, *)
(*       mcol (ff2m ff) j = ff2v (fun i => ff i j). *)
(*     Admitted. *)

(* End mrow_mcol. *)

(* Section test. *)
(*   Let M1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]]. *)
(*   Let f0 : fin 3 := nat2finS 0. *)
(*   Let f1 : fin 3 := nat2finS 1. *)
(*   (* Compute mrow M1 f0. *) *)
(*   (* Compute mrow M1 f1. *) *)
(*   (* Compute mcol M1 f0. *) *)
(*   (* Compute mcol M1 f1. *) *)
(* End test. *)


(* ======================================================================= *)
(** ** Construct matrix from vector and matrix *)

(* Section mcons. *)
(*   Context {A:Type} (Azero:A). *)
  
(*   (** Construct a matrix with a row vector and a a matrix *) *)
(*   Definition mconsr {r c} (V : @vec A c) (M : mat A r c) : mat A (S r) c := *)
(*     vcons V M. *)
  
(*   (** Construct a matrix with a column row vector and a a matrix *) *)
(*   Definition mconsc {r c} (V : @vec A r) (M : mat A r c) : mat A r (S c). *)
(*     refine (mkvec (map2 vcons (vdata V) (vdata M)) _). *)
(*     apply map2_length; apply vlength. *)
(*   Defined. *)
  
(*   (* (** Construct a matrix by rows with the matrix which row number is 0 *) *) *)
(*   (* Lemma mconsr_mr0 : forall {n} (V : rvec n) (M : mat A 0 n), mconsr V M = V. *) *)
(*   (* Proof. *) *)
(*   (*   intros. destruct V as [d1 pH1 pW1], M as [d2 pH2 pW2]. apply meq_iff. simpl. *) *)
(*   (*   apply length_zero_iff_nil in pH2. subst. rewrite <- list_length1_eq_hd; auto. *) *)
(*   (* Qed. *) *)

(*   (* (** Construct a matrix by columns with the matrix which column number is 0 *) *) *)
(*   (* Lemma mconsc_mc0 : forall {n} (V : cvec n) (M : mat A n 0), mconsc V M = V. *) *)
(*   (* Proof. *) *)
(*   (*   intros. destruct V as [d1 pH1 pW1], M as [d2 pH2 pW2]. apply meq_iff. simpl. *) *)
(*   (*   rewrite consc_dl_w0; auto. *) *)
(*   (*   - clear d2 pH2 pW2. *) *)
(*   (*     revert n pH1 pW1. induction d1; intros; simpl in *. auto. *) *)
(*   (*     destruct n. lia. inversion pH1. inversion pW1. *) *)
(*   (*     f_equal; auto. rewrite <- list_length1_eq_hd; auto. apply (IHd1 n); auto. *) *)
(*   (*   - rewrite hdc_length. lia. *) *)
(*   (* Qed. *) *)
  
(* End mcons. *)


(* ==================================== *)
(** ** matrix column shift *)
(* Section mcsh. *)
(*   Context {A} (Azero : A). *)
(*   (* Notation "M $ i $ j " := (vnth Azero (vnth vzero M i) j) : mat_scope. *) *)

(*   (* (** left shift column. *) *) *)
(*   (* (*     [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *) *) *)
(*   (* Definition mcshl {r c} (M : mat A r c) (k : nat) : mat A r c := *) *)
(*   (*   ff2m (fun i j => M $ i $ (j + k)). *) *)

(*   (* (** right shift column. *) *) *)
(*   (* (*     [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *) *) *)
(*   (* Definition mcshr {r c} (M : mat r c) (k : nat) : mat r c := *) *)
(*   (*   f2m (fun i j => if j <? k then Azero else (M $ i $ (j - k))). *) *)

(*   (* (** left loop shift column. *) *) *)
(*   (* (*     [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *) *) *)
(*   (* Definition mclshl {r c} (M : mat r c) (k : nat) : mat r c := *) *)
(*   (*   f2m (fun i j => M $ i $ (nat_lshl c j k)). *) *)

(*   (* (** right shift column *) *) *)
(*   (* Definition mclshr {r c} (M : mat r c) (k : nat) : mat r c := *) *)
(*   (*   f2m (fun i j => M $ i $ (nat_lshr c j k)). *) *)

(* End mcsh. *)

Section test.
  Let m1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l (mcshl 0 m1 1). *)
  (* Compute m2l (mcshr 0 m1 1). *)
  (* Compute m2l (mclshl 0 m1 1). *)
  (* Compute m2l (mclshr 0 m1 1). *)
End test.


(** ** matrix transpose *)
Section mtrans.
  Context {A : Type} (Azero : A).

  (* Definition mtrans_old {r c} (M : mat A r c) : mat A c r := *)
  (*   vmap (fun j => mcol M j) (vfinseq c). *)
  
  Definition mtrans {r c} (M : mat A r c) : mat A c r := fun i j => M j i.

  (* (** (M\T).j = col(M,j) *) *)
  (* Lemma vnth_mtrans_eq_mcol : forall {r c} (M : mat A r c) (j : fin c), *)
  (*     (mtrans M) $ j = mcol M j. *)
  (* Proof. *)
  (*   intros. unfold mtrans. rewrite vnth_vmap. f_equal. apply vnth_vfinseq. *)
  (* Qed. *)

  (** (M\T)[i,*] = M[*,i] *)
  Lemma vnth_mtrans : forall {r c} (M : mat A r c) i, (mtrans M)$i = fun j => M$j$i.
  Proof. intros. auto. Qed.

  (** Transpose twice return back *)
  Lemma mtrans_mtrans : forall {r c} (M : mat A r c), mtrans (mtrans M) = M.
  Proof. intros. auto. Qed.

End mtrans.

Notation "M \T" := (mtrans M) : mat_scope.


(** ** Diagonal matrix *)
(* Section mdiag. *)
(*   Context {A} (Azero:A). *)

(*   (** A matrix is a diagonal matrix *) *)
(*   Definition mdiag {n} (M : smat A n) : Prop := *)
(*     forall i j, i <> j -> M$i$j = Azero. *)

(*   (** Transpose of a diagonal matrix keep unchanged *) *)
(*   Lemma mtrans_diag : forall {n} (M : smat A n), mdiag M -> M\T = M. *)
(*   Proof. *)
(*     intros. apply (meq_iff_mnth Azero). intros. unfold mdiag in *. *)
(*     rewrite (mnth_mtrans Azero). *)
(*     destruct (finEqdec i j). *)
(*     - subst. auto. *)
(*     - rewrite !H; auto. *)
(*   Qed. *)

(*   (** Construct a diagonal matrix *) *)
(*   Definition mdiagMk {n} (v : @vec A n) : @smat A n := *)
(*     ff2m (fun i j => if (finEqdec i j) then v$i else Azero). *)

(*   (** mdiagMk is correct *) *)
(*   Lemma mdiagMk_spec : forall {n} (v : @vec A n), mdiag (mdiagMk v). *)
(*   Proof. *)
(*     intros. hnf. intros. unfold mdiagMk. unfold ff2m. *)
(*     rewrite (vnth_ff2v (vzero Azero n)). *)
(*     rewrite (vnth_ff2v Azero). destruct finEqdec; auto. easy. *)
(*   Qed. *)

(*   (** (mdiagMk l)[i,i] = l[i] *) *)
(*   Lemma mnth_mdiagMk_same : forall {n} (v : @vec A n) i, (mdiagMk v)$i$i = vnth v i. *)
(*   Proof. *)
(*     intros. unfold mdiagMk. unfold ff2m. *)
(*     rewrite (vnth_ff2v (vzero Azero n)). rewrite (vnth_ff2v Azero). *)
(*     destruct finEqdec; easy. *)
(*   Qed. *)

(*   (** (mdiagMk l)[i,j] = 0 *) *)
(*   Lemma mnth_mdiagMk_diff : forall {n} (v : @vec A n) i j, *)
(*       i <> j -> (mdiagMk v)$i$j = Azero. *)
(*   Proof. *)
(*     intros. pose proof (mdiagMk_spec v). unfold mdiag in H0. auto. *)
(*   Qed. *)

(* End mdiag. *)


(* Lemma map_repeat_ext : forall {A B} (l : list A) (f : A -> B) Bzero n, *)
(*     length l = n -> (forall a : A, f a = Bzero) -> map f l = repeat Bzero n. *)
(* Proof. *)
(*   intros. revert n H. induction l; intros; simpl in *. *)
(*   - subst. simpl. auto. *)
(*   - destruct n; simpl. lia. f_equal; auto. *)
(* Qed. *)


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
  Lemma mtrans_0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. auto. Qed.

  (** mat0[i,j] = 0 *)
  Lemma mnth_mat0 : forall {r c} i j, @mat0 r c $ i $ j = Azero.
  Proof. intros. auto. Qed.
  
  (* (** *** Unit matrix *) *)
  (* Definition mat1 {n} : smat n := *)
  (*   ff2m (fun i j => if finEqdec i j then Aone else Azero). *)
      
  (* (** mat1\T = mat1 *) *)
  (* Lemma mtrans_1 : forall {n : nat}, (@mat1 n)\T = mat1. *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. *)
  (*   rewrite (mnth_mtrans Azero). unfold mat1. *)
  (*   rewrite !(mnth_ff2m Azero). *)
  (*   destruct (finEqdec i j), (finEqdec j i); subst; try easy. *)
  (* Qed. *)

  (* (** mat1[i,i] = 1 *) *)
  (* Lemma mnth_mat1_same : forall {n} i, (@mat1 n) $ i $ i = Aone. *)
  (* Proof. *)
  (*   intros. unfold mat1. rewrite (mnth_ff2m Azero). destruct finEqdec; easy. *)
  (* Qed. *)

  (* (** i <> j -> mat1[i,j] = 0 *) *)
  (* Lemma mnth_mat1_diff : forall {n} i j, i <> j -> @mat1 n $ i $ j = Azero. *)
  (* Proof. *)
  (*   intros. unfold mat1. rewrite (mnth_ff2m Azero). destruct finEqdec; easy. *)
  (* Qed. *)

  (* (** mat1 is diagonal matrix *) *)
  (* Lemma mat1_diag : forall {n : nat}, mdiag Azero (@mat1 n). *)
  (* Proof. intros. hnf. intros. rewrite mnth_mat1_diff; auto. Qed. *)


  (** *** Matrix Trace *)
  
  (* Definition mtrace {n : nat} (M : smat n) : A := *)
  (*   vsum (vmap (fun i => M$i$i) (vfinseq n)). *)

  (* (** tr(M\T) = tr(M) *) *)
  (* Lemma mtrace_trans : forall {n} (M : smat n), mtrace (M\T) = mtrace(M). *)
  (* Proof. *)
  (*   intros. unfold mtrace. f_equal. f_equal. apply functional_extensionality. *)
  (*   intros. rewrite (mnth_mtrans Azero); auto. *)
  (* Qed. *)

  
  (** *** Matrix Addition *)
  Definition madd {r c} (M1 M2 : mat r c) : mat r c := mmap2 Aadd M1 M2.
  Infix "+" := madd : mat_scope.

  (* Lemma madd_comm : forall {r c} (M1 M2 : mat r c), M1 + M2 = M2 + M1. *)
  (* Proof. intros. apply mmap2_comm. Qed. *)
  
  (* Lemma madd_assoc : forall {r c} (M1 M2 M3 : mat r c), *)
  (*     (M1 + M2) + M3 = M1 + (M2 + M3). *)
  (* Proof. intros. apply mmap2_assoc. Qed. *)
  
  (* (** 0 + M = M *) *)
  (* Lemma madd_0_l : forall {r c} (M : mat r c), mat0 + M = M. *)
  (* Proof. *)
  (*   intros. unfold madd. apply (meq_iff_mnth Azero). intros. *)
  (*   rewrite !vnth_vmap2. rewrite mnth_mat0. apply AG. *)
  (* Qed. *)

  (* (** M + 0 = M *) *)
  (* Lemma madd_0_r : forall {r c} (M : mat r c), M + mat0 = M. *)
  (* Proof. intros. rewrite madd_comm, madd_0_l; auto. Qed. *)
  
  (* Instance Associative_madd : forall r c, @Associative (mat r c) madd. *)
  (* Proof. intros. constructor. apply madd_assoc. Qed. *)

  (* Instance Commutative_madd : forall r c, @Commutative (mat r c) madd. *)
  (* Proof. intros. constructor. apply madd_comm. Qed. *)

  (* Instance IdentityLeft_madd : forall r c, @IdentityLeft (mat r c) madd mat0. *)
  (* Proof. intros. constructor. apply madd_0_l. Qed. *)

  (* Instance IdentityRight_madd : forall r c, @IdentityRight (mat r c) madd mat0. *)
  (* Proof. intros. constructor. apply madd_0_r. Qed. *)

  (* Instance Monoid_madd : forall r c, Monoid (@madd r c) mat0. *)
  (* Proof. *)
  (*   intros. repeat constructor; intros; *)
  (*     try apply associative; *)
  (*     try apply identityLeft; *)
  (*     try apply identityRight. *)
  (* Qed. *)
  
  (* (** (M1+M2)[i,j] = M1[i,j] + M2[i,j] *) *)
  (* Lemma mnth_madd : forall {r c} (M1 M2 : mat r c) i j, *)
  (*     (M1 + M2) $ i $ j = (M1$i$j + M2$i$j)%A. *)
  (* Proof. intros. unfold madd. rewrite !vnth_vmap2. auto. Qed. *)

  (* (** (M1 + M2)\T = M1\T + M2\T *) *)
  (* Lemma mtrans_madd : forall {r c} (M1 M2 : mat r c), (M1 + M2)\T = M1\T + M2\T. *)
  (* Proof. *)
  (*   intros. unfold madd. apply (meq_iff_mnth Azero). intros. *)
  (*   rewrite !vnth_vmap2. rewrite !(mnth_mtrans Azero). *)
  (*   rewrite !vnth_vmap2. auto. *)
  (* Qed. *)

  (* (** tr(M1 + M2) = tr(M1) + tr(M2) *) *)
  (* Lemma mtrace_madd : forall {n} (M1 M2 : smat n), *)
  (*     (mtrace (M1 + M2)%M = mtrace(M1) + mtrace(M2))%A. *)
  (* Proof. *)
  (*   intros. unfold madd. unfold mtrace. apply vsum_add. intros. *)
  (*   rewrite !vnth_vmap. rewrite vnth_vfinseq. rewrite !vnth_vmap2. auto. *)
  (* Qed. *)


  (** *** Matrix Opposition *)
  Definition mopp {r c} (M : mat r c) : mat r c := mmap Aopp M.
  Notation "- M" := (mopp M) : mat_scope.
  
  (* Lemma madd_opp_l : forall {r c} (M : mat r c), (-M) + M = mat0. *)
  (* Proof. *)
  (*   intros. unfold madd,mopp. apply (meq_iff_mnth Azero). intros. *)
  (*   rewrite !vnth_vmap2. rewrite !vnth_vmap. rewrite mnth_mat0. apply AG. *)
  (* Qed. *)
    
  (* Lemma madd_opp_r : forall {r c} (M : mat r c), M + (-M) = mat0. *)
  (* Proof. intros. rewrite madd_comm. apply madd_opp_l. Qed. *)

  (* Instance InverseLeft_madd : forall r c, @InverseLeft (mat r c) madd mat0 mopp. *)
  (* Proof. intros. constructor. apply madd_opp_l. Qed. *)

  (* Instance InverseRight_madd : forall r c, @InverseRight (mat r c) madd mat0 mopp. *)
  (* Proof. intros. constructor. apply madd_opp_r. Qed. *)

  (* Instance AGroup_madd : forall r c, @AGroup (mat r c) madd mat0 mopp. *)
  (* Proof. *)
  (*   intros. repeat constructor; *)
  (*     try apply associative; *)
  (*     try apply identityLeft; *)
  (*     try apply identityRight; *)
  (*     try apply inverseLeft; *)
  (*     try apply inverseRight; *)
  (*     try apply commutative. *)
  (* Qed. *)

  (* Now, we ca use group theory on <madd, mat0, mopp, msub> *)

  (* (** (M1 + M2) + M3 = (M1 + M3) + M2 *) *)
  (* Lemma madd_perm : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) + M3 = (M1 + M3) + M2. *)
  (* Proof. intros. rewrite !associative. f_equal. apply commutative. Qed. *)
  
  (* (** - (- M) = M *) *)
  (* Lemma mopp_mopp : forall {r c} (M : mat r c), - (- M) = M. *)
  (* Proof. intros. apply group_inv_inv. Qed. *)

  (* (** -M1 = M2 <-> M1 = -M2 *) *)
  (* Lemma mopp_exchange : forall {r c} (M1 M2 : mat r c), -M1 = M2 <-> M1 = -M2. *)
  (* Proof. *)
  (*   intros. split; intros. *)
  (*   - rewrite <- H. rewrite mopp_mopp. easy. *)
  (*   - rewrite H. rewrite mopp_mopp. easy.  *)
  (* Qed. *)

  (* (** - (mat0) = mat0 *) *)
  (* Lemma mopp_mat0 : forall {r c:nat}, - (@mat0 r c) = mat0. *)
  (* Proof. intros. apply group_inv_id. Qed. *)

  (* (** - (m1 + m2) = (-m1) + (-m2) *) *)
  (* Lemma mopp_madd : forall {r c : nat} (M1 M2 : mat r c), - (M1 + M2) = (-M1) + (-M2). *)
  (* Proof. intros. rewrite group_inv_distr. apply commutative. Qed. *)

  (* (** (- M)\T = - (M\T) *) *)
  (* Lemma mtrans_mopp : forall {r c} (M : mat r c), (- M)\T = - (M\T). *)
  (* Proof. *)
  (*   intros. unfold mopp. apply (meq_iff_mnth Azero). intros. *)
  (*   rewrite (mnth_mtrans Azero). rewrite !vnth_vmap. *)
  (*   rewrite (mnth_mtrans Azero). auto. *)
  (* Qed. *)

  (* (** tr(- M) = - (tr(m)) *) *)
  (* Lemma mtrace_mopp : forall {n} (M : smat n), mtrace(-M) = (- (mtrace M))%A. *)
  (* Proof. *)
  (*   intros. unfold mopp. unfold mtrace. apply vsum_opp. intros. *)
  (*   rewrite !vnth_vmap. rewrite vnth_vfinseq. auto. *)
  (* Qed. *)
  
  
  (** *** Matrix Subtraction *)
  Definition msub {r c} (M1 M2 : mat r c) : mat r c := M1 + (-M2).
  Infix "-" := msub : mat_scope.

  (* (** M1 - M2 = - (M2 - M1) *) *)
  (* Lemma msub_comm : forall {r c} (M1 M2 : mat r c), M1 - M2 = - (M2 - M1). *)
  (* Proof. intros. unfold msub. rewrite group_inv_distr. *)
  (*        rewrite group_inv_inv. auto. Qed. *)

  (* (** (M1 - M2) - M3 = M1 - (M2 + M3) *) *)
  (* Lemma msub_assoc : forall {r c} (M1 M2 M3 : mat r c), *)
  (*     (M1 - M2) - M3 = M1 - (M2 + M3). *)
  (* Proof. intros. unfold msub. group. f_equal. *)
  (*        rewrite group_inv_distr. apply commutative. Qed. *)

  (* (** (M1 + M2) - M3 = M1 + (M2 - M3) *) *)
  (* Lemma msub_assoc1 : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) - M3 = M1 + (M2 - M3). *)
  (* Proof. intros. unfold msub. group. Qed. *)

  (* (** (M1 - M2) - M3 = M1 - (M3 - M2) *) *)
  (* Lemma msub_assoc2 : forall {r c} (M1 M2 M3 : mat r c), (M1 - M2) - M3 = (M1 - M3) - M2. *)
  (* Proof. intros. unfold msub. group. f_equal. apply commutative. Qed. *)
  
  (* (** 0 - M = - M *) *)
  (* Lemma msub_0_l : forall {r c} (M : mat r c), mat0 - M = - M. *)
  (* Proof. intros. unfold msub. group. Qed. *)
  
  (* (** M - 0 = M *) *)
  (* Lemma msub_0_r : forall {r c} (M : mat r c), M - mat0 = M. *)
  (* Proof. intros. unfold msub. rewrite (@group_inv_id _ madd mat0); auto. *)
  (*        group. apply AGroup_madd. Qed. *)
  
  (* (** M - M = 0 *) *)
  (* Lemma msub_self : forall {r c} (M : mat r c), M - M = mat0. *)
  (* Proof. intros. unfold msub. group. Qed. *)

  (* (** (M1 - M2)\T = M1\T - M2\T *) *)
  (* Lemma mtrans_msub : forall {r c} (M1 M2 : mat r c), (M1 - M2)\T = M1\T - M2\T. *)
  (* Proof. intros. unfold msub. rewrite mtrans_madd. f_equal. apply mtrans_mopp. Qed. *)

  (* (** tr(M1 - M2) = tr(M1) - tr(M2) *) *)
  (* Lemma mtrace_msub : forall {n} (M1 M2 : smat n), *)
  (*     mtrace (M1 - M2) = (mtrace M1 - mtrace M2)%A. *)
  (* Proof. intros. unfold msub. rewrite mtrace_madd, mtrace_mopp. auto. Qed. *)

  
  Context `{AR : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : make_ring_theory.

  Notation vdot v1 v2 := (@vdot _ Aadd Azero Amul _ v1 v2).
  Notation "< v1 , v2 >" := (vdot v1 v2) : vec_scope.

  
  (* Notation for "vsum" *)
  (* Notation "'\sum' f" := (vsum (ff2v f)). *)

  (** Dot product is associativity on form `u * M * v` *)

  (* <<V1, M\T>, V2> = Σ Σ (V1.i * M.i.j * V2.j) *)
  (* Lemma vdot_vdotM_l : forall {r c} (V1 : @vec A r) (M : mat r c) (V2 : @vec A c), *)
  (*     vdot (vmap (fun V : vec r => <V1,V>) (M \T)) V2 = *)
  (*       \sum (fun j:fin c => \sum (fun i:fin r => V1$i * M$i$j * V2$j)). *)
  (* Proof. *)
  (*   intros. unfold vdot. *)
  (*   rewrite (vmap2_eq_vmap Azero). *)
  (*   rewrite (ff2v_eq_vmap_vfinseq Azero). f_equal. f_equal. *)
  (*   apply functional_extensionality; intros. *)
  (*   rewrite (vsum_cmul) with (k:=(V2$x)) (V2:=ff2v (fun i => V1$i*M$i$x)). *)
  (*   - rewrite commutative. f_equal. *)
  (*     rewrite (ff2v_eq_vmap_vfinseq Azero). rewrite vnth_vmap. f_equal. *)
  (*     rewrite (vmap2_eq_vmap Azero). f_equal. *)
  (*     apply functional_extensionality; intros. f_equal. *)
  (*     rewrite (mnth_mtrans Azero). auto. *)
  (*   - intros. rewrite !(vnth_ff2v Azero). ring. *)
  (* Qed. *)

  (* <V1, <M, V2>> = Σ Σ (V1.i * M.i.j * V2.j) *)
  (* Lemma vdot_vdotM_r : forall {r c} (V1 : @vec A r) (M : mat r c) (V2 : @vec A c), *)
  (*     vdot V1 (vmap (fun V : vec c  => <V,V2>) M) = *)
  (*       \sum (fun j:fin c => \sum (fun i:fin r => V1$i * M$i$j * V2$j)). *)
  (* Proof. *)
  (*   intros. unfold vdot. rewrite vsum_vsum_exchg. *)
  (*   rewrite (vmap2_eq_vmap Azero). *)
  (*   rewrite (ff2v_eq_vmap_vfinseq Azero). f_equal. f_equal. *)
  (*   apply functional_extensionality; intros. *)
  (*   rewrite (vsum_cmul) with (k:=(V1$x)) (V2:=ff2v (fun i => M$x$i*V2$i)). *)
  (*   - f_equal. rewrite (ff2v_eq_vmap_vfinseq Azero). rewrite vnth_vmap. f_equal. *)
  (*     rewrite (vmap2_eq_vmap Azero). auto. *)
  (*   - intros. rewrite !(vnth_ff2v Azero). ring. *)
  (* Qed. *)
  
  (* Lemma vdotM_assoc : forall {r c} (V1 : @vec A r) (M : mat r c) (V2 : @vec A c), *)
  (*     vdot (vmap (fun V : vec r  => <V1,V>) (M\T)) V2 = *)
  (*       vdot V1 (vmap (fun V : vec c  => <V,V2>) M). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite vdot_vdotM_l. rewrite vdot_vdotM_r. auto. *)
  (* Qed. *)
  
  (** *** Matrix Scalar Multiplication *)
  Definition mcmul {r c : nat} (a : A) (M : mat r c) : mat r c :=
    vmap (vmap (Amul a)) M.
  Infix "c*" := mcmul : mat_scope.

  (* (** (a * M)[i,j] = a * M[i,j] *) *)
  (* Lemma mnth_mcmul : forall {r c} (M : mat r c) a i j, *)
  (*     (a c* M)$i$j = a * (M$i$j). *)
  (* Proof. intros. unfold mcmul. rewrite !vnth_vmap. auto. Qed. *)

  (* (** a1 * (a2 * M) = (a1 * a2) * M *) *)
  (* Lemma mcmul_assoc : forall {r c} (M : mat r c) a1 a2, *)
  (*     a1 c* (a2 c* M) = (a1 * a2)%A c* M. *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul. *)
  (*   rewrite !vnth_vmap. ring. *)
  (* Qed. *)
  
  (* (** a1 * (a2 * M) = a2 * (a1 * M) *) *)
  (* Lemma mcmul_perm : forall {r c} (M : mat r c) a1 a2, *)
  (*     a1 c* (a2 c* M) = a2 c* (a1 c* M). *)
  (* Proof. intros. rewrite !mcmul_assoc. f_equal. ring. Qed. *)

  (* (** a * (M1 + M2) = (a * M1) + (a * M2) *) *)
  (* Lemma mcmul_madd_distr : forall {r c} a (M1 M2 : mat r c), *)
  (*     a c* (M1 + M2) = (a c* M1) + (a c* M2). *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul, madd. *)
  (*   rewrite !vnth_vmap. rewrite !vnth_vmap2. rewrite !vnth_vmap. ring. *)
  (* Qed. *)
  
  (* (** (a1 + a2) * M = (a1 * M) + (a2 * M) *) *)
  (* Lemma mcmul_add_distr : forall {r c} a1 a2 (M : mat r c), *)
  (*     (a1 + a2)%A c* M = (a1 c* M) + (a2 c* M). *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul, madd. *)
  (*   rewrite !vnth_vmap. rewrite !vnth_vmap2. rewrite !vnth_vmap. ring. *)
  (* Qed. *)

  (* (* 0 c* M = mat0 *) *)
  (* Lemma mcmul_0_l : forall {r c} (M : mat r c), Azero c* M = mat0. *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul. *)
  (*   rewrite !vnth_vmap. rewrite !mnth_mat0. ring. *)
  (* Qed. *)

  (* (** a c* mat0 = mat0 *) *)
  (* Lemma mcmul_0_r : forall {r c} a, a c* (@mat0 r c) = mat0. *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul. *)
  (*   rewrite !vnth_vmap. rewrite !mnth_mat0. ring. *)
  (* Qed. *)
  
  (* (* 1 c* A = A *) *)
  (* Lemma mcmul_1 : forall {r c} (M : mat r c), Aone c* M = M. *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul. *)
  (*   rewrite !vnth_vmap. ring. *)
  (* Qed. *)
  
  (* (* (-a) * M = - (a * M) *) *)
  (* Lemma mcmul_opp : forall {r c} a (M : mat r c), (- a)%A c* M = - (a c* M). *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul, mopp. *)
  (*   rewrite !vnth_vmap. ring. *)
  (* Qed. *)
  
  (* (* a * (-M) = - (a * M) *) *)
  (* Lemma mcmul_mopp : forall {r c} a (M : mat r c), a c* (-M) = - (a c* M). *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul, mopp. *)
  (*   rewrite !vnth_vmap. ring. *)
  (* Qed. *)
  
  (* (* (-a) * (- M) = a * M *) *)
  (* Lemma mcmul_opp_mopp : forall {r c} a (M : mat r c), *)
  (*     (- a)%A c* (- M) = a c* M. *)
  (* Proof. intros. rewrite mcmul_mopp, mcmul_opp. rewrite mopp_mopp. auto. Qed. *)

  (* (** a c* (M1 - M2) = (a c* M1) - (a c* M2) *) *)
  (* Lemma mcmul_msub : forall {r c} a (M1 M2 : mat r c), *)
  (*     a c* (M1 - M2) = (a c* M1) - (a c* M2). *)
  (* Proof. *)
  (*   intros. unfold msub. rewrite mcmul_madd_distr. f_equal. *)
  (*   rewrite mcmul_mopp. auto. *)
  (* Qed. *)
  
  (* (** 1 c* m = m *) *)
  (* Lemma mcmul_1_l : forall {r c} (M : mat r c), Aone c* M = M. *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul. *)
  (*   rewrite !vnth_vmap. ring. *)
  (* Qed. *)

  (* (** a c* mat1 = mdiag([a,a,...]) *) *)
  (* Lemma mcmul_1_r : forall {n} a, a c* (@mat1 n) = mdiagMk Azero (vrepeat a). *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. unfold mcmul. *)
  (*   rewrite !vnth_vmap. destruct (finEqdec i j). *)
  (*   - subst. rewrite mnth_mat1_same. rewrite mnth_mdiagMk_same.  *)
  (*     rewrite vnth_vrepeat. ring. *)
  (*   - rewrite mnth_mat1_diff; auto. rewrite mnth_mdiagMk_diff; auto. ring. *)
  (* Qed. *)

  (* (** (a c* M)\T = a c* (m\T) *) *)
  (* Lemma mtrans_mcmul : forall {r c} (a : A) (M : mat r c), (a c* M)\T = a c* (M\T). *)
  (* Proof. *)
  (*   intros. apply (meq_iff_mnth Azero). intros. *)
  (*   rewrite (mnth_mtrans Azero). rewrite !mnth_mcmul. rewrite (mnth_mtrans Azero). *)
  (*   auto. *)
  (* Qed. *)

  (* (** tr (a c* M) = a * tr (m) *) *)
  (* Lemma mtrace_mcmul : forall {n} (a : A) (M : smat n), *)
  (*     mtrace (a c* M) = (a * mtrace M)%A. *)
  (* Proof. *)
  (*   intros. unfold mcmul. unfold mtrace. apply vsum_cmul. intros. *)
  (*   rewrite !vnth_vmap. rewrite vnth_vfinseq. auto. *)
  (* Qed. *)

  
  (** *** Matrix Multiplication *)

  (* structural-style *)
  Definition mmul_old {r c t : nat} (M1 : mat r c) (M2 : mat c t) : mat r t :=
    vmap (fun v1 => vmap (fun v2 => <v1,v2>) (mtrans M2)) M1.
  
  (* functional-style *)
  Definition mmul {r c t : nat} (M1 : mat r c) (M2 : mat c t) : mat r t :=
    fun i j => <M1$i, (fun k=>M2$k$j)>.

  Infix "*" := mmul : mat_scope.

  (** (M1 * M2) * M3 = M1 * (M2 * M3) *)
  Lemma mmul_assoc : forall {m n r s} (M1 : mat m n) (M2 : mat n r) (M3 : mat r s),
      (M1 * M2) * M3 = M1 * (M2 * M3).
  Proof.
    intros. unfold mmul, vdot, vsum, vmap2.
    apply (veq_iff_vnth); intros. apply (veq_iff_vnth); intros.
    (* remember (fun i1 i2 => M1 i i2 * M2 i2 i1 * M3 i1 i0)%A as f. *)
    pose proof (fseqsum_fseqsum_exchg r n
                  (fun i1 i2 => M1 i i2 * M2 i2 i1 * M3 i1 i0)%A).
    match goal with
    | H: ?a1 = ?b1 |- ?a2 = ?b2 => replace a2 with a1;[replace b2 with b1|]; auto
    end.
    - f_equal. extensionality j. apply fseqsum_cmul; intros. ring.
    - f_equal. extensionality j. rewrite commutative.
      apply fseqsum_cmul; intros. ring.
  Qed.
?

  (** M1 * (M2 + M3) = M1 * M2 + M1 * M3 *)
  Lemma mmul_madd_distr_l : forall {r c t} (M1 : mat r c) (M2 M3 : mat c t),
      M1 * (M2 + M3) = (M1 * M2) + (M1 * M3).
  Proof.
    intros.
    unfold mmul, madd.
    apply (meq_iff_mnth Azero); intros.
    rewrite !vnth_vmap2. rewrite !vnth_vmap.
    rewrite vnth_mtrans_eq_mcol. ?
    rewrite vnth_vmap2.
    
    
    Search  vmap2.
    rewrite !vmap2_eq_vmap.
    rewrite vmap2.
    Search mmap2.
    rewrite mmap2
    
    intros. destruct M1,M2,M3. apply meq_iff; simpl. rewrite dltrans_dmap2; auto.
    rewrite (dldotdl_dmap2_distr_l _ _ _ mwidth0); auto with mat. subst; auto.
  Qed.
  
  (** (M1 + M2) * M3 = M1 * M3 + M2 * M3 *)
  Lemma mmul_madd_distr_r : forall {r c t} (M1 M2 : mat r c) (M3 : mat c t),
      (M1 + M2) * M3 = (M1 * M3) + (M2 * M3).
  Proof.
    intros. destruct M1,M2,M3. apply meq_iff; simpl.
    rewrite (dldotdl_dmap2_distr_r _ _ _ mwidth0); auto with mat.
  Qed.

  (** (-M1) * M2 = - (M1 * M2) *)
  Lemma mmul_mopp_l : forall {r c t} (M1 : mat r c) (M2 : mat c t),
      (-M1) * M2 = -(M1 * M2).
  Proof.
    intros. destruct M1,M2. apply meq_iff; simpl.
    rewrite dldotdl_dmap_distr_l with (c:=c); auto with mat; intros; ring.
  Qed.

  (** M1 * (-M2) = - (M1 * M2) *)
  Lemma mmul_mopp_r : forall {r c t} (M1 : mat r c) (M2 : mat c t),
      M1 * (-M2) = -(M1 * M2).
  Proof.
    intros. destruct M1,M2. apply meq_iff; simpl.
    rewrite <- dldotdl_dmap_distr_r with (c:=c); auto with mat; intros; try ring.
    rewrite dltrans_dmap; auto.
  Qed.

  (** M1 * (M2 - M3) = M1 * M2 - M1 * M3 *)
  Lemma mmul_msub_distr_l : forall {r c t} (M1 : mat r c) (M2 M3 : mat c t),
      M1 * (M2 - M3) = (M1 * M2) - (M1 * M3).
  Proof.
    intros. unfold msub. rewrite mmul_madd_distr_l. f_equal.
    rewrite mmul_mopp_r. auto.
  Qed.
  
  (** (M1 - M2) * M3 = M1 * M3 - M2 * M3 *)
  Lemma mmul_msub_distr_r : forall {r c t} (M1 M2 : mat r c) (M3 : mat c t),
      (M1 - M2) * M3 = (M1 * M3) - (M2 * M3).
  Proof.
    intros. unfold msub. rewrite mmul_madd_distr_r. f_equal.
    rewrite mmul_mopp_l. auto.
  Qed.
  
  (** 0 * M = 0 *)
  Lemma mmul_0_l : forall {r c t} (M : mat c t), mat0 * M = mat0 r t.
  Proof.
    intros. destruct M. apply meq_iff; simpl. rewrite dldotdl_zero_l; auto with mat.
  Qed.
  
  (** M * 0 = 0 *)
  Lemma mmul_0_r : forall {r c t} (M : mat r c), M * mat0 = mat0 r t.
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    rewrite dltrans_zero. rewrite dldotdl_zero_r; auto.
  Qed.
  
  (** 1 * M = M *)
  Lemma mmul_1_l : forall {r c} (M : mat r c), mat1 * M = M.
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    rewrite dldotdl_dlunit_l; auto with mat. apply dltrans_dltrans; auto.
  Qed.
  
  (** M * 1 = M *)
  Lemma mmul_1_r : forall {r c} (M : mat r c), M * mat1 = M.
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    rewrite dltrans_dlunit. rewrite dldotdl_dlunit_r; auto with mat.
  Qed.

  (** (a * b) c* M = a c* (b c* M) *)
  Lemma mcmul_mul_assoc : forall {r c} (a b : A) (M : mat r c),
      (a * b)%A c* M = a c* (b c* M).
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    rewrite dmap_dmap. f_equal. apply functional_extensionality.
    intros. apply associative.
  Qed.

  (** (a c* M1) * M2 = a c* (M1 * M2) *)
  Lemma mmul_mcmul_l : forall {r c s} (a : A) (M1 : mat r c) (M2 : mat c s), 
      (a c* M1) * M2 = a c* (M1 * M2).
  Proof.
    intros. destruct M1,M2. apply meq_iff; simpl.
    rewrite (dldotdl_dmap_distr_l) with (c:=c); auto; intros; try ring.
    apply dltrans_width; auto.
  Qed.
  
  (** M1 * (a c* M2) = a c* (M1 * M2) *)
  Lemma mmul_mcmul_r : forall {r c s} (a : A) (M1 : mat r c) (M2 : mat c s), 
      M1 * (a c* M2) = a c* (M1 * M2).
  Proof.
    intros. destruct M1,M2. apply meq_iff; simpl.
    rewrite <- (dldotdl_dmap_distr_r) with (c:=c); auto; intros; try ring.
    - rewrite dltrans_dmap; auto.    
    - apply dltrans_width; auto.
  Qed.

  (** (M1 * M2)\T = M2\T * M1\T *)
  Lemma mtrans_mmul : forall {r c s} (M1 : mat r c) (M2 : mat c s),
      (M1 * M2)\T = M2\T * M1\T.
  Proof.
    intros. destruct M1,M2. apply meq_iff; simpl.
    rewrite dltrans_dltrans; auto.
    rewrite <- dldotdl_comm with (c:=c); auto with mat.
  Qed.

  (** tr (M1 * M2) = tr (M2 * M1) *)
  Lemma mtrace_mmul_comm : forall {r c} (M1 : mat r c) (M2 : mat c r),
      mtrace (M1 * M2) = mtrace (M2 * M1).
  Proof.
    intros. destruct M1 as [m1 pH1 pW1], M2 as [m2 pH2 pW2].
    unfold mmul,mtrace; simpl.
    revert r c m2 pH1 pW1 pH2 pW2. induction m1; intros; simpl in *.
    2:{
      Abort.
  
  
  (** Properties below, need a field structure *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Context `{ADec : Dec A}.

  
  (** k * M = 0 -> (k = 0) \/ (M = 0) *)
  Lemma mcmul_eq0_imply_m0_or_k0 : forall {r c} (M : mat r c) k,
      k c* M = mat0 -> (k = Azero)%A \/ (M = mat0).
  Proof.
    intros. destruct M.
    unfold mcmul in H. apply meq_iff in H. simpl in H.
    apply dlcmul_zero_imply_k0_or_dlzero in H; auto. destruct H; auto.
    right. apply meq_iff; auto.
  Qed.

  (** (M <> 0 /\ k * M = 0) -> M = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (M : mat r c) k,
      M <> mat0 -> k c* M = mat0 -> (k = Azero)%A.
  Proof. intros. apply mcmul_eq0_imply_m0_or_k0 in H0; auto. tauto. Qed.

  (** k * M = M -> k = 1 \/ M = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} k (M : mat r c),
      k c* M = M -> (k = Aone)%A \/ (M = mat0).
  Proof.
    intros. destruct M.
    unfold mcmul in H. apply meq_iff in H. simpl in H.
    apply (dlcmul_fixpoint_imply_k1_or_dlzero (r:=r) (c:=c)) in H; auto.
    destruct H; auto. right. apply meq_iff; auto.
  Qed.
  
  (** (M1 <> 0 /\ M2 <> 0 /\ k * M1 = M2) -> k <> 0 *)
  Lemma mcmul_eq_mat_implfy_not_k0 : forall {r c} (M1 M2 : mat r c) k,
      M1 <> mat0 -> M2 <> mat0 -> k c* M1 = M2 -> k <> Azero.
  Proof.
    intros. intro. destruct M1,M2.
    rewrite <- meq_iff in H,H0,H1. simpl in *. unfold dmap in H1.
    rewrite (map_ext) with (g:=map (fun x=>Azero)) (l:=mdata0) in H1.
    - pose proof (@dmap_eq_zero _ Azero r c mdata0). unfold dmap in H3.
      rewrite H3 in H1; auto.
    - intros. apply map_ext. intros. rewrite H2. ring.
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


(** ** Matrix_1x1 to scalar *)
Section mat2scalar.

  Context {A} (Azero : A).
  
  Definition mat2scalar (M : mat A 1 1) : A.
  Proof.
    destruct M as [dl].
    refine (hd Azero (hd [] dl)).
  Defined.
  
End mat2scalar.

Module coordinate_transform_test.

  Import Reals.
  Open Scope R.
  
  (* ref:
  https://en.wikipedia.org/wiki/Matrix_(mathematics)#Basic_operations
   *)

  Infix "*" := Rmult.
  Infix "+" := Rplus.
  Infix "+" := (madd (Aadd:=Rplus)) : mat_scope.
  Infix "*" := (mmul (Aadd:=Rplus) (Amul:=Rmult) (Azero:=R0)) : mat_scope.
  Infix "c*" := (mcmul (Amul:=Rmult)) : mat_scope.

  Open Scope mat_scope.

  Definition M1 := l2m 0 2 3 [[1;3;1];[1;0;0]].
  Definition M2 := l2m 0 2 3 [[0;0;5];[7;5;0]].
  Definition M3 := l2m 0 2 3 [[1;3;6];[8;5;0]].
  Example madd_m1_m2_eq_m3 : M1 + M2 = M3.
  Proof. apply meq_iff. cbn. repeat f_equal; ring. Qed.

  Definition M4 := l2m 0 2 3 [[1; 8;-3];[4;-2; 5]].
  Definition M5 := l2m 0 2 3 [[2;16;-6];[8;-4;10]].
  Example mscale_2_m4_eq_m5 : 2 c* M4 = M5.
  Proof. apply meq_iff. cbn. repeat f_equal; ring. Qed.
  
  Definition M6 := l2m 0 2 3 [[1;2;3];[0;-6;7]].
  Definition M7 := l2m 0 3 2 [[1;0];[2;-6];[3;7]].
  Example mtrans_m6_eq_m7 : M6\T = M7.
  Proof. apply meq_iff. cbn. auto. Qed.
  
  Variable θ ψ φ : R.
  Definition Rx (α : R) : mat 3 3 :=
    mk_mat_3_3
      1         0           0
      0         (cos α)     (sin α)
      0         (-sin α)%R    (cos α).

  Definition Ry (β : R) : mat 3 3 :=
    mk_mat_3_3
      (cos β)   0           (-sin β)%R
      0         1           0
      (sin β)   0           (cos β).

  Definition Rz (γ : R) : mat 3 3 :=
    mk_mat_3_3 
      (cos γ)   (sin γ)   0
      (-sin γ)  (cos γ)   0
      0         0         1.

  Definition R_b_e_direct : mat 3 3 :=
    (mk_mat_3_3
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
  Proof. apply meq_iff. cbn. repeat (f_equal; try ring). Qed.
  
End coordinate_transform_test.
