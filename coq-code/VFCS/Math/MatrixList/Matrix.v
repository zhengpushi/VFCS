(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Record-List model
  author    : ZhengPu Shi
  date      : 2021.12

  remark    :
 *)


Require Export TupleExt Hierarchy.
Require Export ListExt.
Require Import Extraction.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.

(* Global Hint Rewrite map_length seq_length : list. *)


(* ======================================================================= *)
(** ** Definition of Matrix Type *)
Section mat_def.

  (* I have another idea, if the properties mheight and mwidth should defined 
     with a boolean equation, such as "legnth mdata =? r" ? Thus the proof effort
     should be reduced or automated? *)
  Record mat {A : Type} (r c : nat) : Type :=
    mk_mat {
        mdata : dlist A;
        mheight : length mdata = r;
        mwidth : width mdata c
      }.
  
End mat_def.

Arguments mk_mat {A r c}.
Arguments mdata {A r c}.
Arguments mheight {A r c}.
Arguments mwidth {A r c}.


(* matrix can be used as a dlist *)
(* Coercion mdata : mat >-> dlist. *)


(** square matrix type *)
Definition smat {A} n := (@mat A n n).

(** Vector type *)
Definition rvec {A} n := (@mat A 1 n).
Definition cvec {A} n := (@mat A n 1).


(* ======================================================================= *)
(** ** Equality of matrix *)


(* Matrix equality could be proved by the eqaulities of size and data *)
Lemma meq_iff : forall {A r c} (M1 M2 : @mat A r c),
    mdata M1 = mdata M2 <-> M1 = M2.
Proof.
  intros. destruct M1 as [d1 ph1 pw1], M2 as [d2 ph2 pw2]; simpl in *.
  split; intros.
  - subst. f_equal; apply proof_irrelevance.
  - inversion H. auto.
Qed.

Corollary meq_if_mdata : forall {A r c} (M1 M2 : @mat A r c),
    mdata M1 = mdata M2 -> M1 = M2.
Proof. intros. apply meq_iff. auto. Qed.


(* ======================================================================= *)
(** ** Get element of a matrix *)
Section mnth.
  Context {A} {Azero : A} {r c : nat}.

  Definition mnth (M : mat r c) (ri ci : nat) : A :=
    nth ci (nth ri (mdata M) []) Azero.

  Notation "M $ i $ j" := (mnth M i j).

  Lemma meq_iff_mnth : forall (M1 M2 : mat r c),
      M1 = M2 <->
        (forall (ri cj : nat), ri < r -> cj < c -> M1 $ ri $ cj = M2 $ ri $ cj).
  Proof.
    intros. rewrite <- meq_iff.
    destruct M1 as [d1 ph1 pw1], M2 as [d2 ph2 pw2]; unfold mnth; simpl.
    apply dlist_eq_iff_nth_nth; auto.
  Qed.

End mnth.

Arguments mnth {A} Azero {r c}.

Global Hint Unfold mnth : core.
Notation "M $ i $ j " := (mnth _ M i j) : mat_scope.
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



(** ** Convert between function and matrix *)
Section f2m_m2f.
  
  Context {A} (Azero : A).

  Definition f2m {r c} (f : nat -> nat -> A) : @mat A r c :=
    mk_mat (@f2dl A r c f) (f2dl_length r c f) (f2dl_width r c f).

  (** (f2m f)[i,j] = f i j *)
  Lemma mnth_f2m : forall {r c} f i j,
      i < r -> j < c -> mnth Azero (@f2m r c f) i j = f i j.
  Proof. intros. unfold mnth,f2m. simpl. rewrite nth_f2dl; auto. Qed.
    
  Definition m2f {r c} (M : mat r c) : (nat -> nat -> A) :=
    dl2f (r:=r) (c:=c) (Azero:=Azero) (mdata M).

End f2m_m2f.


(* (* ======================================================================= *) *)
(* (** ** Matrix Automation *) *)

(* (** Useful tactic for solving A = B for concrete A, B *) *)

(* (** Solve i < 0 *) *)
(* Ltac solve_end := *)
(*   match goal with *)
(*   | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H *)
(*   end. *)

(* (** Convert mat to function *) *)
(* Ltac mat2fun := *)
(*   repeat match goal with *)
(*     | M : mat ?r ?c |- _ => destruct m as [m]; simpl in * *)
(*     end. *)

(* (** Solve mnth *) *)
(* Ltac solve_mnth := *)
(*   repeat match goal with *)
(*     | H: context [ mnth ] |- _ => unfold mnth in H *)
(*     | |- context [mnth] => unfold mnth; simpl *)
(*     | H: context [?c >? ?j]  |- _ => destruct (Nat.ltb_spec0 j c) in H *)
(*     | |- context[ (?c >? ?j)%nat ] => destruct (Nat.ltb_spec0 j c) *)
(*     end; simpl in *; try easy. *)
(*     (* end; simpl; try easy. *) *)

(* (** Convert meq to element equal *) *)
(* (**  *)
(*   Modification of this tactic: *)
(*   1. use an alternate lemma NatExt.lt_S_n instead of lt_S_n, because Coq report it  *)
(*      is deprecated since 8.16 *)
(*   2. disable "clear Hi, clear Hj", because these two conditions are needed in some *)
(*      cases.  *)
(*   3. call "mat_to_fun" first, to unpack the mat structure to a function *)
(*  *) *)
(* Ltac by_cell := *)
(*   intros; *)
(*   let i := fresh "i" in *)
(*   let j := fresh "j" in *)
(*   let Hi := fresh "Hi" in *)
(*   let Hj := fresh "Hj" in *)
(*   intros i j Hi Hj; simpl; try solve_end; *)
(*   mat2fun; repeat solve_mnth; *)
(*   repeat (destruct i as [|i]; simpl; *)
(*           [|apply NatExt.lt_S_n in Hi]; try solve_end); *)
(*   (* clear Hi; *) *)
(*   repeat (destruct j as [|j]; simpl; *)
(*           [|apply NatExt.lt_S_n in Hj]; try solve_end) *)
(* (* clear Hj *) *)
(* . *)

(* Global Ltac lma := *)
(*   by_cell; *)
(*   try ( *)
(*       try lia; *)
(*       try (compute; ring); *)
(*       try (compute; field); *)
(*       try (compute; easy)); *)
(*   simpl. *)

(* 矩阵相等的自动化简 (linear matrix algebra) *)
Ltac lma :=
  (* 需要重复执行多个动作，也不要报错，所以 repeat 正合适 *)
  repeat match goal with
    (* 凡是 M1 = M2，转换为 (mdata M1) = (mdata M2) *)
    | |- @eq (Matrix.mat _ _) _ _ => apply meq_if_mdata; simpl
    | |- @eq (Matrix.smat _) _ _ => apply meq_if_mdata; simpl
    (* 列表相等，转换为头尾各自相等 *)
    | |- cons _ _ = cons _ _ => f_equal
    end.




(** ** matrix with specific size *)

Section mat_specific.
  Context {A : Type}.
  Variable r c : nat.
  Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : A.

  (** *** Create matrix *)
  Definition mk_mat_0_c : @mat A 0 c.
    refine (mk_mat [] _ _); auto. constructor; auto. Defined.

  Definition mk_mat_r_0 : @mat A r 0.
    refine (mk_mat (dnil r) _ _); auto.
    apply dnil_length. apply dnil_width. Defined.

  Definition mk_mat_1_c (d : list A) : @mat A 1 (length d).
    refine (mk_mat [d] _ _); auto. constructor; auto. Defined.
  
  Definition mk_mat_r_1 (d : list A) : @mat A (length d) 1.
    refine (mk_mat (row2col d) _ _); auto.
    rewrite row2col_length; auto. apply row2col_width. Defined.

  Definition mk_mat_1_1 : @mat A 1 1.
    refine (mk_mat [[a11]] _ _); auto. constructor; auto. Defined.

  Definition mk_mat_1_2 : @mat A 1 2.
    refine (mk_mat [[a11;a12]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_2_1 : @mat A 2 1.
    refine (mk_mat [[a11];[a21]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_2_2 : @mat A 2 2.
    refine (mk_mat [[a11;a12];[a21;a22]] _ _); auto. constructor; auto. Defined.

  Definition mk_mat_1_3 : @mat A 1 3.
    refine (mk_mat [[a11;a12;a13]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_2_3 : @mat A 2 3.
    refine (mk_mat [[a11;a12;a13];[a21;a22;a23]] _ _); auto.
    constructor; auto. Defined.
  Definition mk_mat_3_1 : @mat A 3 1.
    refine (mk_mat [[a11];[a21];[a31]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_3_2 : @mat A 3 2.
    refine (mk_mat [[a11;a12];[a21;a22];[a31;a23]] _ _); auto.
    constructor; auto. Defined.
  Definition mk_mat_3_3 : @mat A 3 3.
    refine (mk_mat [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]] _ _); auto.
    constructor; auto. Defined.

  Definition mk_mat_1_4 : @mat A 1 4.
    refine (mk_mat [[a11;a12;a13;a14]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_4_1 : @mat A 4 1.
    refine (mk_mat [[a11];[a21];[a31];[a41]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_4_4 : @mat A 4 4.
    refine (mk_mat [[a11;a12;a13;a14];[a21;a22;a23;a24];
                    [a31;a32;a33;a34];[a41;a42;a43;a44]] _ _); auto.
    constructor; auto. Defined.


  (** *** Decompose matrix *)

  (* Lemma mat2elems_2_2 : forall (M : @mat A 2 2), *)
  (*     mdata M = [[d!0!0; d!0!1]; [d!1!0; d!1!1]]. *)
  (* Proof. *)
  (*   intros. repeat (destruct d; simpl in *; repeat (solve_dlist2elems); *)
  (*                   try apply list2elems_2; auto). *)
  (* Qed. *)
  
End mat_specific.


(** ** Convert between dlist and mat *)

Section l2m_m2l.
  Context {A : Type} (Azero : A).


  (** Get fixed-length list *)
  Fixpoint listN (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => (hd Azero l) :: (listN (tl l) n')
    end.
  
  Lemma listN_length : forall (l : list A) (n : nat), length (listN l n) = n.
  Proof. intros l n. gd l. induction n; intros; simpl; auto. Qed.
  
  Lemma listN_eq : forall (l : list A) (n : nat), length l = n -> listN l n = l.
  Proof.
    intros l n. gd l. induction n; intros; simpl.
    - apply length_zero_iff_nil in H. easy.
    - destruct l. easy. inv H. f_equal; auto.
  Qed.
  
  (* Get fixed-shape dlist *)
  Fixpoint dlistN (dl : dlist A) (r c : nat) : dlist A :=
    match r with
    | 0 => []
    | S n' => (listN (hd nil dl) c) :: (dlistN (tl dl) n' c)
    end.
  
  Lemma dlistN_length : forall (dl : dlist A) (r c : nat), length (dlistN dl r c) = r.
  Proof. intros dl r. gd dl. induction r; intros; simpl; auto. Qed.
  
  Lemma dlistN_width : forall (dl : dlist A) (r c : nat), width (dlistN dl r c) c.
  Proof.
    unfold width; intros dl r. revert dl.
    induction r; intros; simpl; auto. constructor; auto.
    apply listN_length.
  Qed.
  
  Lemma dlistN_eq : forall (dl : dlist A) (r c : nat),
      length dl = r -> width dl c -> dlistN dl r c = dl.
  Proof.
    intros dl r. gd dl. induction r; intros; simpl; auto.
    - apply length_zero_iff_nil in H. easy.
    - destruct dl. easy. inv H. inv H0.
      rewrite IHr; auto. simpl. rewrite listN_eq; auto.
  Qed.

  Definition l2m (r c : nat) (dl : dlist A) : mat r c :=
    mk_mat (dlistN dl r c) (dlistN_length dl r c) (dlistN_width dl r c).
  
  Lemma l2m_inj : forall {r c} (d1 d2 : dlist A),
      length d1 = r -> width d1 c ->
      length d2 = r -> width d2 c ->
      d1 <> d2 -> l2m r c d1 <> l2m r c d2.
  Proof.
    intros. unfold l2m. intro. inversion H4.
    rewrite !dlistN_eq in H6; auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (M : mat r c), (exists d, l2m r c d = M).
  Proof.
    intros. destruct M as [d ph pw].
    exists d. unfold l2m; simpl.
    apply meq_iff; simpl. apply dlistN_eq; auto.
  Qed.

  (** mat to dlist *)
  Definition m2l {r c} (M : mat r c) : dlist A := mdata M.

  Lemma m2l_length : forall {r c} (M : mat r c), length (m2l M) = r.
  Proof. intros. apply mheight. Qed.

  Lemma m2l_width : forall {r c} (M : mat r c), width (m2l M) c.
  Proof. intros. apply mwidth. Qed.

  Lemma m2l_inj : forall {r c} (M1 M2 : mat r c), M1 <> M2 -> m2l M1 <> m2l M2.
  Proof. intros. rewrite meq_iff. auto. Qed.

  Lemma m2l_surj : forall {r c} (d : dlist A),
      length d = r -> width d c -> (exists M : mat r c, m2l M = d).
  Proof. intros. exists (mk_mat d H H0). auto. Qed.

  (* relation between l2m and M2l *)
  Lemma l2m_m2l_id : forall {r c} (M : mat r c), (@l2m r c (m2l M)) = M.
  Proof.
    intros. destruct M; simpl. apply meq_iff; simpl. apply dlistN_eq; auto.
  Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : dlist A),
      length dl = r -> width dl c -> m2l (@l2m r c dl) = dl.
  Proof. intros. unfold l2m,m2l. simpl. apply dlistN_eq; auto. Qed.

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

  
(** ** Construct matrix with two matrices *)
Section mapp.
  Context {A : Type}.
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (M1 : @mat A r1 c) (M2 : @mat A r2 c)
    : @mat A (r1 + r2) c.
    refine (mk_mat (mdata M1 ++ mdata M2) _ _).
    - rewrite app_length. rewrite !mheight. auto.
    - apply app_width. split. apply M1. apply M2.
  Defined.

  (** Append matrix by column *)
  Definition mappc {r c1 c2} (M1 : @mat A r c1) (M2 : @mat A r c2)
    : @mat A r (c1 + c2).
    refine (mk_mat (dlappc (mdata M1) (mdata M2)) _ _).
    - apply dlappc_length. apply mheight. apply mheight.
    - apply dlappc_width. apply mwidth. apply mwidth.
  Defined.
  
End mapp.


(** ** Elementary Row Transform *)

Section RowTrans.
  Context `{HRing : ARing}.

  (** 第 i 行乘以 k *)
  Definition mrowK {r c} (m : @mat A r c) (i : nat) (k : A) : @mat A r c.
    refine (mk_mat (dlistRowK (Amul:=Amul) (mdata m) i k) _ _).
    - eapply dlistRowK_length; apply m.
    - eapply dlistRowK_width; apply m.
  Defined.
  
  (** 交换 i1,i2 两行 *)
  Definition mrowSwap {r c} (m : @mat A r c) (i1 i2 : nat) : @mat A r c.
    refine (mk_mat (dlistRowSwap (mdata m) i1 i2) _ _).
    - apply dlistRowSwap_length with (c:=c); apply m.
    - apply dlistRowSwap_width with (r:=r); apply m.
  Defined.

  (** 第 i1 行的 k 倍 加到第 i2 行 *)
  Definition mrowKAdd {r c} (m : @mat A r c) (i1 i2 : nat) (k : A) : @mat A r c.
    refine (mk_mat (dlistRowKAdd (Aadd:=Aadd)(Amul:=Amul) (mdata m) i1 i2 k) _ _).
    - eapply dlistRowKAdd_length; apply m.
    - eapply dlistRowKAdd_width; apply m.
  Defined.

End RowTrans.

Require QcExt.
Section test.
  Import QcExt.
  Let m1 : smat 2 := l2m 0 2 2 (Q2Qc_dlist [[1;2];[3;4]]%Q).
  
  Notation mrowK := (mrowK (Amul:=Qcmult)).
  Notation mrowKAdd := (mrowKAdd (Aadd:=Qcplus) (Amul:=Qcmult)).
  
  (* Compute mrowK m1 0 (Q2Qc 2). *)
  (* Compute mrowK m1 1 (Q2Qc 2). *)
  (* Compute mrowK m1 2 (Q2Qc 2). *)
  
  (* Compute mrowSwap m1 0 0. *)
  (* Compute mrowSwap m1 0 1. *)
  (* Compute mrowSwap m1 0 2. *)

  (* Compute mrowKAdd m1 0 1 (Q2Qc 2). *)
  (* Compute mrowKAdd m1 1 0 (Q2Qc 2). *)
End test.
          


(** ** Matrix map *)
Section mmap.

  Context {A B : Type} {r c : nat}.
  Variable f : A -> B.
  
  Definition mmap (M : @mat A r c) : @mat B r c.
    refine (mk_mat (dmap f (mdata M)) _ _).
    - rewrite dmap_length. apply M.
    - apply dmap_width. apply M.
  Defined.

End mmap.


(** ** Matrix map2 to a dlist *)
Section mmap2dl.
  
  Context {A B C : Type} {r c : nat}.
  Variable f : A -> B -> C.

  Definition mmap2dl (M1 : @mat A r c) (M2 : @mat B r c) : dlist C :=
    dmap2 f (mdata M1) (mdata M2).

  Lemma mmap2dl_length : forall (M1 : @mat A r c) (M2 : @mat B r c),
      length (mmap2dl M1 M2) = r.
  Proof. 
    intros; simpl. unfold mmap2dl. rewrite dmap2_length;
      repeat rewrite mheight; auto.
  Qed.

  Lemma mmap2dl_width : forall (M1 : @mat A r c) (M2 : @mat B r c),
      width (mmap2dl M1 M2) c.
  Proof. 
    intros; simpl. unfold mmap2dl. apply dmap2_width; apply mwidth.
  Qed.

End mmap2dl.


(** ** Matrix map2 *)
Section mmap2.

  Context {A B C : Type} {r c : nat}.
  
  Definition mmap2 (f : A -> B -> C) (M1 : @mat A r c) (M2 : @mat B r c) : @mat C r c.
    refine (mk_mat (dmap2 f (mdata M1) (mdata M2)) _ _).
    rewrite dmap2_length. apply mheight. rewrite !mheight; auto.
    apply dmap2_width; apply mwidth.
  Defined.

End mmap2.


(** ** Matrix map2 with same base type *)
Section mmap2_sametype.

  Context `{Commutative A Aadd}.
  Lemma mmap2_comm : forall {r c} (M1 M2 : mat r c),
      mmap2 Aadd M1 M2 = mmap2 Aadd M2 M1.
  Proof. intros. apply meq_iff; simpl. apply dmap2_comm. Qed.
  
  Context `{Associative A Aadd}.
  Lemma mmap2_assoc : forall {r c} (M1 M2 M3 : mat r c),
      mmap2 Aadd (mmap2 Aadd M1 M2) M3 = mmap2 Aadd M1 (mmap2 Aadd M2 M3).
  Proof. intros. apply meq_iff; simpl. apply dmap2_assoc. Qed.
  
End mmap2_sametype.


(* ==================================== *)
(** ** matrix column shift *)
Section mcsh.

  Context {A} (Azero : A).
  Notation "M $ i $ j " := (mnth Azero M i j) : mat_scope.

  (** left shift column. *)
  (*     [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *)
  Definition mcshl {r c} (M : @mat A r c) (k : nat) : @mat A r c :=
    f2m (fun i j => M $ i $ (j + k)).

  (** right shift column. *)
  (*     [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *)
  Definition mcshr {r c} (M : mat r c) (k : nat) : mat r c :=
    f2m (fun i j => if j <? k then Azero else (M $ i $ (j - k))).

  (** left loop shift column. *)
  (*     [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *)
  Definition mclshl {r c} (M : mat r c) (k : nat) : mat r c :=
    f2m (fun i j => M $ i $ (nat_lshl c j k)).

  (** right shift column *)
  Definition mclshr {r c} (M : mat r c) (k : nat) : mat r c :=
    f2m (fun i j => M $ i $ (nat_lshr c j k)).

End mcsh.

Section test.
  Let m1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l (mcshl 0 m1 1). *)
  (* Compute m2l (mcshr 0 m1 1). *)
  (* Compute m2l (mclshl 0 m1 1). *)
  (* Compute m2l (mclshr 0 m1 1). *)
End test.



(** ** matrix transpose *)
Section mtrans.

  Context {A : Type}.
  
  Definition mtrans {r c} (M : @mat A r c) : mat c r :=
    mk_mat (dltrans (mdata M) c) 
      (dltrans_length (mdata M) c (mwidth M))
      (dltrans_width (mdata M) r c (mheight M) (mwidth M)).
  
  (** Transpose twice return back *)
  Lemma mtrans_trans : forall {r c} (M : mat r c), mtrans (mtrans M) = M.
  Proof. intros. apply meq_iff; simpl. apply dltrans_dltrans; apply M. Qed.

  Context (Azero : A).
  Notation "M $ i $ j " := (mnth Azero M i j) : mat_scope.
  
  (** (M\T)[i,j] = M[j,i] *)
  Lemma mnth_mtrans : forall {r c} (M : mat r c) i j,
      i < r -> j < c -> (mtrans M)$j$i = M$i$j.
  Proof.
    intros. destruct M as [m pH pW]. unfold mtrans, mnth. simpl.
    rewrite dltrans_ij with (r:=r); auto.
  Qed.

End mtrans.

Notation "M \T" := (mtrans M) : mat_scope.



(** ** Diagonal matrix *)
Section mdiag.
  Context {A} (Azero:A).
  Notation "M $ i $ j " := (mnth Azero M i j) : mat_scope.
  
  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (M : smat n) : Prop :=
    forall i j, i < n -> j < n -> i <> j -> M$i$j = Azero.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (M : smat n), mdiag M -> M\T = M.
  Proof.
    intros. destruct M as [d pH pW]. apply meq_iff. simpl in *.
    rewrite (dlist_eq_iff_nth_nth n n (Azero:=Azero)); auto with mat.
    intros. rewrite (dltrans_ij d n n); auto.
    unfold mdiag in H. unfold mnth in H. simpl in H.
    destruct (i =? j) eqn:E1.
    - apply Nat.eqb_eq in E1. subst. auto.
    - apply Nat.eqb_neq in E1. rewrite !H; auto.
  Qed.

  (** Construct a diagonal matrix *)
  Definition mdiagMk n (l : list A) : @smat A n :=
    f2m (fun i j => if i =? j then nth i l Azero else Azero).

  (** mdiagMk is correct *)
  Lemma mdiagMk_spec : forall {n} (l : list A), mdiag (@mdiagMk n l).
  Proof.
    intros. hnf. intros. unfold mdiagMk. rewrite mnth_f2m; auto.
    apply Nat.eqb_neq in H1. rewrite H1. auto.
  Qed.

  (** (mdiagMk l)[i,j] = 0 *)
  Lemma mdiagMk_ij : forall {n} (l : list A) i j,
      i < n -> j < n -> i <> j -> (mdiagMk n l)$i$j = Azero.
  Proof.
    intros. pose proof (@mdiagMk_spec n l).
    unfold mdiag in H2. auto.
  Qed.

  (** (mdiagMk l)[i,i] = l[i] *)
  Lemma mdiagMk_ii : forall {n} (l : list A) i,
      i < n -> (mdiagMk n l)$i$i = nth i l Azero.
  Proof.
    intros. unfold mdiagMk. rewrite mnth_f2m; auto.
    rewrite Nat.eqb_refl. auto.
  Qed.

End mdiag.



(** ** matrix algebra *)
(* addition,opposition,subtraction, trace, scalar multiplication, multiplication *)
Section malg.

  Context `{AG:AGroup A Aadd Azero Aopp} {Aone : A}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b)).
  Infix "-" := Asub : A_scope.

  Notation "A $ i $ j " := (@mnth _ Azero _ _ A i j).

  (** *** Zero matrix *)
  Definition mat0 {r c} := mk_mat (dlzero Azero r c) dlzero_length dlzero_width.
  
  (** mat0\T = mat0 *)
  Lemma mtrans_0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. apply meq_iff; simpl. apply dltrans_zero. Qed.

  
  (** *** Unit matrix *)
  Definition mat1 {n} := mk_mat (dlunit Azero Aone n) dlunit_length dlunit_width.

  (** mat1\T = mat1 *)
  Lemma mtrans_1 : forall {n : nat}, (@mat1 n)\T = mat1.
  Proof. intros. apply meq_iff; simpl. apply dltrans_dlunit. Qed.

  Notation "M $ i $ j " := (mnth Azero M i j).

  (** i < n -> j < n -> i <> j -> mat1[i,j] = 0 *)
  Lemma mat1_ij : forall {n} i j,
      i < n -> j < n -> i <> j -> @mat1 n $ i $ j = Azero.
  Proof.
    unfold mat1,mnth. simpl.
    induction n; intros. lia. 
    destruct i; simpl.
    - destruct j; simpl. lia. apply nth_repeat.
    - destruct j.
      + rewrite consc_nthj0 with (r:=n); try lia.
        apply nth_repeat. apply repeat_length. apply dlunit_length.
      + rewrite (consc_nthSj) with (r:=n)(c:=n); try lia.
        apply IHn; lia. apply repeat_length. apply dlunit_length.
  Qed.

  (** i < n -> mat1[i,i] = 1 *)
  Lemma mat1_ii : forall {n} i, i < n -> (@mat1 n) $ i $ i = Aone.
  Proof.
    unfold mat1,mnth. simpl.
    induction n; intros. lia.
    destruct i; simpl. auto.
    rewrite consc_nthSj with (r:=n)(c:=n); try lia.
    apply IHn. lia.
    apply repeat_length. apply dlunit_length.
  Qed.

  (** mat1 is diagonal matrix *)
  Lemma mat1_diag : forall {n : nat}, mdiag Azero (@mat1 n).
  Proof.
    intros. hnf. intros. unfold mat1,mnth. simpl. apply dlunit_ij; auto.
  Qed.


  (** *** Matrix Trace *)
  
  Definition mtrace {n : nat} (M : @smat A n) : A :=
    let l : list A := map (fun i => nth i (nth i (mdata M) []) Azero) (seq 0 n) in
    fold_left Aadd l Azero.

  (** tr(M\T) = tr(M) *)
  Lemma mtrace_trans : forall {n} (M : @smat A n), mtrace (M\T) = mtrace(M).
  Proof.
    unfold mtrace. intros. f_equal.
    destruct M as [d pH pW]; simpl.
    f_equal. apply dltrans_ii_fun; auto.
  Qed.

  
  (** *** Matrix Addition *)
  Definition madd {r c} (M1 M2 : mat r c) : mat r c := mmap2 Aadd M1 M2.
  Infix "+" := madd : mat_scope.

  Lemma madd_comm : forall {r c} (M1 M2 : mat r c), M1 + M2 = M2 + M1.
  Proof. intros. apply meq_iff, map2_comm.
         constructor. apply map2_comm. apply AG. Qed.
  
  Lemma madd_assoc : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) + M3 = M1 + (M2 + M3).
  Proof. intros. apply meq_iff, map2_assoc.
         constructor. apply map2_assoc. apply AG. Qed.
  
  (** 0 + M = M *)
  Lemma madd_0_l : forall {r c} (M : mat r c), mat0 + M = M.
  Proof. intros. apply meq_iff, dladd_zero_l; apply M. Qed.

  (** M + 0 = M *)
  Lemma madd_0_r : forall {r c} (M : mat r c), M + mat0 = M.
  Proof. intros. apply meq_iff, dladd_zero_r; apply M. Qed.
  
  Instance Associative_madd : forall r c, @Associative (mat r c) madd.
  Proof. intros. constructor. apply madd_assoc. Qed.

  Instance Commutative_madd : forall r c, @Commutative (mat r c) madd.
  Proof. intros. constructor. apply madd_comm. Qed.

  Instance IdentityLeft_madd : forall r c, @IdentityLeft (mat r c) madd mat0.
  Proof. intros. constructor. apply madd_0_l. Qed.

  Instance IdentityRight_madd : forall r c, @IdentityRight (mat r c) madd mat0.
  Proof. intros. constructor. apply madd_0_r. Qed.

  Instance Monoid_madd : forall r c, Monoid (@madd r c) mat0.
  Proof. intros. repeat constructor; intros.
         apply associative. apply identityLeft. apply identityRight. Qed.
  

  (** (M1+M2)[i,j] = M1[i,j] + M2[i,j] *)
  Lemma mnth_madd : forall {r c} (M1 M2 : mat r c) i j,
      (M1 + M2)%M $ i $ j = (M1$i$j + M2$i$j)%A.
  Proof.
    intros. unfold madd. unfold mnth.
    destruct M1 as [d1 pH1 pW1], M2 as [d2 pH2 pW2]. simpl. unfold dmap2.
    destruct (i <? r) eqn:Ei.
    - apply Nat.ltb_lt in Ei.
      rewrite map2_nth with (n:=r); auto.
      destruct (j <? c) eqn:Ej.
      + apply Nat.ltb_lt in Ej.
        rewrite map2_nth with (n:=c); auto.
        * rewrite !dlist_nth_length with (c:=c); auto; lia.
        * rewrite !dlist_nth_length with (c:=c); auto; lia.
      + apply Nat.ltb_ge in Ej. rewrite !nth_overflow.
        * monoid_simpl.
        * rewrite !dlist_nth_length with (c:=c); auto; lia.
        * rewrite !dlist_nth_length with (c:=c); auto; lia.
        * rewrite map2_length with (n:=c); auto.
          rewrite !dlist_nth_length with (c:=c); auto; lia.
          rewrite !dlist_nth_length with (c:=c); auto; lia.
    - apply Nat.ltb_ge in Ei.
      rewrite !(@nth_overflow _ _ i); try lia.
      + simpl. destruct j; monoid_simpl.
      + rewrite map2_length with (n:=r); auto.
  Qed.

  (** (M1 + M2)\T = M1\T + M2\T *)
  Lemma mtrans_madd : forall {r c} (M1 M2 : mat r c), (M1 + M2)\T = M1\T + M2\T.
  Proof.
    intros. unfold madd. unfold mtrans.
    destruct M1 as [d1 pH1 pW1], M2 as [d2 pH2 pW2]; simpl.
    apply meq_iff; simpl. apply dltrans_dmap2; auto. lia.
  Qed.

  (** tr(M1 + M2) = tr(M1) + tr(M2) *)
  Lemma mtrace_madd : forall {n} (M1 M2 : @smat A n),
      (mtrace (M1 + M2)%M = mtrace(M1) + mtrace(M2))%A.
  Proof.
    intros. unfold madd. unfold mtrace.
    destruct M1 as [d1 pH1 pW1], M2 as [d2 pH2 pW2]; simpl. unfold dmap2.
    apply fold_left_add with (n:=n);
      try rewrite map_length, seq_length; auto.
    intros.
    rewrite !nth_map_seq; auto.
    rewrite !Nat.add_0_r.
    rewrite (nth_nth_map2_map2_rw _ d1 d2 n n); auto.
  Qed.



  (** *** Matrix Opposition *)
  Definition mopp {r c} (M : mat r c) : mat r c := mmap Aopp M.
  Notation "- M" := (mopp M) : mat_scope.
  
  Lemma madd_opp_l : forall {r c} (M : mat r c), (-M) + M = mat0.
  Proof.
    intros. destruct M as [d pH pW]. unfold madd, mopp. apply meq_iff; simpl.
    unfold dmap2,dmap,dlzero. revert c d pH pW. induction r; intros; simpl.
    - apply length_zero_iff_nil in pH. subst. auto.
    - destruct d. easy. simpl. f_equal.
      + simpl in *. inv pW. inv pH. clear H2. induction l; auto.
        simpl. f_equal; auto. group_simp.
      + apply IHr; auto. inv pW. auto.
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
  Proof.
    intros. split; intros.
    - rewrite <- H. rewrite mopp_mopp. easy.
    - rewrite H. rewrite mopp_mopp. easy. 
  Qed.

  (** - (mat0) = mat0 *)
  Lemma mopp_mat0 : forall {r c:nat}, - (@mat0 r c) = mat0.
  Proof. intros. apply group_inv_id. Qed.

  (** - (m1 + m2) = (-m1) + (-m2) *)
  Lemma mopp_madd : forall {r c : nat} (M1 M2 : mat r c), - (M1 + M2) = (-M1) + (-M2).
  Proof. intros. rewrite group_inv_distr. apply commutative. Qed.

  (** (- M)\T = - (M\T) *)
  Lemma mtrans_mopp : forall {r c} (M : mat r c), (- M)\T = - (M\T).
  Proof.
    intros. destruct M as [d pH pW].
    unfold mopp,mtrans. apply meq_iff; simpl.
    revert r c pH pW. induction d; intros; simpl in *.
    - rewrite dmap_dnil. auto.
    - destruct r. lia. inversion pH. inversion pW.
      rewrite IHd with (r:=r); auto; try lia.
      rewrite consc_map_dmap. auto.
  Qed.

  (** tr(- M) = - (tr(m)) *)
  Lemma mtrace_mopp : forall {n} (M : smat n), mtrace(-M) = (- (mtrace M))%A.
  Proof.
    intros. unfold mopp. unfold mtrace.
    destruct M as [d pH pW]. simpl.
    apply fold_left_opp with (n:=n);
      try rewrite map_length, seq_length; auto.
    intros.
    rewrite !nth_map_seq; auto.
    rewrite !Nat.add_0_r. unfold dmap.
    rewrite (nth_nth_map_map) with (r:=n)(c:=n); auto.
  Qed.
  
  
  (** *** Matrix Subtraction *)
  Definition msub {r c} (M1 M2 : mat r c) : mat r c := M1 + (-M2).
  Infix "-" := msub : mat_scope.

  (** M1 - M2 = - (M2 - M1) *)
  Lemma msub_comm : forall {r c} (M1 M2 : mat r c), M1 - M2 = - (M2 - M1).
  Proof. intros. unfold msub. rewrite group_inv_distr.
         rewrite group_inv_inv. auto. Qed.

  (** (M1 - M2) - M3 = M1 - (M2 + M3) *)
  Lemma msub_assoc : forall {r c} (M1 M2 M3 : mat r c),
      (M1 - M2) - M3 = M1 - (M2 + M3).
  Proof. intros. unfold msub. group_simp. f_equal.
         rewrite group_inv_distr. apply commutative. Qed.

  (** (M1 + M2) - M3 = M1 + (M2 - M3) *)
  Lemma msub_assoc1 : forall {r c} (M1 M2 M3 : mat r c), (M1 + M2) - M3 = M1 + (M2 - M3).
  Proof. intros. unfold msub. group_simp. Qed.

  (** (M1 - M2) - M3 = M1 - (M3 - M2) *)
  Lemma msub_assoc2 : forall {r c} (M1 M2 M3 : mat r c), (M1 - M2) - M3 = (M1 - M3) - M2.
  Proof. intros. unfold msub. group_simp. f_equal. apply commutative. Qed.
  
  (** 0 - M = - M *)
  Lemma msub_0_l : forall {r c} (M : mat r c), mat0 - M = - M.
  Proof. intros. unfold msub. group_simp. Qed.
  
  (** M - 0 = M *)
  Lemma msub_0_r : forall {r c} (M : mat r c), M - mat0 = M.
  Proof. intros. unfold msub. rewrite (@group_inv_id _ madd mat0); auto.
         group_simp. apply AGroup_madd. Qed.
  
  (** M - M = 0 *)
  Lemma msub_self : forall {r c} (M : mat r c), M - M = mat0.
  Proof. intros. unfold msub. group_simp. Qed.

  (** (M1 - M2)\T = M1\T - M2\T *)
  Lemma mtrans_msub : forall {r c} (M1 M2 : mat r c), (M1 - M2)\T = M1\T - M2\T.
  Proof. intros. unfold msub. rewrite mtrans_madd. f_equal. apply mtrans_mopp. Qed.

  (** tr(M1 - M2) = tr(M1) - tr(M2) *)
  Lemma mtrace_msub : forall {n} (M1 M2 : smat n),
      mtrace (M1 - M2) = (mtrace M1 - mtrace M2)%A.
  Proof. intros. unfold msub. rewrite mtrace_madd, mtrace_mopp. auto. Qed.
  
  
  (* (** m2l (M1 + M2) = (m2l M1) + (m2l M2) *) *)
  (* Lemma m2l_madd_homo : forall r c (M1 M2 : mat r c), *)
  (*     (m2l (M1 + M2) = dmap2 Aadd (m2l m1) (m2l M2))%dlist. *)
  (* Proof. *)
  (*   intros. destruct m1,m2. simpl. easy. *)
  (* Qed. *)

  
  Context `{AR : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : make_ring_theory.
  
  
  (** *** Matrix Scalar Multiplication *)
  Definition mcmul {r c : nat} (a : A) (M : @mat A r c) : @mat A r c.
    refine (mk_mat (dmap (fun x => Amul a x) (mdata M)) _ _).
    - rewrite dmap_length. apply mheight.
    - apply dmap_width. apply mwidth.
  Defined.
  Infix "c*" := mcmul : mat_scope.

  Definition mmulc {r c : nat} (M : @mat A r c) (a : A) : @mat A r c.
    refine (mk_mat (dmap (fun x => Amul x a) (mdata M)) _ _).
    - rewrite dmap_length. apply mheight.
    - apply dmap_width. apply mwidth.
  Defined.
  Infix "*c" := mmulc : mat_scope.
  
  (** a * M = M * a *)
  Lemma mmulc_eq_mcmul : forall {r c} (M : mat r c) a, M *c a = a c* M.
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    rewrite dmap_ext with (g:=(fun x => (a*x)%A)). easy.
    intros. ring.
  Qed.

  (** a1 * (a2 * M) = (a1 * a2) * M *)
  Lemma mcmul_assoc : forall {r c} (M : mat r c) a1 a2,
      a1 c* (a2 c* M) = (a1 * a2)%A c* M.
  Proof.
    intros. destruct M. apply meq_iff; simpl. unfold dmap; simpl.
    rewrite map_map. apply map_ext. intros.
    rewrite map_map. apply map_ext. intros. ring.
  Qed.
  
  (** a1 * (a2 * M) = a2 * (a1 * M) *)
  Lemma mcmul_perm : forall {r c} (M : mat r c) a1 a2,
      a1 c* (a2 c* M) = a2 c* (a1 c* M).
  Proof. intros. rewrite !mcmul_assoc. f_equal. ring. Qed.

  (** a * (M1 + M2) = (a * M1) + (a * M2) *)
  Lemma mcmul_madd_distr : forall {r c} a (M1 M2 : mat r c),
      a c* (M1 + M2) = (a c* M1) + (a c* M2).
  Proof.
    intros. destruct M1,M2. apply meq_iff; simpl.
    apply symmetry. apply dmap2_dmap_hom. intros. ring.
  Qed.
  
  (** (a1 + a2) * M = (a1 * M) + (a2 * M) *)
  Lemma mcmul_add_distr : forall {r c} a1 a2 (M : mat r c),
      (a1 + a2)%A c* M = (a1 c* M) + (a2 c* M).
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    rewrite (dmap2_dmap_dmap _ _ (fun x => (a1 + a2) * x)%A). easy. intros. ring.
  Qed.

  (** (a * M)[i,j] = a * M[i,j] *)
  Lemma mnth_mcmul : forall {r c} (M : mat r c) a i j,
      i < r -> j < c -> (a c* M)$i$j = a * (M$i$j).
  Proof.
    intros. destruct M as [m pH pW]. unfold mnth. simpl. unfold dmap.
    rewrite nth_nth_map_map with (r:=r)(c:=c); auto.
  Qed.

  (* 0 c* M = mat0 *)
  Lemma mcmul_0_l : forall {r c} (M : mat r c), Azero c* M = mat0.
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    rewrite dmap_ext with (g:=(fun x => Azero)).
    - apply dmap_eq_zero; auto.
    - intros. ring. 
  Qed.

  (** a c* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a c* (@mat0 r c) = mat0.
  Proof.
    intros. unfold mat0; apply meq_iff; simpl.
    unfold dmap,dlzero. rewrite map_repeat. f_equal.
    unfold lzero. rewrite map_repeat. f_equal. apply ring_mul_0_r.
  Qed.
  
  (* 1 c* A = A *)
  Lemma mcmul_1 : forall {r c} (M : mat r c), Aone c* M = M.
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    apply map_id. intros. apply map_id. intros. ring.
  Qed.
  
  (* (-a) * M = - (a * M) *)
  Lemma mcmul_opp : forall {r c} a (M : mat r c), (- a)%A c* M = - (a c* M).
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    unfold dmap.
    rewrite map_map. apply map_ext. intros.
    rewrite map_map. apply map_ext. intros. ring.
  Qed.
  
  (* a * (-M) = - (a * M) *)
  Lemma mcmul_mopp : forall {r c} a (M : mat r c), a c* (-M) = - (a c* M).
  Proof.
    intros. destruct M. apply meq_iff; simpl.
    unfold dmap.
    rewrite !map_map. apply map_ext. intros.
    rewrite !map_map. apply map_ext. intros. ring.
  Qed.
  
  (* (-a) * (- M) = a * M *)
  Lemma mcmul_opp_mopp : forall {r c} a (M : mat r c),
      (- a)%A c* (- M) = a c* M.
  Proof. intros. rewrite mcmul_mopp, mcmul_opp. rewrite mopp_mopp. auto. Qed.

  (** a c* (M1 - M2) = (a c* M1) - (a c* M2) *)
  Lemma mcmul_msub : forall {r c} a (M1 M2 : mat r c),
      a c* (M1 - M2) = (a c* M1) - (a c* M2).
  Proof.
    intros. unfold msub. rewrite mcmul_madd_distr. f_equal.
    rewrite mcmul_mopp. auto.
  Qed.
  
  (** 1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (M : mat r c), Aone c* M = M.
  Proof.
    intros. destruct M; apply meq_iff; simpl.
    unfold dmap. apply map_id. intros. apply map_id. intros. group_simp.
  Qed.

  (** a c* mat1 = mdiag([a,a,...]) *)
  Lemma mcmul_1_r : forall {n} a, a c* (@mat1 n) = mdiagMk Azero n (repeat a n). 
  Proof.
    intros.
    rewrite (meq_iff_mnth (Azero:=Azero)). intros.
    rewrite mnth_mcmul; auto.
    destruct (ri =? cj) eqn:Eij.
    - apply Nat.eqb_eq in Eij. subst.
      rewrite mat1_ii; auto. rewrite mdiagMk_ii; auto.
      rewrite nth_repeat_same; auto. monoid_simpl.
    - apply Nat.eqb_neq in Eij. subst.
      rewrite mat1_ij; auto. rewrite mdiagMk_ij; auto.
      apply ring_mul_0_r.
  Qed.

  (** (a c* M)\T = a c* (m\T) *)
  Lemma mtrans_mcmul : forall {r c} (a : A) (M : mat r c), (a c* M)\T = a c* (M\T).
  Proof.
    intros. rewrite (meq_iff_mnth (Azero:=Azero)). intros.
    rewrite mnth_mtrans,!mnth_mcmul; auto. rewrite mnth_mtrans; auto.
  Qed.

  (** tr (a c* M) = a * tr (m) *)
  Lemma mtrace_mcmul : forall {n} (a : A) (M : smat n),
      mtrace (a c* M) = (a * mtrace M)%A.
  Proof.
    intros. destruct M as [m pH pW]. unfold mtrace, mcmul; simpl.
    apply fold_left_mul with (n:=n).
    - rewrite map_length, seq_length; auto.
    - rewrite map_length, seq_length; auto.
    - intros. rewrite !nth_map_seq; auto. rewrite Nat.add_0_r.
      unfold dmap. rewrite nth_nth_map_map with (r:=n)(c:=n); auto.
  Qed.

  
  (** *** Matrix Multiplication *)
  Definition mmul {r c t : nat} (M1 : @mat A r c) (M2 : @mat A c t) : @mat A r t.
    refine (mk_mat (dldotdl (Aadd:=Aadd) (Azero:=Azero) (Amul:=Amul)
                      (mdata M1) (mdata (mtrans M2))) _ _).
    - destruct M1 as [dl1 H1 W1], M2 as [dl2 H2 W2]; simpl.
      apply dldotdl_length; auto.
    - destruct M1 as [dl1 H1 W1], M2 as [dl2 H2 W2]; simpl.
      apply (dldotdl_width _ _ _ c); auto with mat.
  Defined.
  Infix "*" := mmul : mat_scope.

  (** (M1 * M2) * M3 = M1 * (M2 * M3) *)
  Lemma mmul_assoc : forall {r c t s} (M1 : mat r c) (M2 : mat c t) (M3 : mat t s),
      (M1 * M2) * M3 = M1 * (M2 * M3).
  Proof.
    intros. destruct M1,M2,M3. apply meq_iff; simpl.
    apply dldotdl_assoc; auto with mat.
  Qed.

  (** M1 * (M2 + M3) = M1 * M2 + M1 * M3 *)
  Lemma mmul_madd_distr_l : forall {r c t} (M1 : mat r c) (M2 M3 : mat c t),
      M1 * (M2 + M3) = (M1 * M2) + (M1 * M3).
  Proof.
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
  Lemma mmul_0_l : forall {r c t} (M : mat c t), mat0 * M = @mat0 r t.
  Proof.
    intros. destruct M. apply meq_iff; simpl. rewrite dldotdl_zero_l; auto with mat.
  Qed.
  
  (** M * 0 = 0 *)
  Lemma mmul_0_r : forall {r c t} (M : mat r c), M * mat0 = @mat0 r t.
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
    
    (* Definition det_of_mat_3_3 (M : @mat A 3 3) : A := *)
    (*   let b1 := (M.11 * M.22 * M.33)%A in *)
    (*   let b2 := (M.12 * M.23 * M.31)%A in *)
    (*   let b3 := (M.13 * M.21 * M.32)%A in *)
    (*   let c1 := (M.11 * M.23 * M.32)%A in *)
    (*   let c2 := (M.12 * M.21 * M.33)%A in *)
    (*   let c3 := (M.13 * M.22 * M.31)%A in *)
    (*   let b := (b1 + b2 + b3)%A in *)
    (*   let c := (c1 + c2 + c3)%A in *)
    (*   (b - c)%A. *)

    (* Definition skew_sym_mat_of_v3 (V : @cvec A 3) : @mat A 3 3. *)
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
  
  Definition mat2scalar (M : @mat A 1 1) : A.
  Proof.
    destruct M as [dl].
    refine (hd Azero (hd [] dl)).
  Defined.
  
End mat2scalar.


(* ======================================================================= *)
(** ** Get row and column of a matrix *)
Section mrow_mcol.

  Context {A} {Azero : A} {r c : nat}.
  
  Definition mrow_error (m : @mat A r c) (i : nat) : option (list A) :=
    nth_error (mdata m) i.
  
  Definition mrow (m : @mat A r c) (i : nat) : list A :=
    nth i (mdata m) (repeat Azero c).

  Definition mcol_error (m : @mat A r c) (j : nat) : option (list A) :=
    nthc_error (mdata m) j.
  
  Definition mcol (m : @mat A r c) (j : nat) : list A :=
    nthc Azero (mdata m) j.

  (*   Lemma mrow_length : forall {r c} i (m : mat r c), length (mrow i m) = c. *)
  (*   Proof. intros. unfold mrow. rewrite map_length. apply seq_length. Qed. *)

  (*   (** (mrow m i)[j] = m[i][j] *) *)
  (*   Lemma nth_mrow : forall {r c} i j (m : mat r c) a, *)
  (*       i < r -> j < c -> (nth j (mrow i m) a == m ! i ! j)%T. *)
  (*   Proof. *)
  (*     intros. unfold mrow. rewrite nth_map_seq; auto. *)
  (*     rewrite Nat.add_0_r. rewrite mnth_eq_mnth_raw; auto. easy. *)
  (*   Qed. *)

End mrow_mcol.

Section test.
  Let m1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute mrow m1 0. *)
  (* Compute mrow m1 1. *)
  (* Compute mcol m1 0. *)
  (* Compute mcol m1 1. *)
End test.


(* ======================================================================= *)
(** ** Construct matrix from vector and matrix *)

Section mcons.

  Context {A:Type} (Azero:A).
  
  (** Construct a matrix with a row vector and a a matrix *)
  Definition mconsr {r c} (V : @rvec A c) (M : @mat A r c) : @mat A (S r) c.
    destruct V as [v], M as [m].
    refine (mk_mat ((hd [] v) :: m) _ _); simpl; auto.
    unfold width in *. constructor; auto.
    destruct v; try easy. simpl. inv mwidth0. auto.
  Defined.
  
  (** Construct a matrix with a column row vector and a a matrix *)
  Definition mconsc {r c} (V : @cvec A r) (M : @mat A r c) : @mat A r (S c).
    destruct V as [v], M as [m].
    refine (mk_mat (consc (hdc Azero v) m) _ _).
    - apply consc_length; auto. rewrite hdc_length; auto.
    - apply consc_width; auto. rewrite hdc_length; subst; auto.
  Defined.
  
  (** Construct a matrix by rows with the matrix which row number is 0 *)
  Lemma mconsr_mr0 : forall {n} (V : rvec n) (M : @mat A 0 n), mconsr V M = V.
  Proof.
    intros. destruct V as [d1 pH1 pW1], M as [d2 pH2 pW2]. apply meq_iff. simpl.
    apply length_zero_iff_nil in pH2. subst. rewrite <- list_length1_eq_hd; auto.
  Qed.

  (** Construct a matrix by columns with the matrix which column number is 0 *)
  Lemma mconsc_mc0 : forall {n} (V : cvec n) (M : @mat A n 0), mconsc V M = V.
  Proof.
    intros. destruct V as [d1 pH1 pW1], M as [d2 pH2 pW2]. apply meq_iff. simpl.
    rewrite consc_dl_w0; auto.
    - clear d2 pH2 pW2.
      revert n pH1 pW1. induction d1; intros; simpl in *. auto.
      destruct n. lia. inversion pH1. inversion pW1.
      f_equal; auto. rewrite <- list_length1_eq_hd; auto. apply (IHd1 n); auto.
    - rewrite hdc_length. lia.
  Qed.
  
End mcons.


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
