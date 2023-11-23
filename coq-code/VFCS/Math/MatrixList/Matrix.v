(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with function (Safe version)
  author    : ZhengPu Shi
  date      : 2021.12

  remark    :
  1. This is the safe version of NatFun implementation, that means,
     we modified the definition of matrix type to improve the type safety.
  2. The old definition of matrix type is:
  
        Definition mat {T} (r c : nat) := nat -> nat -> A.

     while new definition of matrix type is:

        Record mat {T} (r c : nat) := mk_mat { matf : nat -> nat -> T }.
 *)


Require Export TupleExt Hierarchy.
Require Export ListExt.


Generalizable Variable T Teq Tadd Topp Tmul Tinv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope T_scope.
Open Scope mat_scope.

(* Global Hint Rewrite map_length seq_length : list. *)


(* ======================================================================= *)
(** ** Definition of Matrix Type *)
Section mat_def.

  (* I have another idea, if the properties mheight and mwidth should defined 
     with a boolean equation, such as "legnth mdata =? r" ? Thus the proof effort
     should be reduced or automated? *)
  Record mat {T : Type} (r c : nat) : Type :=
    mk_mat {
        mdata : list (list T);
        mheight : length mdata = r;
        mwidth : width mdata c
      }.
  
End mat_def.

Arguments mk_mat {T r c}.
Arguments mdata {T r c}.
Arguments mheight {T r c}.
Arguments mwidth {T r c}.


(* matrix can be used as a dlist *)
(* Coercion mdata : mat >-> dlist. *)


(** square matrix *)
Notation smat T n := (@mat T n n).


(* ======================================================================= *)
(** ** Equality of matrix *)


(* Matrix equality could be proved by the eqaulities of size and data *)
Lemma meq_iff : forall {T r c} (m1 m2 : @mat T r c),
    mdata m1 = mdata m2 <-> m1 = m2.
Proof.
  intros. destruct m1 as [d1 ph1 pw1], m2 as [d2 ph2 pw2]; simpl in *.
  split; intros.
  - subst. f_equal; apply proof_irrelevance.
  - inversion H. auto.
Qed.


(* ======================================================================= *)
(** ** Get element of a matrix *)
Section mnth.
  Context {T} {T0 : T} {r c : nat}.

  Definition mnth (m : mat r c) (ri ci : nat) : T :=
    nth ci (nth ri (mdata m) []) T0.

  Notation "m $ i $ j" :=
    (mnth m i j) (at level 20, i at next level, j at next level).

  Lemma meq_iff_mnth : forall (m1 m2 : mat r c),
      m1 = m2 <->
        (forall (ri cj : nat), ri < r -> cj < c -> m1 $ ri $ cj = m2 $ ri $ cj).
  Proof.
    intros. rewrite <- meq_iff.
    destruct m1 as [d1 ph1 pw1], m2 as [d2 ph2 pw2]; unfold mnth; simpl.
    apply dlist_eq_iff_nth_nth; auto.
  Qed.

End mnth.

Arguments mnth {T} T0 {r c}.

Global Hint Unfold mnth : core.
Notation "A $ i $ j " := (mnth A i j) : mat_scope.
Notation "A .11" := (A $ 0 $ 0) : mat_scope.
Notation "A .12" := (A $ 0 $ 1) : mat_scope.
Notation "A .13" := (A $ 0 $ 2) : mat_scope.
Notation "A .14" := (A $ 0 $ 3) : mat_scope.
Notation "A .21" := (A $ 1 $ 0) : mat_scope.
Notation "A .22" := (A $ 1 $ 1) : mat_scope.
Notation "A .23" := (A $ 1 $ 2) : mat_scope.
Notation "A .24" := (A $ 1 $ 3) : mat_scope.
Notation "A .31" := (A $ 2 $ 0) : mat_scope.
Notation "A .32" := (A $ 2 $ 1) : mat_scope.
Notation "A .33" := (A $ 2 $ 2) : mat_scope.
Notation "A .34" := (A $ 2 $ 3) : mat_scope.
Notation "A .41" := (A $ 3 $ 0) : mat_scope.
Notation "A .42" := (A $ 3 $ 1) : mat_scope.
Notation "A .43" := (A $ 3 $ 2) : mat_scope.
Notation "A .44" := (A $ 3 $ 3) : mat_scope.


(** ** Convert between function and matrix *)
Section f2m_m2f.
  
  Context {T} (T0 : T).

  Definition f2m {r c} (f : nat -> nat -> T) : @mat T r c :=
    mk_mat (@f2dl T r c f) (f2dl_length r c f) (f2dl_width r c f).
    
  Definition m2f {r c} (m : mat r c) : (nat -> nat -> T) :=
    dl2f (r:=r) (c:=c) (T0:=T0) (mdata m).

End f2m_m2f.


(* (* ======================================================================= *) *)
(* (** ** Matrix Automation *) *)

(* (** Useful tactic for solving T = B for concrete A, B *) *)

(* (** Solve i < 0 *) *)
(* Ltac solve_end := *)
(*   match goal with *)
(*   | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H *)
(*   end. *)

(* (** Convert mat to function *) *)
(* Ltac mat2fun := *)
(*   repeat match goal with *)
(*     | m : mat ?r ?c |- _ => destruct m as [m]; simpl in * *)
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



(** ** matrix with specific size *)

Section mat_specific.
  Context {T : Type}.
  Variable r c : nat.
  Variable t11 t12 t13 t14 t21 t22 t23 t24 t31 t32 t33 t34 t41 t42 t43 t44 : T.
  
  Definition mk_mat_0_c : @mat T 0 c.
    refine (mk_mat [] _ _); auto. constructor; auto. Defined.

  Definition mk_mat_r_0 : @mat T r 0.
    refine (mk_mat (dnil r) _ _); auto.
    apply dnil_length. apply dnil_width. Defined.

  Definition mk_mat_1_c (d : list T) (H : length d = c)  : @mat T 1 c.
    refine (mk_mat [d] _ _); auto. constructor; auto. Defined.
  
  Definition mk_mat_r_1 (d : list T) (H : length d = r)  : @mat T r 1.
    refine (mk_mat (row2col d) _ _); auto.
    rewrite row2col_length; auto. apply row2col_width. Defined.

  Definition mk_mat_1_1 : @mat T 1 1.
    refine (mk_mat [[t11]] _ _); auto. constructor; auto. Defined.

  Definition mk_mat_1_2 : @mat T 1 2.
    refine (mk_mat [[t11;t12]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_2_1 : @mat T 2 1.
    refine (mk_mat [[t11];[t21]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_2_2 : @mat T 2 2.
    refine (mk_mat [[t11;t12];[t21;t22]] _ _); auto. constructor; auto. Defined.

  Definition mk_mat_1_3 : @mat T 1 3.
    refine (mk_mat [[t11;t12;t13]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_2_3 : @mat T 2 3.
    refine (mk_mat [[t11;t12;t13];[t21;t22;t23]] _ _); auto.
    constructor; auto. Defined.
  Definition mk_mat_3_1 : @mat T 3 1.
    refine (mk_mat [[t11];[t21];[t31]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_3_2 : @mat T 3 2.
    refine (mk_mat [[t11;t12];[t21;t22];[t31;t23]] _ _); auto.
    constructor; auto. Defined.
  Definition mk_mat_3_3 : @mat T 3 3.
    refine (mk_mat [[t11;t12;t13];[t21;t22;t23];[t31;t32;t33]] _ _); auto.
    constructor; auto. Defined.

  Definition mk_mat_1_4 : @mat T 1 4.
    refine (mk_mat [[t11;t12;t13;t14]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_4_1 : @mat T 4 1.
    refine (mk_mat [[t11];[t21];[t31];[t41]] _ _); auto. constructor; auto. Defined.
  Definition mk_mat_4_4 : @mat T 4 4.
    refine (mk_mat [[t11;t12;t13;t14];[t21;t22;t23;t24];
                    [t31;t32;t33;t34];[t41;t42;t43;t44]] _ _); auto.
    constructor; auto. Defined.
  
End mat_specific.


(** ** Convert between dlist and mat *)

Section l2m_m2l.
  Context {T : Type} (T0 : T).

  (** list to fixed-length list *)
  Fixpoint l2v_aux (l : list T) (n : nat) : list T :=
    match n with
    | 0 => []
    | S n' => (hd T0 l) :: (l2v_aux (tl l) n')
    end.
  
  Lemma l2v_aux_length : forall (l : list T) (n : nat), length (l2v_aux l n) = n.
  Proof. intros l n. gd l. induction n; intros; simpl; auto. Qed.
  
  Lemma l2v_aux_eq : forall (l : list T) (n : nat) (H1 : length l = n), l2v_aux l n = l.
  Proof.
    intros l n. gd l. induction n; intros; simpl.
    - apply length_zero_iff_nil in H1. easy.
    - destruct l. easy. inv H1. f_equal; auto.
  Qed.
  
  (* list list to fixed-shape list list *)
  Fixpoint l2m_aux (dl : list (list T)) (r c : nat) : list (list T) :=
    match r with
    | 0 => []
    | S n' => (l2v_aux (hd nil dl) c) :: (l2m_aux (tl dl) n' c)
    end.
  
  Lemma l2m_aux_length : forall (dl : list (list T)) (r c : nat), length (l2m_aux dl r c) = r.
  Proof. intros dl r. gd dl. induction r; intros; simpl; auto. Qed.
  
  Lemma l2m_aux_width : forall (dl : list (list T)) (r c : nat), width (l2m_aux dl r c) c.
  Proof.
    unfold width; intros dl r. revert dl.
    induction r; intros; simpl; auto. constructor; auto.
    apply l2v_aux_length.
  Qed.
  
  Lemma l2m_aux_eq : forall (dl : list (list T)) (r c : nat)
                       (H1 : length dl = r) (H2 : width dl c),
      l2m_aux dl r c = dl.
  Proof.
    intros dl r. gd dl. induction r; intros; simpl; auto.
    - apply length_zero_iff_nil in H1. easy.
    - destruct dl. easy. inv H1. inv H2.
      rewrite IHr; auto. simpl. rewrite l2v_aux_eq; auto.
  Qed.

  Definition l2m (r c : nat) (dl : list (list T)) : mat r c :=
    mk_mat (l2m_aux dl r c) (l2m_aux_length dl r c) (l2m_aux_width dl r c).
  
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list T)),
      length d1 = r -> width d1 c -> 
      length d2 = r -> width d2 c -> 
      ~(d1 = d2) -> ~(l2m r c d1 = l2m r c d2).
  Proof.
    intros. unfold l2m. intro. inversion H4.
    rewrite !l2m_aux_eq in H6; auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m r c d = m).
  Proof.
    intros. destruct m as [d ph pw].
    exists d. unfold l2m; simpl.
    apply meq_iff; simpl. apply l2m_aux_eq; auto.
  Qed.

  (** mat to dlist *)
  Definition m2l {r c} (m : mat r c) : dlist T := mdata m.

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof. intros. apply mheight. Qed.

  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof. intros. apply mwidth. Qed.

  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~(m1 = m2) -> m2l m1 <> m2l m2.
  Proof. intros. rewrite meq_iff. auto. Qed.

  Lemma m2l_surj : forall {r c} (d : dlist T),
      length d = r -> width d c -> (exists m : mat r c, m2l m = d).
  Proof. intros. exists (mk_mat d H H0). auto. Qed.

  (* relation between l2m and m2l *)
  Lemma l2m_m2l_id : forall {r c} (m : mat r c), (@l2m r c (m2l m)) = m.
  Proof.
    intros. destruct m; simpl. apply meq_iff; simpl. apply l2m_aux_eq; auto.
  Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : dlist T),
      length dl = r -> width dl c -> m2l (@l2m r c dl) = dl.
  Proof. intros. unfold l2m,m2l. simpl. apply l2m_aux_eq; auto. Qed.

End l2m_m2l.

Section test.
  Let m1 := l2m 9 2 2 [[1;2];[3;4]].
  Let m2 := l2m 9 2 2 [[1];[3;4]].
  Let m3 := l2m 9 2 2 [[1;2];[3]].
  Let m4 := l2m 9 2 2 [[1;2;3];[3;4]].
  Let m5 := l2m 9 2 2 [[1;2];[3;4;5]].
  Compute m2l m1.
  Compute m2l m2.
  Compute m2l m3.
  Compute m2l m4.
  Compute m2l m5.
End test.


(** ** Matrix map *)
Section mmap.

  Context {T U : Type} {r c : nat}.
  Variable f : T -> U.
  
  Definition mmap (m : @mat T r c) : @mat U r c.
    refine (mk_mat (dmap f (mdata m)) _ _).
    - rewrite dmap_length. apply m.
    - apply dmap_width. apply m.
  Defined.

End mmap.


(** ** Matrix map2 to a dlist *)
Section mmap2dl.
  
  Context {T U V : Type} {r c : nat}.
  Variable f : T -> U -> V.

  Definition mmap2dl (m1 : @mat T r c) (m2 : @mat U r c) : list (list V) :=
    dmap2 f (mdata m1) (mdata m2).

  Lemma mmap2dl_length : forall (m1 : @mat T r c) (m2 : @mat U r c),
      length (mmap2dl m1 m2) = r.
  Proof. 
    intros; simpl. unfold mmap2dl. rewrite dmap2_length;
      repeat rewrite mheight; auto.
  Qed.

  Lemma mmap2dl_width : forall (m1 : @mat T r c) (m2 : @mat U r c),
      width (mmap2dl m1 m2) c.
  Proof. 
    intros; simpl. unfold mmap2dl. apply dmap2_width; apply mwidth.
  Qed.

End mmap2dl.


(** ** Matrix map2 *)
Section mmap2.

  Context {T U V : Type} {r c : nat}.
  
  Definition mmap2 (f : T -> U -> V) (m1 : @mat T r c) (m2 : @mat U r c) : @mat V r c.
    refine (mk_mat (dmap2 f (mdata m1) (mdata m2)) _ _).
    rewrite dmap2_length. apply m1. rewrite !mheight; auto.
    apply dmap2_width; apply mwidth.
  Defined.

End mmap2.


(** ** Matrix map2 with same base type *)
Section mmap2_sametype.

  Context `{Commutative T Tadd}.
  Lemma mmap2_comm : forall {r c} (m1 m2 : mat r c),
      mmap2 Tadd m1 m2 = mmap2 Tadd m2 m1.
  Proof. intros. apply meq_iff; simpl. apply dmap2_comm. Qed.
  
  Context `{Associative T Tadd}.
  Lemma mmap2_assoc : forall {r c} (m1 m2 m3 : mat r c),
      mmap2 Tadd (mmap2 Tadd m1 m2) m3 = mmap2 Tadd m1 (mmap2 Tadd m2 m3).
  Proof. intros. apply meq_iff; simpl. apply dmap2_assoc. Qed.
  
End mmap2_sametype.


(** ** zero matrix and unit matrix *)
Section mat0_mat1.

  Context {T : Type} (T0 T1 : T).
  Definition mat0 {r c} := mk_mat (dlzero T0 r c) dlzero_length dlzero_width.
  Definition mat1 {n} := mk_mat (dlunit T0 T1 n) dlunit_length dlunit_width.

End mat0_mat1.


(** ** matrix transpose *)
Section mtrans.

  Context {T : Type}.
  
  Definition mtrans {r c} (m : @mat T r c) : mat c r :=
    mk_mat (dltrans (mdata m) c) 
      (dltrans_length (mdata m) c (mwidth m))
      (dltrans_width (mdata m) r c (mheight m) (mwidth m)).
  
  (** Transpose twice return back *)
  Lemma mtrans_trans : forall {r c} (m : mat r c), mtrans (mtrans m) = m.
  Proof. intros. apply meq_iff; simpl. apply dltrans_trans; apply m. Qed.
  
End mtrans.


(** ** matrix addition,opposition,subtraction *)
Section madd_opp_sub.

  Context `{AG:AGroup T Tadd T0 Topp}.
  Notation Asub := (fun a b => Tadd a (Topp b)).
  
  (** matrix addition *)
  Definition madd {r c} (m1 m2 : mat r c) : mat r c := mmap2 Tadd m1 m2.
  Infix "+" := madd : mat_scope.
  
  (** matrix opposition *)
  Definition mopp {r c} (m : mat r c) : mat r c := mmap Topp m.
  Notation "- m" := (mopp m) : mat_scope.
  
  (* matrix subtraction *)
  Definition msub {r c} (m1 m2 : mat r c) : mat r c := m1 + (-m2).
  Infix "-" := msub : mat_scope.

  Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 = m2 + m1.
  Proof. intros. apply meq_iff, map2_comm.
         constructor. apply map2_comm. apply AG. Qed.
  
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 = m1 + (m2 + m3).
  Proof. intros. apply meq_iff, map2_assoc.
         constructor. apply map2_assoc. apply AG. Qed.
  
  (** 0 + m = m *)
  Lemma madd_0_l : forall {r c} (m : mat r c), (mat0 T0) + m = m.
  Proof. intros. apply meq_iff, dladd_zero_l; apply m. Qed.

  (** m + 0 = m *)
  Lemma madd_0_r : forall {r c} (m : mat r c), m + (mat0 T0) = m.
  Proof. intros. apply meq_iff, dladd_zero_r; apply m. Qed.

  Lemma madd_opp_l : forall {r c} (m : mat r c), (-m) + m = mat0 T0.
  Proof.
    intros. destruct m as [d pH pW]. unfold madd, mopp. apply meq_iff; simpl.
    unfold dmap2,dmap,dlzero. revert c d pH pW. induction r; intros; simpl.
    - apply length_zero_iff_nil in pH. subst. auto.
    - destruct d. easy. simpl. f_equal.
      + simpl in *. inv pW. inv pH. clear H2. induction l; auto.
        simpl. f_equal; auto. group_simp.
      + apply IHr; auto. inv pW. auto.
  Qed.
    
  Lemma madd_opp_r : forall {r c} (m : mat r c), m + (-m) = mat0 T0.
  Proof. intros. rewrite madd_comm. apply madd_opp_l. Qed.
  
  
  Instance Associative_madd : forall r c, @Associative (mat r c) madd.
  Proof. intros. constructor. apply madd_assoc. Qed.

  Instance Commutative_madd : forall r c, @Commutative (mat r c) madd.
  Proof. intros. constructor. apply madd_comm. Qed.

  Instance IdentityLeft_madd : forall r c, @IdentityLeft (mat r c) madd (mat0 T0).
  Proof. intros. constructor. apply madd_0_l. Qed.

  Instance IdentityRight_madd : forall r c, @IdentityRight (mat r c) madd (mat0 T0).
  Proof. intros. constructor. apply madd_0_r. Qed.

  Instance InverseLeft_madd : forall r c, @InverseLeft (mat r c) madd (mat0 T0) mopp.
  Proof. intros. constructor. apply madd_opp_l. Qed.

  Instance InverseRight_madd : forall r c, @InverseRight (mat r c) madd (mat0 T0) mopp.
  Proof. intros. constructor. apply madd_opp_r. Qed.

  Instance AGroup_madd : forall r c, @AGroup (mat r c) madd (mat0 T0) mopp.
  Proof.
    intros. repeat constructor;
      try apply associative;
      try apply identityLeft;
      try apply identityRight;
      try apply inverseLeft;
      try apply inverseRight;
      try apply commutative.
  Qed.

  (* Now, we ca use group theory on <madd, mat0, mopp> *)
  
  (** - (- m) = m *)
  Lemma mopp_opp : forall {r c} (m : mat r c), - (- m) = m.
  Proof. intros. apply group_inv_inv. Qed.

  Lemma mopp_exchange : forall {r c} (m1 m2 : mat r c), -m1 = m2 <-> m1 = -m2.
  Proof.
    intros. split; intros.
    - rewrite <- H. rewrite mopp_opp. easy.
    - rewrite H. rewrite mopp_opp. easy. 
  Qed.

  Lemma mopp_mat0 : forall {r c:nat}, - (@mat0 T T0 r c) = mat0 T0.
  Proof. intros. apply group_inv_id. Qed.

  (* m1 - m2 = - (m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 = - (m2 - m1).
  Proof. intros. unfold msub. rewrite group_inv_distr.
         rewrite group_inv_inv. auto. Qed.

  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c),
      (m1 - m2) - m3 = m1 - (m2 + m3).
  Proof.
    intros. unfold msub. group_simp. f_equal.
    rewrite group_inv_distr. apply commutative. Qed.
  
  (** 0 - m = - m *)
  Lemma msub_0_l : forall {r c} (m : mat r c), (mat0 T0) - m = - m.
  Proof. intros. unfold msub. group_simp. Qed.
  
  (** m - 0 = m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - (mat0 T0) = m.
  Proof. intros. unfold msub. rewrite (@group_inv_id _ madd (mat0 T0)); auto.
         group_simp. apply AGroup_madd. Qed.
  
  (** m - m = 0 *)
  Lemma msub_self : forall {r c} (m : mat r c), m - m = (mat0 T0).
  Proof. intros. unfold msub. group_simp. Qed.

  (* (** m2l (m1 + m2) = (m2l m1) + (m2l m2) *) *)
  (* Lemma m2l_madd_homo : forall r c (m1 m2 : mat r c), *)
  (*     (m2l (m1 + m2) = dmap2 Tadd (m2l m1) (m2l m2))%dlist. *)
  (* Proof. *)
  (*   intros. destruct m1,m2. simpl. easy. *)
  (* Qed. *)
  
End madd_opp_sub.


(** ** matrix multiplication *)
Section mcmul_mmulc_mmul.

  Context `{R:Ring T Tadd T0 Topp Tmul T1}.
  Add Ring ring_inst : make_ring_theory.
  
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- a" := (Topp a) : T_scope.

  Infix "+" := (madd (Tadd:=Tadd)) : mat_scope.
  Notation "- m" := (mopp (Topp:=Topp) m) : mat_scope.

  Definition mcmul {r c : nat} (a : T) (m : @mat T r c) : @mat T r c.
    refine (mk_mat (dmap (fun x => Tmul a x) (mdata m)) _ _).
    - rewrite dmap_length. destruct m. simpl. auto.
    - apply dmap_width. destruct m. simpl. auto.
  Defined.
  Infix "c*" := mcmul : mat_scope.

  Definition mmulc {r c : nat} (m : @mat T r c) (a : T) : @mat T r c.
    refine (mk_mat (dmap (fun x => Tmul x a) (mdata m)) _ _).
    - rewrite dmap_length. destruct m. simpl. auto.
    - apply dmap_width. destruct m. simpl. auto.
  Defined.
  Infix "*c" := mmulc : mat_scope.

  Definition mmul {r c t : nat} (m1 : @mat T r c) (m2 : @mat T c t) : @mat T r t.
    refine (mk_mat (dldotdl (Tadd:=Tadd) (T0:=T0) (Tmul:=Tmul)
                      (mdata m1) (mdata (mtrans m2))) _ _).
    - destruct m1 as [dl1 H1 W1], m2 as [dl2 H2 W2]; simpl.
      apply dldotdl_length; auto.
    - destruct m1 as [dl1 H1 W1], m2 as [dl2 H2 W2]; simpl.
      apply (dldotdl_width _ _ _ c); auto with mat.
  Defined.
  Infix "*" := mmul : mat_scope.

  (** matrix muliplication left distributve over addition. 
      A * (B + C) = A * B + A * C *)
  Lemma mmul_add_distr_l : forall {r c t} (m1 : mat r c) (m2 m3 : mat c t),
      m1 * (m2 + m3) = (m1 * m2) + (m1 * m3).
  Proof.
    intros. destruct m1,m2,m3. apply meq_iff; simpl. rewrite dltrans_dmap2; auto.
    rewrite (dldotdl_dmap2_distr_r _ _ _ mwidth0); auto with mat. subst; auto.
  Qed.
  
  (** matrix muliplication right distributve over addition. 
        (A + B) * C = A * C + B * C *)
  Lemma mmul_add_distr_r : forall {r c t} (m1 m2 : mat r c) (m3 : mat c t),
      (m1 + m2) * m3 = (m1 * m3) + (m2 * m3).
  Proof.
    intros. destruct m1,m2,m3. apply meq_iff; simpl.
    rewrite (dldotdl_dmap2_distr_l _ _ _ mwidth0); auto with mat.
  Qed.

  (** matrix muliplication association. 
        (A * B) * C = A * (B * C) *)
  Lemma mmul_assoc : forall {r c t s} (m1 : mat r c) (m2 : mat c t) (m3 : mat t s),
      (m1 * m2) * m3 = m1 * (m2 * m3).
  Proof.
    intros. destruct m1,m2,m3. apply meq_iff; simpl.
    apply dldotdl_assoc; auto with mat.
  Qed.
  
  (** 0 * A = 0 *)
  Lemma mmul_0_l : forall {r c t} (m : mat c t), (mat0 T0) * m = (@mat0 T T0 r t).
  Proof.
    intros. destruct m. apply meq_iff; simpl. rewrite dldotdl_zero_l; auto with mat.
  Qed.
  
  (** A * 0 = 0 *)
  Lemma mmul_0_r : forall {r c t} (m : mat r c), m * (mat0 T0) = (@mat0 T T0 r t).
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    rewrite dltrans_zero. rewrite dldotdl_zero_r; auto.
  Qed.
  
  (** 1 * A = A *)
  Lemma mmul_1_l : forall {r c} (m : mat r c), (mat1 T0 T1) * m = m.
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    rewrite dldotdl_dlunit_l; auto with mat. apply dltrans_trans; auto.
  Qed.
  
  (** A * 1 = A *)
  Lemma mmul_1_r : forall {r c} (m : mat r c), m * (mat1 T0 T1) = m.
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    rewrite dltrans_dlunit. rewrite dldotdl_dlunit_r; auto with mat.
  Qed.
  
  (** a * A = A * a *)
  Lemma mmulc_eq_mcmul : forall {r c} (m : mat r c) a, m *c a = a c* m.
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    rewrite dmap_ext with (g:=(fun x => (a*x)%T)). easy.
    intros. ring.
  Qed.

  (** a * (b * A) = (a * b) * A *)
  Lemma mcmul_assoc : forall {r c} (m : mat r c) a1 a2,
      a1 c* (a2 c* m) = (a1 * a2)%T c* m.
  Proof.
    intros. destruct m. apply meq_iff; simpl. unfold dmap; simpl.
    (* Remark: with the help of "map_ext on setoid", the proof is simplified. *)
    rewrite map_map. apply map_ext. intros.
    rewrite map_map. apply map_ext. intros. ring.
  Qed.
  
  (** a * (b * A) = b * (a * A) *)
  Lemma mcmul_perm : forall {r c} (m : mat r c) a1 a2,
      a1 c* (a2 c* m) = a2 c* (a1 c* m).
  Proof.
    intros. destruct m. apply meq_iff; simpl. unfold dmap; simpl.
    (* Remark: with the help of "map_ext on setoid", the proof is simplified. *)
    rewrite !map_map. apply map_ext. intros.
    rewrite !map_map. apply map_ext. intros. ring.
  Qed.

  (** a * (A + B) = (a * A) + (a * B) *)
  Lemma mcmul_distr_l : forall {r c} a (m1 m2 : mat r c),
      a c* (m1 + m2) = (a c* m1) + (a c* m2).
  Proof.
    intros. destruct m1,m2. apply meq_iff; simpl.
    apply symmetry. apply dmap2_dmap_hom. intros. ring.
  Qed.
  
  (** (a + b) * A = (a * A) + (b * A) *)
  Lemma mcmul_distr_r : forall {r c} a1 a2 (m : mat r c),
      (a1 + a2)%T c* m = (a1 c* m) + (a2 c* m).
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    rewrite (dmap2_dmap_dmap _ _ (fun x => (a1 + a2) * x)%T). easy. intros. ring.
  Qed.

  (* 0 c* A = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), T0 c* m = mat0 T0.
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    rewrite dmap_ext with (g:=(fun x => T0)).
    - apply dmap_eq_zero; auto.
    - intros. ring. 
  Qed.
  
  (* 1 c* A = A *)
  Lemma mcmul_1 : forall {r c} (m : mat r c), T1 c* m = m.
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    apply map_id. intros. apply map_id. intros. ring.
  Qed.
  
  (* (-a) * A = - (a * A) *)
  Lemma mcmul_neg : forall {r c} a (m : mat r c), (- a)%T c* m = - (a c* m).
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    unfold dmap.
    rewrite map_map. apply map_ext. intros.
    rewrite map_map. apply map_ext. intros. ring.
  Qed.
  
  (* (-a) * (- A) = a * A *)
  Lemma mcmul_neg_mopp : forall {r c} a (m : mat r c),
      (- a)%T c* (- m) = a c* m.
  Proof.
    intros. destruct m. apply meq_iff; simpl.
    unfold dmap.
    rewrite map_map. apply map_ext. intros.
    rewrite map_map. apply map_ext. intros. ring.
  Qed.

  (** Properties below, need a field structure *)
  Context `{F:Field T Tadd T0 Topp Tmul T1 Tinv}.
  Context `{TDec : Dec T}.
  
  (** k * A = 0 -> (k = 0) \/ (A = 0) *)
  Lemma mcmul_eq0_imply_m0_or_k0 : forall {r c} (m : mat r c) k,
      k c* m = mat0 T0 -> (k = T0)%T \/ (m = mat0 T0).
  Proof.
    intros. destruct m.
    unfold mcmul in H. apply meq_iff in H. simpl in H.
    apply dlcmul_zero_imply_k0_or_dlzero in H; auto. destruct H; auto.
    right. apply meq_iff; auto.
  Qed.

  (** (A <> 0 \/ k * A = 0) -> k = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : mat r c) k,
      m <> mat0 T0 -> k c* m = mat0 T0 -> (k = T0)%T.
  Proof. intros. apply mcmul_eq0_imply_m0_or_k0 in H0; auto. tauto. Qed.

  (** k * A = A -> k = 1 \/ A = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} k (m : mat r c),
      k c* m = m -> (k = T1)%T \/ (m = mat0 T0).
  Proof.
    intros. destruct m.
    unfold mcmul in H. apply meq_iff in H. simpl in H.
    apply (dlcmul_fixpoint_imply_k1_or_dlzero (r:=r) (c:=c)) in H; auto.
    destruct H; auto. right. apply meq_iff; auto.
  Qed.
  
  (** (m1 <> 0 /\ m2 <> 0 /\ k * m1 = m2) -> k <> 0 *)
  Lemma mcmul_eq_mat_implfy_not_k0 : forall {r c} (m1 m2 : mat r c) k,
      m1 <> mat0 T0 -> m2 <> mat0 T0 -> k c* m1 = m2 -> k <> T0.
  Proof.
    intros. intro. destruct m1,m2.
    rewrite <- meq_iff in H,H0,H1. simpl in *. unfold dmap in H1.
    rewrite (map_ext) with (g:=map (fun x=>T0)) (l:=mdata0) in H1.
    - pose proof (@dmap_eq_zero _ T0 r c mdata0). unfold dmap in H3.
      rewrite H3 in H1; auto.
    - intros. apply map_ext. intros. rewrite H2. ring.
  Qed.

End mcmul_mmulc_mmul.

(* Arguments mmul T0 Tadd Tmul {r c t}. *)
(* Arguments mcmul Tmul {r c}. *)
(* Arguments mmulc Tmul {r c}. *)


(** ** Matrix_1x1 to scalar *)
Section mat_1_1_to_scalar.

  Context {T:Type} (T0 : T).
  
  Definition mat_1_1_to_s (m : @mat T 1 1) : T.
  Proof.
    destruct m as [dl].
    refine (hd T0 (hd [] dl)).
  Defined.
  
End mat_1_1_to_scalar.


(* ======================================================================= *)
(** ** Extra Properties *)
Section Extra.

  Context {T:Type} (T0:T).
  (** Vector type *)
  Definition vecr n := @mat T 1 n.
  Definition vecc n := @mat T n 1.
  
  (** Construct a matrix with a row vector and a a matrix *)
  Definition mconsr {r c} (v : vecr c) (m : @mat T r c) : @mat T (S r) c.
    destruct v as [v], m as [m].
    refine (mk_mat ((hd [] v) :: m) _ _); simpl; auto.
    unfold width in *. constructor; auto.
    destruct v; try easy. simpl. inv mwidth0. auto.
  Defined.
  
  (** Construct a matrix with a column row vector and a a matrix *)
  Definition mconsc {r c} (v : vecc r) (m : @mat T r c) : @mat T r (S c).
    destruct v as [v], m as [m].
    refine (mk_mat (consc (hdc T0 v) m) _ _).
    - apply consc_length; auto. rewrite hdc_length; auto.
    - apply consc_width; auto. rewrite hdc_length; subst; auto.
  Defined.
  
  (* (** Equality of two forms of ConstructByRow *) *)
  (* Lemma mconsr_eq {r c} (v : vecr c) (m : @mat T r c) : mconsr v m = (v, m). *)
  (* Proof. unfold mconsr. auto. Qed. *)
  
  (* (** Construct a matrix by rows with the matrix which row number is 0 *) *)
  (* Lemma mconsr_mr0 : forall {n} (v : @vec T n) (m : @mat T 0 n), *)
  (*   mconsr v m = [v]. *)
  (* Proof. intros. destruct m. unfold mconsr. auto. Qed. *)
  
  (* (** Construct a matrix by rows with the matrix which row column is 0 *) *)
  (* Lemma mconsr_mc0 : forall {n} (v : @vec T 0) (m : @mat T n 0), *)
  (*   mconsr v m = (tt, m). *)
  (* Proof. intros. destruct v. unfold mconsr. auto. Qed. *)
  
  (* (** Construct a matrix by columns with the matrix which row number is 0 *) *)
  (* Lemma mconsc_mr0 : forall {n} (v : @vec T 0) (m : @vec (@vec T n) 0), *)
  (*   mconsc v m = tt. *)
  (* Proof. intros. destruct m. unfold mconsc. auto. Qed.   *)

  
  (* Definition det_of_mat_3_3 (m : mat 3 3) : T := *)
  (*   let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := *)
  (*     m2t_3x3 m in *)
  (*   let b1 := (a11 * a22 * a33)%T in *)
  (*   let b2 := (a12 * a23 * a31)%T in *)
  (*   let b3 := (a13 * a21 * a32)%T in *)
  (*   let c1 := (a11 * a23 * a32)%T in *)
  (*   let c2 := (a12 * a21 * a33)%T in *)
  (*   let c3 := (a13 * a22 * a31)%T in *)
  (*   let b := (b1 + b2 + b3)%T in *)
  (*   let c := (c1 + c2 + c3)%T in *)
  (*     (b - c)%T. *)

  (* Definition skew_sym_mat_of_v3 (v : V3) : mat 3 3. *)
  (* Proof. *)
  (*   destruct (v3_to_t3 v) as [[x y] z]. *)
  (*   refine (mk_mat_3_3  *)
  (*     T0    (-z)    y *)
  (*     z     T0     (-x) *)
  (*     (-y)  x       T0)%T. *)
  (* Defined. *)
  
  (* Definition v3cross (v1 v2 : V3) : vec 3 := (skew_sym_mat_of_v3 v1) * v2. *)
  
  (* Definition so3 (m : mat 3 3) : Prop :=  *)
  (*   let so3_mul_unit : Prop := (m \T) * m = mat1 3 in *)
  (*   let so3_det : Prop := (det_of_mat_3_3 m) = Aone in *)
  (*     so3_mul_unit /\ so3_det. *)

End Extra.


(* ======================================================================= *)
(** ** Matrix Inversion with gauss elimination, by ShenNan. *)
Section MatInv.

  (** fold a sequence to a value *)
  Fixpoint reduce {T} (n: nat) (f: T -> nat -> T) (zero: T) : T :=
    match n with
    | O => zero
    | S n' => f (reduce n' f zero) n'
    end.
  
  (* The process of "reduce 5 f 0" *)
  (* f (reduce 4 f 0) 4 *)
  (* f (f (reduce 3 f 0) 3) 4 *)
  (* f (f (f (reduce 2 f 0) 2) 3) 4 *)
  (* f (f (f (f (reduce 1 f 0) 1) 2) 3) 4 *)
  (* f (f (f (f (f (reduce 0 f 0) 1) 2) 3) 4 *)
  (* f (f (f (f (f 0 1) 2) 3) 4 *)
  (* Compute reduce 5 Nat.add 0. *)

  (* Understand the "reduce" function *)
  Section test.
    (*   R a f 3 *)
    (* = f (R a f 2) 2 *)
    (* = f (f (R a f 1) 1) 2 *)
    (* = f (f (f (R a f 0) 0) 1) 2 *)
    (* = f (f (f a 0) 1) 2 *)
    (* that is: (a0 + f0) + f1 + ... *)
    Let Fixpoint reduce' {T} (a0:T) (f: T -> nat -> T) (n:nat) : T :=
      match n with
      | O => a0
      | S n' => f (reduce' a0 f n') n'
      end.

    Import Reals.
    Let f1 : nat -> R := fun i => INR i.
    (* Compute reduce' R0 (fun r0 i => Rplus r0 (f1 i)) 5. *)
    (* Compute reduce' 0 Nat.add 5. *)

  End test.


  (** 任给两个序列f g，个数n，以及关系R，生成所有这些点对点对上的关系 *)
  Definition pointwise_n {T} (n: nat) (R: relation T) : relation (nat -> T) :=
    fun (f g : nat -> T) => forall (i: nat), i < n -> R (f i) (g i).

  (** 对于序列m1 m2, 若前 S n 个点对上都有关系R，则前 n 个点对上也有关系R。*)
  Lemma pointwise_n_decr {A}:
    forall (n : nat) (m1 m2 : nat -> A) (R : relation A),
      pointwise_n (S n) R m1 m2 -> pointwise_n n R m1 m2.
  Proof. unfold pointwise_n. intuition. Qed.

  
  Context `{F : Field}.
  Infix "+" := Tadd.
  Infix "*" := Tmul.
  Infix "*" := (mmul (T0:=T0)(Tadd:=Tadd)(Tmul:=Tmul)) : mat_scope.

  (* sum f(0) f(1) ... f(k-1) *)
  Notation sum k f := (reduce k (fun acc x => (acc + f x)%T) T0).

  (** (m1 * m2)[i,j] = m1.row[i] dot m2.col[j] *)
  Parameter Mtimes_help : forall {m n p} (m1: @mat T m n) (m2: @mat T n p),
    forall i j,
      i < m -> j < p ->
      mnth T0 (m1 * m2)%M i j =
        sum n (fun k => ((mnth T0 m1 i k) * (mnth T0 m2 k j))%T).

  (** (f m1 m2)[i,j] = f m1[i,j] m2[i,j] *)
  Parameter Melement_op_help :
    forall {m n} (m1: @mat T m n) (m2: @mat T m n) (op: T -> T -> T),
    forall i j,
      i < m -> j < n ->
      mnth T0 (mmap2 op m1 m2) i j = op (mnth T0 m1 i j) (mnth T0 m2 i j).

End MatInv.


Module coordinate_transform_test.

  Import Reals.
  Open Scope R.
  
  (* ref:
  https://en.wikipedia.org/wiki/Matrix_(mathematics)#Basic_operations
   *)

  Infix "*" := Rmult.
  Infix "+" := Rplus.
  Infix "+" := (madd (Tadd:=Rplus)) : mat_scope.
  Infix "*" := (mmul (Tadd:=Rplus) (Tmul:=Rmult) (T0:=R0)) : mat_scope.
  Infix "c*" := (mcmul (Tmul:=Rmult)) : mat_scope.
  Notation "m \T" := (mtrans m) : mat_scope.

  Open Scope mat_scope.

  Definition m1 := l2m 0 2 3 [[1;3;1];[1;0;0]].
  Definition m2 := l2m 0 2 3 [[0;0;5];[7;5;0]].
  Definition m3 := l2m 0 2 3 [[1;3;6];[8;5;0]].
  Example madd_m1_m2_eq_m3 : m1 + m2 = m3.
  Proof. apply meq_iff. cbn. repeat f_equal; ring. Qed.

  Definition m4 := l2m 0 2 3 [[1; 8;-3];[4;-2; 5]].
  Definition m5 := l2m 0 2 3 [[2;16;-6];[8;-4;10]].
  Example mscale_2_m4_eq_m5 : 2 c* m4 = m5.
  Proof. apply meq_iff. cbn. repeat f_equal; ring. Qed.
  
  Definition m6 := l2m 0 2 3 [[1;2;3];[0;-6;7]].
  Definition m7 := l2m 0 3 2 [[1;0];[2;-6];[3;7]].
  Example mtrans_m6_eq_m7 : m6\T = m7.
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


(* ==================================== *)
(** ** Determinant of a matrix *)

Section mdet.
  Context `{R : Ring}.
  Add Ring ring_inst : (make_ring_theory R).
  
  Infix "=" := Teq : T_scope.
  Infix "!=" := (fun a b => ~(a = b)) : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Asub := (fun x y => Tadd x (Topp y)).
  Infix "-" := Asub : T_scope.
  Infix "*" := Tmul : T_scope.

  Infix "*" := (mmul (Tadd:=Tadd)(T0:=T0)(Tmul:=Tmul)) : mat_scope.
  Infix "=" := (@meq _ Teq _ _) : mat_scope.
  Notation smat n := (smat T n).

  (** *** Determinant of a square matrix (original definition) *)
  Section def.

    (* ? *)
    (* Variable a b c : T. *)
    (* Compute perm 0 (seq 0 3). *)
    (* Let dl := perm 0 (seq 0 3). *)
    (* Let l := [1;2;3]. *)
    (* Compute nth 1 l 0. *)
    (* Compute map (fun i => (i, nth i l 0)) (seq 0 3). *)
    (* Compute map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)

  End def.
  (* Let dl1 := map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)
  (* Variable a00 a01 a02 a10 a11 a12 a20 a21 a22 : T. *)
  (* Definition m : smat 3 := mat_3_3 a00 a01 a02 a10 a11 a12 a20 a21 a22. *)
  (* Compute map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)

  (* (** all items in a determinant *) *)
  (* Let dl2 := map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)
  (* Compute dl2. *)

  (* Definition n := 3. *)
  (* Compute perm 0 (seq 0 n). (* *)
   (*  = [[0; 1; 2]; [0; 2; 1]; [1; 0; 2]; [1; 2; 0]; [2; 0; 1]; [2; 1; 0]] *)
   (*  : list (list nat) *) *)

  (* Definition item_of_det {n : nat} (m : smat n) (l : list nat) : T := *)
  (*   fold_left Tmul (map (fun i => m!i!(nth i l 0)) l) T1. *)

  (* (** Definition of determinant *) *)
  (* Definition det_def {n : nat} (m : smat n) : T := *)
  (*   fold_left Tadd (map (fun l => item_of_det m l) (perm 0 (seq 0 n))) T0. *)

  (* Compute det_orig m. *)
  
  (* Compute fold_left Tmul [a00;a01;a02]. *)
  (* Compute fold_left Tadd. *)
  

  (** Get the sub square matrix which remove r-th row and c-th column
        from a square matrix. *)
  Definition msubmat {n} (m : smat (S n)) (r c : nat) : smat n :=
    f2m
      (fun i j =>
         let i' := (if i <? r then i else S i) in
         let j' := (if j <? c then j else S j) in
         m $ i' $ j').

  Global Instance submat_mor (n : nat) :
    Proper (meq (Teq:=Teq) => eq => eq => meq (Teq:=Teq)) (@msubmat n).
  Proof. simp_proper. lma. all: apply H; auto; lia. Qed.
  

  (** Try to prove a proposition such as:
      "~(exp1 = 0) -> ~(exp2 = 0)" *)
  Ltac reverse_neq0_neq0 :=
    match goal with
    | H: ~(?e1 = T0)%T |- ~(?e2 = T0)%T =>
        let H1 := fresh "H1" in
        intro H1; destruct H; ring_simplify; ring_simplify in H1;
        try rewrite H1; try easy
    end.

  (** Determinant of a square matrix, by expanding the first row *)
  Fixpoint mdet {n} : smat n -> T :=
    match n with
    | 0 => fun _ => T1
    | S n' =>
        fun m =>
          fold_left Tadd
            (map (fun i =>
                    let a := if Nat.even i then (m$0$i) else (-(m$0$i))%T in
                    let d := mdet (msubmat m 0 i) in
                    (a * d)%T) (seq 0 n)) T0
    end.

  Global Instance mdet_mor (n : nat) : Proper (meq (Teq:=Teq) => Teq) (@mdet n).
  Proof.
    simp_proper. induction n; intros; try easy. simpl.
    apply fold_left_aeq_mor.
    - apply map_seq_eq. intros. f_equiv.
      + destruct (Nat.even i). apply H; lia. f_equiv. apply H; lia.
      + apply IHn. rewrite H. easy.
    - f_equiv. f_equiv.
      + apply m2f_mor; auto; lia.
      + apply IHn. rewrite H. easy.
  Qed.

  (** *** Properties of determinant *)
  Section props.

    Lemma mdet_1 : forall {n}, (@mdet n (mat1 T0 T1) = T1)%T.
    Proof.
    Admitted.

    Lemma mdet_mtrans : forall {n} (m : smat n), (mdet (m\T) = mdet m)%T.
    Proof.
    Admitted.

    Lemma mdet_mmul : forall {n} (m p : smat n), (mdet (m * p)%M = mdet m * mdet p)%T.
    Proof.
    Admitted.

  End props.

  
  (** *** Determinant on concrete dimensions *)
  Section mdet_concrete.

    (** Determinant of a matrix of dimension-1 *)
    Definition mdet1 (m : smat 1) := m.11.

    (** mdet1 m = mdet m *)
    Lemma mdet1_eq_mdet : forall m, (mdet1 m = mdet m)%T.
    Proof. intros. mat2fun. ring. Qed.
    
    (** mdet m <> 0 <-> mdet_exp <> 0 *)
    Lemma mdet1_neq0_iff : forall (m : smat 1),
        (mdet m != T0) <-> (m.11 != T0).
    Proof. intros. split; intros; mat2fun; reverse_neq0_neq0. Qed.

    (** Determinant of a matrix of dimension-2 *)
    Definition mdet2 (m : smat 2) := (m.11*m.22 - m.12*m.21)%T.

    (** mdet2 m = mdet m *)
    Lemma mdet2_eq_mdet : forall m, (mdet2 m = mdet m)%T.
    Proof. intros. mat2fun. cbv. ring. Qed.

    (** mdet m <> 0 <-> mdet_exp <> 0 *)
    Lemma mdet2_neq0_iff : forall (m : smat 2),
        mdet m != T0 <->  (m.11*m.22 - m.12*m.21 != T0)%T.
    Proof. intros. split; intros; mat2fun; reverse_neq0_neq0. Qed.

    (** Determinant of a matrix of dimension-3 *)
    Definition mdet3 (m : smat 3) :=
      (m.11 * m.22 * m.33 - m.11 * m.23 * m.32 - 
         m.12 * m.21 * m.33 + m.12 * m.23 * m.31 + 
         m.13 * m.21 * m.32 - m.13 * m.22 * m.31)%T.

    (** mdet3 m = mdet m *)
    Lemma mdet3_eq_mdet : forall m, (mdet3 m = mdet m)%T.
    Proof. intros. mat2fun. cbv. ring. Qed.
    
    (** mdet m <> 0 <-> mdet_exp <> 0 *)
    Lemma mdet3_neq0_iff : forall (m : smat 3),
        mdet m != T0 <->
          (m.11 * m.22 * m.33 - m.11 * m.23 * m.32 - 
             m.12 * m.21 * m.33 + m.12 * m.23 * m.31 + 
             m.13 * m.21 * m.32 - m.13 * m.22 * m.31 != T0)%T.
    Proof. intros. split; intros; mat2fun; reverse_neq0_neq0. Qed.

    (** Determinant of a matrix of dimension-4 *)
    Definition mdet4 (m : smat 4) :=
      (m.11*m.22*m.33*m.44 - m.11*m.22*m.34*m.43 - m.11*m.23*m.32*m.44 + m.11*m.23*m.34*m.42 +
         m.11*m.24*m.32*m.43 - m.11*m.24*m.33*m.42 - m.12*m.21*m.33*m.44 + m.12*m.21*m.34*m.43 +
         m.12*m.23*m.31*m.44 - m.12*m.23*m.34*m.41 - m.12*m.24*m.31*m.43 + m.12*m.24*m.33*m.41 +
         m.13*m.21*m.32*m.44 - m.13*m.21*m.34*m.42 - m.13*m.22*m.31*m.44 + m.13*m.22*m.34*m.41 +
         m.13*m.24*m.31*m.42 - m.13*m.24*m.32*m.41 - m.14*m.21*m.32*m.43 + m.14*m.21*m.33*m.42 +
         m.14*m.22*m.31*m.43 - m.14*m.22*m.33*m.41 - m.14*m.23*m.31*m.42 + m.14*m.23*m.32*m.41)%T.

    (** mdet4 m = mdet m *)
    Lemma mdet4_eq_mdet : forall m, (mdet4 m = mdet m)%T.
    Proof. intros. mat2fun. cbv. ring. Qed.
    
  End mdet_concrete.

End mdet.
  

(* ==================================== *)
(** ** Inverse matrix with the help of determinant and adjoint matrix. *)
Section matrix_inversion.
  Context `{R:Ring}.
  Add Ring ring_thy_inst : (make_ring_theory R).

  Infix "=" := Teq : T_scope.
  Infix "!=" := (fun a b => ~(a = b)) : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Asub := (fun x y => Tadd x (Topp y)).
  Infix "-" := Asub : T_scope.
  Infix "*" := Tmul : T_scope.

  Infix "*" := (@mmul T Tadd T0 Tmul _ _ _) : mat_scope.
  Infix "c*" := (@mcmul T Tmul _ _) : mat_scope.
  Infix "=" := (meq (Teq:=Teq)) : mat_scope.
  (* Notation "m ! i ! j " := (mnth T0 m i j) : mat_scope. *)
  Notation mat1 := (mat1 T0 T1).
  Notation l2m := (@l2m T T0 _ _).
  Notation smat n := (smat T n).
  Notation mdet := (mdet (Tadd:=Tadd)(T0:=T0)(Topp:=Topp)(Tmul:=Tmul)(T1:=T1)).
  Notation mdet2 := (mdet2 (Tadd:=Tadd)(Topp:=Topp)(Tmul:=Tmul)).
  Notation mdet3 := (mdet3 (Tadd:=Tadd)(Topp:=Topp)(Tmul:=Tmul)).
  Notation mdet4 := (mdet4 (Tadd:=Tadd)(Topp:=Topp)(Tmul:=Tmul)).

  (** Try to prove a proposition such as:
      "~(exp1 = 0) -> ~(exp2 = 0)" *)
  Ltac reverse_neq0_neq0 :=
    match goal with
    | H: ~(?e1 = T0)%T |- ~(?e2 = T0)%T =>
        let H1 := fresh "H1" in
        intro H1; destruct H; ring_simplify; ring_simplify in H1;
        try rewrite H1; try easy
    end.

  (** T square matrix is invertible, if its determinant is nonzero *)
  Definition minvertible {n} (m : smat n) : Prop :=
    exists m' : smat n, (m * m' = mat1) \/ (m' * m = mat1).

  (** invertible mat1 *)
  Lemma minvertible_1 : forall n : nat, @minvertible n mat1.
  Proof.
  Admitted.

  (** T square matrix is invertible, if its determinant is nonzero *)
  Lemma minvertible_iff_mdet_n0 : forall {n} (m : smat n),
      minvertible m <-> mdet m <> T0.
  Proof.
  Admitted.

  (** invertible m -> invertible (m\T) *)
  Lemma minvertible_trans : forall n (m : smat n),
      minvertible m -> minvertible (m\T).
  Proof.
  Admitted.

  (** invertible m -> invertible p -> invertible (m * p) *)
  Lemma minvertible_mul : forall n (m p : smat n),
      minvertible m -> minvertible p -> minvertible (m * p).
  Proof.
  Admitted.

  
  (** *** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  (** That is: adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  Section adj.

    Definition madj {n} : smat n -> smat n := 
      match n with
      | O => fun m => m 
      | S n' =>
          fun m =>
            f2m (fun i j =>
                   let s := if Nat.even (i + j) then T1 else (-T1)%T in
                   let d := mdet (msubmat m j i) in 
                   (s * d)%T)
      end.

    Global Instance madj_mor (n:nat) :
      Proper (meq (Teq:=Teq) => meq (Teq:=Teq)) (@madj n).
    Proof.
      simp_proper. intros. destruct n; auto. simpl.
      unfold meq; intros; simpl. f_equiv. rewrite H. easy.
    Qed.

  End adj.

  (** *** We need a field structure *)
  Context `{F:Field T Tadd T0 Topp Tmul T1 Tinv Teq}.
  Add Field field_thy_inst : (make_field_theory F).

  Notation "/ a" := (Tinv a) : T_scope.
  Notation Tdiv := (fun x y => Tmul x (Tinv y)).
  Infix "/" := Tdiv : T_scope.

  (** *** Cramer rule *)
  Section cramer_rule.
    
    (** Exchange one column of a square matrix *)
    Definition mchgcol {n} (m : smat n) (k : nat) (v : mat n 1) : smat n :=
      f2m (fun i j => if (Nat.eqb j k) then (v$i$0)%nat else m$i$j).
    
    (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid only when D is not zero *)
    Definition cramerRule {n} (A : smat n) (b : mat n 1) : mat n 1 :=
      let D := mdet T in
      f2m (fun i j => let Di := mdet (mchgcol T i b) in (Di / D)).
    
  End cramer_rule.

  
  (** *** Matrix Inversion *)
  Section inv.

    Definition minv {n} (m : smat n) := (T1 / mdet m) c* (madj m).
    Notation "m ⁻¹" := (minv m) : mat_scope.

    Global Instance minv_mor (n : nat) :
      Proper (meq (Teq:=Teq) => meq (Teq:=Teq)) (@minv n).
    Proof. simp_proper. intros. unfold minv. rewrite H. easy. Qed.
    
    (** m * p = mat1 -> m ⁻¹ = p *)
    Lemma mmul_eq1_iff_minv_l : forall {n} (m p : smat n),
        m * p = mat1 <-> minv m = p.
    Proof.
    Admitted.

    (** m * p = mat1 <-> p ⁻¹ = m *)
    Lemma mmul_eq1_iff_minv_r : forall {n} (m p : smat n),
        m * p = mat1 <-> minv p = m.
    Proof.
    Admitted.

    (** invertible m -> invertible (m⁻¹) *)
    Lemma minvertible_inv : forall {n} (m : smat n), minvertible m -> minvertible (m⁻¹).
    Proof.
    Admitted.

    (** m * m⁻¹ = mat1 *)
    Lemma mmul_minv_r : forall {n} (m : smat n), m * m⁻¹ = mat1.
    Proof.
    Admitted.

    (** m⁻¹ * m = mat1 *)
    Lemma mmul_minv_l : forall {n} (m : smat n), (minv m) * m = mat1.
    Proof.
    Admitted.

    (** mat1 ⁻¹ = mat1 *)
    Lemma minv_1 : forall {n}, @minv n mat1 = mat1.
    Proof.
    Admitted.

    (** m ⁻¹ ⁻¹ = m *)
    Lemma minv_minv : forall {n} (m : smat n), minvertible m -> m ⁻¹ ⁻¹ = m.
    Proof.
    Admitted.

    (** (m * m') ⁻¹ = m' ⁻¹ * m ⁻¹ *)
    Lemma minv_mmul : forall {n} (m m' : smat n),
        minvertible m -> minvertible m' -> (m * m')⁻¹ = m' ⁻¹ * m ⁻¹.
    Proof.
    Admitted.

    (** (m\T) ⁻¹ = (m ⁻¹)\T *)
    Lemma minv_mtrans : forall {n} (m : smat n), minvertible m -> (m\T) ⁻¹ = (m ⁻¹)\T.
    Proof.
    Admitted.

    (** mdet (m⁻¹) = 1 / (mdet m) *)
    Lemma mdet_minv : forall {n} (m : smat n), (mdet (m ⁻¹) = T1 / (mdet m))%T.
    Admitted.
    
  End inv.

  
  (** *** Direct compute inversion of a symbol matrix of 1/2/3rd order. *)
  Section FindFormula.
    Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : T.
    Let m1 := mk_mat_1_1 (T0:=T0) a11.
    Let m2 := mk_mat_2_2 (T0:=T0) a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 (T0:=T0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
    Let m4 := mk_mat_4_4 (T0:=T0)
                a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44.

    (* Compute (m2l (minv m1)). *)
    (* Compute (m2l (minv m2)). *)
    (* Compute (m2l (minv m3)). *)
    (* Compute (m2l (minv m4)). *)
    (* Although this is correct, but the expression is too long. *)
    (* We want to simplify it with RAST *)
    
  End FindFormula.

  
  (** *** Inversion matrix of common finite dimension *)
  Section concrete.
    Definition minv1 (m : smat 1) : smat 1 := l2m [[T1/m.11]].

    (** mdet m <> 0 -> minv1 m = inv m *)
    Lemma minv1_eq_inv : forall m, mdet m != T0 -> minv1 m = minv m.
    Proof. lma. reverse_neq0_neq0. Qed.

    (** minv1 m * m = mat1 *)
    Lemma minv1_correct_l : forall (m : smat 1),
        mdet m != T0 -> (minv1 m) * m = mat1.
    Proof. lma. reverse_neq0_neq0. Qed.

    (** m * minv1 m = mat1 *)
    Lemma minv1_correct_r : forall (m : smat 1),
        mdet m != T0 -> m * (minv1 m) = mat1.
    Proof. lma. reverse_neq0_neq0. Qed.

    (* ==================================== *)
    (** ** Inversion matrix of dimension-2 *)
    Definition minv2 (m : smat 2) : smat 2 :=
      let d := mdet2 m in
      (l2m [[m.22/d; -m.12/d]; [-m.21/d; m.11/d]])%T.

    (** mdet m <> 0 -> minv2 m = inv m *)
    Lemma minv2_eq_inv : forall m, mdet m != T0 -> minv2 m = minv m.
    Proof. lma; reverse_neq0_neq0. Qed.
    
    (** minv2 m * m = mat1 *)
    Lemma minv2_correct_l : forall (m : smat 2),
        mdet m != T0 -> (minv2 m) * m = mat1.
    Proof. lma; reverse_neq0_neq0. Qed.
    
    (** m * minv2 m = mat1 *)
    Lemma minv2_correct_r : forall (m : smat 2),
        mdet m != T0 -> m * (minv2 m) = mat1.
    Proof. lma; reverse_neq0_neq0. Qed.
    
    (* ==================================== *)
    (** ** Inversion matrix of dimension-3 *)
    (* Note, this formula could be provided from matlab, thus avoiding manual work *)
    Definition minv3 (m : smat 3) : smat 3 :=
      let d := mdet3 m in
      (l2m
         [[(m.22*m.33-m.23*m.32)/d; -(m.12*m.33-m.13*m.32)/d; (m.12*m.23-m.13*m.22)/d];
          [-(m.21*m.33-m.23*m.31)/d; (m.11*m.33-m.13*m.31)/d; -(m.11*m.23-m.13*m.21)/d];
          [(m.21*m.32-m.22*m.31)/d; -(m.11*m.32-m.12*m.31)/d; (m.11*m.22-m.12*m.21)/d]])%T.
    
    (** mdet m <> 0 -> minv3 m = inv m *)
    Lemma minv3_eq_inv : forall m, mdet m != T0 -> minv3 m = minv m.
    Proof.
      (* lma; reverse_neq0_neq0. *)
      Opaque Matrix.mdet Matrix.mdet3.
      lma;  rewrite mdet3_eq_mdet; field_simplify; f_equiv; auto.
      Transparent Matrix.mdet Matrix.mdet3.
      all: cbv; field; auto.
    Qed.
    
    (** minv3 m * m = mat1 *)
    Lemma minv3_correct_l : forall (m : smat 3),
        mdet m != T0 -> (minv3 m) * m = mat1.
    Proof.
      lma; reverse_neq0_neq0.
    Qed.
    
    (** m * minv3 m = mat1 *)
    Lemma minv3_correct_r : forall (m : smat 3),
        mdet m != T0 -> m * (minv3 m) = mat1.
    Proof. lma; reverse_neq0_neq0. Qed.

    (* ==================================== *)
    (** ** Inversion matrix of dimension-3 *)
    (* Note, this formula could be provided from matlab, thus avoiding manual work *)
    Definition minv4 (m : smat 4) : smat 4 :=
      let d := mdet4 m in
      l2m
        [[(m.22*m.33*m.44 - m.22*m.34*m.43 - m.23*m.32*m.44 + m.23*m.34*m.42 + m.24*m.32*m.43 - m.24*m.33*m.42)/d;
          -(m.12*m.33*m.44 - m.12*m.34*m.43 - m.13*m.32*m.44 + m.13*m.34*m.42 + m.14*m.32*m.43 - m.14*m.33*m.42)/d;
          (m.12*m.23*m.44 - m.12*m.24*m.43 - m.13*m.22*m.44 + m.13*m.24*m.42 + m.14*m.22*m.43 - m.14*m.23*m.42)/d;
          -(m.12*m.23*m.34 - m.12*m.24*m.33 - m.13*m.22*m.34 + m.13*m.24*m.32 + m.14*m.22*m.33 - m.14*m.23*m.32)/d];
         [-(m.21*m.33*m.44 - m.21*m.34*m.43 - m.23*m.31*m.44 + m.23*m.34*m.41 + m.24*m.31*m.43 - m.24*m.33*m.41)/d;
          (m.11*m.33*m.44 - m.11*m.34*m.43 - m.13*m.31*m.44 + m.13*m.34*m.41 + m.14*m.31*m.43 - m.14*m.33*m.41)/d;
          -(m.11*m.23*m.44 - m.11*m.24*m.43 - m.13*m.21*m.44 + m.13*m.24*m.41 + m.14*m.21*m.43 - m.14*m.23*m.41)/d;
          (m.11*m.23*m.34 - m.11*m.24*m.33 - m.13*m.21*m.34 + m.13*m.24*m.31 + m.14*m.21*m.33 - m.14*m.23*m.31)/d];
         [(m.21*m.32*m.44 - m.21*m.34*m.42 - m.22*m.31*m.44 + m.22*m.34*m.41 + m.24*m.31*m.42 - m.24*m.32*m.41)/d;
          -(m.11*m.32*m.44 - m.11*m.34*m.42 - m.12*m.31*m.44 + m.12*m.34*m.41 + m.14*m.31*m.42 - m.14*m.32*m.41)/d;
          (m.11*m.22*m.44 - m.11*m.24*m.42 - m.12*m.21*m.44 + m.12*m.24*m.41 + m.14*m.21*m.42 - m.14*m.22*m.41)/d;
          -(m.11*m.22*m.34 - m.11*m.24*m.32 - m.12*m.21*m.34 + m.12*m.24*m.31 + m.14*m.21*m.32 - m.14*m.22*m.31)/d];
         [-(m.21*m.32*m.43 - m.21*m.33*m.42 - m.22*m.31*m.43 + m.22*m.33*m.41 + m.23*m.31*m.42 - m.23*m.32*m.41)/d;
          (m.11*m.32*m.43 - m.11*m.33*m.42 - m.12*m.31*m.43 + m.12*m.33*m.41 + m.13*m.31*m.42 - m.13*m.32*m.41)/d;
          -(m.11*m.22*m.43 - m.11*m.23*m.42 - m.12*m.21*m.43 + m.12*m.23*m.41 + m.13*m.21*m.42 - m.13*m.22*m.41)/d;
          (m.11*m.22*m.33 - m.11*m.23*m.32 - m.12*m.21*m.33 + m.12*m.23*m.31 + m.13*m.21*m.32 - m.13*m.22*m.31)/d]]%T.
    
    (** mdet m <> 0 -> minv4 m = inv m *)
    Lemma minv4_eq_inv : forall m, mdet m != T0 -> minv4 m = minv m.
    (* Proof. *)
    (*   (* lma; reverse_neq0_neq0. *) *)
    (*   Opaque Matrix.mdet Matrix.mdet3. *)
    (*   lma;  rewrite mdet4_eq_mdet; field_simplify; f_equiv; auto. *)
    (*   Transparent Matrix.mdet Matrix.mdet3. *)
    (*   all: cbv; field; auto. *)
    (*   Qed. *)
    Admitted.

    (** minv4 m * m = mat1 *)
    Lemma minv4_correct_l : forall (m : smat 4),
        mdet m != T0 -> (minv4 m) * m = mat1.
    (* Proof. lma; reverse_neq0_neq0. Qed. *)
    Admitted.
    
    (** m * minv4 m = mat1 *)
    Lemma minv4_correct_r : forall (m : smat 4),
        mdet m != T0 -> m * (minv4 m) = mat1.
    (* Proof. lma; reverse_neq0_neq0. Qed. *)
    Admitted.
  
  End concrete.

End matrix_inversion.

Section test.
  (* T Formal Proof of Sasaki-Murao Algorithm
     https://pdfs.semanticscholar.org/ddc3/e8185e10a1d476497de676a3fd1a6ae29595.pdf
   *)
  Import ZArith.
  Open Scope Z.
  Let m1 := @l2m _ 0 4 4 [[2;2;4;5];[5;8;9;3];[1;2;8;5];[6;6;7;1]].
  Notation mdet := (mdet (Tadd:=Z.add) (Topp:=Z.opp) (Tmul:=Z.mul) (T0:=0) (T1:=1)).
  (* Compute mdet m1. *)
End test.


(* ==================================== *)
(** ** Orthogonal matrix *)
Section OrthogonalMatrix.

  (*
  Ref: 
  1. https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group
  2. https://en.wikipedia.org/wiki/Orthogonal_matrix

  -------------------------- O(n) -----------------------------------
  In mathematics, the orthogonal group in dimension n, denoted O(n), is the 
  group of distance-preserving transformations of a Euclidean space of dimension
  n that preserve a fixed point, where the group operation is given by composing
  transformations. 

  The orthogonal group is sometimes called the general orthogonal group, by 
  analogy with the general linear group. Equivalently, it is the group of 
  n × n matrices, where the group operation is given by matrix multiplication 
  (an orthogonal matrix is a real matrix whose inverse equals its transpose). 

  By extension, for any field F, an n × n matrix with entries in F such that its 
  inverse equals its transpose is called an orthogonal matrix over F. 
  The n × n orthogonal matrices form a subgroup, denoted O(n,F), of the general 
  linear group GL(n,F); that is 
         O(n,F) = {Q ∈ GL(n,F) ∣ Q\T * Q = Q * Q\T = I}.
  
  -------------------------- O(3) -----------------------------------
  Every rotation maps an orthonormal basis of R^3 to another orthonormal basis.
  Like any linear transformation of finite-dimensional vector spaces, a rotation 
  can always be represented by a matrix.

  Let R be a given rotation. With respect to the standard basis e1, e2, e3 of R^3 
  the columns of R are given by (Re1, Re2, Re3). Since the standard basis is 
  orthonormal, and since R preserves angles and length, the columns of R form 
  another orthonormal basis. This orthonormality condition can be expressed in 
  the form 
     R\T * R = R * R\T = I,
  where R\T denotes the transpose of R and I is the 3 × 3 identity matrix. 
  Matrices for which this property holds are called orthogonal matrices.

  The group of all 3 × 3 orthogonal matrices is denoted O(3), and consists of all 
  proper and improper rotations.

  In addition to preserving length, proper rotations must also preserve 
  orientation. 
  T matrix will preserve or reverse orientation according to whether the 
  determinant of the matrix is positive or negative. 
  For an orthogonal matrix R, note that "det R\T = det R" implies 
  "(det R)^2 = 1", so that "det R = ±1".

  The subgroup of orthogonal matrices with determinant +1 is called the special 
  orthogonal group, denoted SO(3). 
  Thus every rotation can be represented uniquely by an orthogonal matrix with unit 
  determinant. Moreover, since composition of rotations corresponds to matrix 
  multiplication, the rotation group is isomorphic to the special orthogonal group 
  SO(3).

  Improper rotations correspond to orthogonal matrices with determinant −1, and 
  they do not form a group because the product of two improper rotations is a 
  proper rotation. 

  ----------- 中文笔记 ---------------
  Orthogonal: 正交的，一般用于描述一组基是相互正交的（垂直的）
  Orthonormal Basic: 标准正交基，两两正交，并且单个向量具有单位长度。
  Gram-Schmidt: 施密特正交化。以2维为例，该算法保持r1不变，r3的改变最多。
  有一种无偏差的递增正交化算法，不偏向特定轴，需要多次迭代（比如10次），然后用1次
    标准的Gram-Schmidt算法来保证完全正交。
  O(n): Orthogonal Group 正交群（保距，行列式为±1）
  SO(n): Special Orthogonal Group 特殊正交群（保持手性，行列式为1）
    Proper rotation: 正确的旋转 (行列式为1)
    Improper rotation: 错误的旋转（行列式为-1）, rotation-reflect, 旋转反射，瑕旋转
  ----------------------
  补充一些理论：
  1. 特殊矩阵：对称（自伴）、斜对称（斜伴）、正交（酉）、正规矩阵
      实矩阵                      复矩阵
      条件           名称         条件            名称
  (1) T = A\T        对称阵       T = A\H         自伴阵
  (2) T = -A\T       斜称阵       T = -A\H        斜伴阵
  (3) AA\T = E       正交阵       AA\H = E        酉矩阵
  (4)                            T A\H=A\H T      正规矩阵
  其中，(1),(2),(3)都是正规矩阵

  正规矩阵的一个定理：每个 n*n 正规矩阵A，都有一个由对应于特征值λ1,...,λn的特征向量
  组成的完全正交基 x1,...,xn。
  若设 U = (x1,...,xn)，则 U 是酉矩阵，并且有
  U^{-1} T U = 对角阵 {λ1,...,λn}

  正交矩阵的应用（旋转）：若一个 n*n 实矩阵A是正交的，则其特征值等于
  ±1 或 e^{±iϕ}成对出现（ϕ是实数）。
  
  2. 特征值、特征向量、矩阵的谱
  (1) 方阵A，使方程 T x = λ x 有非零解时，λ(复数)称一个特征值，x称对应的特征向量
  (2) A的所有特征值的集合称为A的谱 σ(A)，A的特征值的绝对值的最大值称为A的谱半径，记做 r(A)
  (3) 特征方程：det(A-λE)=0，其解是A的特征值λ，λ的重数称为代数重数。
  (4) 设矩阵U是正交的（酉的），U的谱由数 e^{±iϕ} 组成，
      变换 x' = U x 对应于笛卡尔坐标系中的正向旋转，旋转角ϕ
      x1' = x1 * cos ϕ + x2 * sin ϕ
      y1' = - x1 * sin ϕ + x2 * cos ϕ
  (5) 谱定理
  (i) 自伴矩阵的谱在实直线上
  (ii) 斜伴矩阵的谱在虚轴上
  (iii) 酉矩阵的谱在单位圆上

  3. 正交性

   *)

  Context `{F : Field}.
  Add Field field_inst : (make_field_theory F).
  Notation "1" := T1 : T_scope.
  Notation "0" := T0 : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "=" := Teq : T_scope.
  Infix "=" := (@meq _ Teq _ _) : mat_scope.
  Infix "*" := (@mmul _ Tadd T0 Tmul _ _ _) : mat_scope.
  Notation "m ⁻¹" := (@minv _ Tadd T0 Topp Tmul T1 Tinv _ m) : mat_scope.
  Notation smat n := (smat T n).
  Notation mat1 n := (@mat1 _ T0 T1 n).
  Notation minvertible := (@minvertible _ Tadd T0 Tmul T1 Teq _).
  Notation mdet := (@mdet _ Tadd T0 Topp Tmul T1 _).

  (* ================== *)
  (** *** Orthogonal matrix *)

  (** T square matrix m is an orthogonal matrix *)
  Definition morth {n} (m : smat n) : Prop := m\T * m = mat1 n.

  (** orthogonal m -> invertible m *)
  Lemma morth_invertible : forall {n} (m : smat n),
      morth m -> minvertible m.
  Proof. intros. hnf in *. exists (m\T). auto. Qed.

  (** orthogonal m -> m⁻¹ = m\T *)
  Lemma morth_imply_inv_eq_trans : forall {n} (m : smat n),
      morth m -> m⁻¹ = m\T.
  Proof. intros. red in H. apply mmul_eq1_iff_minv_r in H. auto. Qed.

  (** m⁻¹ = m\T -> orthogonal m*)
  Lemma minv_eq_trans_imply_morth : forall {n} (m : smat n),
      m⁻¹ = m\T -> morth m.
  Proof. intros. apply mmul_eq1_iff_minv_r in H. auto. Qed.

  (** orthogonal m <-> m\T * m = mat1 *)
  Lemma morth_iff_mul_trans_l : forall {n} (m : smat n),
      morth m <-> m\T * m = mat1 n.
  Proof. intros. red. auto. Qed.

  (** orthogonal m <-> m * m\T = mat1 *)
  Lemma morth_iff_mul_trans_r : forall {n} (m : smat n),
      morth m <-> m * m\T = mat1 n.
  Proof.
    intros. split; intros H.
    - apply mmul_eq1_iff_minv_r in H. rewrite <- H. apply mmul_minv_r.
    - red. apply mmul_eq1_iff_minv_l in H. rewrite <- H. apply mmul_minv_l.
  Qed.

  (** orthogonal mat1 *)
  Lemma morth_1 : forall {n}, morth (mat1 n).
  Proof. intros. red. rewrite mtrans_1, mmul_1_r. easy. Qed.

  (** orthogonal m -> orthogonal p -> orthogonal (m * p) *)
  Lemma morth_mul : forall {n} (m p : smat n),
      morth m -> morth p -> morth (m * p).
  Proof.
    intros. red. red in H, H0. rewrite mtrans_mmul.
    rewrite mmul_assoc. rewrite <- (mmul_assoc _ m).
    rewrite H. rewrite mmul_1_l. rewrite H0. easy.
  Qed.

  (** orthogonal m -> orthogonal m\T *)
  Lemma morth_mtrans : forall {n} (m : smat n), morth m -> morth (m\T).
  Proof.
    intros. red. rewrite mtrans_mtrans.
    apply morth_iff_mul_trans_r in H. auto.
  Qed.

  (** orthogonal m -> orthogonal m⁻¹ *)
  Lemma morth_minv : forall {n} (m : smat n), morth m -> morth (m⁻¹).
  Proof.
    intros. red.
    rewrite morth_imply_inv_eq_trans; auto. rewrite mtrans_mtrans.
    apply morth_iff_mul_trans_r; auto.
  Qed.
  
  (* ================== *)
  (** *** O(n): General Orthogonal Group, General Linear Group *)
  (* https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group *)
  Section GOn.
    
    (** The set of GOn *)
    Record GOn (n: nat) := {
        GOn_mat :> smat n;
        GOn_props : morth GOn_mat
      }.

    (** Equality of elements in GOn *)
    Definition GOn_eq {n} (s1 s2 : GOn n) : Prop := GOn_mat _ s1 = GOn_mat _ s2.

    (** GOn_eq is equivalence relation *)
    Lemma GOn_eq_equiv : forall n, Equivalence (@GOn_eq n).
    Proof.
      intros. unfold GOn_eq. constructor; hnf; intros; try easy.
      rewrite H; easy.
    Qed.

    (** Multiplication of elements in GOn *)
    Definition GOn_mul {n} (s1 s2 : GOn n) : GOn n.
      refine (Build_GOn n (s1 * s2) _).
      destruct s1 as [s1 H1], s2 as [s2 H2]. simpl.
      apply morth_mul; auto.
    Defined.

    (** Identity element in GOn *)
    Definition GOn_1 {n} : GOn n.
      refine (Build_GOn n (mat1 n) _).
      apply morth_1.
    Defined.

    (** GOn_mul is a proper morphism respect to GOn_eq *)
    Lemma GOn_mul_proper : forall n, Proper (GOn_eq => GOn_eq => GOn_eq) (@GOn_mul n).
    Proof. unfold GOn_eq in *. simp_proper. intros. simpl. rewrite H,H0. easy. Qed.

    (** GOn_mul is associative *)
    Lemma GOn_mul_assoc : forall n, Associative GOn_mul (@GOn_eq n).
    Proof. unfold GOn_eq. intros. constructor. intros; simpl. apply mmul_assoc. Qed.

    (** GOn_1 is left-identity-element of GOn_mul operation *)
    Lemma GOn_mul_id_l : forall n, IdentityLeft GOn_mul GOn_1 (@GOn_eq n).
    Proof. unfold GOn_eq. intros. constructor. intros; simpl. apply mmul_1_l. Qed.
    
    (** GOn_1 is right-identity-element of GOn_mul operation *)
    Lemma GOn_mul_id_r : forall n, IdentityRight GOn_mul GOn_1 (@GOn_eq n).
    Proof. unfold GOn_eq. intros. constructor. intros; simpl. apply mmul_1_r. Qed.

    (** <GOn, +, 1> is a monoid *)
    Lemma Monoid_GOn : forall n, Monoid (@GOn_mul n) GOn_1 GOn_eq.
    Proof.
      intros. constructor.
      - apply GOn_mul_proper.
      - apply GOn_eq_equiv.
      - apply GOn_mul_assoc.
      - apply GOn_mul_id_l.
      - apply GOn_mul_id_r.
    Qed.

    (** Inverse operation of multiplication in GOn *)
    Definition GOn_inv {n} (s : GOn n) : GOn n.
      refine (Build_GOn n (s\T) _). destruct s as [s H1]. simpl.
      apply morth_mtrans; auto.
    Defined.

    (** GOn_inv is a proper morphism respect to GOn_eq *)
    Lemma GOn_inv_proper : forall n, Proper (GOn_eq => GOn_eq) (@GOn_inv n).
    Proof. unfold GOn_eq in *. simp_proper. intros. simpl. rewrite H. easy. Qed.

    (** GOn_inv is left-inversion of <GOn_mul,GOn_1> *)
    Lemma GOn_mul_inv_l : forall n, InverseLeft GOn_mul GOn_1 GOn_inv (@GOn_eq n).
    Proof. unfold GOn_eq. intros. constructor. intros; simpl. apply a. Qed.

    (** GOn_inv is right-inversion of <GOn_mul,GOn_1> *)
    Lemma GOn_mul_inv_r : forall n, InverseRight GOn_mul GOn_1 GOn_inv (@GOn_eq n).
    Proof.
      unfold GOn_eq. intros. constructor. intros; simpl.
      apply morth_iff_mul_trans_r. apply a.
    Qed.

    (** <GOn, +, 1, /s> is a group *)
    Theorem Group_GOn : forall n, Group (@GOn_mul n) GOn_1 GOn_inv GOn_eq.
    Proof.
      intros. constructor.
      - apply Monoid_GOn.
      - apply GOn_mul_inv_l.
      - apply GOn_mul_inv_r.
      - apply GOn_mul_proper.
      - apply GOn_inv_proper.
    Qed.
  
    (** *** Extract the properties of GOn to its carrier *)

    (** m⁻¹ = m\T *)
    Lemma GOn_imply_inv_eq_trans : forall {n} (s : GOn n),
        let m := GOn_mat n s in
        m⁻¹ = m\T.
    Proof.
      intros. unfold m. destruct s as [m' H]. simpl in *.
      rewrite morth_imply_inv_eq_trans; auto. easy.
    Qed.

  End GOn.

  
  (* ================== *)
  (** ** SO(n): Special Orthogonal Group, Rotation Group *)
  (* https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group *)
  Section SOn.

    (** The set of SOn *)
    Record SOn (n: nat) := {
        SOn_mat :> smat n;
        SOn_props : (morth SOn_mat) /\ (mdet SOn_mat = 1)%T
      }.

    Definition SOn_eq {n} (s1 s2 : SOn n) : Prop := SOn_mat _ s1 = SOn_mat _ s2.

    Definition SOn_mul {n} (s1 s2 : SOn n) : SOn n.
      refine (Build_SOn n (s1 * s2) _).
      destruct s1 as [s1 [H1 H1']], s2 as [s2 [H2 H2']]. simpl. split.
      - apply morth_mul; auto.
      - rewrite mdet_mmul. rewrite H1', H2'. ring.
    Defined.

    Definition SOn_1 {n} : SOn n.
      refine (Build_SOn n (mat1 n) _). split.
      apply morth_1. apply mdet_1.
    Defined.

    (** SOn_eq is equivalence relation *)
    Lemma SOn_eq_equiv : forall n, Equivalence (@SOn_eq n).
    Proof.
      intros. unfold SOn_eq. constructor; hnf; intros; try easy.
      rewrite H; easy.
    Qed.

    (** SOn_mul is a proper morphism respect to SOn_eq *)
    Lemma SOn_mul_proper : forall n, Proper (SOn_eq => SOn_eq => SOn_eq) (@SOn_mul n).
    Proof. unfold SOn_eq in *. simp_proper. intros. simpl. rewrite H,H0. easy. Qed.

    (** SOn_mul is associative *)
    Lemma SOn_mul_assoc : forall n, Associative SOn_mul (@SOn_eq n).
    Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_assoc. Qed.

    (** SOn_1 is left-identity-element of SOn_mul operation *)
    Lemma SOn_mul_id_l : forall n, IdentityLeft SOn_mul SOn_1 (@SOn_eq n).
    Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_1_l. Qed.
    
    (** SOn_1 is right-identity-element of SOn_mul operation *)
    Lemma SOn_mul_id_r : forall n, IdentityRight SOn_mul SOn_1 (@SOn_eq n).
    Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_1_r. Qed.
    
    (** <SOn, +, 1> is a monoid *)
    Lemma Monoid_SOn : forall n, Monoid (@SOn_mul n) SOn_1 SOn_eq.
    Proof.
      intros. constructor.
      - apply SOn_mul_proper.
      - apply SOn_eq_equiv.
      - apply SOn_mul_assoc.
      - apply SOn_mul_id_l.
      - apply SOn_mul_id_r.
    Qed.

    Definition SOn_inv {n} (s : SOn n) : SOn n.
      refine (Build_SOn n (s\T) _).
      destruct s as [s [H1 H2]]; simpl. split.
      apply morth_mtrans; auto. rewrite mdet_mtrans. auto.
    Defined.

    (** SOn_inv is a proper morphism respect to SOn_eq *)
    Lemma SOn_inv_proper : forall n, Proper (SOn_eq => SOn_eq) (@SOn_inv n).
    Proof. unfold SOn_eq in *. simp_proper. intros. simpl. rewrite H. easy. Qed.

    (** SOn_inv is left-inversion of <SOn_mul,SOn_1> *)
    Lemma SOn_mul_inv_l : forall n, InverseLeft SOn_mul SOn_1 SOn_inv (@SOn_eq n).
    Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply a. Qed.

    (** SOn_inv is right-inversion of <SOn_mul,SOn_1> *)
    Lemma SOn_mul_inv_r : forall n, InverseRight SOn_mul SOn_1 SOn_inv (@SOn_eq n).
    Proof.
      unfold SOn_eq. intros. constructor. intros; simpl.
      apply morth_iff_mul_trans_r. apply a.
    Qed.

    (** <SOn, +, 1, /s> is a group *)
    Theorem Group_SOn : forall n, Group (@SOn_mul n) SOn_1 SOn_inv SOn_eq.
    Proof.
      intros. constructor.
      - apply Monoid_SOn.
      - apply SOn_mul_inv_l.
      - apply SOn_mul_inv_r.
      - apply SOn_mul_proper.
      - apply SOn_inv_proper.
    Qed.

    (** *** Extract the properties of SOn to its carrier *)

    (** m⁻¹ = m\T *)
    Lemma SOn_imply_inv_eq_trans : forall {n} (s : SOn n),
        let m := SOn_mat n s in
        m⁻¹ = m\T.
    Proof.
      intros. unfold m. destruct s as [m' [H1 H2]]. simpl in *.
      rewrite morth_imply_inv_eq_trans; auto. easy.
    Qed.

  End SOn.

End OrthogonalMatrix.


(* ==================================== *)
(** ** Matrix inversion by Gauss Elimination, original by Shen Nan *)
Section gauss_elimination.
  Context `{F:Field}.
  Add Field field_inst : (make_field_theory F).

  Context {Teqdec: Dec Teq}.

  Infix "=" := Teq : T_scope.
  Infix "!=" := (fun a b => ~(a = b)) : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Asub := (fun x y => Tadd x (Topp y)).
  Infix "-" := Asub : T_scope.
  Infix "*" := Tmul : T_scope.

  Infix "+" := (@madd T Tadd _ _) : mat_scope.
  Infix "*" := (@mmul T Tadd T0 Tmul _ _ _) : mat_scope.
  Notation "/ a" := (Tinv a) : T_scope.
  Infix "c*" := (@mcmul T Tmul _ _) : mat_scope.
  Infix "=" := (meq (Teq:=Teq)) : mat_scope.
  (* Notation "m ! i ! j " := (mnth T0 m i j) : mat_scope. *)
  Notation mat1 := (@mat1 _ T0 T1).
  (* Notation l2m := (@l2m T T0 _ _). *)

  (** *** 初等行变换 (brt: Basic Row Transform) *)

  (* 
     0 0 0
     0 0 0
     0 c 0
   *)
  (* T matrix which only one element is non-zero *)
  Definition brt_e {r c} (ri rj : nat) (k : T) : mat r c :=
    f2m (fun i j => if (i =? ri) && (j =? rj) then k else T0).

  
  (* Multiply k times of a row *)
  (*
    1 0 0
    0 c 0
    0 0 1
   *)
  Definition brt_cmul {r c} (ri : nat) (k : T) : mat r c :=
    f2m (fun i j => if i =? j then (if i =? ri then k else T1) else T0).

  (* 第 y 行的 k 倍加到第 x 行 *)
  (* 
     1 0 0
     0 1 0
     0 c 1
   *)
  (* Definition row_add_to_row {n} (x y : nat) (k : T) : mat n n := *)
  (*   mat1 + (brt_e x y k). *)

  (** Add k times of rj-th row to rj-th row *)
  Definition brt_add {n} (ri rj : nat) (k : T) : mat n n :=
    (* f2m (fun i j => *)
    (*           if (i =? ri) && (j =? rj) *)
    (*           then k *)
    (*           else (if i =? j then T1 else T0)). *)
    mat1 + (brt_e ri rj k).

  
  (** 交换两行 *)
  (*
    x =1 , y=2

    1 0 0  -1 0 0   0 0 0   0 0 0   0 1 0    0 1 0
    0 1 0 + 0 0 0 + 0-1 0 + 1 0 0 + 0 0 0  = 1 0 0
    0 0 1   0 0 0   0 0 0   0 0 0   0 0 0    0 0 1
   *)
  (* Definition swap {n} (x y : nat) : mat n n := *)
  (*   mat1 + (e x x (-T1)) + (e y y (-T1)) + (e x y T1) + (e y x T1). *)

  Definition brt_swap {n} (ri rj : nat) : mat n n :=
    (* f2m (fun i j => *)
    (*           if i =? ri *)
    (*           then (if j =? rj then T1 else T0) *)
    (*           else (if i =? rj *)
    (*                 then (if j =? ri then T1 else T0) *)
    (*                 else (if i =? j then T1 else T0))). *)
    mat1
    + (brt_e ri ri (-T1))
    + (brt_e rj rj (-T1))
    + (brt_e ri rj T1)
    + (brt_e rj ri T1).

  Definition invertible {n} (M : mat n n) :=
    exists M', M * M' = mat1 /\ M' * M = mat1.

  (* 
 1 2 1      
-1-3 1  =>  return 0
 1 0 6     
[(n - i)++, y] , i 
得到第一个非0 *)
  (** 从第i行开始，检查第y列的第一个非零元素的序号 *)
  Fixpoint get_first_none_zero {n} (MA: mat n n) (i: nat) (y: nat) : nat :=
    match i with
    | O => n
    | S i' =>
        if ((MA $ (n - i) $ y) =? T0) then
          get_first_none_zero MA i' y
        else
          n - i
    end.

  (* 某一行加到另一行 *)
  Fixpoint elem_change_down {n} (MA: mat n n) (x: nat) (cur: nat) : mat n n * mat n n :=
    match cur with
    | O => (mat1, MA)
    | S cur' =>
        (* 将第 n-cur 行的 MA[n-cur,x] 倍加到第 n 行 *)
        let ee := brt_add (n - cur) x (- (MA $ (n - cur) $ x)) in
        (* 递归进行，左侧是构造的初等矩阵的累乘，右侧是变换后的矩阵 *)
        let (E', EA') := elem_change_down (ee * MA) x cur' in
        (E' * ee, EA')
    end.

  Fixpoint row_echelon_form {n} (MA: mat n n) (i: nat) : option (mat n n * mat n n) :=
    match i with
    | O => Some (mat1, MA)
    | S i' =>
        let r := get_first_none_zero MA i (n - i) in
        if (r =? n) then
          None
        else
          let M0 := (brt_swap (n - i) r) * MA in
          (* 把当前0行和第一个非0行互换 *)
          let ee := (brt_cmul (n - i) (/(M0 $ (n - i) $ (n - i)))) in
          (* 保证这一列第一个数字是1 *)
          let (E', EA') := elem_change_down (ee * M0) (n - i) (i - 1) in
          (* 下面元素全部与当前行相减，变成0 *)
          let ret := row_echelon_form EA' i' in
          match ret with
          | None => None
          | Some (E'', EA'') => Some (E'' * E' * ee * brt_swap (n - i) r, EA'')
          end
    end.

  Fixpoint elem_change_up {n} (MA: mat n n) (x: nat) (i: nat) :=
    match i with
    | O => (mat1, MA)
    | S i' =>
        let ee := brt_add i' x (- (MA $ i' $ x)) in
        let (E, MT) := elem_change_up (ee * MA) x i' in
        (E * ee, MT)
    end.

  Fixpoint fst_to_I {n} (MA: mat n n) (i: nat) :=
    match i with
    | O => (mat1, MA)
    | S i' =>
        let (E, MT) := elem_change_up (MA) i' i' in
        let (E', MT') := fst_to_I MT i' in
        (E' * E, MT')
    end.

  Definition minv_gauss {n} (MA: mat n n) := 
    match row_echelon_form MA n with
    | None => None
    | Some (E, MT) => Some (fst (fst_to_I MT n) * E)
    end.

End gauss_elimination.

Section test.
  Import ZArith.
  Open Scope Z.

  Definition z_brt_swap := (@brt_swap _ Z.add 0 Z.opp 1).
  (* Compute m2l (z_brt_swap 3 0 2). *)
  (* Compute m2l (z_brt_swap 3 1 2). *)
  
  Definition z_elem_change_down {n} (m:mat n n) i j :=
    @elem_change_down _ Z.add 0 Z.opp Z.mul 1 _ m i j. 

  Let m1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  
  (* Compute get_first_none_zero (T0:=0) m1 3 0. *)
  
  (* Compute let (m1,m2) := z_elem_change_down m1 0 0 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 1 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 2 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 3 in m2l m2. *)
  
End test.


(* ==================================== *)
(** ** test *)
Section test.
  Import QArith Qcanon.
  Open Scope Q.
  Open Scope Qc_scope.
  Open Scope mat_scope.

  Infix "=" := (meq (Teq:=eq)) : mat_scope.


  Coercion Q2Qc : Q >-> Qc.

  Definition m1 := (mk_mat_3_3 (T0:=0) 1 2 3 4 5 6 7 8 9)%Qc.
  (* Compute mtrace (Tadd:=Qcplus)(T0:=0)(n:=3) m1. *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Qc.
  Definition m2 := mk_mat_3_3 (T0:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
  (* Compute mrow 1 m2. *)

  (** *** rewrite support test *)
  Notation mcmul := (mcmul (Tmul:=Qcmult)).
  Infix "c*" := mcmul : mat_scope.

  Goal forall r c (m1 m2 : mat r c) (x : Qc), m1 = m2 -> x c* m1 = x c* m2.
  Proof. intros. f_equiv. easy. Qed.

  (** *** rewrite support test (cont.) *)
  Notation msub := (msub (Tadd:=Qcplus)(Topp:=Qcopp)).
  Infix "-" := msub : mat_scope.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 = m2 -> m3 = m4 -> m1 - m3 = m2 - m4.
  Proof. clear. intros. rewrite H,H0. easy. Qed.

End test.
