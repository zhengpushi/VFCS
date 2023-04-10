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
  
        Definition mat {A} (r c : nat) := nat -> nat -> A.

     while new definition of matrix type is:

        Record mat {A} (r c : nat) := mk_mat { matf : nat -> nat -> A }.
 *)


Require Export TupleExt ListExt AlgebraStructure.
Require AlgebraStructureSetoid.
Module Export ASS := AlgebraStructureSetoid. (* a short name *)
Require Export Sequence.


Generalizable Variable A B C Aadd Aopp Amul Ainv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.

(* Global Hint Rewrite map_length seq_length : list. *)


(* ======================================================================= *)
(** ** Matrix type *)
Section def.

  (** We define a _matrix_ as a record which contain only one filed _matf_,
      and that is a function of "nat -> nat -> A" type.
      Meanwhile, we give two arguments r and c as the parts of mat type to represent 
      the rows and columns of a matrix. *)
  Record mat {A} (r c : nat) : Type :=
    mk_mat { matf : nat -> nat -> A }.
  
End def.

Arguments mk_mat {A r c}.
Arguments matf {A r c}.

(** square matrix *)
Notation smat A n := (@mat A n n).


(* ======================================================================= *)
(** ** Equality of matrix *)
Section meq.
  Context {A : Type}.
  
  (** Two matrices are considered equal if each corresponding element
      whose index is in the bounds is equal.  *)
  Definition meq {r c : nat} (m1 m2 : @mat A r c) : Prop := 
    forall i j, i < r -> j < c -> matf m1 i j = matf m2 i j.
  Infix "==" := meq : mat_scope.
  
  Lemma meq_refl : forall {r c} (m : mat r c), m == m.
  Proof. intros. intros i j Hi Hj. auto. Qed.
  
  Lemma meq_sym : forall {r c} (m1 m2 : mat r c), m1 == m2 -> m2 == m1.
  Proof. intros r c m1 m2 H1. intros i j Hi Hj. rewrite H1; auto. Qed.

  Lemma meq_trans : forall {r c} (m1 m2 m3 : mat r c),  m1 == m2 -> m2 == m3 -> m1 == m3.
  Proof. intros r c m1 m2 m3 H1 H2. intros i j Hi Hj. rewrite H1, <- H2; auto. Qed.

  Global Instance meq_equiv : forall r c : nat, Equivalence (@meq r c).
  Proof.
    constructor; intro; intros.
    apply meq_refl. apply meq_sym; auto. apply meq_trans with y; auto.
  Qed.
  
  (** Meq is decidable *)
  Global Instance meq_dec {Dec_Aeq : Decidable (@eq A)} : forall {r c}, Decidable (@meq r c).
  Proof. intros. constructor. intros. apply seq2eq_dec. Qed.
  
End meq.
Infix "==" := meq : mat_scope.


(* ======================================================================= *)
(** ** Get element of a matrix *)
Section mnth.
  Context {A : Type} (A0 : A).

  (* Unsafe access (caller must assure the index manually) *)
  Notation "m $ i $ j " := (matf (A:=A) m i j) : mat_scope.

  Lemma meq_eta : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall i j, i < r -> j < c -> m1$i$j = m2$i$j).
  Proof. auto. reflexivity. Qed.

  (* Safe access (any index is accepted, but only valid index is used) *)
  Definition mnth {r c} (m : mat r c) (i j : nat) : A :=
    if (i <? r) && (j <? c)
    then m$i$j
    else A0.
  Notation "m ! i ! j " := (mnth m i j) : mat_scope.

  Lemma mnth_eq_mnth_raw : forall {r c : nat} (m : mat r c),
    forall i j, i < r -> j < c -> m!i!j = m$i$j.
  Proof.
    intros. unfold mnth.
    destruct (Nat.ltb_spec0 i r), (Nat.ltb_spec0 j c); simpl; auto; easy.
  Qed.

  (** meq, iff mnth. Note: left side is unsafe, right side is safe *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall i j, i < r -> j < c -> m1!i!j = m2!i!j).
  Proof.
    intros. unfold mnth. unfold meq. split; intros.
    - destruct (Nat.ltb_spec0 i r), (Nat.ltb_spec0 j c); simpl; auto; auto.
    - specialize (H i j H0 H1).
      destruct (Nat.ltb_spec0 i r), (Nat.ltb_spec0 j c); simpl; auto; easy.
  Qed.

End mnth.

Global Hint Unfold mnth : core.
Notation "m $ i $ j " := (matf m i j) : mat_scope.


(* ======================================================================= *)
(** ** Matrix Automation *)

(** Useful tactic for solving A = B for concrete A, B *)

(** Solve i < 0 *)
Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.

(** Convert mat to function *)
Ltac mat_to_fun :=
  repeat match goal with
  | m : mat ?r ?c |- _ => destruct m as [m]; simpl in *
  end.

(** Solve mnth *)
Ltac solve_mnth :=
  repeat match goal with
    | H: context [ mnth ] |- _ => unfold mnth in H
    | |- context [mnth] => unfold mnth; simpl
    | H: context [?c >? ?j]  |- _ => destruct (Nat.ltb_spec0 j c) in H
    | |- context[ (?c >? ?j)%nat ] => destruct (Nat.ltb_spec0 j c)
    end; simpl in *; try easy.

(** Convert meq to element equal *)
(** 
  Modification of this tactic:
  1. use an alternate lemma NatExt.lt_S_n instead of lt_S_n, because Coq report it 
     is deprecated since 8.16
  2. disable "clear Hi, clear Hj", because these two conditions are needed in some
     cases. 
  3. call "mat_to_fun" first, to unpack the mat structure to a function
 *)
Ltac by_cell :=
  intros;
  let i := fresh "i" in
  let j := fresh "j" in
  let Hi := fresh "Hi" in
  let Hj := fresh "Hj" in
  intros i j Hi Hj; simpl; try solve_end;
  mat_to_fun; repeat solve_mnth;
  repeat (destruct i as [|i]; simpl;
          [|apply NatExt.lt_S_n in Hi]; try solve_end);
  (* clear Hi; *)
  repeat (destruct j as [|j]; simpl;
          [|apply NatExt.lt_S_n in Hj]; try solve_end)
(* clear Hj *)
.

Global Ltac lma :=
  by_cell;
  try (
      try lia;
      try (compute; ring);
      try (compute; field);
      try (compute; easy));
  simpl.


(* ======================================================================= *)
(** ** Get row of a matrix *)
Section mrow.
  Context {A : Type} (A0 : A).
  Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope.

  (** Get a row which row index is i *)
  Definition mrow {r c : nat} (i : nat) (m : mat r c) : list A :=
    map (fun j => m$i$j) (seq 0 c).

  Lemma mrow_length : forall {r c} i (m : mat r c), length (mrow i m) = c.
  Proof. intros. unfold mrow. rewrite map_length. apply seq_length. Qed.

  (** (mrow m i)[j] = m[i][j] *)
  Lemma nth_mrow : forall {r c} i j (m : mat r c) a,
      i < r -> j < c -> nth j (mrow i m) a = m ! i ! j.
  Proof.
    intros. unfold mrow. rewrite nth_map_seq; auto.
    rewrite Nat.add_0_r. rewrite mnth_eq_mnth_raw; auto.
  Qed.
  
End mrow.


(* ======================================================================= *)
(** Convert between dlist and mat (version 1, l2m is strict) *)

(* Section l2m_m2l. *)
  
(*   Context {A : Type} (A0 : A). *)
(*   (* Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope. *) *)
  
(*   (** dlist to matrix with specified row and column numbers *) *)
(*   Definition l2m {r c} (dl : dlist A) : mat r c := *)
(*     mk_mat (fun i j => *)
(*               if (i <? r) && (j <? c) *)
(*               then nth j (nth i dl []) A0 *)
(*               else A0). *)
  
(*   (** mat to dlist *) *)
(*   Definition m2l {r c} (m : mat r c) : dlist A := *)
(*     map (fun i => (map (fun j => m$i$j) (seq 0 c))) (seq 0 r). *)

(*   Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r. *)
(*   Proof. intros. unfold m2l. rewrite map_length, seq_length. auto. Qed. *)
  
(*   Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c. *)
(*   Proof. *)
(*     intros. unfold width,m2l. apply Forall_map. *)
(*     apply Forall_nth. intros. rewrite map_length, seq_length; auto. *)
(*   Qed. *)

(*   Lemma l2m_m2l_id : forall {r c} (m : mat r c), (@l2m r c (m2l m)) == m. *)
(*   Proof. lma. unfold m2l. rewrite ?nth_map_seq; auto. Qed. *)

(*   Lemma m2l_l2m_id : forall {r c} (dl : dlist A), *)
(*       length dl = r -> width dl c -> m2l (@l2m r c dl) = dl. *)
(*   Proof. *)
(*     intros. unfold l2m,m2l. simpl. *)
(*     rewrite (dlist_eq_iff_nth r c (A0:=A0)); auto. *)
(*     - intros. rewrite ?nth_map_seq; auto. rewrite ?Nat.add_0_r. solve_mnth. *)
(*     - rewrite map_length, seq_length; auto. *)
(*     - apply width_map. intros. rewrite map_length, seq_length; auto. *)
(*   Qed. *)

(*   Lemma l2m_inj : forall {r c} (d1 d2 : dlist A), *)
(*       length d1 = r -> width d1 c -> length d2 = r -> width d2 c -> *)
(*       d1 <> d2 -> ~(@l2m r c d1 == l2m d2). *)
(*   Proof. *)
(*     intros. unfold l2m. intro. unfold meq in *. simpl in *. destruct H3. *)
(*     rewrite (dlist_eq_iff_nth r c (A0:=A0)); auto. *)
(*     intros. specialize (H4 i j H3 H5). solve_mnth. *)
(*   Qed. *)
  
(*   Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m d == m). *)
(*   Proof. intros. exists (@m2l r c m). apply l2m_m2l_id. Qed. *)
  
(*   Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~(m1 == m2) -> m2l m1 <> m2l m2. *)
(*   Proof. *)
(*     intros. destruct m1 as [m1], m2 as [m2]. unfold meq in *; simpl in *. *)
(*     unfold m2l. unfold mnth. simpl. intro. *)
(*     destruct H. intros. *)
(*     rewrite (dlist_eq_iff_nth r c (A0:=A0)) in H0; *)
(*       autorewrite with list; auto. *)
(*     - specialize (H0 i j H H1). *)
(*       rewrite ?nth_map_seq in H0; auto. rewrite ?Nat.add_0_r in H0. solve_mnth. *)
(*     - apply width_map. intros. autorewrite with list; auto. *)
(*     - apply width_map. intros. autorewrite with list; auto. *)
(*   Qed. *)
  
(*   Lemma m2l_surj : forall {r c} (d : dlist A), *)
(*       length d = r -> width d c -> (exists m : mat r c, m2l m = d). *)
(*   Proof. intros. exists (l2m d). apply m2l_l2m_id; auto. Qed. *)

(* End l2m_m2l. *)

(* Let m := @l2m _ 0 2 2 [[1;2;3;4];[10;11;12;13]]. *)
(* Compute m2l m. *)

(* Global Hint Resolve m2l_length : mat. *)
(* Global Hint Resolve m2l_width : mat. *)

(* ======================================================================= *)
(** Convert between dlist and mat (version 2, l2m is efficient) *)

Section l2m_m2l.
  Context {A : Type} (A0 : A).
  (* Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope. *)
  
  (** dlist to matrix with specified row and column numbers *)
  Definition l2m {r c} (dl : dlist A) : mat r c :=
    mk_mat (fun i j => nth j (nth i dl []) A0).
  
  (** mat to dlist *)
  Definition m2l {r c} (m : mat r c) : dlist A :=
    map (fun i => (map (fun j => m$i$j) (seq 0 c))) (seq 0 r).

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof. intros. unfold m2l. rewrite map_length, seq_length. auto. Qed.
  
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
    intros. unfold width,m2l. apply Forall_map.
    apply Forall_nth. intros. rewrite map_length, seq_length; auto.
  Qed.

  Lemma l2m_m2l_id : forall {r c} (m : mat r c), (@l2m r c (m2l m)) == m.
  Proof. lma. unfold m2l. rewrite ?nth_map_seq; auto. Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : dlist A),
      length dl = r -> width dl c -> m2l (@l2m r c dl) = dl.
  Proof.
    intros. unfold l2m,m2l. simpl.
    rewrite (dlist_eq_iff_nth r c (A0:=A0)); auto.
    - intros. rewrite ?nth_map_seq; auto. rewrite ?Nat.add_0_r. solve_mnth.
    - rewrite map_length, seq_length; auto.
    - apply width_map. intros. rewrite map_length, seq_length; auto.
  Qed.

  Lemma l2m_inj : forall {r c} (d1 d2 : dlist A),
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      d1 <> d2 -> ~(@l2m r c d1 == l2m d2).
  Proof.
    intros. unfold l2m. intro. unfold meq in *. simpl in *. destruct H3.
    rewrite (dlist_eq_iff_nth r c (A0:=A0)); auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m d == m).
  Proof. intros. exists (@m2l r c m). apply l2m_m2l_id. Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~(m1 == m2) -> m2l m1 <> m2l m2.
  Proof.
    intros. destruct m1 as [m1], m2 as [m2]. unfold meq in *; simpl in *.
    unfold m2l. unfold mnth. simpl. intro.
    destruct H. intros.
    rewrite (dlist_eq_iff_nth r c (A0:=A0)) in H0;
      autorewrite with list; auto.
    - specialize (H0 i j H H1).
      rewrite ?nth_map_seq in H0; auto. rewrite ?Nat.add_0_r in H0. solve_mnth.
    - apply width_map. intros. autorewrite with list; auto.
    - apply width_map. intros. autorewrite with list; auto.
  Qed.
  
  Lemma m2l_surj : forall {r c} (d : dlist A),
      length d = r -> width d c -> (exists m : mat r c, m2l m = d).
  Proof. intros. exists (l2m d). apply m2l_l2m_id; auto. Qed.

End l2m_m2l.

(* Notation m2ln := (@m2l nat). *)
(* Notation l2mn r c := (@l2m nat 0 r c). *)
(* Let m1 := l2mn 2 2 [[1;2];[3;4]]. *)
(* Let m2 := l2mn 2 2 [[1];[3;4]]. *)
(* Let m3 := l2mn 2 2 [[1;2];[3]]. *)
(* Let m4 := l2mn 2 2 [[1;2;3];[3;4]]. *)
(* Let m5 := l2mn 2 2 [[1;2];[3;4;5]]. *)
(* Compute m2ln m1. *)
(* Compute m2ln m2. *)
(* Compute m2ln m3. *)
(* Compute m2ln m4. *)
(* Compute m2ln m5. *)


(* ======================================================================= *)
(** ** Get column *)
Section mcol.
  Context {A : Type} {A0 : A}.
  
  Definition mcol {r c : nat} (m : mat r c) (j : nat) : list A :=
    let fix f r i0 :=
      match r with
      | O => nil
      | S r' => m $ i0 $ j :: (f r' (S i0))
      end in
    f r 0.
  
End mcol.

(* Let m1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]]. *)
(* Compute mcol m1 0. *)
(* Compute mcol m1 1. *)
(* Compute mcol m1 3. *)


(* ======================================================================= *)
(** ** matrix shift *)
Section mshift.
  Context {A : Type} {A0 : A}.
  Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope.

  (** left shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *)
  Definition mcshl {r c} (m : @mat A r c) (k : nat) : mat r c :=
    mk_mat (fun i j => m $ i $ (j + k)).

  (** right shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *)
  Definition mcshr {r c} (m : @mat A r c) (k : nat) : mat r c :=
    mk_mat (fun i j => if j <? k then A0 else (m $ i $ (j - k))).

  (** left loop shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *)
  Definition mclshl {r c} (m : @mat A r c) (k : nat) : mat r c :=
    mk_mat (fun i j => m $ i $ (nat_lshl c j k)).

  (** right shift column *)
  Definition mclshr {r c} (m : @mat A r c) (k : nat) : mat r c :=
    mk_mat (fun i j => m $ i $ (nat_lshr c j k)).

End mshift.

(* Let m1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]]. *)
(* Compute m2l (mcshl m1 1). *)
(* Compute m2l (mcshr (A0:=0) m1 1). *)
(* Compute m2l (mclshl m1 1). *)
(* Compute m2l (mclshr m1 1). *)

(* ======================================================================= *)
(** ** Construct matrix with vector and matrix *)
Section mcons.
  Context {A : Type} {A0 : A}.
  
  Notation vecr n := (@mat A 1 n).
  Notation vecc n := (@mat A n 1).

  (** Construct a matrix by rows, i.e., a row vector and a matrix *)
  Definition mconsr {r c} (v : vecr c) (m : mat r c) : mat (S r) c :=
    mk_mat (fun i j => match i with
                     | O => v $ 0 $ j
                     | S i' => m $ i' $ j
                     end).
  
  (** Construct a matrix by columns, i.e., a column vector and a matrix *)
  Definition mconsc {r c} (v : vecc r) (m : mat r c) : mat r (S c) :=
    mk_mat (fun i j => match j with
                     | O => v $ i $ 0
                     | S j' => m $ i $ j'
                     end).

      
  (** mconsr rewrite *)
  (* Lemma mconsr_eq {r c} (v : vecr c) (m : mat r c) : mconsr v m == (v, m). *)
  (* Proof. unfold mconsr. auto. Qed. *)
  
  (** Construct a matrix by rows with the matrix which row number is 0 *)
  Lemma mconsr_mr0 : forall {n} (v : vecr n) (m : mat 0 n), mconsr v m == v.
  Proof. lma. Qed.
  
  (** Construct a matrix by columns with the matrix which column number is 0 *)
  Lemma mconsc_mr0 : forall {n} (v : vecc n) (m : mat n 0), mconsc v m == v.
  Proof. lma. Qed.

End mcons.


(* ======================================================================= *)
(** ** Make concrete matrix *)
Section mk_mat.
  Context {A : Type} {A0 : A}.
  Notation l2m := (l2m A0).
  
  Definition mk_mat_0_c c : mat 0 c := l2m [].

  Definition mk_mat_1_1 (a11 : A) : mat 1 1 := l2m [[a11]].
  Definition mk_mat_1_2 (a11 a12 : A) : mat 1 2 := l2m [[a11;a12]].
  Definition mk_mat_1_3 (a11 a12 a13 : A) : mat 1 3 := l2m [[a11;a12;a13]].
  Definition mk_mat_1_4 (a11 a12 a13 a14 : A) : mat 1 4 := l2m [[a11;a12;a13;a14]].
  Definition mk_mat_1_c c (l : list A) : mat 1 c := l2m [l].
  
  Definition mk_mat_r_0 r : mat r 0 := l2m [].

  Definition mk_mat_2_1 (a11 a21 : A) : mat 2 1 := l2m [[a11];[a21]].
  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2 := l2m [[a11;a12];[a21;a22]].
  
  Definition mk_mat_3_1 (a11 a21 a31 : A) : mat 3 1 := l2m [[a11];[a21];[a31]].
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 :=
    l2m [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]].

  Definition mk_mat_4_1 (a11 a21 a31 a41 : A) : mat 4 1 :=
    l2m [[a11];[a21];[a31];[a41]].
  Definition mk_mat_4_4 (a11 a12 a13 a14 a21 a22 a23 a24
                           a31 a32 a33 a34 a41 a42 a43 a44 : A) : mat 4 4 :=
    l2m [[a11;a12;a13;a14]; [a21;a22;a23;a24];[a31;a32;a33;a34]; [a41;a42;a43;a44]].
  
  Definition mk_mat_r_1 r (l : list A) : mat r 1 :=
    mk_mat (fun i j : nat => if (j =? 0)%nat then (nth i l A0) else A0).
End mk_mat.


(* ======================================================================= *)
(** ** Mapping of matrix *)
Section Map.
  Context {A : Type} {A0 : A}.
  (* Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope. *)
  
  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c :=
    mk_mat (fun i j => f (m $ i $ j)).
  
  Definition mmap2 {r c} (f : A -> A -> A) (m1 m2 : mat r c) : mat r c :=
    mk_mat (fun i j => f (m1 $ i $ j) (m2 $ i $ j)).
  
  Lemma mmap2_comm : forall {r c} (f : A -> A -> A) (m1 m2 : mat r c)
                            {Comm : Commutative f}, 
      mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof. intros. intros i j Hi Hj. apply Comm. Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A) (m1 m2 m3 : mat r c)
                             {Assoc : Associative f}, 
      mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof. intros. intros i j Hi Hj. apply Assoc. Qed.
  
End Map.


(* ======================================================================= *)
(** ** Matrix transposition *)
Section mtrans.
  Context {A : Type}.
  
  Definition mtrans {r c} (m : @mat A r c): mat c r := mk_mat (fun i j => m$j$i).
  Notation "m \T" := (mtrans m) : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mtrans_mor : forall r c, Proper (meq ==> meq) (mtrans (r:=r)(c:=c)).
  Proof.
    simp_proper. lma. unfold meq in H; simpl in H.
    specialize (H j i Hj Hi). solve_mnth.
  Qed.

  (** Transpose twice keep unchanged. *)
  Lemma mtrans_trans : forall {r c} (m : @mat A r c), m \T \T == m.
  Proof. lma. Qed.

End mtrans.
Notation "m \T" := (mtrans m) : mat_scope.


(* ======================================================================= *)
(** ** Zero matrirx and identity matrix *)
Section mat0_mat1.
  Context {A : Type} (A0 A1 : A).

  (** Zero matrix *)
  Definition mat0 {r c : nat} : mat r c := mk_mat (fun _ _ => A0).

  (** Identity matrix *)
  Definition mat1 {n : nat} : mat n n :=
    mk_mat (fun i j => if (i =? j)%nat then A1 else A0).
  
  (** mat0\T = mat0 *)
  Lemma mtrans_0 : forall {r c : nat}, (@mat0 r c)\T == mat0.
  Proof. lma. Qed.
  
  (** mat1\T = mat1 *)
  Lemma mtrans_1 : forall {n : nat}, (@mat1 n)\T == mat1.
  Proof. lma. replace (j =? i) with (i =? j); auto. apply Nat.eqb_sym. Qed.

End mat0_mat1.


(* ======================================================================= *)
(** ** Matrix algebra *)
(** Matrix addition, opposition, subtraction, scalar multiplication, multiplication. *)
Section malg.
  Context `{AG : AGroup}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  Infix "-" := Asub : A_scope.

  Infix "+" := (ladd (Aadd:=Aadd)) : list_scope.
  (* Infix "==" := (eqlistA Aeq) : list_scope. *)
  Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope.
  Notation smat n := (smat A n).
  Notation seqsum := (seqsum (Aadd:=Aadd) (A0:=A0)).

  (** *** Matrix trace *)
  Definition mtrace {n : nat} (m : smat n) : A := seqsum (fun i => m$i$i) n.
  Notation "'tr' m" := (mtrace m) : mat_scope.
  
  (** show it is a proper morphism *)
  Global Instance mtrace_mor : forall n, Proper (meq ==> eq) (mtrace (n:=n)).
  Proof.
    simp_proper. intros. mat_to_fun. unfold meq in H; simpl in H.
    unfold mtrace. simpl. apply seqsum_eq. auto.
  Qed.

  (** tr(m\T) = tr(m) *)
  Lemma mtrace_trans : forall {n} (m : smat n), tr (m\T) = tr(m).
  Proof. intros. unfold mtrace. apply seqsum_eq. easy. Qed.


  (** *** Matrix addition *)

  (** Note that, we use "m$i$j" instead of "m!i!i" to get element, for simplicity. *)
  Definition madd {r c} (m1 m2 : mat r c) : mat r c :=
    mk_mat (fun i j => m1$i$j + m2$i$j).
  Infix "+" := madd : mat_scope.

  (** show it is a proper morphism *)
  Global Instance madd_mor : forall r c, Proper (meq ==> meq ==> meq) (madd (r:=r)(c:=c)).
  Proof.
    simp_proper. lma. rewrite (meq_iff_mnth A0) in H,H0.
    specialize (H i j Hi Hj). specialize (H0 i j Hi Hj).
    solve_mnth. rewrite H,H0. auto.
  Qed.

  (** m1 + m2 = m2 + m1 *)
  Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == (m2 + m1).
  Proof. lma. amonoid_simp. Qed.

  (** (m1 + m2) + m3 = m1 + (m2 + m3) *)
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof. lma. monoid_simp. Qed.

  (** mat0 + m = m *)
  Lemma madd_0_l : forall {r c} (m : mat r c), mat0 A0 + m == m. 
  Proof. lma. monoid_simp. Qed.

  (** m + mat0 = m *)
  Lemma madd_0_r : forall {r c} (m : mat r c), m + mat0 A0 == m. 
  Proof. lma. monoid_simp. Qed.
  
  (** Get element of addition with two matrics equal to additon of 
      corresponded elements. *)
  Lemma madd_nth : forall {r c} (m1 m2 : mat r c) i j,
      (m1 + m2) ! i ! j = ((m1!i!j) + (m2!i!j))%A.
  Proof. intros. solve_mnth; monoid_simp. Qed.

  (** (m1 + m2)[i] = m1[i] + m2[i] *)
  Lemma mrow_madd : forall {r c} i (m1 m2 : mat r c),
      i < r -> mrow i (m1 + m2) = ((mrow i m1) + (mrow i m2))%list.
  Proof.
    intros. unfold mrow.
    apply nth_ext with (d:=A0) (d':=A0).
    - rewrite ladd_length with (n:=c); rewrite map_length, seq_length; auto.
    - intros. rewrite map_length, seq_length in H0.
      unfold ladd. rewrite map2_nth with (a:=A0) (b:=A0); auto.
      rewrite !nth_map_seq; auto.
      all: try rewrite map_length, seq_length; auto. monoid_simp.
  Qed.

  (** (m1 + m2)\T = m1\T + m2\T *)
  Lemma mtrans_add : forall {r c} (m1 m2 : mat r c), (m1 + m2)\T == m1\T + m2\T.
  Proof. lma. Qed.

  (** tr(m1 + m2) = tr(m1) + tr(m2) *)
  Lemma mtrace_add : forall {n} (m1 m2 : smat n), tr (m1 + m2) = (tr(m1) + tr(m2))%A.
  Proof. intros. unfold mtrace. rewrite <- seqsum_add. apply seqsum_eq. easy. Qed.

  (** Monoid structure over {madd,mat0,meq} *)
  Global Instance Monoid_MatAadd : forall r c, ASS.Monoid (@madd r c) (mat0 A0) meq.
  intros; constructor; try apply meq_equiv; try constructor; intros.
  apply madd_mor. apply madd_assoc. apply madd_0_l. apply madd_0_r. Qed.

  Section test.
    Goal forall r c (m1 m2 : @mat A r c), mat0 A0 + m1 == m1.
      ASS.monoid_simp. Qed.
  End test.
  
  (** *** Matrix opposition *)
  
  Definition mopp {r c} (m : mat r c) : mat r c :=
    mk_mat (fun i j => - (m$i$j)).
  Notation "- a" := (mopp a) : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mopp_mor : forall r c, Proper (meq ==> meq) (mopp (r:=r)(c:=c)).
  Proof.
    simp_proper. lma. rewrite (meq_iff_mnth A0) in H.
    specialize (H i j Hi Hj). solve_mnth. rewrite H. auto.
  Qed.

  (** - (m1 + m2) = (-m1) + (-m2) *)
  Lemma mopp_add : forall {r c : nat} (m1 m2 : mat r c), - (m1 + m2) == (-m1) + (-m2).
  Proof. lma. rewrite group_inv_distr. apply commutative. Qed.

  (** (-m) + m = mat0 *)
  Lemma madd_opp_l : forall r c (m : mat r c), (-m) + m == mat0 A0.
  Proof. lma. group_simp. Qed.

  (** m + (-m) = mat0 *)
  Lemma madd_opp_r : forall r c (m : mat r c), m + (-m) == mat0 A0.
  Proof. lma. group_simp. Qed.

  (** - (- m) = m *)
  Lemma mopp_opp : forall {r c} (m : mat r c), - (- m) == m.
  Proof. lma. apply group_inv_inv. Qed.

  (** - mat0 = mat0 *)
  Lemma mopp_0 : forall {r c}, - (@mat0 _ A0 r c) == mat0 A0.
  Proof. lma. apply group_inv_id. Qed.

  (** (m1 + m2)\T = m1\T + m2\T *)
  Lemma mtrans_opp : forall {r c} (m : mat r c), (- m)\T == - (m\T).
  Proof. lma. Qed.

  (** tr(- m) = - (tr(m)) *)
  Lemma mtrace_opp : forall {n} (m : smat n), tr (- m) = (- (tr(m)))%A.
  Proof. intros. unfold mtrace. rewrite seqsum_opp. apply seqsum_eq. easy. Qed.


  (** *** Matrix subtraction *)
  
  Definition msub {r c} (m1 m2 : mat r c) : mat r c := m1 + (-m2).
  Infix "-" := msub : mat_scope.

  (** show it is a proper morphism *)
  Global Instance msub_mor : forall r c, Proper (meq ==> meq ==> meq) (msub (r:=r)(c:=c)).
  Proof. simp_proper. intros. unfold msub. rewrite H,H0. easy. Qed.

  (** Rewrite msub: m1 - m2 = m1 + (-m2) *)
  Lemma msub_rw : forall {r c} (m1 m2 : mat r c), m1 - m2 == m1 + (-m2).
  Proof. intros. easy. Qed.

  (** m1 - m2 = -(m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
  Proof. lma. rewrite group_inv_distr,group_inv_inv; auto. Qed.

  (** (m1 - m2) - m3 = m1 - (m2 + m3) *)
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof. lma. rewrite group_inv_distr. monoid_simp. f_equal. amonoid_simp. Qed.

  (** (m1 + m2) - m3 = m1 + (m2 - m3) *)
  Lemma msub_assoc1 : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) - m3 == m1 + (m2 - m3).
  Proof. lma. monoid_simp. Qed.

  (** (m1 - m2) - m3 = m1 - (m3 - m2) *)
  Lemma msub_assoc2 : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == (m1 - m3) - m2.
  Proof. lma. rewrite ?associative; f_equiv. amonoid_simp. Qed.

  (** mat0 - m = - m *)
  Lemma msub_0_l : forall {r c} (m : mat r c), mat0 A0 - m == - m.
  Proof. lma. monoid_simp. Qed.

  (** m - mat0 = m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - mat0 A0 == m.
  Proof. lma. rewrite (group_inv_id (G:=AG)). monoid_simp. Qed.

  (** m - m = mat0 *)
  Lemma msub_self : forall {r c} (m : mat r c), m - m == (mat0 A0).
  Proof. lma. group_simp. Qed.

  (** (m1 - m2)\T = m1\T - m2\T *)
  Lemma mtrans_sub : forall {r c} (m1 m2 : mat r c), (m1 - m2)\T == m1\T - m2\T.
  Proof. lma. Qed.

  (** tr(m1 - m2) = tr(m1) - tr(m2) *)
  Lemma mtrace_sub : forall {n} (m1 m2 : smat n), tr (m1 - m2) = (tr(m1) - tr(m2))%A.
  Proof. intros. unfold mtrace. rewrite seqsum_opp. rewrite <- seqsum_add.
         apply seqsum_eq. easy. Qed.


  (** *** Group structure over {madd,mat0,mopp,meq} *)
  Global Instance Group_MatAadd : forall r c, ASS.Group (@madd r c) (mat0 A0) mopp meq.
  intros; constructor; try apply meq_equiv.
  apply Monoid_MatAadd.
  constructor. apply madd_opp_l.
  constructor. apply madd_opp_r.
  apply madd_mor. apply mopp_mor. Qed.

  Section test.
    Goal forall r c (m1 m2 : @mat A r c), mat0 A0 + m1 + (-m2) + m2 == m1.
      intros.
      (* rewrite ASS.identityLeft. *)
      (* rewrite ASS.associative. *)
      (* rewrite ASS.inverseLeft. *)
      ASS.group_simp.
    Qed.
  End test.

  (** *** Abelian group structure over {madd,mat0,mopp,meq} *)
  Global Instance AGroup_MatAadd : forall r c, ASS.AGroup (@madd r c) (mat0 A0) mopp meq.
  intros; constructor; try apply meq_equiv. apply Group_MatAadd.
  constructor. apply Group_MatAadd. all: constructor; apply madd_comm. Qed.

  
  (** *** Below, we need a ring structure *)
  Context `{R : Ring A Aadd A0 Aopp Amul A1}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : (make_ring_theory R).


  (** *** Scalar multiplication of matrix *)

  (** Left scalar multiplication of matrix *)
  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c :=
    mk_mat (fun i j => (a * m$i$j)).
  Infix "c*" := mcmul : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mcmul_mor : forall r c, Proper (eq ==> meq ==> meq) (mcmul (r:=r)(c:=c)).
  Proof.
    simp_proper. lma. rewrite meq_eta in H0.
    specialize (H0 i j Hi Hj). solve_mnth. rewrite H,H0. easy.
  Qed.

  (** 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), A0 c* m == mat0 A0.
  Proof. lma. Qed.

  (** a c* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a c* (@mat0 _ A0 r c) == mat0 A0.
  Proof. lma. Qed.

  (** 1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), A1 c* m == m.
  Proof. lma. Qed.

  (** a c* mat1 equal to a diagonal matrix which main diagonal elements all are a *)
  Lemma mcmul_1_r : forall {n} a,
      a c* (@mat1 _ A0 A1 n) == mk_mat (fun i j => if (i =? j)%nat then a else A0).
  Proof.
    lma. unfold mcmul,mat1. destruct (i =? j); ring.
  Qed.

  (** a c* (b c* m) = (a * b) c* m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == (a * b) c* m.
  Proof. lma. Qed.

  (** a c* (b c* m) = b c* (a c* m) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == b c* (a c* m).
  Proof. lma. Qed.

  (** a c* (m1 + m2) = (a c* m1) + (a c* m2) *)
  Lemma mcmul_add_distr_l : forall {r c} (a : A) (m1 m2 : mat r c), 
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof. lma. Qed.
  
  (** (a + b) c* m = (a c* m) + (b c* m) *)
  Lemma mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c), 
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof. lma. Qed.

  (** (a c* m)\T = a c* (m\T) *)
  Lemma mtrans_cmul : forall {r c} (a : A) (m : mat r c), (a c* m)\T == a c* (m\T).
  Proof. lma. Qed.

  (** tr (a c* m) = a * tr (m) *)
  Lemma mtrace_cmul : forall {n} (a : A) (m : smat n), tr (a c* m) = a * tr (m).
  Proof.
    unfold mtrace,mcmul; intros. rewrite seqsum_cmul_l. apply seqsum_eq.
    intros. simpl. ring.
  Qed.

  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    mk_mat (fun i j => (m$i$j * a)).
  Infix "*c" := mmulc : mat_scope.
  
  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
  Proof. lma. Qed.

  (** show it is a proper morphism *)
  Global Instance mmulc_mor : forall r c, Proper (meq ==> eq ==> meq) (mmulc (r:=r)(c:=c)).
  Proof. simp_proper. intros. rewrite ?mmulc_eq_mcmul. rewrite H,H0. easy. Qed.

  
  (** *** Matrix multiplication *)
  Definition mmul {r c s : nat} (m1 : mat r c) (m2 : mat c s) : mat r s :=
    mk_mat (fun i k => seqsum (fun j => m1$i$j * m2$j$k) c).
  Infix "*" := mmul : mat_scope.

  (** show it is a proper morphism *)
  Global Instance mmul_mor : forall r c s,
      Proper (meq ==> meq ==> meq) (mmul (r:=r)(c:=c)(s:=s)).
  Proof.
    simp_proper. lma. apply seqsum_eq. intros k Hk.
    unfold meq in H,H0. simpl in H,H0.
    specialize (H i k Hi Hk). specialize (H0 k j Hk Hj).
    rewrite H,H0. ring.
  Qed.

  (** (m1 * m2) * m3 = m1 * (m2 * m3) *)
  Lemma mmul_assoc : forall {r c s t : nat} (m1 : mat r c) (m2 : mat c s) (m3: mat s t), 
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    lma. induction c; simpl.
    - apply seqsum_seq0. intros. ring.
    - rewrite <- IHc. rewrite seqsum_cmul_l. rewrite <- seqsum_add.
      apply seqsum_eq; intros. ring.
  Qed.

  (** m1 * (m2 + m3) = m1 * m2 + m1 * m3 *)
  Lemma mmul_add_distr_l : forall {r c s : nat} (m1 : mat r c) (m2 m3 : mat c s), 
      m1 * (m2 + m3) == m1 * m2 + m1 * m3.
  Proof. lma. rewrite <- seqsum_add. apply seqsum_eq; intros. ring. Qed.
  
  (** (m1 + m2) * m3 = m1 * m3 + m2 * m3 *)
  Lemma mmul_add_distr_r : forall {r c s : nat} (m1 m2 : mat r c) (m3 : mat c s),
      (m1 + m2) * m3 == m1 * m3 + m2 * m3.
  Proof. lma. rewrite <- seqsum_add. apply seqsum_eq; intros. ring. Qed.

  (** m1 * (m2 - m3) = m1 * m2 - m1 * m3 *)
  Lemma mmul_sub_distr_l : forall {r c s : nat} (m1 : mat r c) (m2 m3 : mat c s), 
      m1 * (m2 - m3) == m1 * m2 - m1 * m3.
  Proof. lma. rewrite seqsum_opp. rewrite <- seqsum_add. apply seqsum_eq; intros.
         ring. Qed.
  
  (** (m1 - m2) * m3 = m1 * m3 - m2 * m3 *)
  Lemma mmul_sub_distr_r : forall {r c s : nat} (m1 m2 : mat r c) (m3 : mat c s),
      (m1 - m2) * m3 == m1 * m3 - m2 * m3.
  Proof. lma. rewrite seqsum_opp. rewrite <- seqsum_add. apply seqsum_eq; intros.
         ring. Qed.

  (** - (m1 * m2) = (-m1) * m2 *)
  Lemma mopp_mul_l : forall {r c s : nat} (m1 : mat r c) (m2 : mat c s),
      - (m1 * m2) == (-m1) * m2.
  Proof. lma. rewrite seqsum_opp. apply seqsum_eq; intros. ring. Qed.

  (** - (m1 * m2) = m1 * (-m2) *)
  Lemma mopp_mul_r : forall {r c s : nat} (m1 : mat r c) (m2 : mat c s),
      - (m1 * m2) == m1 * (-m2).
  Proof. lma. rewrite seqsum_opp. apply seqsum_eq; intros. ring. Qed.

  (** mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c s} (m : mat c s), (@mat0 _ A0 r c) * m == mat0 A0.
  Proof. lma. apply seqsum_seq0. intros. ring. Qed.

  (** m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c s} (m : mat r c), m * (@mat0 _ A0 c s) == mat0 A0.
  Proof. lma. apply seqsum_seq0. intros. ring. Qed.

  (** mat1 * m = m *)
  Lemma mmul_1_l : forall {r c : nat} (m : mat r c), mat1 A0 A1 * m == m.
  Proof.
    lma. apply (seqsum_unique _ _ _ i); auto.
    - rewrite Nat.eqb_refl. ring.
    - intros. bdestruct (i =? j0). easy. ring.
  Qed.

  (** m * mat1 = m *)
  Lemma mmul_1_r : forall {r c : nat} (m : mat r c), m * mat1 A0 A1 == m.
  Proof.
    lma. apply (seqsum_unique _ _ _ j); auto.
    - rewrite Nat.eqb_refl. ring.
    - intros. bdestruct (j0 =? j). lia. ring.
  Qed.
  
  (* a c* (m1 * m2) = (a c* m1) * m2. *)
  Lemma mcmul_mul_assoc : forall {r c s} (a : A) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == (a c* m1) * m2.
  Proof. lma. rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring. Qed.
  
  (** m1 * (a c* m2) = a c* (m1 * m2). *)
  Lemma mcmul_mul_perm : forall {r c s} (a : A) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == m1 * (a c* m2).
  Proof. lma. rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring. Qed.
  
  (** (a c* m)\T = a c* (m\T) *)
  Lemma mtrans_mul : forall {r c s} (m1 : mat r c) (m2 : mat c s),
      (m1 * m2)\T == m2\T * m1\T.
  Proof. lma. apply seqsum_eq. intros. ring. Qed.

  (** tr (m1 * m2) = tr (m2 * m1) *)
  Lemma mtrace_mul : forall {r c} (m1 : mat r c) (m2 : mat c r),
      tr (m1 * m2) = tr (m2 * m1).
  Proof.
    unfold mtrace; intros. unfold mmul. mat_to_fun.
    rewrite seqsum_seqsum_exchg.
    apply seqsum_eq. intros. apply seqsum_eq. intros. ring.
  Qed.

  
  (** *** Hardmard product *)
  
  (** Hardmard product (also known as the element-wise product, entrywise product 
      or Schur product).
      It is a binary operation that takes two matrices of the same dimensions and 
      produces another matrix of the same dimension as the operandds, where each 
      element i,j is the product of elements i,j of the original two matrices.

      The hardmard product is associative, distribute and commutative *)
  Definition mhp {n : nat} (m1 m2 : smat n) : smat n :=
    mk_mat (fun i j => (m1$i$j * m2$i$j)%A).
  Infix "⦿" := mhp : mat_scope.

  
  
End malg.

Global Hint Unfold
  madd mopp msub mcmul mmul
  : mat.

(** Notes, these notations need to be re-declare with suitable arguments,
    Thus, we shouldn't declare them here. *)
(* Infix "+" := madd : mat_scope. *)
(* Notation "- a" := (mopp a) : mat_scope. *)
(* Infix "-" := msub : mat_scope. *)
(* Infix "*" := mmul : mat_scope. *)
(* Infix "c*" := mcmul : mat_scope. *)
(* Infix "*c" := mmulc : mat_scope. *)


(* ======================================================================= *)
(** ** Convert between tuples and matrix *)
Section t2m_m2t.
  Context {A : Type} (A0 : A).
  (* Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope. *)
  
  (** Tuples 3x3 -> mat_3x3 *)
  Definition t2m_3_3 (t : @T_3_3 A) : @mat A 3 3.
  Proof.
    destruct t as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    exact (mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33).
  Defined.

  (** mat_3x3 -> tuple 3x3. That is: ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) *)
  Definition m2t_3_3 (m : mat 3 3) : @T_3_3 A :=
    ((m$0$0, m$0$1, m$0$2),
      (m$1$0, m$1$1, m$1$2),
      (m$2$0, m$2$1, m$2$2)).

  (** m[0,0]: mat_1x1 -> A *)
  Definition m2t_1_1 (m : @mat A 1 1) := m$0$0.

End t2m_m2t.


(* ======================================================================= *)
(** ** trace *)
Section trace.
  Context {A : Type} {Aadd: A -> A -> A} {A0 : A}.
  (* Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope. *)
  Notation smat n := (smat A n).

  (** Trace *)
  Definition trace {n : nat} (m : smat n) := 
    seqsum (Aadd:=Aadd)(A0:=A0) (fun i => m$i$i) n.

End trace.


(* ======================================================================= *)
(** ** Some tactic for automation *)

(** Try to prove a proposition such as:
      "~(exp1 == 0) -> ~(exp2 = 0)" *)
Ltac reverse_neq0_neq0 A0 :=
  try match goal with
    | H : ?e1 <> A0 |- ?e2 <> A0 =>
        let H1 := fresh "H1" in
        intro H1; destruct H; ring_simplify; ring_simplify in H1;
        try rewrite H1; auto
    end.


(* ======================================================================= *)
(** ** Determinant of a matrix *)


Section det.
  Context `{R : Ring}.
  Add Ring ring_inst : (make_ring_theory R).
  
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation smat n := (smat A n).

  (** Get the sub square matrix which remove r-th row and c-th column
        from a square matrix. *)
  Definition submat {n} (m : smat (S n)) (r c : nat) : smat n :=
    mk_mat
      (fun i j =>
         let i' := (if i <? r then i else S i) in
         let j' := (if j <? c then j else S j) in
         m $ i' $ j').
  
  (* Determinant of a square matrix (original definition) *)
  (* Variable a b c : A. *)
  (* Compute perm 0 (seq 0 3). *)
  (* Let dl := perm 0 (seq 0 3). *)
  (* Let l := [1;2;3]. *)
  (* Compute nth 1 l 0. *)
  (* Compute map (fun i => (i, nth i l 0)) (seq 0 3). *)
  (* Compute map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)
  (* Let dl1 := map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)
  (* Variable a00 a01 a02 a10 a11 a12 a20 a21 a22 : A. *)
  (* Definition m : smat 3 := mat_3_3 a00 a01 a02 a10 a11 a12 a20 a21 a22. *)
  (* Compute map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)

  (* (** all items in a determinant *) *)
  (* Let dl2 := map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)
  (* Compute dl2. *)

  (* Definition n := 3. *)
  (* Compute perm 0 (seq 0 n). (* *)
   (*  = [[0; 1; 2]; [0; 2; 1]; [1; 0; 2]; [1; 2; 0]; [2; 0; 1]; [2; 1; 0]] *)
   (*  : list (list nat) *) *)

  (* Definition item_of_det {n : nat} (m : smat n) (l : list nat) : A := *)
  (*   fold_left Amul (map (fun i => m!i!(nth i l 0)) l) A1. *)

  (* (** Definition of determinant *) *)
  (* Definition det_def {n : nat} (m : smat n) : A := *)
  (*   fold_left Aadd (map (fun l => item_of_det m l) (perm 0 (seq 0 n))) A0. *)

  (* Compute det_orig m. *)
  
  (* Compute fold_left Amul [a00;a01;a02]. *)
  (* Compute fold_left Aadd. *)

  (** Determinant of a square matrix, by expanding the first row *)
  Fixpoint det {n} : smat n -> A :=
    match n with
    | 0 => fun _ => A1
    | S n' =>
        fun m =>
          fold_left Aadd
            (map (fun i =>
                    let a := if Nat.even i then (m$0$i) else (-(m$0$i))%A in
                    let d := det (submat m 0 i) in
                    (a * d)%A) (seq 0 n)) A0
    end.
  
  (** *** Properties of determinant *)
  Section props.

    (** Determinant of a matrix of dimension-1 *)
    Definition det1 (m : smat 1) := m$0$0.

    (** det1 m = det m *)
    Lemma det1_eq_det : forall m, det1 m = det m.
    Proof. intros. mat_to_fun. cbv. ring. Qed.
    
    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det1_neq0_iff : forall (m : smat 1),
        det m <> A0 <->  m$0$0 <> A0.
    Proof. intros. split; intros; mat_to_fun; reverse_neq0_neq0 A0. Qed.

    (** Determinant of a matrix of dimension-2 *)
    Definition det2 (m : smat 2) := (m$0$0 * m$1$1 - m$0$1 * m$1$0)%A.

    (** det2 m = det m *)
    Lemma det2_eq_det : forall m, det2 m = det m.
    Proof. intros. mat_to_fun. cbv. ring. Qed.

    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det2_neq0_iff : forall (m : smat 2),
        det m <> A0 <->  m$0$0 * m$1$1 - m$0$1 * m$1$0 <> A0.
    Proof. intros. split; intros; mat_to_fun; reverse_neq0_neq0 A0. Qed.

    (** Determinant of a matrix of dimension-3 *)
    Definition det3 (m : smat 3) :=
      (m$0$0 * m$1$1 * m$2$2 - m$0$0 * m$1$2 * m$2$1 - 
         m$0$1 * m$1$0 * m$2$2 + m$0$1 * m$1$2 * m$2$0 + 
         m$0$2 * m$1$0 * m$2$1 - m$0$2 * m$1$1 * m$2$0)%A.

    (** det3 m = det m *)
    Lemma det3_eq_det : forall m, det3 m = det m.
    Proof. intros. mat_to_fun. cbv. ring. Qed.
    
    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det3_neq0_iff : forall (m : smat 3),
        det m <> A0 <->
          m$0$0 * m$1$1 * m$2$2 - m$0$0 * m$1$2 * m$2$1 - 
            m$0$1 * m$1$0 * m$2$2 + m$0$1 * m$1$2 * m$2$0 + 
            m$0$2 * m$1$0 * m$2$1 - m$0$2 * m$1$1 * m$2$0 <> A0.
    Proof. intros. split; intros; mat_to_fun; reverse_neq0_neq0 A0. Qed.

  End props.

End det.


(* ======================================================================= *)
(** ** Inverse matrix with the help of determinant and adjoint matrix. *)
Section matrix_inversion.
  Context `{R:Ring}.
  Add Ring ring_thy_inst : (make_ring_theory R).

  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.

  Infix "*" := (@mmul A Aadd A0 Amul _ _ _) : mat_scope.
  Infix "c*" := (@mcmul A Amul _ _) : mat_scope.
  Infix "==" := meq : mat_scope.
  (* Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope. *)
  Notation mat1 := (mat1 A0 A1).
  Notation l2m := (@l2m A A0 _ _).
  Notation smat n := (smat A n).
  Notation det := (det (Aadd:=Aadd)(A0:=A0)(Aopp:=Aopp)(Amul:=Amul)(A1:=A1)).
  Notation det2 := (det2 (Aadd:=Aadd)(Aopp:=Aopp)(Amul:=Amul)).
  Notation det3 := (det3 (Aadd:=Aadd)(Aopp:=Aopp)(Amul:=Amul)).
  
  (** *** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  (** That is: adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  Section adj.

    Definition madj {n} : smat n -> smat n := 
      match n with
      | O => fun m => m 
      | S n' =>
          fun m =>
            mk_mat (fun i j =>
                      let s := if Nat.even (i + j) then A1 else (-A1)%A in
                      let d := det (submat m j i) in 
                      (s * d)%A)
      end.

  End adj.

  (** *** We need a field structure *)
  Context `{F:@Field A Aadd A0 Aopp Amul A1 Ainv}.
  Add Field field_thy_inst : (make_field_theory F).

  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun x y => Amul x (Ainv y)).
  Infix "/" := Adiv : A_scope.

  (** *** Cramer rule *)
  Section cramer_rule.
    
    (** Exchange one column of a square matrix *)
    Definition mchgcol {n} (m : smat n) (k : nat) (v : mat n 1) : smat n :=
      mk_mat (fun i j => if (Nat.eqb j k) then (v$i$0)%nat else m$i$j).
    
    (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid only when D is not zero *)
    Definition cramerRule {n} (A : smat n) (b : mat n 1) : mat n 1 :=
      let D := det A in
      mk_mat (fun i j => let Di := det (mchgcol A i b) in (Di / D)).
    
  End cramer_rule.

  
  (** *** Matrix Inversion *)
  Section inv.

    Definition minv {n} (m : smat n) := (A1 / det m) c* (madj m).

    Lemma minv_correct_r : forall n (m : smat n), m * (minv m) == mat1.
    Proof.
      induction n; intros.
      - lma.
      - 
    Abort.
  End inv.

  (** *** Inversion matrix of common finite dimension *)
  Section concrete.
    Definition inv_1_1 (m : smat 1) : smat 1 :=
      let a00 := m$0$0 in
      l2m [[A1/a00]].

    (** det m <> 0 -> inv_1_1 m = inv m *)
    Lemma inv_1_1_eq_inv : forall m, det m <> A0 -> inv_1_1 m == minv m.
    Proof. lma. reverse_neq0_neq0 A0. Qed.

    (** inv_1_1 m * m = mat1 *)
    Lemma inv_1_1_correct_l : forall (m : smat 1),
        det m <> A0 -> (inv_1_1 m) * m == mat1.
    Proof. lma. reverse_neq0_neq0 A0. Qed.

    (** m * inv_1_1 m = mat1 *)
    Lemma inv_1_1_correct_r : forall (m : smat 1),
        det m <> A0 -> m * (inv_1_1 m) == mat1.
    Proof. lma. reverse_neq0_neq0 A0. Qed.

    (* ======================================================================= *)
    (** ** Inversion matrix of dimension-2 *)
    Definition inv_2_2 (m : smat 2) : smat 2 :=
      let a00 := m$0$0 in
      let a01 := m$0$1 in
      let a10 := m$1$0 in
      let a11 := m$1$1 in
      let d := det2 m in
      (l2m [[a11/d; -a01/d]; [-a10/d; a00/d]])%A.

    (** det m <> 0 -> inv_2_2 m = inv m *)
    Lemma inv_2_2_eq_inv : forall m, det m <> A0 -> inv_2_2 m == minv m.
    Proof. lma; reverse_neq0_neq0 A0. Qed.
    
    (** inv_2_2 m * m = mat1 *)
    Lemma inv_2_2_correct_l : forall (m : smat 2),
        det m <> A0 -> (inv_2_2 m) * m == mat1.
    Proof. lma; reverse_neq0_neq0 A0. Qed.
    
    (** m * inv_2_2 m = mat1 *)
    Lemma inv_2_2_correct_r : forall (m : smat 2),
        det m <> A0 -> m * (inv_2_2 m) == mat1.
    Proof. lma; reverse_neq0_neq0 A0. Qed.
    
    (* ======================================================================= *)
    (** ** Inversion matrix of dimension-3 *)
    (* Note, this formula could be provided from matlab, thus avoiding manual work *)
    Definition inv_3_3 (m : smat 3) : smat 3 :=
      let a00 := m$0$0 in
      let a01 := m$0$1 in
      let a02 := m$0$2 in
      let a10 := m$1$0 in
      let a11 := m$1$1 in
      let a12 := m$1$2 in
      let a20 := m$2$0 in
      let a21 := m$2$1 in
      let a22 := m$2$2 in
      let d := det3 m in
      (l2m
         [[(a11*a22 - a12*a21)/d; -(a01*a22 - a02*a21)/d; (a01*a12 - a02*a11)/d];
          [-(a10*a22 - a12*a20)/d; (a00*a22 - a02*a20)/d; -(a00*a12 - a02*a10)/d];
          [(a10*a21 - a11*a20)/d; -(a00*a21 - a01*a20)/d; (a00*a11 - a01*a10)/d]])%A.
    
    (** det m <> 0 -> inv_3_3 m = inv m *)
    Lemma inv_3_3_eq_inv : forall m, det m <> A0 -> inv_3_3 m == minv m.
    Proof. lma; reverse_neq0_neq0 A0. Qed.
    
    (** inv_3_3 m * m = mat1 *)
    Lemma inv_3_3_correct_l : forall (m : smat 3),
        det m <> A0 -> (inv_3_3 m) * m == mat1.
    Proof. lma; reverse_neq0_neq0 A0. Qed.
    
    (** m * inv_3_3 m = mat1 *)
    Lemma inv_3_3_correct_r : forall (m : smat 3),
        det m <> A0 -> m * (inv_3_3 m) == mat1.
    Proof. lma; reverse_neq0_neq0 A0. Qed.
  End concrete.
  
  (* ======================================================================= *)
  (** ** Direct compute inversion of a symbol matrix of 1/2/3rd order. *)
  Section FindFormula.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
    Let m1 := mk_mat_1_1 (A0:=A0) a11.
    Let m2 := mk_mat_2_2 (A0:=A0) a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

    (* Compute (m2l (minv m1)). *)
    (* Compute (m2l (minv m2)). *)
    (* Compute (m2l (minv m3)). *)
    (* Although this is correct, but the expression is too long. *)
    (* We want to simplify it with RAST *)
    
  End FindFormula.

End matrix_inversion.

Section test.
  (* A Formal Proof of Sasaki-Murao Algorithm
     https://pdfs.semanticscholar.org/ddc3/e8185e10a1d476497de676a3fd1a6ae29595.pdf
   *)
  Import ZArith.
  Open Scope Z.
  Let m1 := @l2m _ 0 4 4 [[2;2;4;5];[5;8;9;3];[1;2;8;5];[6;6;7;1]].
  Notation det := (det (Aadd:=Z.add) (Aopp:=Z.opp) (Amul:=Z.mul) (A0:=0) (A1:=1)).
  (* Compute det m1. *)
  (* Check det. *)
End test.


(* ======================================================================= *)
(** ** Matrix inversion by Gauss Elimination, original by Shen Nan *)
Section gauss_elimination.
  Context `{F:Field}.
  Add Field field_inst : (make_field_theory F).

  Context {Aeqdec: Decidable (@eq A)}.

  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.

  Infix "+" := (@madd A Aadd _ _) : mat_scope.
  Infix "*" := (@mmul A Aadd A0 Amul _ _ _) : mat_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "c*" := (@mcmul A Amul _ _) : mat_scope.
  Infix "==" := meq : mat_scope.
  (* Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope. *)
  Notation mat1 := (@mat1 _ A0 A1).
  (* Notation l2m := (@l2m A A0 _ _). *)

  (** *** 初等行变换 (brt: Basic Row Transform) *)

  (* 
     0 0 0
     0 0 0
     0 c 0
   *)
  (* A matrix which only one element is non-zero *)
  Definition brt_e {r c} (ri rj : nat) (k : A) : mat r c :=
    mk_mat (fun i j => if (i =? ri) && (j =? rj) then k else A0).

  
  (* Multiply k times of a row *)
  (*
    1 0 0
    0 c 0
    0 0 1
   *)
  Definition brt_cmul {r c} (ri : nat) (k : A) : mat r c :=
    mk_mat (fun i j => if i =? j then (if i =? ri then k else A1) else A0).

  (* 第 y 行的 k 倍加到第 x 行 *)
  (* 
     1 0 0
     0 1 0
     0 c 1
   *)
  (* Definition row_add_to_row {n} (x y : nat) (k : A) : mat n n := *)
  (*   mat1 + (brt_e x y k). *)

  (** Add k times of rj-th row to rj-th row *)
  Definition brt_add {n} (ri rj : nat) (k : A) : mat n n :=
    (* mk_mat (fun i j => *)
    (*           if (i =? ri) && (j =? rj) *)
    (*           then k *)
    (*           else (if i =? j then A1 else A0)). *)
    mat1 + (brt_e ri rj k).

  
  (** 交换两行 *)
  (*
    x =1 , y=2

    1 0 0  -1 0 0   0 0 0   0 0 0   0 1 0    0 1 0
    0 1 0 + 0 0 0 + 0-1 0 + 1 0 0 + 0 0 0  = 1 0 0
    0 0 1   0 0 0   0 0 0   0 0 0   0 0 0    0 0 1
   *)
  (* Definition swap {n} (x y : nat) : mat n n := *)
  (*   mat1 + (e x x (-A1)) + (e y y (-A1)) + (e x y A1) + (e y x A1). *)

  Definition brt_swap {n} (ri rj : nat) : mat n n :=
    (* mk_mat (fun i j => *)
    (*           if i =? ri *)
    (*           then (if j =? rj then A1 else A0) *)
    (*           else (if i =? rj *)
    (*                 then (if j =? ri then A1 else A0) *)
    (*                 else (if i =? j then A1 else A0))). *)
    mat1
    + (brt_e ri ri (-A1))
    + (brt_e rj rj (-A1))
    + (brt_e ri rj A1)
    + (brt_e rj ri A1).

  Definition invertible {n} (M : mat n n) :=
    exists M', M * M' == mat1 /\ M' * M == mat1.

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
        if ((MA $ (n - i) $ y) ==? A0) then
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
  
  (* Compute get_first_none_zero (A0:=0) m1 3 0. *)
  
  (* Compute let (m1,m2) := z_elem_change_down m1 0 0 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 1 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 2 in m2l m2. *)
  (* Compute let (m1,m2) := z_elem_change_down m1 0 3 in m2l m2. *)
  
End test.


(* ======================================================================= *)
(** ** test *)
Section test.
  Import QArith Qcanon.
  Open Scope Q.
  Open Scope Qc_scope.
  Open Scope mat_scope.

  Coercion Q2Qc : Q >-> Qc.

  Definition m1 := (mk_mat_3_3 (A0:=0) 1 2 3 4 5 6 7 8 9)%Qc.
  (* Compute trace (Aadd:=Qcplus)(A0:=0)(n:=3) m1. *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Qc.
  Definition m2 := mk_mat_3_3 (A0:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
  (* Compute mrow 1 m2. *)

  (** *** rewrite support test *)
  Notation mcmul := (mcmul (Amul:=Qcmult)).
  Infix "c*" := mcmul : mat_scope.

  Goal forall r c (m1 m2 : mat r c) (x : Qc), m1 == m2 -> x c* m1 == x c* m2.
  Proof. intros. f_equiv. easy. Qed.

  (** *** rewrite support test (cont.) *)
  Notation msub := (msub (Aadd:=Qcplus)(Aopp:=Qcopp)).
  Infix "-" := msub : mat_scope.

  (* we need to write declaration on Qc once again. *)
  Instance msub_mor_Qc_demo : forall r c,  Proper (meq ==> meq ==> (@meq _ r c)) msub.
  Proof. intros. apply (msub_mor (A0:=0)). Qed.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 == m2 -> m3 == m4 -> m1 - m3 == m2 - m4.
  Proof. clear. intros. f_equiv. easy. easy. Qed.

End test.
