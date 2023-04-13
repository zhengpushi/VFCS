(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for list
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference "A Gentle Introduction to Type Classes and Relations in Coq"
  2. Owing to Setoid，lots of properties of list need to re-proof.
  
  history   :
  1. 2021.12, by ZhengPu Shi.
     first version

  2. 2022.05, by ZhengPu Shi.
     split big file into small modules

  3. 2022.10, by ZhengPu Shi
     Setoid version
  
  4. 2023.04, by ZhengPu Shi
     eq version, for simplicity
 *)

Require Export AlgebraStructure.
Require Export NatExt.
Require Export List SetoidList. Export ListNotations.

Open Scope nat_scope.
Open Scope A.
Open Scope list.

Generalizable Variables A B C Aeq Beq Ceq.
Generalizable Variables Aadd Aopp Amul Ainv.


(** A dlist is a list of list A. ("d" means double) *)
Notation dlist A := (list (list A)).


(* ======================================================================= *)
(** ** Properties of cons *)

Section cons.
  Context `{Aeq : relation A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** cons is a proper morphism *)
  Lemma cons_aeq_mor : Proper (Aeq ==> eqlistA Aeq ==> eqlistA Aeq) (@cons A).
  Proof.
    intros x y H1 l1 l2 H2. destruct l1,l2; auto.
  Qed.

  Global Existing Instance cons_aeq_mor.

  (** Equality of cons, iff both parts are equal *)
  Lemma cons_eq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      a1 :: l1 == a2 :: l2 <-> (a1 == a2)%A /\ l1 == l2.
  Proof.
    intros. split; intros H; inversion H; subst; auto.
  Qed.

  (** Inequality of cons, iff at least one parts are not equal *)
  Lemma cons_neq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      ~(a1 :: l1 == a2 :: l2) <-> (~(a1 == a2)%A \/ ~(l1 == l2)).
  Proof.
    intros. split; intro H.
    - rewrite cons_eq_iff in H.
      apply not_and_or in H; auto.
    - intro. inversion H0. subst. destruct H; auto.
  Qed.

End cons.


(* ======================================================================= *)
(** ** General properties on list A *)

Section Props_listA.

  (** eqlistA eq and eq are same relation *)
  Lemma eqlistA_eq_same_relation : forall {A} (l1 l2 : list A),
      eqlistA eq l1 l2 <-> l1 = l2.
  Proof.
    intros A l1. induction l1; destruct l2; simpl; split; intros; auto; try easy.
    - inv H. f_equal. apply IHl1. auto.
    - inv H. easy.
  Qed.

  (** eqlistA eqlistA eq and eq are same relation *)
  Lemma eqlistA_eq_same_relation2 : forall {A} (l1 l2 : list (list A)),
      eqlistA (eqlistA eq) l1 l2 <-> l1 = l2.
  Proof.
    intros A l1. induction l1; destruct l2; simpl; split; intros; auto; try easy.
    - inv H. f_equal.
      + apply eqlistA_eq_same_relation; auto.
      + apply IHl1. auto.
    - inv H. easy.
  Qed.

  Context `{Aeq:relation A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  
  (** Redefine 'length_zero_iff_nil', original is opaque, make it transparent t *)
  Lemma length_zero_iff_nil : forall (l : list A), length l = 0 <-> l == [].
  Proof.
    intros. destruct l; intros; split; intros; auto; try easy.
  Defined.

  (** list equality is decidable on setoid *)
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Lemma list_eq_dec : (forall x y : A, {(x == y)%A} + {~(x == y)%A}) ->
                      forall l1 l2 : list A, {l1 == l2} + {~(l1 == l2)}.
  Proof.
    intros H l1. induction l1; destruct l2; intros;
      try (left; easy); try (right; easy).
    destruct (H a a0),(IHl1 l2); auto.
    - right. intro. inv H0. easy.
    - right. intro. inv H0. easy.
    - right. intro. inv H0. easy.
  Qed.
  
End Props_listA.


(* ======================================================================= *)
(** ** Properties of hd and tl *)
Section hd_tl.
  Context {A : Type}.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** hd is a proper morphism *)
  Lemma hd_aeq_mor : Proper (Aeq ==> eqlistA Aeq ==> Aeq) (@hd A).
  Proof.
    unfold Proper, respectful.
    intros. destruct x0, y0; simpl; try easy. inv H0. auto.
  Qed.
  Global Existing Instance hd_aeq_mor.
  
  (** tl is a proper morphism *)
  Lemma tl_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq) (@tl A).
  Proof.
    unfold Proper, respectful.
    intros. destruct x, y; simpl; try easy. inv H. auto.
  Qed.
  Global Existing Instance tl_aeq_mor.
  
  (** length of tl. (pred version) *)
  Lemma tl_length : forall (l : list A), length (tl l) = pred (length l).
  Proof.
    induction l; auto.
  Qed.

End hd_tl.


(* ======================================================================= *)
(** ** Properties of nth *)

Section nth.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

    (** nth is a proper morphism *)
  Lemma nth_aeq_mor : Proper (eq ==> eqlistA Aeq ==> Aeq ==> Aeq) (@nth A).
  Proof.
    unfold Proper, respectful.
    intros i j H; inv H. rename j into i.
    intros l1 l2. revert l2 i.
    induction l1; destruct l2,i; intros; simpl in *; try easy.
    - inv H. easy.
    - inv H. auto.
  Qed.

  Global Existing Instance nth_aeq_mor.
    
  (** nth [] a = a *)
  Lemma nth_nil : forall (a : A) (i : nat), (nth i [] a == a)%A.
  Proof.
    intros. destruct i; simpl; easy.
  Qed.

  (** Two list equal iff all nth visit equal *)
  Lemma list_eq_iff_nth (a1 a2 : A) : forall n (l1 l2 : list A)
                                     (H1 : length l1 = n) (H2 : length l2 = n),
      l1 == l2 <-> (forall (i : nat), i < n -> (nth i l1 a1 == nth i l2 a2)%A).
  Proof.
    intros n l1. revert n. induction l1; intros; simpl in *; subst.
    - split; intros; try easy. apply List.length_zero_iff_nil in H2. rewrite H2. easy.
    - split; intros; try easy.
      + destruct l2; try easy.
        inversion H. subst.
        destruct i; simpl; auto.
        simpl in H2. inversion H2.
        specialize (IHl1 (length l1) l2 eq_refl H3).
        rewrite IHl1 in H7. apply H7. lia.
      + destruct l2; simpl in *; try easy.
        assert (a == a0)%A.
        { specialize (H 0).
          assert (0 < S (length l1)) by lia.
          apply H in H0; auto. }
        assert (l1 == l2).
        { rewrite (IHl1 (length l1)); auto. intros.
          specialize (H (S i)); simpl in H. apply H. lia. }
        rewrite H0,H1. easy.
  Qed.

  (** nth_ext (setoid version) *)
  Lemma nth_ext : forall (l1 l2 : list A) (d1 d2 : A),
      length l1 = length l2 ->
      (forall i, i < length l1 -> (nth i l1 d1 == nth i l2 d2)%A) -> l1 == l2.
  Proof.
    intros. rewrite list_eq_iff_nth with (a1:=d1)(a2:=d2)(n:=length l1); auto.
  Qed.

  (** Get from repeat x and default value x always return x *)
  Lemma nth_repeat_same : forall (a : A) (n i : nat),
      (nth i (repeat a n) a == a)%A.
  Proof.
    intros a n. induction n; destruct i; simpl; easy.
  Qed.

End nth.


(* ======================================================================= *)
(** ** Properties of length *)
Section length.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** decompose a list which length is 1 *)

  (** Note that, we need this lemma to split a list with only one element,
      although the definition end with "Defined", we cannot got a explicit 
      result by Compute. In practice, won't use this lemma if you needn't *)
  Lemma list_length_1 : forall (l : list A),
      length l = 1 -> {x | l == [x]}.
  Proof. 
    destruct l; intros. inversion H. inversion H.
    apply List.length_zero_iff_nil in H1. subst. exists a. easy.
  Defined.

  Section Test.
    Let l := [1].
    Definition h : length l = 1. auto. Defined.
    (*   Compute proj2_sig (list_length_1 l h). *)
  End Test.

  (** a list has only one element equal to [hd _ l] *)
  Lemma list_length1_eq_hd : forall (x : A) (l:list A), 
      length l = 1 -> [hd x l] == l.
  Proof.
    intros x l. destruct l.
    - intros. simpl in *. lia.
    - intros. simpl in *. f_equal.
      apply eq_add_S in H. apply List.length_zero_iff_nil in H. subst. easy.
  Qed.

  (** decompose a list which length is S n *)
  Lemma list_length_Sn : forall (l : list A) n,
      length l = S n -> {x & { t | l == x :: t}}.
  Proof.
    destruct l; intros. inversion H. exists a. exists l. easy.
  Qed.

  (** decompose a list which length is S (S n) *)
  Lemma list_length_SSn : forall (l : list A) n,
      length l = S (S n) -> {x & { y & { t | l = x :: y :: t}}}.
  Proof.
    destruct l; intros. inversion H.
    exists a. destruct l. inversion H.
    exists a0. exists l. auto.
  Qed.

  (** Split list which length is 1 *)
  Lemma list_length1_neq : forall (l : list A) (a b : A), 
      (length (a :: l) = 1 /\ ~((a :: l) == [b])) -> (~(a == b)%A /\ l == []).
  Proof.
    intros l. induction l; intros; destruct H.
    - simpl in *. split; auto.
    - simpl in *. easy. 
  Qed.

End length.

Section test.
  Let l := [1].
  Let h : length l = 1. auto. Defined.
  (* Compute proj1_sig (list_length_1 l h). *)
End test.


(* ======================================================================= *)
(** ** Set element of a list *)

Section chg.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** *** Set element with a constant value *)
  Fixpoint lst_chg (l : list A) (i : nat) (x : A) : list A :=
    match l, i with
    | [], _ => []
    | a :: l, 0 => x :: l
    | a :: l, S i => a :: (lst_chg l i x)
    end.

  (** Length property *)
  Lemma lst_chg_length : forall (l : list A) ni n x, 
      length l = n ->
      length (lst_chg l ni x) = n.
  Proof.
    intros l; induction l; auto. induction ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  (** *** Set element with a generation function *)

  (** auxiliary function, i0 is given position, i is changing every loop *)
  Fixpoint lst_chgf_aux (l : list A) (i0 i : nat) (f : nat -> A) : list A :=
    match l with
    | [] => []
    | a :: l' =>
        match i with
        | 0 => f i0 :: l'
        | S i' => a :: (lst_chgf_aux l' i0 i' f)
        end
    end.

  Definition lst_chgf (l : list A) (i : nat) (f : nat -> A) : list A :=
    lst_chgf_aux l i i f.
  
  (** Length property *)
  Lemma lst_chgf_aux_length : forall (l : list A) ni n ni0 f, 
      length l = n -> length (lst_chgf_aux l ni0 ni f) = n.
  Proof.
    intros l; induction l; auto. destruct ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  Lemma lst_chgf_length : forall (l : list A) n ni f, 
      length l = n -> length (lst_chgf l ni f) = n.
  Proof. intros. apply lst_chgf_aux_length; auto. Qed.

End chg.

(* Let f_gen := fun (i : nat) => (i + 5). *)
(* Compute lst_chgf [1;2;3] 0 f_gen. *)
(* Compute lst_chgf [1;2;3] 1 f_gen. *)


(* ======================================================================= *)
(** ** Other induction principle of list *)

Section ind.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (* (** Induction principle by length of a list *) *)
  (* Lemma list_ind_length : forall (P : list A -> Prop), *)
  (*     (forall n l, length l = n -> P l) -> (forall l, P l). *)
  (* Proof. *)
  (*   intros. apply (H (length l)). auto. *)
  (* Qed. *)

  (** Two step induction principle for list *)
  Theorem list_ind2 : forall (P : list A -> Prop),
      (* 新增的前提，表示 P 与 Aeq 是相容的 *)
      (forall l1 l2 : list A, l1 == l2 -> P l1 -> P l2) ->
      (P []) -> 
      (forall a, P [a]) -> 
      (forall l a b, P l -> P (a :: b :: l)) ->
      (forall l, P l).
  Proof.
    intros P Hx H0 H1 H2. apply ind_nat_list. induction n using nat_ind2. 
    - intros. apply List.length_zero_iff_nil in H; subst; auto.
    - intros. apply list_length_1 in H. destruct H. apply (Hx [x]); easy.
    - destruct l; auto. destruct l; auto.
      intros. apply H2. apply IHn. simpl in H. lia.
  Qed.

End ind.


(* ======================================================================= *)
(** ** list repeat properties *)

Section repeat.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (eqlistA Aeq).

  Lemma repeat_aeq_mor : Proper (Aeq ==> eq ==> (eqlistA Aeq)) (@repeat A).
  Proof.
    unfold Proper, respectful.
    intros a b Hab i j. revert j.
    induction i; intros.
    - subst; simpl. easy.
    - destruct j. easy. simpl. apply cons_aeq_mor; auto.
  Qed.
  
  Global Existing Instance repeat_aeq_mor.

  (** repeat S n times equal to another form *)
  Lemma list_repeat_Sn (A0 : A) : forall n, repeat A0 (S n) == A0 :: repeat A0 n.
  Proof.
    intros. simpl. easy.
  Qed.

End repeat.


(* ======================================================================= *)
(** ** List with constant value 0 *)
Section lzero.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).
  
  (** A friendly name for zero list *)
  Definition lzero (A0 : A) n := repeat A0 n.

  (** lzero's length law *)
  Lemma lzero_length (A0 : A) : forall n, length (lzero A0 n) = n.
  Proof.
    intros. apply repeat_length.
  Qed.

  (** append two zero list to a zero list satisfy length relation *)
  Lemma lzero_app (A0 : A) : forall n1 n2,
      lzero A0 n1 ++ lzero A0 n2 == lzero A0 (n1 + n2).
  Proof.
    unfold lzero. intros. rewrite repeat_app. easy.
  Qed.

End lzero.


(* ======================================================================= *)
(** ** Properties of mapping a list *)

Section map_A_B_C.
  Context `{Aeq : relation A} `{Beq : relation B} `{Equiv_Ceq : Equivalence C Ceq}.
  Infix "==" := (eqlistA Ceq).

  (** map_map setoid version *)
  Lemma map_map : forall (f : A -> B) (g : B -> C) (l : list A),
      map g (map f l) == map (fun x : A => g (f x)) l.
  Proof.
    intros f g l. induction l; simpl; try easy.
    apply cons_aeq_mor; auto.
    easy.
  Qed.

End map_A_B_C.


(** map for two types *)
Section map_A_B.

  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Context `{Equiv_Beq:Equivalence B Beq}.
  Infix "==" := (Beq) : A_scope.
  Infix "==" := (eqlistA Beq).

  (** map is a proper morphism *)
  Lemma map_aeq_mor : Proper ((Aeq ==> Beq) ==> eqlistA Aeq ==> eqlistA Beq) (@map A B).
  Proof.
    unfold Proper, respectful.
    intros f1 f2 Hf l1.
    induction l1.
    - intros [|l2]; intros; simpl in *; auto. inv H.
    - intros [|l2]; intros; simpl in *. inv H. inv H.
      constructor; auto.
  Qed.

  Global Existing Instance map_aeq_mor.

  (** map_ext setoid version *)
  Lemma map_ext : forall (f g : A -> B),
      (forall a : A, (f a == g a)%A) -> forall l : list A, map f l == map g l.
  Proof.
    intros f g H l. induction l; intros; try easy.
    simpl. rewrite H,IHl. easy.
  Qed.
  
  (** map is equal, imply the list is equal *)
  Lemma map_eq_imply_eq : forall (f : A -> B) (l1 l2 : list A),
      map f l1 == map f l2 ->
      Bijective f (Aeq:=Aeq) (Beq:=Beq) ->
      eqlistA Aeq l1 l2.
  Proof.
    intros f l1. induction l1; intros; destruct l2; simpl in *; try easy.
    apply cons_eq_iff in H. destruct H.
    constructor; auto.
    destruct H0 as [Hinj Hbij].
    apply inj_pres_eq with (a1:=a)(a2:=a0) in Hinj; auto.
  Qed.

  (** map_ext_in_iff setoid version *)
  Lemma map_ext_in_iff : forall (f g : A -> B) (l : list A),
      map f l == map g l <-> (forall a : A, In a l -> (f a == g a)%A).
  Proof.
    intros f g l. induction l; intros; simpl; split; intros; try easy.
    - inversion H; subst. rewrite IHl in H6. destruct H0.
      + subst. easy.
      + apply H6. auto.
    - apply cons_aeq_mor; auto.
      apply IHl. auto.
  Qed.

  (** map and repeat is communtative *)
  Lemma map_repeat (f : A -> B) : forall (a : A) n, 
      (map f (repeat a n)) == (repeat (f a) n).
  Proof. 
    induction n; simpl; auto. constructor; auto. easy.
  Qed.
  
End map_A_B.


(** map for one type *)
Section map_A.

  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** Extented map_id lemma, which needn't the function is a exactly format of
     "forall x, x" *)
  Lemma map_id : forall (l : list A) (f : A -> A) (H: forall a, (f a == a)%A),
      (map f l == l)%list.
  Proof.
    induction l; intros; simpl. easy. apply cons_eq_iff; split; auto.
  Qed.

  (** reverse of map_id *)
  Lemma map_id_rev : forall (l : list A) (f : A -> A),
      map f l == l -> (forall x, In x l -> (f x == x)%A).
  Proof. induction l; intros; simpl in *. easy. inv H. destruct H0; subst; auto. Qed.

  (** lzero equal to map to_zero *)
  Lemma map_eq_zero : forall l (A0 : A) (f : A -> A) n,
      (forall x : A, (f x == A0)%A) -> length l = n -> map f l == lzero A0 n.
  Proof.
    induction l; intros; simpl in *. subst. simpl. easy.
    destruct n. easy. inv H0. simpl.
    apply cons_aeq_mor; auto.
  Qed.
    
  (** Mapping is fixpoint, iff f is id *)
  Lemma map_fixpoint_imply_id (f : A -> A) : forall (l : list A), 
      map f l == l -> (forall x, In x l -> (f x == x)%A).
  Proof.
    induction l; intros; simpl in *. easy. inversion H.
    destruct H0. subst; auto. apply IHl; auto.
  Qed.

  (** Simplify of nth+map+seq *)
  Lemma nth_map_seq : forall i f n m (a0:A),
      i < m -> (nth i (map f (seq n m)) a0 == f (i + n))%A.
  Proof.
    intros. gd m. gd f. gd i. induction n.
    - intros i f m. gd f. gd i. induction m.
      + intros. lia.
      + intros. simpl. destruct i; try easy.
        rewrite <- seq_shift.
        rewrite List.map_map.
        rewrite IHm; try easy. lia.
    - intros. rewrite <- seq_shift. rewrite List.map_map.
      rewrite IHn; auto. replace (S (i + n)) with (i + S n); auto. easy.
  Qed.

  (** Simplify of map+nth+seq *)
  (* Note: the lower index of seq is 0, it could extend to any nat number later *)
  Lemma map_nth_seq  : forall n (l : list A) A0,
      length l = n -> map (fun i => nth i l A0) (seq 0 n) == l.
  Proof.
    induction n.
    - intros. simpl. apply List.length_zero_iff_nil in H; subst. easy.
    - intros. simpl. destruct l.
      + simpl in *; lia.
      + apply cons_aeq_mor; try easy. inversion H.
        rewrite <- seq_shift.
        rewrite map_map; auto.
        simpl. rewrite H1. rewrite IHn; easy.
  Qed.

  (** Equality of map+seq, iff corresponding elements are equal *)
  Lemma map_seq_eq : forall n (f g : nat -> A),
      map f (seq 0 n) == map g (seq 0 n) <-> (forall i, i < n -> (f i == g i)%A).
  Proof.
    intros; split; intros.
    - rewrite map_ext_in_iff in H. apply H. apply in_seq. lia.
    - apply map_ext_in_iff. intros. apply H. apply in_seq in H0. lia.
  Qed.

End map_A.


(* ======================================================================= *)
(** ** Mapping two lists to a list *)

Section map2.

  (** Definitions *)
  Section defs.
    Context {A B C : Type}.
    Variable f : A -> B -> C.
    
    (** map operation to two list *)
    Fixpoint map2 (l1 : list A) (l2 : list B) : list C :=
      match l1, l2 with
      | x1 :: t1, x2 :: t2 => (f x1 x2) :: (map2 t1 t2)
      | _, _ => []
      end.
  End defs.

  (** Properties of map2 with three different types *)
  Section props_ABC.
    Context {A B C :Type} {Aeq:relation A} {Beq:relation B} {Ceq:relation C}.
    Context `{Equiv_Ceq : Equivalence C Ceq}.
    Context {f : A -> B -> C}.
    Context (fProper : Proper (Aeq ==> Beq ==> Ceq) f).
    Infix "==" := (eqlistA Ceq).

    Lemma map2_aeq_mor :
      Proper (eqlistA Aeq ==> eqlistA Beq ==> eqlistA Ceq) (map2 f).
    Proof.
      intros a1. induction a1.
      - intros a2 Ha b1 b2 Hb. destruct b1,a2,b2; try easy.
      - intros a2 Ha b1 b2 Hb. destruct b1,a2,b2; try easy.
        simpl. inversion Ha. inversion Hb. subst.
        apply cons_eq_iff. split.
        + apply fProper; auto.
        + apply IHa1; auto.
    Qed.
    Global Existing Instance map2_aeq_mor.
  
    (** length of map2 *)
    Lemma map2_length : forall (l1 : list A) (l2 : list B) n,
        length l1 = n -> length l2 = n -> length (map2 f l1 l2) = n.
    Proof. 
      induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy.
    Qed.
    
    (** map2 to two lists could be separated by two segments with same length *)
    Lemma map2_app : forall (la1 la2 : list A) (lb1 lb2 : list B),
        length la1 = length lb1 -> length la2 = length lb2 ->
        map2 f (la1 ++ la2) (lb1 ++ lb2) == (map2 f la1 lb1) ++ (map2 f la2 lb2).
    Proof.
      induction la1, lb1; intros; simpl; auto; simpl in H; try easy.
      apply cons_aeq_mor; try easy.
      apply IHla1; auto.
    Qed.
  
    (** map2 [] l = [] *)
    Lemma map2_nil_l : forall l, map2 f [] l == [].
    Proof. destruct l; easy. Qed.

    (** map2 l [] = [] *)
    Lemma map2_nil_r : forall l, map2 f l [] == [].
    Proof. destruct l; easy. Qed.

    (** tail of map2, equal to map2 to tail *)
    Lemma tail_map2 : forall l1 l2, tl (map2 f l1 l2) == map2 f (tl l1) (tl l2).
    Proof. destruct l1, l2; simpl; try easy. rewrite map2_nil_r; auto. Qed.

    (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *)
    Lemma map2_nth : forall l1 l2 i a b c,
        i < length l1 -> i < length l2 -> Ceq (f a b) c ->
        Ceq (nth i (map2 f l1 l2) c) (f (nth i l1 a) (nth i l2 b)).
    Proof.
      induction l1; intros; simpl in *; try lia.
      destruct l2; simpl in *; try lia.
      destruct i; try easy.
      apply IHl1; try lia. auto.
    Qed.
    
  End props_ABC.

  (**  Properties of map2 with one type *)
  Section props_A.
    Context `{Equiv_Aeq:Equivalence A Aeq}.
    Context `{Aadd:A->A->A} `{Aopp:A->A}.
    Infix "+" := Aadd : A_scope.
    Notation "- a" := (Aopp a) : A_scope.
    Notation Asub := (fun a b => a + (-b)).
    Infix "==" := (Aeq) : A_scope.
    Infix "==" := (eqlistA Aeq).

    (** l1 . l2 = l2 . l1 *)
    Context {Comm : Commutative Aadd Aeq}.
    Lemma map2_comm : forall l1 l2, map2 Aadd l1 l2 == map2 Aadd l2 l1.
    Proof.
      induction l1; destruct l2; simpl; auto.
      f_equiv; auto. apply commutative.
    Qed.
    
    (** (l1 . l2) . l3 = l1 . (l2 . l3) *)
    Context {Assoc:Associative Aadd Aeq}.
    Lemma map2_assoc : forall l1 l2 l3,
        map2 Aadd (map2 Aadd l1 l2) l3 == map2 Aadd l1 (map2 Aadd l2 l3).
    Proof.
      induction l1; destruct l2,l3; simpl; auto.
      f_equiv; auto. apply associative.
    Qed.

    (** map2 over map is homorphism *)
    (* In fact, I don't know how to naming this property yet. *)
    Lemma map2_map_hom :
      forall l1 l2 (H : forall a b : A, (Aopp (Aadd a b) == Aadd (Aopp a) (Aopp b))%A),
        map2 Aadd (map Aopp l1) (map Aopp l2) == map Aopp (map2 Aadd l1 l2).
    Proof.
      intros. revert l2.
      induction l1; destruct l2; simpl; try easy.
      apply cons_aeq_mor; auto. easy.
    Qed.

    
    (** *** The properties below, need a monoid structure *)
    Context `{M : Monoid _ Aadd A0 Aeq}.

    (** map2 lzero l = l *)
    Lemma map2_zero_l : forall l n, length l = n -> map2 Aadd (lzero A0 n) l == l.
    Proof.
      induction l; intros; subst; simpl in *. easy. rewrite IHl; auto. monoid_simp.
    Qed.

    (** map2 l lzero = l *)
    Lemma map2_zero_r : forall l n, length l = n -> map2 Aadd l (lzero A0 n) == l.
    Proof.
      induction l; intros; subst; simpl in *. easy. rewrite IHl; auto. monoid_simp.
    Qed.

    
    (** *** The properties below, need a group structure *)
    Context `{G : Group A Aadd A0 Aopp Aeq}.

    (* l1 - l2 = - (l2 - l1) *)
    Lemma map2_sub_comm : forall (l1 l2 : list A),
        map2 Asub l1 l2 == map Aopp (map2 Asub l2 l1).
    Proof.
      induction l1; destruct l2; intros; simpl in *; auto.
      apply cons_aeq_mor; auto.
      rewrite group_inv_distr. rewrite group_inv_inv. easy.
    Qed.

    (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
    Lemma map2_sub_perm : forall (l1 l2 l3 : list A),
        map2 Asub (map2 Asub l1 l2) l3 == map2 Asub (map2 Asub l1 l3) l2.
    Proof.
      induction l1,l2,l3; simpl; auto. apply cons_aeq_mor; auto.
      rewrite ?associative.
      apply monoidAaddProper; try easy. apply commutative.
    Qed.
    
    (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
    Lemma map2_sub_assoc : forall (l1 l2 l3 : list A),
        map2 Asub (map2 Asub l1 l2) l3 == map2 Asub l1 (map2 Aadd l2 l3).
    Proof.
      induction l1,l2,l3; simpl; auto. apply cons_aeq_mor; auto.
      rewrite associative. apply monoidAaddProper; try easy.
      rewrite group_inv_distr. apply commutative.
    Qed.

    (** 0 - l = - l *)
    Lemma map2_sub_zero_l : forall l n, 
        length l = n -> map2 Asub (lzero A0 n) l == map Aopp l.
    Proof.
      induction l; simpl; intros. apply map2_nil_r.
      induction n ; simpl. inversion H. apply cons_aeq_mor; auto.
      group_simp.
    Qed.
    
    (** l - 0 = l *)
    Lemma map2_sub_zero_r : forall l n, 
        length l = n -> map2 Asub l (lzero A0 n) == l.
    Proof.
      induction l; simpl; intros; auto. destruct n; simpl. inversion H.
      apply cons_aeq_mor; auto.
      rewrite group_inv_id. group_simp.
    Qed.
    
    (** l - l = 0 *)
    Lemma map2_sub_self : forall l n, 
        length l = n -> map2 Asub l l == (lzero A0 n).
    Proof.
      induction l; simpl; intros; subst; try easy.
      apply cons_aeq_mor; auto. group_simp.
    Qed.

  End props_A.

  (** Properties of map2 (other forms) *)
  Section props_others.
    
    Context {A B : Type}.
    Context {Beq : relation B}.
    Infix "==" := (Beq) : A_scope.
    Infix "==" := (eqlistA Beq) : list_scope.

    Lemma map2_map_map : forall (f1 f2 g : A -> B) (h : B -> B -> B)
                           (H : forall x, (h (f1 x) (f2 x) == g x)%A)
                           (l : list A),
        map2 h (map f1 l) (map f2 l) == map g l.
    Proof.
      induction l; simpl; auto.
    Qed.

  End props_others.

End map2.


(* ======================================================================= *)
(** ** fold of list *)
Section fold.
  Context `{M:Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** fold_right is a Proper morphism *)
  Lemma fold_right_aeq_mor : Proper (Aeq ==> eqlistA Aeq ==> Aeq) (fold_right Aadd).
  Proof.
    intros x y H l1. induction l1; intros l2 H2; destruct l2; try easy.
    inv H2. simpl. apply monoidAaddProper; try easy.
    apply IHl1. easy.
  Qed.
  Global Existing Instance fold_right_aeq_mor.

  (** fold_left is a proper relation *)
  Lemma fold_left_aeq_mor :
    Proper (eqlistA Aeq ==> Aeq ==> Aeq) (fold_left Aadd).
  Proof.
    intros l1. induction l1; intros l2 Hl a1 a2 Ha.
    - inv Hl. simpl. auto.
    - destruct l2. easy. inv Hl.
      simpl. apply IHl1; auto.
      rewrite Ha,H2. easy.
  Qed.
  Global Existing Instance fold_left_aeq_mor.

End fold.


(* ======================================================================= *)
(** ** concatenation of dlist: dlist -> list *)
Section concat.
  
  (** fold_left of list nat and add operation with different initial value *)
  Lemma fold_left_nat_initial : forall (l : list nat) n,
      fold_left Nat.add l n = fold_left Nat.add l 0 + n.
  Proof.
    induction l; intros; auto.
    simpl. rewrite IHl. rewrite (IHl a). lia.
  Qed.

  (** Length of concat operation *)
  Lemma concat_length : forall A (l : dlist A),
      length (concat l) = fold_left Nat.add (map (@length A) l) 0.
  Proof.
    intros A l.
    induction l; simpl; auto.
    rewrite app_length. rewrite IHl. rewrite (fold_left_nat_initial _ (length a)).
    lia.
  Qed.

End concat.


(* ======================================================================= *)
(** ** Convert between list and function *)
Section f2l_l2f.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  Definition f2l {n : nat} (f : nat -> A) : list A := map f (seq 0 n).

  Definition l2f {n : nat} (l : list A) : nat -> A := fun i => nth i l A0.

  Lemma f2l_length : forall n f, length (@f2l n f) = n.
  Proof. intros. unfold f2l. rewrite map_length. apply seq_length. Qed.

End f2l_l2f.

Section test.
  (** [1;2;3] *)
  Let f := fun i => i + 1.
  Let l := @f2l nat 3 f.
  (* Compute l. *)

  Let g := @l2f nat 0 3 l.
  (* Compute (g 0, g 1, g 2). *)
End test.  


(* ======================================================================= *)
(** ** Addition, Opposition and Subtraction of list *)
Section ladd_opp_sub.

  (** Let's have a group G *)
  Context `{G : Group}.
  Notation Asub := (fun a b => Aadd a (Aopp b)).
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** l1 + l2 *)
  Definition ladd (l1 l2 : list A) : list A := map2 Aadd l1 l2.
  Infix "+" := ladd : list_scope.

  Lemma ladd_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq ==> eqlistA Aeq) ladd.
  Proof.
    apply map2_aeq_mor. apply groupAaddProper.
  Qed.
  
  Global Existing Instance ladd_aeq_mor.

  (** - l *)
  Definition lopp (l : list A) : list A := map Aopp l.
  Notation "- l" := (lopp l) : list_scope.
  
  Lemma lopp_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq) lopp.
  Proof.
    apply map_aeq_mor. apply groupAoppProper.
  Qed.

  Global Existing Instance lopp_aeq_mor.
  
  (** l1 - l2 *)
  Definition lsub (l1 l2 : list A) : list A := map2 Asub l1 l2.
  Infix "-" := lsub : list_scope.

  Lemma lsub_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq ==> eqlistA Aeq) lsub.
  Proof.
    apply map2_aeq_mor.
    unfold Proper, respectful.
    intros. apply monoidAaddProper; try easy. apply groupAoppProper. auto.
  Qed.

  Global Existing Instance lsub_aeq_mor.


  (** length of ladd *)
  Lemma ladd_length : forall l1 l2 n,
      length l1 = n -> length l2 = n -> length (l1 + l2) = n.
  Proof. intros. apply map2_length; auto. Qed.
  
  (** [] + l = [] *)
  Lemma ladd_nil_l : forall l, ladd l [] == [].
  Proof. apply map2_nil_r. Qed.
  
  (** l + [] = [] *)
  Lemma ladd_nil_r : forall l, ladd [] l == [].
  Proof. apply map2_nil_l. Qed.

  (** 0 + l = l *)
  Lemma ladd_0_l : forall l n, length l = n -> ladd (lzero A0 n) l == l.
  Proof. intros. unfold ladd. apply map2_zero_l; auto. Qed.

  (** l + 0 = l *)
  Lemma ladd_0_r : forall l n, length l = n -> ladd l (lzero A0 n) == l.
  Proof. intros. apply map2_zero_r; auto. Qed.

  (** 0 - l = - l *)
  Lemma lsub_0_l : forall l n, length l = n -> (lzero A0 n) - l == - l.
  Proof. apply map2_sub_zero_l. Qed.
  
  (** l - 0 = l *)
  Lemma lsub_0_r : forall l n, length l = n -> l - (lzero A0 n) == l.
  Proof. apply map2_sub_zero_r. Qed.
  
  (** l - l = 0 *)
  Lemma lsub_self : forall l n, length l = n -> l - l == lzero A0 n.
  Proof. apply map2_sub_self. Qed.


  (** Let's have an abelian group AG *)
  Context `{AG : AGroup A Aadd A0 Aopp Aeq}.

  (** l1 + l2 = l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, l1 + l2 == l2 + l1.
  Proof. apply map2_comm; auto. Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma lsub_assoc : forall (l1 l2 l3 : list A), (l1 - l2) - l3 == l1 - (l2 + l3).
  Proof. intros. apply map2_sub_assoc. Qed.

  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma lsub_perm : forall (l1 l2 l3 : list A), (l1 - l2) - l3 == (l1 - l3) - l2.
  Proof. apply map2_sub_perm. Qed.

  (** l1 - l2 = - (l2 - l1) *)
  Lemma lsub_comm : forall (l1 l2 : list A), l1 - l2 == - (l2 - l1).
  Proof. intros. apply map2_sub_comm. Qed.
  
End ladd_opp_sub.


(* ======================================================================= *)
(** ** constant multiplication of list *)
Section lcmul_lmulc.
  (** Let's have a ring R *)
  Context `{R:Ring}.
  Add Ring ring_inst : (make_ring_theory R).
  
  Infix "*" := Amul : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  Context `{Dec:Decidable A Aeq}.
  
  (** a * l *)
  Definition lcmul (a : A) (l : list A) : list A := map (fun x => a * x) l.
  
  (** l * a *)
  Definition lmulc (l : list A) (a : A) : list A := map (fun x => x * a) l.
  
  (** cmul keep its length *)
  Lemma lcmul_length : forall a l n, length l = n -> length (lcmul a l) = n.
  Proof. intros. unfold lcmul. rewrite map_length; auto. Qed.
  
  (** a * l = l * a *)
  Lemma lmulc_lcmul : forall a l, lmulc l a == lcmul a l.
  Proof. induction l; simpl; auto. f_equiv; auto. ring. Qed.
  
  (** a * (x :: l) = (a * x) :: (a * l) *)
  Lemma lcmul_cons : forall a x l, lcmul a (x :: l) == (a * x) :: (lcmul a l).
  Proof. intros. simpl. easy. Qed.

  (** a * [] = [] *)
  Lemma lcmul_nil : forall a, lcmul a [] == [].
  Proof. intros. simpl. easy. Qed.
  
  (** [] * a = [] *)
  Lemma lmulc_nil : forall a, lmulc [] a == [].
  Proof. intros. simpl. easy. Qed.
  
  (** 0 c* l = 0 *)
  Lemma lcmul_0_l : forall l n, length l = n -> lcmul A0 l == lzero A0 n.
  Proof. induction l; intros; subst; simpl in *; auto. f_equiv; auto. ring. Qed.

  (** a * 0 = 0 *)
  Lemma lcmul_0_r : forall a n, lcmul a (lzero A0 n) == lzero A0 n.
  Proof. intros. unfold lcmul,lzero. rewrite map_repeat. f_equiv. ring. Qed.
  
  (** Let's have a field F *)
  Context `{F : Field A Aadd A0 Aopp Amul A1 Ainv Aeq}.
  
  (** k * l = l -> k = 1 \/ l = 0 *)
  Lemma lcmul_eq_imply_k1_or_l0 : forall (l : list A) n (k : A),
      length l = n -> lcmul k l == l -> ((k == A1)%A \/ l == lzero A0 n).
  Proof.
    induction l; intros. subst; auto. destruct n; auto. easy. simpl in *.
    injection H. intros H1. apply cons_eq_iff in H0. destruct H0.
    apply IHl with (k:=k) in H1; auto.
    apply field_mul_eq_imply_a1_or_b0 in H0; auto.
    destruct H0,H1; auto.
  Qed.
  
  (** k * l = 0 -> k = 0 \/ l = 0 *)
  Lemma lcmul_eq0_imply_k0_or_lzero : forall (l : list A) {n} (k : A),
      length l = n -> lcmul k l == lzero A0 n -> ((k == A0)%A \/ l == lzero A0 n).
  Proof.
    induction l; intros. subst; auto.
    destruct n. easy. simpl in *. inversion H. rewrite H2 in *.
    apply cons_eq_iff in H0. destruct H0.
    apply field_mul_eq0_imply_a0_or_b0 in H0; auto.
    apply IHl in H1; auto. destruct H0, H1; auto.
  Qed.
  
End lcmul_lmulc.


(* ======================================================================= *)
(** ** product of two lists *)
Section ldot.
  (** Let's have a ring R *)
  Context `{R:Ring}.
  Add Ring ring_inst : (make_ring_theory R).

  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "+" := (ladd (Aadd:=Aadd)) : list_scope.
  Infix "c*" := (lcmul (Amul:=Amul)) : list_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  
  (** dot product, marked as l1 ⋅ l2 *)
  Definition ldot (l1 l2 : list A) : A := fold_right Aadd A0 (map2 Amul l1 l2).
  Infix "⋅" := ldot : list_scope.

  (** map is respect to aeq *)
  Lemma ldot_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq ==> Aeq) ldot.
  Proof.
    unfold Proper, respectful.
    intros. unfold ldot. rewrite H,H0. easy.
  Qed.

  Global Existing Instance ldot_aeq_mor.

  (** l1 ⋅ l2 = l2 ⋅ l1 *)
  Lemma ldot_comm : forall (l1 l2 : list A), (l1 ⋅ l2 == l2 ⋅ l1)%A.
  Proof. intros. unfold ldot. rewrite map2_comm; auto. apply R. Qed.
  
  (** [] ⋅ l = 0 *)
  Lemma ldot_nil_l : forall (l : list A), (nil ⋅ l == A0)%A.
  Proof. intros. destruct l; simpl; try easy. Qed.
  
  (** l ⋅ [] = 0 *)
  Lemma ldot_nil_r : forall (l : list A), (l ⋅ nil == A0)%A.
  Proof. intros. destruct l; simpl; try easy. Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2,
      ((x1 :: l1) ⋅ (x2 :: l2) == (x1 * x2) + (l1 ⋅ l2))%A.
  Proof. induction l1,l2; simpl; intros; try easy. Qed.
  
  (** 0 ⋅ l = 0 *)
  Lemma ldot_0_l : forall l n, ((lzero A0 n) ⋅ l == A0)%A.
  Proof. induction l,n; simpl; intros; try easy. rewrite ldot_cons. rewrite IHl. ring.
  Qed.
  
  (** l ⋅ 0 = 0 *)
  Lemma ldot_0_r : forall l n, (l ⋅ (lzero A0 n) == A0)%A.
  Proof. intros. rewrite ldot_comm. apply ldot_0_l. Qed.
  
  (** ldot left distributve over map2: l1 ⋅ (map l2 l3) = l1 ⋅ l2 + l1 ⋅ l3 *)
  Lemma ldot_map2_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (l1 ⋅ (map2 Aadd l2 l3) == (l1 ⋅ l2) + (l1 ⋅ l3))%A.
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite !ldot_cons. rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.

  (** ldot right distributve over map2: (map + l1 l2) ⋅ l3 = l1 ⋅ l3 + l2 ⋅ l3 *)
  Lemma ldot_map2_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      ((map2 Aadd l1 l2) ⋅ l3 == (l1 ⋅ l3) + (l2 ⋅ l3))%A.
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite ?ldot_cons. ring_simplify. rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.

  (** ldot left distributive over ladd: l1 ⋅ (l2 + l3) = l1 ⋅ l2 + l1 ⋅ l3 *)
  Lemma ldot_ladd_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (l1 ⋅ (l2 + l3) == (l1 ⋅ l2) + (l1 ⋅ l3))%A.
  Proof. intros. apply ldot_map2_distr_l with (r:=r); auto. Qed.
  
  (** ldot right distributive over ladd: (l1 + l2) ⋅ l3 = l1 ⋅ l3 + l2 ⋅ l3 *)
  Lemma ldot_ladd_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      ((l1 + l2) ⋅ l3 == (l1 ⋅ l3) + (l2 ⋅ l3))%A.
  Proof. intros. apply ldot_map2_distr_r with (r:=r); auto. Qed.
  
  (** ldot left distributive over lcmul and mul: (x * l1) ⋅ l2 = x * (l1 ⋅ l2) *)
  Lemma ldot_lcmul_distr_l : forall l1 l2 x, ((x c* l1) ⋅ l2 == x * (l1 ⋅ l2))%A.
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite !ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot right distributive over lcmul and mul.
      l1 ⋅ (x * l2) = x * (l1 ⋅ l2) *)
  Lemma ldot_lcmul_distr_r : forall l1 l2 x, (l1 ⋅ (x c* l2) == x * (l1 ⋅ l2))%A.
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite !ldot_cons. rewrite IHl1. ring.
  Qed.

End ldot.


(* ======================================================================= *)
(** ** Generate special list *)
Section GenerateSpecialList.
  (** Let's have a ring R *)
  Context `{R:Ring}.
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).
  
  (** create a list for unit matrix, which length is n and almost all elements 
    are A0 excepts i-th is A1. *)
  Fixpoint list_unit (n i : nat) : list A :=
    match n, i with
    | 0, _ => []
    | S n, 0 => A1 :: (repeat A0 n)
    | S n, S i => A0 :: (list_unit n i)
    end.

  (* Compute list_unit 0 2. (* [] *) *)
  (* Compute list_unit 3 0. (* [1;0;0] *) *)
  (* Compute list_unit 3 1. (* [0;1;0] *) *)
  (* Compute list_unit 3 2. (* [0;0;1] *) *)
  (* Compute list_unit 3 3. (* [0;0;0] *) *)

  Lemma list_unit_length : forall n i, length (list_unit n i) = n.
  Proof.
    induction n; auto. destruct i; simpl; auto. rewrite repeat_length. auto.
  Qed.
  
  (** list_unit(n,i) [i] = A1, when i < n *)
  Lemma list_unit_A1 : forall n i, i < n -> (nth i (list_unit n i) A0 == A1)%A.
  Proof.
    induction n; intros; auto. easy.
    destruct i; simpl; try easy. apply IHn. lia.
  Qed.
  
  (** list_unit(n,i) [j] = A0, when i < n /\ j <> i *)
  Fact list_unit_spec1 : forall n i j, i < n -> j <> i ->
                                  (nth j (list_unit n i) A0 == A0)%A.
  Proof.
    induction n; intros; auto. easy. destruct i,j; simpl; try easy.
    apply nth_repeat_same. apply IHn; lia.
  Qed.
  
  (** list_unit(n,i) [j] = A0, j <> i *)
  Lemma list_unit_A0 : forall n i j, j <> i -> (nth j (list_unit n i) A0 == A0)%A.
  Proof.
    induction n; auto; simpl; intros.
    - destruct j; easy.
    - destruct i,j; simpl; try easy. apply nth_repeat_same. apply IHn. auto.
  Qed.
  
End GenerateSpecialList.


(* ======================================================================= *)
(** ** Convert list to fixed-length list *)
Section list_to_listN.
  Context `{M:Monoid}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** Get list from a given list and given length, too many data will be ignored 
      and too less data will be filled with A0 *)
  Fixpoint list_to_listN (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => (hd A0 l) :: (list_to_listN (tl l) n')
    end.
  
  Lemma list_to_listN_length : forall (n : nat) (l : list A), length (list_to_listN l n) = n.
  Proof. induction n; intros; simpl; auto. Qed.
  
  Lemma list_to_listN_eq : forall (n : nat) (l : list A),
      length l = n -> list_to_listN l n == l.
  Proof.
    induction n; intros; simpl.
    - apply (length_zero_iff_nil (Aeq:=Aeq)) in H; easy.
    - rewrite IHn; destruct l; simpl in *; try easy. auto.
  Qed.

End list_to_listN.


(* ======================================================================= *)
(** ** width of a dlist *)

Section dlist_width.

  Section defs.

    (** A predicate that every list of a dlist has same length *)
    Definition width {A:Type} (dl : dlist A) (n : nat) : Prop :=
      Forall (fun l => length l = n) dl.
    
  End defs.

  Section props.
    Context {A : Type}.

    (** width property should be kept by its child structure *)
    Lemma width_cons : forall (l : list A) dl n,
        width (l :: dl) n <-> length l = n /\ width dl n.
    Proof. intros. split; intros; inversion H; auto. constructor; auto. Qed.

    (** width property should be kept by every child element *)
    Lemma width_in : forall dl (l : list A) n, width dl n -> In l dl -> length l = n.
    Proof.
      induction dl; intros. inv H0.
      apply in_inv in H0. inv H. destruct H0; auto. subst; auto.
    Qed.

    (** app operation won't change width property *)
    Lemma app_width : forall (dl1 : dlist A) dl2 n, 
        width (dl1 ++ dl2) n <-> width dl1 n /\ width dl2 n.
    Proof.
      unfold width in *.
      induction dl1; intros; split; intros; simpl in *; inv H; auto.
      - apply IHdl1 in H3 as []. split; auto.
      - inv H0. constructor; auto. apply IHdl1. auto.
    Qed.

    (** rev operation won't change width property *)
    Lemma rev_width : forall (dl : dlist A) n, width (rev dl) n -> width dl n.
    Proof.
      unfold width in *.
      induction dl; simpl; intros; auto.
      apply app_width in H. destruct H. inv H0. constructor; auto.
    Qed.

    (** dlist generated by repeat will keep width property same as seed element *)
    Lemma repeat_width : forall (l : list A) n k, length l = k -> width (repeat l n) k.
    Proof. unfold width. induction n; intros; simpl; auto. Qed.

    (** width promise i-th row has same length *)
    Lemma width_imply_nth_length : forall i c (dl : dlist A), 
        i < length dl -> width dl c -> length (nth i dl []) = c.
    Proof.
      unfold width. intros i c dl. revert i c.
      induction dl; intros; simpl in *. lia.
      inv H0. destruct i; auto. apply IHdl; auto. lia.
    Qed.

    (** map width law *)
    Lemma width_map : forall (f: nat -> list A) (rowIdxs : list nat) c,
        (forall i, length (f i) = c) -> width (map f rowIdxs) c.
    Proof. unfold width. intros f idxs. induction idxs; simpl; auto. Qed.
    
  End props.

End dlist_width.


(* ======================================================================= *)
(** ** Set element of a dlist *)
Section dlst_chg.

  (** *** with a constant value *)
  Section by_constant.

    Section defs.
      Context {A : Type}.
      
      (** Set element of a dlist with a constant value *)
      Fixpoint dlst_chg (dl : dlist A) (i j : nat) (x : A) : dlist A :=
        match dl, i with
        | [], _ => []
        | l :: dl, 0 => (lst_chg l j x) :: dl
        | l :: dl, S i' => l :: (dlst_chg dl i' j x)
        end.
    End defs.
    
    (* Compute dlst_chg [] 0 1 9. *)
    (* Compute dlst_chg [[1;2];[3;4;5]] 0 1 9. *)
    (* Compute dlst_chg [[1;2];[3;4;5]] 1 1 9. *)
    (* Compute dlst_chg [[1;2];[3;4;5]] 2 1 9. *)
    (* Compute dlst_chg [[1;2];[3;4;5]] 1 5 9. *)

    Section props.
      Context {A : Type}.
      
      (** Length property *)
      Lemma dlst_chg_length : forall dl i r j (x:A),
          length dl = r -> length (dlst_chg dl i j x) = r.
      Proof. induction dl; destruct i; intros; simpl; auto. destruct r; auto. easy.
      Qed.
      
      (** Width property *)
      Lemma dlst_chg_width : forall dl i c j (x:A), 
          width dl c -> width (dlst_chg dl i j x) c.
      Proof.
        unfold width. induction dl; auto.
        destruct i; intros; simpl in *; auto; inv H; constructor; auto.
        apply lst_chg_length; auto.
      Qed.
    End props.

  End by_constant.

  (** *** with a generation function *)
  Section by_function.

    Section defs.
      Context {A : Type}.

      (** Inner version, i0 is given position, i is changed in every loop *)
      Fixpoint dlst_chgf_aux (dl : dlist A) (i0 i j : nat) (f : nat -> nat -> A)
        : dlist A :=
        match dl, i with
        | [], _ => []
        | l :: dl, 0 => (lst_chgf l j (f i0)) :: dl
        | l :: dl, S i' => l :: (dlst_chgf_aux dl i0 i' j f)
        end. 
      
      (** User version that hide i0 parameter *)
      Definition dlst_chgf (dl : dlist A) (i j : nat) (f : nat -> nat -> A) : dlist A :=
        dlst_chgf_aux dl i i j f.
    End defs.
    
    (* Let f_gen := fun (i j : nat) => (i + j + 10). *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 0 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 1 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 2 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 3 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 4 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 0 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 1 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 2 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 3 f_gen. *)
    (* Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 4 f_gen. *)

    Section props.
      Context {A : Type}.
      
      (** Length property *)
      Lemma dlst_chgf_aux_length : forall dl i r i0 j f, 
          length dl = r -> length (@dlst_chgf_aux A dl i0 i j f) = r.
      Proof. induction dl; destruct i; auto; simpl; intros. destruct r; auto. easy.
      Qed.
      
      Lemma dlst_chgf_length : forall dl r i j f, 
          length dl = r -> length (@dlst_chgf A dl i j f) = r.
      Proof. intros. apply dlst_chgf_aux_length. auto. Qed.
      
      (** Width property *)
      Lemma dlst_chgf_aux_width : forall dl i c i0 j f, 
          width dl c -> width (@dlst_chgf_aux A dl i0 i j f) c.
      Proof.
        unfold width. induction dl; auto. 
        induction i; intros; simpl in *; auto; inv H; constructor; auto.
        apply lst_chgf_length; auto.
      Qed.
      
      Lemma dlst_chgf_width : forall dl i c j f, 
          width dl c -> width (@dlst_chgf A dl i j f) c.
      Proof. intros. apply dlst_chgf_aux_width; auto. Qed.
    End props.

  End by_function.

End dlst_chg.


(* ======================================================================= *)
(** ** Set row of a dlist *)
Section dlst_chgrow.

  (** *** with a constant value *)
  Section by_constant.

    Section defs.
      Context {A : Type}.
      
      Fixpoint dlst_chgrow (dl : dlist A) (i : nat) (l : list A) : dlist A :=
        match dl, i with
        | [], _ => []
        | x :: dl, 0 => l :: dl
        | x :: dl, S i' => x :: (dlst_chgrow dl i' l)
        end.
    End defs.
    
    (* Compute dlst_chgrow [] 0 [8;9]. *)
    (* Compute dlst_chgrow [[1;2];[3;4;5]] 0 [8;9]. *)
    (* Compute dlst_chgrow [[1;2];[3;4;5]] 1 [8;9]. *)
    (* Compute dlst_chgrow [[1;2];[3;4;5]] 2 [8;9].   *)

    Section props.
      Context {A : Type}.

      (** Length property *)
      Lemma dlst_chgrow_length : forall dl i r l, 
          length dl = r -> length (@dlst_chgrow A dl i l) = r.
      Proof.
        induction dl; auto. destruct i; auto; intros; simpl in *.
        destruct r; auto. easy.
      Qed.
      
      (** Width property *)
      Lemma dlst_chgrow_width : forall {A} dl i c l,
          length l = c -> width dl c -> width (@dlst_chgrow A dl i l) c.
      Proof.
        unfold width; induction dl; auto. 
        induction i; intros; simpl in *; inv H0; constructor; auto.
      Qed.
    End props.

  End by_constant.

  
  (** *** with a generation function *)
  Section by_function.

    Section defs.
      Context {A : Type}.
      
      (** Inner version, i0 is given position, i is changed in every loop *)
      Fixpoint dlst_chgrowf_aux (dl : dlist A) (i0 i : nat) (f : nat -> list A)
        : dlist A :=
        match dl, i with
        | [], _ => []
        | l :: dl, 0 => (f i0) :: dl
        | l :: dl, S i' => l :: (dlst_chgrowf_aux dl i0 i' f)
        end. 
      
      (** User version that hide i0 parameter *)
      Definition dlst_chgrowf (dl : dlist A) (i : nat) (f : nat -> list A) : dlist A :=
        dlst_chgrowf_aux dl i i f.
      
    End defs.
    
    (* Let f_gen := fun (i : nat) => [i+10;i+11;i+12]. *)
    (* Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 f_gen. *)
    (* Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 f_gen. *)
    (* Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 2 f_gen. *)
    (* Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 3 f_gen.  *)

    Section props.
      Context {A : Type}.
      
      (** Length property *)
      Lemma dlst_chgrowf_aux_length : forall dl i r i0 f, 
          length dl = r -> length (@dlst_chgrowf_aux A dl i0 i f) = r.
      Proof. induction dl; intros; auto. destruct i; auto. simpl. destruct r; auto.
             easy.
      Qed.
      
      Lemma dlst_chgrowf_length : forall dl r i f, 
          length dl = r -> length (@dlst_chgrowf A dl i f) = r.
      Proof. intros. apply dlst_chgrowf_aux_length. auto. Qed.
      
      (** Width property *)
      Lemma dlst_chgrowf_aux_width : forall dl i c i0 f, 
          length (f i0) = c -> width dl c -> width (@dlst_chgrowf_aux A dl i0 i f) c.
      Proof.
        unfold width; induction dl; auto. 
        induction i; intros; simpl in *; auto; inv H0; constructor; auto.
      Qed.
      
      Lemma dlst_chgrowf_width : forall dl i c f, 
          length (f i) = c -> width dl c ->  width (@dlst_chgrowf A dl i f) c.
      Proof. intros. apply dlst_chgrowf_aux_width; auto. Qed.
    End props.
    
  End by_function.
  
End dlst_chgrow.


(* ======================================================================= *)
(** ** Properties of dlist equal *)
Section dlst_eq.

  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Context `{A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  Open Scope nat.

  (** Two dlists are equal, iff all corresponded (i,j) elements is equal *)
  Lemma dlist_eq_iff_nth :
    forall r c (dl1 dl2 : dlist A)
           (H1 : length dl1 = r) (H2 : length dl2 = r)
           (H3 : width dl1 c) (H4 : width dl2 c),
      dl1 == dl2 <->
        (forall i j, i < r -> j < c ->
                (nth j (nth i dl1 []) A0 == nth j (nth i dl2 []) A0)%A).
  Proof.
    intros; split; intros.
    - rewrite H. easy.
    - apply (list_eq_iff_nth [] [] _ dl1 dl2 H1 H2). intros. subst.
      rewrite (list_eq_iff_nth) with (n:=c); auto;
        apply width_imply_nth_length; auto. lia.
  Qed.

  (* (** dlist_eq is decidable *) *)
  (* Lemma dlist_eq_dec : forall (dl1 dl2 : dlist A) (HDec:Decidable Aeq), *)
  (*     {dl1 == dl2} + {~(dl1 == dl2)}. *)
  (* Proof. intros. apply decidable. Qed. *)

End dlst_eq.


(* ======================================================================= *)
(** ** a dlist with all nil elements *)
Section dnil.
  
  Context `{M:Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  Open Scope nat.
  
  (** a dlist that every list is nil, named as dnil *)
  Fixpoint dnil n : dlist A :=
    match n with
    | O => nil
    | S n' => nil :: (dnil n')
    end.

  (** dnil's length law *)
  Lemma dnil_length : forall n, length (dnil n) = n.
  Proof. induction n; simpl; auto. Qed.

  (** dnil's width law *)
  Lemma dnil_width : forall n, width (dnil n) 0.
  Proof. unfold width; induction n; simpl; auto. Qed.
  
  (** dnil equal to append two child dnil *)
  Lemma dnil_app : forall n1 n2, dnil (n1 + n2) == dnil n1 ++ dnil n2.
  Proof.
    induction n1,n2; simpl; try easy.
    - rewrite app_nil_r. rewrite Nat.add_0_r. easy.
    - rewrite IHn1. simpl. easy.
  Qed.

  (** width dl is zero imply it is a dnil *)
  Lemma dlist_w0_eq_dnil : forall (dl : list (list A)), 
      width dl 0 -> dl == dnil (length dl).
  Proof.
    unfold width; induction dl; simpl; auto.
    intros. inv H. apply cons_aeq_mor; auto. 
    apply length_zero_iff_nil; auto.
  Qed.

  (** reverse a dnil is itself *)
  Lemma dnil_rev : forall n, rev (dnil n) == dnil n.
  Proof.
    induction n; simpl; auto. rewrite IHn. clear IHn. induction n; simpl; auto.
  Qed.

End dnil.


(* ======================================================================= *)
(** ** map2 of dlist *)
Section dlist_map2.

  Context {A B C : Type} {Aeq : relation A} {Beq:relation B} {Ceq:relation C}.
  Context {EqEquivA:Equivalence Aeq}.
  Context {EqEquivB:Equivalence Beq}.
  Context {EqEquivC:Equivalence Ceq}.
  Variable f : A -> B -> C.
  
  Infix "==" := (eqlistA (eqlistA Ceq)).
  Open Scope nat.

  (** map2 dnil dl = dnil *)
  Lemma map2_dnil_l : forall n dl, length dl = n -> map2 (map2 f) (dnil n) dl == dnil n.
  Proof.
    intros. gd dl. induction n; intros; simpl; try easy.
    destruct dl. inversion H. inversion H. rewrite H1. auto.
  Qed.

  (** map2 dl dnil = dnil *)
  Lemma map2_dnil_r : forall dl n, length dl = n -> map2 (map2 f) dl (dnil n) == dnil n.
  Proof.
    intros. gd dl. induction n; intros; simpl; try easy.
    - rewrite map2_nil_r. easy.
    - destruct dl. easy. simpl. rewrite IHn; auto. rewrite map2_nil_r. easy.
  Qed.

End dlist_map2.


(* ======================================================================= *)
(** ** Convert between dlist and function *)
Section f2dl_dl2f.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  (* Infix "==" := (Aeq) : A_scope. *)
  (* Infix "==" := (eqlistA Aeq). *)
  (* Infix "==" := (eqlistA (eqlistA Aeq)). *)

  Definition f2dl {r c : nat} (f : nat -> nat -> A) : dlist A :=
    map (fun i => f2l (n:=c) (f i)) (seq 0 r).

  Definition dl2f {r c : nat} (dl : dlist A) : nat -> nat -> A :=
    fun i j => nth j (nth i dl []) A0.

  Lemma f2dl_length : forall r c f, length (@f2dl r c f) = r.
  Proof. intros. unfold f2dl. rewrite map_length. apply seq_length. Qed.

  Lemma f2dl_width : forall r c f, width (@f2dl r c f) c.
  Proof.
    unfold f2dl,width.
    induction r; intros; simpl; try constructor.
    - apply f2l_length.
    - rewrite <- seq_shift. rewrite List.map_map. apply IHr.
  Qed.

End f2dl_dl2f.

(* (** [[1;2;3];[4;5;6];[7;8;9]] *) *)
(* Let f := fun i j => i * 3 + j + 1. *)
(* Let dl := @f2dl nat 3 3 f. *)
(* Compute dl. *)

(* Let g := @dl2f nat 0 3 3 dl. *)
(* Compute (g 0 0, g 0 1, g 0 2, g 1 0, g 1 1, g 1 2, g 2 0, g 2 1, g 2 2). *)


(* ======================================================================= *)
(** ** Convert between row and col. eg, [1;2;3] <-> [[1];[2];[3]] *)
Section convert_row_and_col.
  Context `{M:Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Convert a list to a dlist, it looks like converting a row to a column. *)
  Fixpoint row2col (l : list A) : dlist A :=
    match l with
    | [] => []
    | x :: tl => [x] :: (row2col tl)
    end.
  
  (** row2col length law *)
  Lemma row2col_length : forall l, length (row2col l) = length l.
  Proof. induction l; simpl; intros; auto. Qed.
  
  (** row2col width law *)
  Lemma row2col_width : forall l, width (row2col l) 1.
  Proof. unfold width; induction l; simpl; intros; auto. Qed.

  Lemma nth_row2col : forall l i,
      i < length l -> (nth i (row2col l) [] == [nth i l A0])%list.
  Proof.
    induction l; intros; simpl in *. lia. destruct i; try easy. apply IHl. lia.
  Qed.
  
  (** Convert a dlist to a list which contain head element, it looks like 
      converting a column to a row. *)
  Fixpoint col2row (dl : dlist A) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd A0 l) :: (col2row tl)
    end.
  
  (** Convert a dlist to list then convert it to a dlist, equal to original dlist. *)
  Lemma row2col_col2row : forall (dl : list (list A)),
      width dl 1 -> row2col (col2row dl) == dl.
  Proof.
    unfold width; induction dl; simpl; auto; intros. inv H.
    apply cons_aeq_mor; auto.
    destruct a; simpl in *; try easy. inv H2.
    apply List.length_zero_iff_nil in H0. subst. easy.
  Qed.
  
  (** Convert a list to dlist then convert it to a list, equal to original 
      list. *)
  Lemma col2row_row2col : forall (l : list A), 
      (col2row (row2col l) == l)%list.
  Proof. induction l; simpl; auto; intros. rewrite IHl. easy. Qed.

End convert_row_and_col.


(* ======================================================================= *)
(** ** head column of a dlist *)
Section hdc.
  Context {A : Type} (A0 : A).
  
  (** Get head column of a dlist *)
  Fixpoint hdc (dl : dlist A) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd A0 l) :: (hdc tl)
    end.
  
  (** hdc length law *)
  Lemma hdc_length : forall dl, length (hdc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
End hdc.


(* ======================================================================= *)
(** ** tail columns of a dlist *)
Section tlc.
  Context {A : Type}.
  
  (** Get tail columns of a dlist *)
  Fixpoint tlc (dl : dlist A) : dlist A :=
    match dl with
    | [] => []
    | l :: tl => (tail l) :: (tlc tl)
    end.
  
  (** tlc length law *)
  Lemma tlc_length : forall dl, length (tlc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
  (** tlc width law when width equal to 0 *)
  Lemma tlc_width0 : forall dl, width dl 0 -> width (tlc dl) 0.
  Proof.
    unfold width; induction dl; simpl; auto. intros. inv H; constructor; auto.
    apply List.length_zero_iff_nil in H2. subst. auto.
  Qed.
  
  (** tlc width law when width not equal to 0 *)
  Lemma tlc_widthS : forall dl c, width dl (S c) -> width (tlc dl) c.
  Proof.
    unfold width; induction dl; intros; simpl; auto. inv H.
    constructor; auto. destruct a; auto. easy.
  Qed.
  
End tlc.


(* ======================================================================= *)
(** ** construct a dlist with a list and a dlist by column *)
Section consc.

  Context `{Equiv_Aeq:Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Construct a dlist by column with a list and a dlist.
      If the list and dlist have different length, then only the
      top elements with minimal length will be kept. *)
  Fixpoint consc (l : list A) (dl : dlist A) : dlist A :=
    match l, dl with
    | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
    | _, _ => []
    end.

  Lemma consc_aeq_mor :
    Proper (eqlistA Aeq ==> eqlistA (eqlistA Aeq) ==> eqlistA (eqlistA Aeq)) consc.
  Proof.
    unfold Proper, respectful.
    induction x; intros.
    - destruct x,y0,y; simpl; try easy.
    - destruct x0,y0,y; simpl; try easy.
      apply cons_eq_iff in H as [->], H0 as [->].
      apply cons_aeq_mor; auto. easy.
  Qed.
  
  Global Existing Instance consc_aeq_mor.

  (** consc_eq, seems like f_equal *)
  Lemma consc_eq_iff : forall (l1 l2 : list A) (dl1 dl2 : list (list A)) n
                         (H1:length l1 = n) (H2:length l2 = n)
                         (H3:length dl1 = n) (H4:length dl2 = n),
      consc l1 dl1 == consc l2 dl2 <-> (l1 == l2)%list /\ dl1 == dl2.
  Proof.
    induction l1.
    - intros. simpl in *. subst. apply List.length_zero_iff_nil in H4,H3,H2.
      subst. easy.
    - intros. destruct l2,dl1,dl2; simpl in *; subst; try easy.
      inv H2. inv H3. inv H4. split; intros.
      + inv H. rewrite IHl1 in H8; auto. inv H8. inv H6.
        rewrite H,H3,H8,H10. easy.
      + inv H. inv H3. inv H4. rewrite H7,H6. apply cons_eq_iff; split; try easy.
        rewrite IHl1; auto.
  Qed.
  
  (** consc length law *)
  Lemma consc_length : forall l dl r,
      length l = r -> length dl = r -> length (consc l dl) = r.
  Proof.
    induction l,dl; simpl; intros; auto. destruct r. inversion H. f_equal.
    inversion H. inversion H0. subst. apply IHl; auto.
  Qed.
  
  (** consc width law *)
  Lemma consc_width : forall l dl c,
      length l = length dl -> width dl c -> width (consc l dl) (S c).
  Proof.
    unfold width; induction l,dl; simpl; intros; auto.
    inv H. inv H0. constructor; auto.
  Qed.

  (** consc with hdc and tlc of a dnil generate lzero *)
  Lemma consc_hdc_tlc_width0 : forall dl r, 
      length dl = r -> width dl 0 -> 
      consc (hdc A0 dl) (tlc dl) == row2col (repeat A0 r).
  Proof.
    unfold width; induction dl; simpl; intros; subst; try easy.
    inv H0. apply List.length_zero_iff_nil in H2. subst. simpl.
    rewrite IHdl; auto. easy.
  Qed.
  
  (** consc with hdc and tlc of a dlist generate itself *)
  Lemma consc_hdc_tlc_widthS : forall dl c, 
      width dl (S c) ->
      consc (hdc A0 dl) (tlc dl) == dl.
  Proof.
    unfold width; induction dl; simpl; intros; auto. inv H.
    apply cons_eq_iff; split; auto.
    - destruct a; simpl in *. easy. easy.
    - apply IHdl with (c:=c). auto.
  Qed.

  (** consc decompose.
    x1::l1 ++ l2::dl2 = (x::l2) :: (l1 ++ dl2)  *)
  Lemma consc_decompose : forall x1 l1 l2 dl2,
      consc (x1::l1) (l2::dl2) == (x1::l2) :: (consc l1 dl2).
  Proof. intros. simpl. easy. Qed.
  
  (** repeat (x :: l) decomposition *)
  Lemma repeat_consr : forall l x n, repeat (x :: l) n == consc (repeat x n) (repeat l n).
  Proof.
    induction n; simpl; auto. rewrite IHn. easy.
  Qed.

End consc.


(* ======================================================================= *)
(** ** Append two dlist *)
Section dlist_app.
  Context {A : Type}.
  
  (** dlist append by row *)
  Definition dlappr := @app (list A).
  
  (** dlist apend by column *)
  Fixpoint dlappc (dl1 dl2 : dlist A) : dlist A :=
    match dl1, dl2 with
    | l1 :: tl1, l2 :: tl2 => (app l1 l2) :: (dlappc tl1 tl2)
    | _, _ => []
    end.

End dlist_app.

Notation "l @@ r" := (dlappc l r) (at level 40) : dlist_scope.


(* ======================================================================= *)
(** ** Zero dlist *)
Section dlzero.

  Context `{Equiv_Aeq:Equivalence A Aeq} (A0:A).
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** dlist constructed by repeated lzero, named as dlzero *)
  Definition dlzero r c := repeat (repeat A0 c) r.

  (** dlzero rewrite *)
  Lemma dlzero_rw : forall r c, repeat (lzero A0 c) r = dlzero r c.
  Proof. auto. Qed.
  
  (** dlzero with (S r) rows could be splited to two parts *)
  Lemma dlzero_Sr : forall {r c}, dlzero (S r) c == (lzero A0 c) :: (dlzero r c).
  Proof. intros. simpl. cbn. easy. Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_dnil : forall {c}, dlzero c 0 == dnil c.
  Proof. induction c; simpl; try easy. rewrite <- IHc. easy. Qed.
  
  (** dlzero heigth law *)
  Lemma dlzero_length : forall {r c}, length (dlzero r c) = r.
  Proof. intros. apply repeat_length. Qed.
  
  (** dlzero width law *)
  Lemma dlzero_width : forall {r c}, width (dlzero r c) c.
  Proof.
    unfold width, dlzero; induction r; intros; simpl; auto. constructor; auto.
    apply lzero_length.
  Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_w0_eq_dnil : forall r, dlzero r 0 == dnil r.
  Proof. 
    induction r; try easy. unfold dlzero in *. simpl in *. rewrite IHr. easy.
  Qed.
  
  (** append two dlzeros by row equal to whole *)
  Lemma dlzero_app_row : forall r1 r2 c, dlzero r1 c ++ dlzero r2 c == dlzero (r1 + r2) c.
  Proof. unfold dlzero. intros. rewrite repeat_app. easy. Qed.
  
  (** append two dlzeros by column equal to whole *)
  Lemma dlzero_app_col : forall r c1 c2,
      ((dlzero r c1) @@ (dlzero r c2)) == dlzero r (c1 + c2).
  Proof.
    induction r; intros; simpl; try easy. unfold dlzero,lzero in *.
    rewrite IHr. simpl. rewrite repeat_app. easy.
  Qed.

End dlzero.


(* ======================================================================= *)
(** ** transpose a dlist *)
Section dltrans.

  Context `{Equiv_Aeq:Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Transposition of a dlist *)
  (* Note: fetch every row and cons by column one bye one.
     c is the columnu number of the dlist. *)
  Fixpoint dltrans (dl : dlist A) (c : nat) : dlist A :=
    match dl with
    | [] => @dnil A c
    | l :: tl => consc l (dltrans tl c)
    end.

  Lemma dltrans_aeq_mor :
    Proper (eqlistA (eqlistA Aeq) ==> eq ==> eqlistA (eqlistA Aeq)) dltrans.
  Proof.
    unfold Proper, respectful.
    induction x; intros.
    - destruct y; subst; easy.
    - destruct y. easy. inv H. simpl. rewrite H4. rewrite (IHx y); easy.
  Qed.

  Global Existing Instance dltrans_aeq_mor.

  (** dltrans length law *)
  Lemma dltrans_length : forall dl c, 
      width dl c -> length (dltrans dl c) = c.
  Proof.
    induction dl; intros; simpl; auto.
    - rewrite dnil_length. auto.
    - inversion H. rewrite consc_length with (r:=c); auto.
  Qed.
  
  (** dltrans width law *)
  Lemma dltrans_width : forall dl r c, 
      length dl = r -> width dl c -> width (dltrans dl c) r.
  Proof.
    unfold width; induction dl; intros; simpl in *; auto.
    - induction c; simpl in *; auto.
    - rewrite <- H. inv H0. apply consc_width.
      + rewrite dltrans_length; auto.
      + apply IHdl; auto. 
  Qed.
  
  (** dltrans dnil = [] *)
  Lemma dltrans_nil : forall n, dltrans (dnil n) 0 == [].
  Proof.
    intros. destruct n; simpl. reflexivity. easy.
  Qed.
  
  (** dltrans consr = consc dltrans *)
  Lemma dltrans_consr : forall dl l c,
      dltrans (l :: dl) c == consc l (dltrans dl c).
  Proof.
    intros. simpl. easy.
  Qed.

  (** dltrans consc = consr dltrans *)
  Lemma dltrans_consc : forall dl l r c,
      length l = r -> length dl = r -> width dl c ->
      dltrans (consc l dl) (S c) == l :: (dltrans dl c).
  Proof.
    unfold width; induction dl; simpl; intros; subst.
    - destruct l; simpl; try easy.
    - destruct l. easy. inv H0. inv H1.
      specialize (IHdl l (length l) (length a) eq_refl H2 H4). simpl.
      destruct (dltrans (consc l dl) (S (length a))). easy. inv IHdl.
      rewrite H3,H6. easy.
  Qed.
  
  (** dltrans twice return back *)
  Lemma dltrans_trans : forall dl r c,
      length dl = r -> width dl c -> dltrans (dltrans dl c) r == dl.
  Proof.
    induction dl; intros; simpl in *.
    - subst. destruct c; simpl; auto.
    - destruct r. auto. inv H. inv H0.
      rewrite dltrans_consc with (r:=length a);
        auto using dltrans_length, dltrans_width.
      f_equiv; auto.
  Qed.
  
  (** dltrans dlzero<r,c> = dlzero<c,r> *)
  Lemma dltrans_zero : forall r c, dltrans (dlzero A0 r c ) c == dlzero A0 c r.
  Proof.
    induction r; intros; simpl; auto. rewrite dlzero_dnil; easy.
    unfold dlzero in *; simpl in *. rewrite IHr.
    rewrite repeat_consr. easy.
  Qed.
  
End dltrans.


(* ======================================================================= *)
(** ** dlist unit, like a identity matrix *)
Section dlunit.

  Context `{Equiv_Aeq:Equivalence A Aeq} {A0 A1:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Build a identity matrix with dlist. *)
  (* there are 4 parts of a dlunit [n x n]: 
      left top element [1 x 1], 
      right top list [1 x (n-1)], 
      left bottom list [(n-1) x 1],
      right bottom square is another small dlunit [(n-1) x (n-1)] *)
  Fixpoint dlunit (n : nat) : dlist A :=
    match n with
    | O => []
    | S n0 => (A1 :: (repeat A0 n0)) :: (consc (repeat A0 n0) (dlunit n0))
    end.
  
  (** dlunit length law *)
  Lemma dlunit_length : forall {n}, length (dlunit n) = n.
  Proof.
    induction n; simpl; auto. f_equal.
    rewrite consc_length with (r:=n); auto. apply repeat_length.
  Qed.
  
  (** dlunit width law *)
  Lemma dlunit_width : forall {n}, width (dlunit n) n.
  Proof.
    unfold width; induction n; simpl; auto. constructor.
    - simpl. f_equal. apply repeat_length.
    - apply consc_width; auto. rewrite repeat_length, dlunit_length; auto.
  Qed.
  
  (** transpose dlunit keep unchanged *)
  Lemma dltrans_dlunit : forall {n}, 
      let u := dlunit n in dltrans u n == u.
  Proof.
    simpl. induction n; simpl; try easy.
    assert ((dltrans (consc (repeat A0 n) (dlunit n)) (S n)) ==
              (repeat A0 n) :: (dltrans (dlunit n) n)).
    { apply dltrans_consc with (r:=n).
      apply repeat_length. apply dlunit_length. apply dlunit_width. }
    destruct (dltrans (consc (repeat A0 n) (dlunit n)) (S n)). easy.
    inv H. rewrite H3,H5,IHn. easy.
  Qed.

End dlunit.


(* ======================================================================= *)
(** ** map of dlist *)

Section dmap.

  Section defs.
    Context {A B : Type}.
    Variable f : A -> B.
    
    (** map operation to dlist *)
    Definition dmap dl := map (map f) dl.
  End defs.
  
  (** properties for map of dlist with f : A -> B *)
  Section props_AB.
    Context `{Equiv_Aeq:Equivalence A Aeq}.
    Context `{Equiv_Beq:Equivalence B Beq}.
    Variable f : A -> B.
    Infix "==" := Beq : A_scope.
    Infix "==" := (eqlistA Beq) : list_scope.
    Infix "==" := (eqlistA (eqlistA Beq)).
    
    (** dmap is a proper morphism *)
    Context {fProper : (Proper (Aeq ==> Beq) f)}.
    Lemma dmap_aeq_mor :
      Proper (eqlistA (eqlistA Aeq) ==> eqlistA (eqlistA Beq)) (dmap f).
    Proof.
      unfold Proper, respectful.
      induction x; destruct y; intros; simpl; try easy. inv H.
      rewrite H3, (IHx y); easy.
    Qed.

    Global Existing Instance dmap_aeq_mor.

    (** dmap length law *)
    Lemma dmap_length : forall dl, length (dmap f dl) = length dl.
    Proof. induction dl; simpl; auto. Qed.
    
    (** dmap width law *)
    Lemma dmap_width : forall dl n, width dl n <-> width (dmap f dl) n.
    Proof.
      unfold width; induction dl; intros; split; intros; simpl in *; auto.
      - inv H. constructor. apply map_length. apply IHdl. auto.
      - inv H. constructor. rewrite map_length. auto. apply IHdl. auto.
    Qed.
    
    (** dmap of cons equal to cons of map and dmap *)
    Lemma dmap_cons : forall l dl, dmap f (l :: dl) == (map f l) :: (dmap f dl).
    Proof. intros. simpl. easy. Qed.
    
    (** dmap of append is distributive *)
    Lemma dmap_app : forall dl1 dl2, dmap f (dl1 ++ dl2) == (dmap f dl1) ++ (dmap f dl2).
    Proof.
      induction dl1; destruct dl2; simpl in *; rewrite ?app_nil_r; try easy.
      rewrite IHdl1. easy.
    Qed.
    
    (** dmap dnil = dnil *)
    Lemma dmap_dnil : forall n, dmap f (dnil n) == dnil n.
    Proof. induction n; simpl; auto. Qed.

    (** dmap extensional law  *)
    Lemma dmap_ext : forall dl (g : A -> B) (H : forall a, (f a == g a)%A),
        dmap f dl == dmap g dl.
    Proof. intros. unfold dmap. apply map_ext. intros. apply map_ext; auto. Qed.

  End props_AB.

  (** map of dlist with f : A -> A *)
  Section props_AA.
    Context `{Equiv_Aeq:Equivalence A Aeq}.
    Infix "==" := Aeq : A_scope.
    Infix "==" := (eqlistA Aeq) : list_scope.
    Infix "==" := (eqlistA (eqlistA Aeq)).

    (** dmap (fun x => A0) dl = dlzero A0 r c *)
    Lemma dmap_f0 : forall {r c} dl (A0:A),
        length dl = r -> width dl c -> dmap (fun (x:A) => A0) dl == dlzero A0 r c.
    Proof.
      intros. unfold dmap,dlzero.

      (* Note that, use "map_eq_zero" cannot prove this lemma.
       Although this method looks very simple. *)
      (* apply map_eq_zero; auto. intros. apply map_eq_zero; try easy. *)
      
      revert r c H H0.
      induction dl; intros; simpl in *.
      - subst. easy.
      - destruct r; try easy. inv H. inv H0. simpl. apply cons_aeq_mor.
        + apply map_eq_zero; auto. easy.
        + apply IHdl; auto.
    Qed.

  End props_AA.
  
End dmap.


(* ======================================================================= *)
(** ** map2 of dlist *)
Section dmap2.

  Section defs.
    (** map operation to two dlists *)
    Definition dmap2 {A B C} (f : A -> B -> C) dl1 dl2 := map2 (map2 f) dl1 dl2.
  End defs.

  Section props_ABC.
    
    Context {A B : Type} `{Equiv_Ceq:Equivalence C Ceq}.
    Variable f : A -> B -> C.
    Infix "==" := (eqlistA (eqlistA Ceq)).
    
    (** dmap2 length law *)
    Lemma dmap2_length : forall dl1 dl2,
        length dl1 = length dl2 -> length (dmap2 f dl1 dl2) = length dl1.
    Proof. induction dl1,dl2; simpl; auto. Qed.
    
    (** dmap2 width law *)
    Lemma dmap2_width : forall dl1 dl2 n,
        width dl1 n -> width dl2 n -> width (dmap2 f dl1 dl2) n.
    Proof. 
      unfold width; induction dl1; intros; simpl in *; auto.
      destruct dl2; auto. inv H. inv H0. constructor.
      apply map2_length; auto. apply IHdl1; auto.
    Qed.
    
    (** dmap2 and consr *)
    Lemma dmap2_consr : forall dl1 dl2 l1 l2,
        dmap2 f (l1 :: dl1) (l2 :: dl2) == (map2 f l1 l2) :: (dmap2 f dl1 dl2).
    Proof. intros. simpl. easy. Qed.
    
    (** dmap2 and consc *)
    Lemma dmap2_consc : forall l1 dl1 l2 dl2 c,
        length l1 = length dl1 -> length l2 = length dl2 ->
        width dl1 c -> width dl2 c ->
        dmap2 f (consc l1 dl1) (consc l2 dl2) ==
          consc (map2 f l1 l2) (dmap2 f dl1 dl2).
    Proof.
      unfold width; induction l1,dl1,l2,dl2; simpl; intros; auto. f_equiv.
      inv H. inv H0. inv H1. inv H2. apply IHl1 with (c:=length l); auto.
    Qed.
    
    (** dmap2 and add *)
    Lemma dmap2_app : forall dla1 dla2 dlb1 dlb2,
        length dla1 = length dlb1 -> length dla2 = length dlb2 ->
        dmap2 f (dla1 ++ dla2) (dlb1 ++ dlb2) ==
          (dmap2 f dla1 dlb1) ++ (dmap2 f dla2 dlb2).
    Proof. intros. unfold dmap2. apply map2_app; auto. Qed.
    
    (** dmap2 dnil dl = dnil *)
    Lemma dmap2_dnil_l : forall dl n,
        length dl = n -> dmap2 f (dnil n) dl == dnil n.
    Proof. intros. unfold dmap2. rewrite map2_dnil_l; auto. easy. Qed.

    (** dmap2 dl dnil = dnil *)
    Lemma dmap2_dnil_r : forall dl n,
        length dl = n -> dmap2 f dl (dnil n) == dnil n.
    Proof. intros. unfold dmap2. rewrite map2_dnil_r; auto. easy. Qed.

    Lemma dmap2_tail : forall dl1 dl2,
        length dl1 = length dl2 ->
        tl (dmap2 f dl1 dl2) == dmap2 f (tl dl1) (tl dl2).
    Proof. intros. unfold dmap2. apply tail_map2. Qed.

    (** Relationship between dltrans and dmap2 *)
    Lemma dltrans_dmap2 : forall dl1 dl2 c,
        length dl1 = length dl2 -> width dl1 c -> width dl2 c ->
        dltrans (dmap2 f dl1 dl2) c ==
          dmap2 f (dltrans dl1 c) (dltrans dl2 c).
    Proof.
      unfold width; induction dl1; intros; simpl in *; subst.
      rewrite dmap2_dnil_l; auto using dltrans_length. easy.
      destruct dl2; simpl.
      - inv H.
      - inv H. inv H0. inv H1. rewrite IHdl1; auto.
        rewrite dmap2_consc with (c:=length dl1);
          auto using dltrans_width, dltrans_length; try easy.
        rewrite dltrans_length; auto.
        rewrite dltrans_length; auto.
    Qed.
    
  End props_ABC.

  (** dmap2 with same base type *)
  Section props_AAA.

    Context `{Aadd:A->A->A}.
    Context `{Equiv_Aeq:Equivalence A Aeq}.
    Infix "+" := Aadd : A_scope.
    Infix "==" := Aeq : A_scope.
    Infix "==" := (eqlistA Aeq) : list_scope.
    Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

    (** dmap2 with dmap of two components *)
    Lemma dmap2_dmap_dmap : forall (f1 f2 g : A -> A) (h : A -> A -> A) 
                              (H : forall x, Aeq (g x) (h (f1 x) (f2 x))) dl,
        (dmap2 h (dmap f1 dl) (dmap f2 dl) == dmap g dl)%dlist.
    Proof.
      induction dl; simpl; auto. rewrite IHdl. f_equiv. apply map2_map_map. easy.
    Qed.

    Variable Aopp : A -> A.
    Notation "- a" := (Aopp a) : A_scope.

    (** dmap2 over dmap is homorphism *)
    Lemma dmap2_dmap_hom : forall (H : forall a b : A, (- (a + b) == (- a) + (- b))%A)
                                  d1 d2,
        (dmap2 Aadd (dmap Aopp d1) (dmap Aopp d2) ==
           dmap Aopp (dmap2 Aadd d1 d2))%dlist.
    Proof.
      intros. revert d2. induction d1,d2; simpl; auto.
      rewrite IHd1. f_equiv. rewrite map2_map_hom; auto. easy.
    Qed.
    
    (** dl1 . dl2 = dl2 . dl1 *)
    Lemma dmap2_comm : forall {Comm : Commutative Aadd Aeq} (dl1 dl2 : dlist A),
        (dmap2 Aadd dl1 dl2 == dmap2 Aadd dl2 dl1)%dlist.
    Proof. induction dl1,dl2; simpl; auto. f_equiv; auto. apply map2_comm; auto. Qed.

    (** (dl1 . dl2) . dl3 = dl1 . (dl2 . dl3) *)
    Lemma dmap2_assoc : forall {Assoc : Associative Aadd Aeq} (dl1 dl2 dl3 : dlist A),
        (dmap2 Aadd (dmap2 Aadd dl1 dl2) dl3 ==
          dmap2 Aadd dl1 (dmap2 Aadd dl2 dl3))%dlist.
    Proof. induction dl1,dl2,dl3; simpl; auto. f_equiv; auto. apply map2_assoc; auto.
    Qed.
    
  End props_AAA.
  
End dmap2.


(* ======================================================================= *)
(** ** Square Zero dlist *)
Section sdlzero.
  Context `{Equiv_Aeq:Equivalence A Aeq} (A0:A).
  Infix "==" := (eqlistA (eqlistA Aeq)).

  (** Square dlist with element zero *)
  Definition sdlzero n := repeat (repeat A0 n) n.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_r : forall r c, r = c -> sdlzero r == dlzero A0 r c.
  Proof. intros. subst. unfold sdlzero, dlzero. easy. Qed.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_c : forall r c, r = c -> sdlzero c == dlzero A0 r c.
  Proof. intros. subst. unfold sdlzero, dlzero. easy. Qed.
  
  (** length(sdl0) = dim(sdl0) *)
  Lemma sdlzero_length : forall n, length (sdlzero n) = n.
  Proof. intros. apply repeat_length. Qed.
  
  (** width(sdl0) = dim(sdl0) *)
  Lemma sdlzero_width : forall n, width (sdlzero n) n.
  Proof.
    intros. unfold sdlzero. induction n. simpl. constructor.
    apply repeat_width. apply repeat_length.
  Qed.
  
End sdlzero.


(* ======================================================================= *)
(** ** addition, opposition, subtraction of two dlist *)
Section dladd_opp_sub.
  Context `{G:Group}.
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (-b)). 
  Infix "-" := Asub : A_scope.

  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  (* dladd,dlopp,dlsub are notations *)
  Notation dladd dl1 dl2 := (dmap2 Aadd dl1 dl2).
  Notation dlopp dl := (dmap Aopp dl).
  Notation dlsub dl1 dl2 := (dmap2 Asub dl1 dl2).

  Infix "+" := dladd : dlist_scope.
  Notation "- a" := (dlopp a) : dlist_scope.
  Infix "-" := dlsub : dlist_scope.

  Open Scope dlist_scope.
  
  (** dl + 0 = dl *)
  Lemma dladd_0_l : forall dl r c, 
      length dl = r -> width dl c -> (dlzero A0 r c) + dl == dl.
  Proof.
    unfold width, dlzero in *. induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - destruct r. easy. inv H. inv H0.
      simpl. f_equiv; auto. rewrite map2_zero_l; auto. easy.
  Qed.
  
  (** 0 + dl = dl *)
  Lemma dladd_0_r : forall dl r c, 
      length dl = r -> width dl c -> dl + (dlzero A0 r c) == dl.
  Proof.
    unfold width, dlzero in *. induction dl; simpl; intros; auto.
    destruct r. easy. simpl. inv H. inv H0. f_equiv; auto.
    rewrite map2_zero_r; auto. easy.
  Qed.
  
  (** 0 - dl = - dl *)
  Lemma dlsub_0_l : forall dl r c, 
      length dl = r -> width dl c -> (dlzero A0 r c) - dl == - dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - induction r. easy. inv H. inv H0. simpl.
      unfold dlzero in *. f_equiv; auto. apply lsub_0_l; auto.
  Qed.
  
  (** dl - 0 = dl *)
  Lemma dlsub_zero_r : forall dl r c, 
      length dl = r -> width dl c -> dl - (dlzero A0 r c) == dl.
  Proof.
    induction dl; simpl; intros; auto. destruct r; simpl. easy.
    inv H. inv H0. f_equiv; auto.
    - apply lsub_0_r; auto.
    - apply IHdl; auto. 
  Qed.
  
  (** dl - dl = 0 *)
  Lemma dlsub_self : forall dl r c,
      length dl = r -> width dl c -> dl - dl == (dlzero A0 r c).
  Proof.
    induction dl; simpl; intros; subst; try easy. inv H0.
    rewrite (IHdl (length dl) (length a)); auto.
    unfold dlzero in *. simpl. f_equiv; auto. apply map2_sub_self; auto.
  Qed.

  (** dl1 - dl2 = - (dl2 - dl1) *)
  Lemma dlsub_comm : forall dl1 dl2 c,
      length dl1 = length dl2 -> width dl1 c -> width dl2 c ->
      dl1 - dl2 == - (dl2 - dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equiv.
    - rewrite map2_sub_comm; auto. easy.
    - inv H. inv H0. inv H1. apply IHdl1 with (c:=length a); auto.
  Qed.

  (* Let's Aadd is commutative *)
  Context {Comm : Commutative Aadd Aeq}.
  
  (** (dl1 - dl2) - dl3 = dl1 - (dl2 + dl3) *)
  Lemma dlsub_assoc : forall dl1 dl2 dl3 c, 
      length dl1 = length dl2 -> length dl2 = length dl3 ->
      width dl1 c -> width dl2 c ->
      (dl1 - dl2) - dl3 == dl1 - (dl2 + dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; intros; auto. f_equiv; auto.
    - apply map2_sub_assoc.
    - inv H. inv H0. unfold width in *. inv H1. inv H2.
      apply IHdl1 with (c:=length a); auto.
  Qed.
  
End dladd_opp_sub.


(* ======================================================================= *)
(** ** list dot dlist, and dlist dot dlist *)
Section ldotdl_dldotdl.
  Context `{R:Ring}.
  Add Ring ring_inst : (make_ring_theory R).
  
  Infix "==" := (Aeq) : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- b" := (Aopp b) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  Infix "-" := Asub : A_scope.

  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).

  Notation ldot := (ldot (Aadd:=Aadd) (A0:=A0) (Amul:=Amul)).
  Notation ladd := (ladd (Aadd:=Aadd)).
  Notation lcmul := (lcmul (Amul:=Amul)).
  Notation dlunit := (dlunit (A0:=A0) (A1:=A1)).
  
  (** list dot product to dlist *)
  Fixpoint ldotdl (l : list A) (dl : dlist A) : list A :=
    match dl with
    | h :: t => (ldot l h) :: (ldotdl l t)
    | [] => []
    end.

  Lemma ldotdl_aeq_mor :
    Proper (eqlistA Aeq ==> eqlistA (eqlistA Aeq) ==> eqlistA Aeq) ldotdl.
  Proof.
    unfold Proper, respectful.
    intros l1 l2 H dl1. revert l1 l2 H. induction dl1; simpl; intros.
    - destruct y; try easy.
    - destruct y; try easy. simpl. inv H0. apply cons_eq_iff; split; auto.
      rewrite H,H4. easy.
  Qed.

  Global Existing Instance ldotdl_aeq_mor.
  
  (** ldotdl left with nil *)
  Lemma ldotdl_nil_l : forall dl r,
      length dl = r -> (ldotdl [] dl == lzero A0 r)%list.
  Proof.
    induction dl; simpl; intros; subst; try easy.
    rewrite ldot_nil_l. rewrite IHdl with (r:=length dl); simpl; easy.
  Qed.
  
  (** ldotdl right with nil *)
  Lemma ldotdl_nil_r : forall r l, (ldotdl l (dnil r) == lzero A0 r)%list.
  Proof. induction r; simpl; intros; auto. rewrite IHr. rewrite ldot_nil_r. easy. Qed.

  (** ldotdl length law *)
  Lemma ldotdl_length : forall dl l r,
      length dl = r -> length (ldotdl l dl) = r.
  Proof.
    induction dl; intros; simpl in *; auto.
    destruct r. easy. rewrite IHdl with (r:=r); auto.
  Qed.
  
  (** ldotdl left distributve over map2 *)
  Lemma ldotdl_map2_distr_l : forall dl l1 l2 {c},
      length l1 = length l2 ->
      length dl = c -> width dl (length l1) ->
      (ldotdl (map2 Aadd l1 l2) dl == map2 Aadd (ldotdl l1 dl) (ldotdl l2 dl))%list.
  Proof.
    induction dl; intros; simpl; auto. inv H1. f_equiv.
    - apply ldot_map2_distr_r with (r:=length l1); auto.
    - apply IHdl with (c:=length dl); auto.
  Qed.

  (** ldotdl right distributve over dmap2 *)
  Lemma ldotdl_dmap2_distr_r : forall l dl1 dl2 {c},
      length l = c ->
      width dl1 c -> width dl2 c ->
      (ldotdl l (dmap2 Aadd dl1 dl2) == map2 Aadd (ldotdl l dl1) (ldotdl l dl2))%list.
  Proof.
    induction dl1,dl2; simpl; intros; auto. inv H0. inv H1. f_equiv.
    - apply ldot_map2_distr_l with (r:=length a); auto. lia.
    - apply IHdl1 with (c:=length l); auto.
  Qed.
  
  (** ldotdl left with zero *)
  Lemma ldotdl_0_l : forall dl r c,
      length dl = r -> width dl c ->
      (ldotdl (lzero A0 c) dl == lzero A0 r)%list.
  Proof.
    induction dl; simpl; intros; auto.
    - subst. easy.
    - inv H0. rewrite IHdl with (r:=length dl); auto. rewrite ldot_0_l. easy.
  Qed.
  
  (** ldotdl right with zero *)
  Lemma ldotdl_0_r : forall l r c,
      length l = c ->
      (ldotdl l (dlzero A0 r c) == lzero A0 r)%list.
  Proof.
    induction r; simpl; intros; auto. unfold dlzero in *. rewrite IHr; auto.
    rewrite ldot_0_r. easy.
  Qed.
  
  (** ldotdl of consr and consc *)
  Lemma ldotdl_consr_consc : forall l2 dl2 l1 x1 r c,
      length l2 = c -> length dl2 = c -> width dl2 r ->
      (ldotdl (x1 :: l1) (consc l2 dl2) == ladd (lcmul x1 l2) (ldotdl l1 dl2))%list.
  Proof.
    induction l2, dl2; simpl; intros; auto. inv H1. f_equiv; auto.
    apply IHl2 with (r:=length l) (c:=length l2); auto.
  Qed.

  (** ldot and ldotdl could swap first two operands.
      l1 . (l2 . dl) = l2 . (l1 . dl^T) *)
  Lemma ldot_ldotdl_swap12 : forall dl l1 l2 r c,
      length l1 = r -> length l2 = c -> length dl = r -> width dl c ->
      (ldot l1 (ldotdl l2 dl) == ldot l2 (ldotdl l1 (dltrans dl c)))%A.
  Proof.
    induction dl,l1; simpl; intros; auto.
    - rewrite ldotdl_nil_l with (r:=c); try apply dnil_length.
      rewrite ldot_0_r; cbv. easy.
    - subst. easy.
    - subst. easy.
    - inv H2. rewrite ldot_cons.
      rewrite ldotdl_consr_consc with (r:=length l1) (c:=length a); auto.
      + rewrite ldot_ladd_distr_l with (r:=length l2);
          auto using lcmul_length, ldotdl_length, dltrans_length.
        rewrite <- IHdl with (r:=length l1); auto.
        rewrite ldot_lcmul_distr_r. easy.
      + rewrite dltrans_length; auto.
      + apply dltrans_width; auto.
  Qed.

  (** ldotdl with consr at right operend *)
  Lemma ldotdl_consr_r : forall l1 l2 dl2 r c,
      length l1 = r -> length l2 = r -> length dl2 = c -> width dl2 r ->
      (ldotdl l1 (l2 :: dl2) == (ldot l1 l2) :: (ldotdl l1 dl2))%list.
  Proof. induction l1,l2,dl2; simpl; intros; try easy. Qed.
  
  (** ldotdl right distributive over ladd.
    (l1 + l2) . dl = l1 . dl + l2.dl *)
  Lemma ldotdl_ladd_distr_r : forall l1 l2 dl r c,
      length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
      (ldotdl (ladd l1 l2) dl == ladd (ldotdl l1 dl) (ldotdl l2 dl))%list.
  Proof.
    induction dl; simpl; intros; auto. inv H2.
    rewrite <- IHdl with (r:=length l1) (c:=length dl); auto.
    rewrite ldot_ladd_distr_r with (r:=length l1); auto. easy.
  Qed.
  
  (** ldotdl with lcmul is assocociative.
      cmul a (dot l dl) = dot (cmul a l) dl *)
  Lemma ldotdl_lcmul_assoc : forall dl a l r c,
      length l = r -> length dl = c -> width dl r ->
      (lcmul a (ldotdl l dl) == ldotdl (lcmul a l) dl)%list.
  Proof.
    induction dl; simpl; intros; auto. inv H1.
    rewrite IHdl with (r:=length l) (c:=length dl); auto.
    rewrite ldot_lcmul_distr_l. easy.
  Qed.

  (** l dotdl E = l *)
  Lemma ldotdl_dlunit : forall l {n},
      length l = n -> (ldotdl l (dlunit n) == l)%list.
  Proof.
    induction l; intros; simpl in *; auto.
    - subst. simpl. auto.
    - destruct n. easy. inv H. simpl. f_equiv.
      + rewrite ldot_cons. rewrite ldot_0_r. ring.
      + rewrite ldotdl_consr_consc with (r:=length l) (c:=length l).
        rewrite IHl; auto. rewrite lcmul_0_r. rewrite ladd_0_l; try easy.
        apply repeat_length. apply dlunit_length. apply dlunit_width.
  Qed.
  
  (** dlist dot product *)
  Fixpoint dldotdl (dl1 dl2 : dlist A) : dlist A :=
    match dl1 with
    | h1 :: t1 => (ldotdl h1 dl2) :: (dldotdl t1 dl2)
    | [] => []
    end.

  Lemma dldotdl_aeq_mor :
    let deq := eqlistA (eqlistA Aeq) in
    Proper (deq ==> deq ==> deq) dldotdl.
  Proof.
    unfold Proper, respectful.
    induction x; intros.
    - destruct y; easy.
    - destruct y; try easy. simpl. inv H. apply cons_eq_iff; split; auto.
      rewrite H4,H0. easy.
  Qed.

  Global Existing Instance dldotdl_aeq_mor.
  
  (** dldotdl length law *)
  Lemma dldotdl_length : forall dl1 dl2 r1,
      length dl1 = r1 -> length (dldotdl dl1 dl2) = r1.
  Proof.
    induction dl1; intros; auto. simpl in *. destruct r1. easy.
    rewrite IHdl1 with (r1:=r1); auto.
  Qed.

  (** dldotdl width law *)
  Lemma dldotdl_width : forall dl1 dl2 r2 c,
      length dl2 = r2 -> width dl1 c -> width dl2 c ->
      width (dldotdl dl1 dl2) r2.
  Proof.
    unfold width; induction dl1; intros; simpl in *; auto. inv H0. constructor.
    - apply ldotdl_length; auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dldotdl consr left *)
  Lemma dldotdl_consr_l : forall l1 dl1 dl2,
      dldotdl (l1 :: dl1) dl2 == (ldotdl l1 dl2) :: (dldotdl dl1 dl2). 
  Proof. simpl. easy. Qed.
  
  (** dldotdl consr right *)
  Lemma dldotdl_consr_r : forall dl1 l2 dl2 c,
      length l2 = c -> width dl1 c -> width dl2 c ->
      dldotdl dl1 (l2 :: dl2) == consc (ldotdl l2 dl1) (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H0. f_equiv.
    rewrite ldot_comm; easy. rewrite IHdl1 with (c:=length l2); auto. easy.
  Qed.
  
  (** dldotdl left distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_l : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl (dmap2 Aadd dl1 dl2) dl3 == 
        dmap2 Aadd (dldotdl dl1 dl3) (dldotdl dl2 dl3).
  Proof.
    induction dl1; destruct dl2; intros; simpl in *; auto.
    inv H. inv H0. f_equiv.
    - apply ldotdl_map2_distr_l with (c:=length dl3); auto.
    - apply IHdl1 with (c:=length a); auto. 
  Qed.
  
  (** dldotdl right distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_r : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl dl1 (dmap2 Aadd dl2 dl3) ==
        dmap2 Aadd (dldotdl dl1 dl2) (dldotdl dl1 dl3).
  Proof.
    induction dl1; simpl; intros; auto. inv H. f_equiv.
    - apply ldotdl_dmap2_distr_r with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dldotdl [] dl = dnil *)
  Lemma dldotdl_nil_l : forall dl, dldotdl dl [] == dnil (length dl).
  Proof. induction dl; simpl; intros; subst; simpl; subst; auto. Qed.
  
  (** dldotdl dl [] = dnil *)
  Lemma dldotdl_nil_r : forall dl, dldotdl dl [] == dnil (length dl).
  Proof. induction dl; simpl; intros; subst; simpl; subst; auto. Qed.

  (** dldotdl zero dl = zero *)
  Lemma dldotdl_zero_l : forall r dl c,
      width dl c -> dldotdl (dlzero A0 r c) dl == dlzero A0 r (length dl).
  Proof.
    induction r; simpl; intros; simpl; unfold dlzero in *; simpl; auto.
    f_equiv; auto. apply ldotdl_0_l; auto.
  Qed.
  
  (** dldotdl dl zero = zero *)
  Lemma dldotdl_zero_r : forall dl c t,
      width dl c -> dldotdl dl (dlzero A0 t c) == dlzero A0 (length dl) t.
  Proof.
    induction dl; simpl; intros; try easy. inv H.
    unfold dlzero; simpl. f_equiv; auto.
    - rewrite dlzero_rw. rewrite ldotdl_0_r; auto. easy.
    - apply IHdl. auto.
  Qed.
  
  (** dltrans for dldotdl with right decomposition *)
  Lemma dltrans_dldotdl_right : forall d1 d2 l2 r,
      dltrans (dldotdl d1 (l2 :: d2)) (S r) ==
        (ldotdl l2 d1) :: (dltrans (dldotdl d1 d2) r).
  Proof.
    unfold width; induction d1; intros; simpl in *. easy.
    specialize (IHd1 d2 l2 r).
    destruct (dltrans (dldotdl d1 (l2 :: d2)) (S r)). easy. inv IHd1.
    rewrite H2,H4. f_equiv. f_equiv. apply ldot_comm.
  Qed.
  
  (** dldotdl commutation *)
  Lemma dldotdl_comm : forall d1 d2 r c,
      length d1 = r -> width d1 c -> width d2 c ->
      dldotdl d1 d2 == dltrans (dldotdl d2 d1) r.
  Proof.
    induction d1; simpl; intros; subst.
    - rewrite dldotdl_nil_r. rewrite dltrans_nil. easy.
    - inv H0. rewrite dltrans_dldotdl_right.
      f_equiv; auto. apply IHd1 with (c:=length a); auto.
  Qed.

  (** l * (d1 . d2)^T = (l . d1^T) . d2 *)
  Lemma ldotdl_dldotdl_dltrans_assoc : forall d1 d2 l {r c},
      length d2 = r -> width d1 c -> width d2 c ->
      (ldotdl l (dltrans (dldotdl d1 d2) r) ==
         ldotdl (ldotdl l (dltrans d1 c)) d2)%list.
  Proof.
    unfold width. induction d1; intros.
    - subst. simpl. rewrite ?ldotdl_nil_r.
      rewrite ldotdl_0_l with (r:=length d2); auto. easy.
    - inv H0. simpl. destruct l.
      + rewrite ldotdl_nil_l with (r:=length d2).
        rewrite ldotdl_nil_l with (r:=length a).
        rewrite ldotdl_0_l with (r:=length d2); auto.
        all:
          repeat (
              try apply consc_length;
              try apply dltrans_length;
              try apply ldotdl_length; try easy).
        apply dldotdl_width with (c:=length a); auto.
      + rewrite ldotdl_consr_consc with (r:=length d1) (c:=length d2).
        rewrite ldotdl_consr_consc with (r:=length d1) (c:=length a).
        rewrite ldotdl_lcmul_assoc with (r:=length a)(c:=length d2); auto.
        rewrite IHd1 with (c:=length a); auto.
        rewrite ldotdl_ladd_distr_r with (r:=length a) (c:=length d2); auto.
        all:
          repeat (
              try apply consc_length;
              try apply dltrans_length;
              try apply dltrans_width;
              try apply lcmul_length;
              try apply ldotdl_length;
              try apply dldotdl_length;
              try apply dldotdl_width; try easy).
        all: apply dldotdl_width with (c:=length a); auto.
  Qed.

  (** dldotdl association *)
  Lemma dldotdl_assoc : forall d1 d2 d3 r c,
      length d3 = r -> width d2 c -> width d3 c ->
      dldotdl (dldotdl d1 (dltrans d2 c)) d3 ==
        dldotdl d1 (dltrans (dldotdl d2 d3) r).
  Proof.
    induction d1; simpl; intros; auto. f_equiv.
    - rewrite ldotdl_dldotdl_dltrans_assoc with (c:=c); auto. easy.
    - apply IHd1; auto.
  Qed.
  
  (** dldotdl left with dlunit *)
  Lemma dldotdl_dlunit_l : forall (dl : dlist A) {c},
      width dl c -> dldotdl (dlunit c) dl == dltrans dl c.
  Proof.
    induction dl; simpl; intros; auto.
    - rewrite dldotdl_nil_r. rewrite dlunit_length. easy.
    - inversion H.
      rewrite dldotdl_consr_r with (c:=c); auto using dlunit_width.
      rewrite IHdl; auto. rewrite ldotdl_dlunit; auto. easy.
  Qed.
  
  (** dldotdl right with dlunit *)
  Lemma dldotdl_dlunit_r : forall (dl : dlist A) {c},
      width dl c -> dldotdl dl (dlunit c) == dl.
  Proof.
    induction dl; simpl; intros; auto. inversion H.
    rewrite IHdl; auto. rewrite ldotdl_dlunit; auto. easy.
  Qed.
  
End ldotdl_dldotdl.


(* ======================================================================= *)
(** ** Properties of dlcmul *)
Section dlcmul_properties.
  Context `{F:Field}.
  Context {Dec_Aeq : Decidable Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Mapping cmul to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlcmul_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : dlist A) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl == dl ->
      ((k == A1)%A \/ dl == dlzero A0 r c).
  Proof.
    unfold width; induction r; intros.
    - rewrite List.length_zero_iff_nil in H1. subst. right. cbv. easy.
    - destruct dl. easy. simpl in *.
      rewrite dlzero_Sr by apply monoidEquiv.
      inversion H1. apply width_cons in H2; destruct H2.
      apply cons_eq_iff in H; destruct H.
      apply (lcmul_eq_imply_k1_or_l0) with (n:=c) in H; auto.
      apply IHr with (c:=c) in H4; auto.
      destruct H,H4; auto. right. f_equiv; auto. subst. auto.
  Qed.

  (** Mapping cmul to dlist got zero imply k = 0 or dlist is zero *)
  Lemma dlcmul_zero_imply_k0_or_dlzero : 
    forall {r c} k (dl : dlist A) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl == (dlzero A0 r c) ->
      ((k == A0)%A \/ dl == dlzero A0 r c).
  Proof.
    unfold dlzero. induction r; intros.
    - rewrite List.length_zero_iff_nil in H1. subst. cbv. auto.
    - destruct dl. auto. simpl in *.
      inversion H1. apply width_cons in H2; destruct H2.
      apply cons_eq_iff in H; destruct H.
      apply IHr in H4; auto.
      apply lcmul_eq0_imply_k0_or_lzero in H; auto.
      destruct H, H4; auto. right. f_equiv; auto. subst; auto.
  Qed.
  
End dlcmul_properties.
