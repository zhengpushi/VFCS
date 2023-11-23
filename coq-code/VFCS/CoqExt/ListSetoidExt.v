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

Require Export Hierarchy.
Require Export NatExt.
Require Export List SetoidList. Export ListNotations.

Open Scope nat_scope.
Open Scope T_scope.
Open Scope list_scope.

Generalizable Variables T U V Teq Ueq Veq.
Generalizable Variables Tadd Topp Tmul Tinv.


(** A dlist is a list of list T. ("d" means double) *)
Notation dlist T := (list (list T)).


(* ======================================================================= *)
(** ** Properties of cons *)

Section cons.
  Context `{Teq : relation T}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq).

  (** cons is a proper morphism *)
  Lemma cons_aeq_mor : Proper (Teq ==> eqlistA Teq ==> eqlistA Teq) (@cons T).
  Proof.
    simp_proper.
    intros x y H1 l1 l2 H2. destruct l1,l2; auto.
  Qed.

  Global Existing Instance cons_aeq_mor.

  (** Equality of cons, iff both parts are equal *)
  Lemma cons_eq_iff : forall (t1 t2 : T) (l1 l2 : list T),
      t1 :: l1 == t2 :: l2 <-> (t1 == t2)%T /\ l1 == l2.
  Proof.
    intros. split; intros H; inversion H; subst; auto.
  Qed.

  (** Inequality of cons, iff at least one parts are not equal *)
  Lemma cons_neq_iff : forall (t1 t2 : T) (l1 l2 : list T),
      ~(t1 :: l1 == t2 :: l2) <-> (~(t1 == t2)%T \/ ~(l1 == l2)).
  Proof.
    intros. split; intro H.
    - rewrite cons_eq_iff in H.
      apply not_and_or in H; auto.
    - intro. inversion H0. subst. destruct H; auto.
  Qed.

End cons.


(* ======================================================================= *)
(** ** General properties on list T *)

Section Props_listA.

  (** eqlistA eq and eq are same relation *)
  Lemma eqlistA_eq_same_relation : forall {T} (l1 l2 : list T),
      eqlistA eq l1 l2 <-> l1 = l2.
  Proof.
    intros T l1. induction l1; destruct l2; simpl; split; intros; auto; try easy.
    - inv H. f_equal. apply IHl1. auto.
    - inv H. easy.
  Qed.

  (** eqlistA eqlistA eq and eq are same relation *)
  Lemma eqlistA_eq_same_relation2 : forall {T} (l1 l2 : list (list T)),
      eqlistA (eqlistA eq) l1 l2 <-> l1 = l2.
  Proof.
    intros T l1. induction l1; destruct l2; simpl; split; intros; auto; try easy.
    - inv H. f_equal.
      + apply eqlistA_eq_same_relation; auto.
      + apply IHl1. auto.
    - inv H. easy.
  Qed.

  Context `{Teq : relation T}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq) : list_scope.
  
  (** Redefine 'length_zero_iff_nil', original is opaque, make it transparent t *)
  Lemma length_zero_iff_nil : forall (l : list T), length l = 0 <-> l == [].
  Proof.
    intros. destruct l; intros; split; intros; auto; try easy.
  Defined.

  (** list equality is decidable on setoid *)
  Context `{Equiv_Teq : Equivalence T Teq}.
  Lemma list_eq_dec : (forall x y : T, {(x == y)%T} + {~(x == y)%T}) ->
                      forall l1 l2 : list T, {l1 == l2} + {~(l1 == l2)}.
  Proof.
    intros H l1. induction l1; destruct l2; intros;
      try (left; easy); try (right; easy).
    destruct (H a t),(IHl1 l2); auto.
    - right. intro. inv H0. easy.
    - right. intro. inv H0. easy.
    - right. intro. inv H0. easy.
  Qed.

  (** cons is a proper morphism *)
  Global Instance length_aeq_mor : Proper (eqlistA Teq ==> eq) (@length T).
  Proof.
    simp_proper.
    intros l1; induction l1; intros l2 H; try easy. inv H; auto.
    destruct l2; try easy. inv H. simpl. f_equal. auto.
  Qed.
  
End Props_listA.


(* ======================================================================= *)
(** ** Properties of hd and tl *)
Section hd_tl.
  Context {A : Type}.

  Context `{Equiv_Teq : Equivalence T Teq}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq).

  (** hd is a proper morphism *)
  Lemma hd_aeq_mor : Proper (Teq ==> eqlistA Teq ==> Teq) (@hd T).
  Proof.
    simp_proper.
    intros. destruct x0, y0; simpl; try easy. inv H0. auto.
  Qed.
  Global Existing Instance hd_aeq_mor.
  
  (** tl is a proper morphism *)
  Lemma tl_aeq_mor : Proper (eqlistA Teq ==> eqlistA Teq) (@tl T).
  Proof.
    simp_proper.
    intros. destruct x, y; simpl; try easy. inv H. auto.
  Qed.
  Global Existing Instance tl_aeq_mor.
  
  (** length of tl. (pred version) *)
  Lemma tl_length : forall (l : list T), length (tl l) = pred (length l).
  Proof.
    induction l; auto.
  Qed.

End hd_tl.


(* ======================================================================= *)
(** ** Properties of nth *)

Section nth.
  Context `{Equiv_Teq : Equivalence T Teq}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq).

    (** nth is a proper morphism *)
  Lemma nth_aeq_mor : Proper (eq ==> eqlistA Teq ==> Teq ==> Teq) (@nth T).
  Proof.
    simp_proper.
    intros i j H; inv H. rename j into i.
    intros l1 l2. revert l2 i.
    induction l1; destruct l2,i; intros; simpl in *; try easy.
    - inv H. easy.
    - inv H. auto.
  Qed.

  Global Existing Instance nth_aeq_mor.
    
  (** nth [] a = a *)
  Lemma nth_nil : forall (t : T) (i : nat), (nth i [] t == t)%T.
  Proof.
    intros. destruct i; simpl; easy.
  Qed.

  (** Two list equal iff all nth visit equal *)
  Lemma list_eq_iff_nth (t1 t2 : T) : forall n (l1 l2 : list T)
                                     (H1 : length l1 = n) (H2 : length l2 = n),
      l1 == l2 <-> (forall (i : nat), i < n -> (nth i l1 t1 == nth i l2 t2)%T).
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
        assert (a == t)%T.
        { specialize (H 0).
          assert (0 < S (length l1)) by lia.
          apply H in H0; auto. }
        assert (l1 == l2).
        { rewrite (IHl1 (length l1)); auto. intros.
          specialize (H (S i)); simpl in H. apply H. lia. }
        rewrite H0,H1. easy.
  Qed.

  (** nth_ext (setoid version) *)
  Lemma nth_ext : forall (l1 l2 : list T) (d1 d2 : T),
      length l1 = length l2 ->
      (forall i, i < length l1 -> (nth i l1 d1 == nth i l2 d2)%T) -> l1 == l2.
  Proof.
    intros. rewrite list_eq_iff_nth with (t1:=d1)(t2:=d2)(n:=length l1); auto.
  Qed.

  (** Get from repeat x and default value x always return x *)
  Lemma nth_repeat_same : forall (t : T) (n i : nat),
      (nth i (repeat t n) t == t)%T.
  Proof.
    intros t n. induction n; destruct i; simpl; easy.
  Qed.

End nth.


(* ======================================================================= *)
(** ** Properties of length *)
Section length.
  Context `{Equiv_Teq : Equivalence T Teq}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq).

  (** decompose a list which length is 1 *)

  (** Note that, we need this lemma to split a list with only one element,
      although the definition end with "Defined", we cannot got a explicit 
      result by Compute. In practice, won't use this lemma if you needn't *)
  Lemma list_length_1 : forall (l : list T),
      length l = 1 -> {x | l == [x]}.
  Proof. 
    destruct l; intros. inversion H. inversion H.
    apply List.length_zero_iff_nil in H1. subst. exists t. easy.
  Defined.

  Section Test.
    Let l := [1].
    Definition h : length l = 1. auto. Defined.
    (*   Compute proj2_sig (list_length_1 l h). *)
  End Test.

  (** a list has only one element equal to [hd _ l] *)
  Lemma list_length1_eq_hd : forall (x : T) (l:list T), 
      length l = 1 -> [hd x l] == l.
  Proof.
    intros x l. destruct l.
    - intros. simpl in *. lia.
    - intros. simpl in *. f_equal.
      apply eq_add_S in H. apply List.length_zero_iff_nil in H. subst. easy.
  Qed.

  (** decompose a list which length is S n *)
  Lemma list_length_Sn : forall (l : list T) n,
      length l = S n -> {x & { t | l == x :: t}}.
  Proof.
    destruct l; intros. inversion H. exists t. exists l. easy.
  Qed.

  (** decompose a list which length is S (S n) *)
  Lemma list_length_SSn : forall (l : list T) n,
      length l = S (S n) -> {x & { y & { t | l = x :: y :: t}}}.
  Proof.
    destruct l; intros. inversion H.
    exists t. destruct l. inversion H.
    exists t0. exists l. auto.
  Qed.

  (** Split list which length is 1 *)
  Lemma list_length1_neq : forall (l : list T) (a b : T), 
      (length (a :: l) = 1 /\ ~((a :: l) == [b])) -> (~(a == b)%T /\ l == []).
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
  Context `{Equiv_Teq : Equivalence T Teq}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq).

  (** *** Set element with a constant value *)
  Fixpoint lst_chg (l : list T) (i : nat) (x : T) : list T :=
    match l, i with
    | [], _ => []
    | a :: l, 0 => x :: l
    | a :: l, S i => a :: (lst_chg l i x)
    end.

  (** Length property *)
  Lemma lst_chg_length : forall (l : list T) ni n x, 
      length l = n ->
      length (lst_chg l ni x) = n.
  Proof.
    intros l; induction l; auto. induction ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  (** *** Set element with a generation function *)

  (** auxiliary function, i0 is given position, i is changing every loop *)
  Fixpoint lst_chgf_aux (l : list T) (i0 i : nat) (f : nat -> T) : list T :=
    match l with
    | [] => []
    | a :: l' =>
        match i with
        | 0 => f i0 :: l'
        | S i' => a :: (lst_chgf_aux l' i0 i' f)
        end
    end.

  Definition lst_chgf (l : list T) (i : nat) (f : nat -> T) : list T :=
    lst_chgf_aux l i i f.
  
  (** Length property *)
  Lemma lst_chgf_aux_length : forall (l : list T) ni n ni0 f, 
      length l = n -> length (lst_chgf_aux l ni0 ni f) = n.
  Proof.
    intros l; induction l; auto. destruct ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  Lemma lst_chgf_length : forall (l : list T) n ni f, 
      length l = n -> length (lst_chgf l ni f) = n.
  Proof. intros. apply lst_chgf_aux_length; auto. Qed.

End chg.

(* Let f_gen := fun (i : nat) => (i + 5). *)
(* Compute lst_chgf [1;2;3] 0 f_gen. *)
(* Compute lst_chgf [1;2;3] 1 f_gen. *)


(* ======================================================================= *)
(** ** Other induction principle of list *)

Section ind.
  Context `{Equiv_Teq : Equivalence T Teq}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq).

  (* (** Induction principle by length of a list *) *)
  (* Lemma list_ind_length : forall (P : list T -> Prop), *)
  (*     (forall n l, length l = n -> P l) -> (forall l, P l). *)
  (* Proof. *)
  (*   intros. apply (H (length l)). auto. *)
  (* Qed. *)

  (** Two step induction principle for list *)
  Theorem list_ind2 : forall (P : list T -> Prop),
      (* 新增的前提，表示 P 与 Teq 是相容的 *)
      (forall l1 l2 : list T, l1 == l2 -> P l1 -> P l2) ->
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
  Context `{Equiv_Teq : Equivalence T Teq}.
  Infix "==" := (eqlistA Teq).

  Lemma repeat_aeq_mor : Proper (Teq ==> eq ==> (eqlistA Teq)) (@repeat T).
  Proof.
    simp_proper.
    intros a b Hab i j. revert j.
    induction i; intros.
    - subst; simpl. easy.
    - destruct j. easy. simpl. apply cons_aeq_mor; auto.
  Qed.
  
  Global Existing Instance repeat_aeq_mor.

  (** repeat S n times equal to another form *)
  Lemma list_repeat_Sn (T0 : T) : forall n, repeat T0 (S n) == T0 :: repeat T0 n.
  Proof.
    intros. simpl. easy.
  Qed.

End repeat.


(* ======================================================================= *)
(** ** List with constant value 0 *)
Section lzero.

  Context `{Equiv_Teq : Equivalence T Teq}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq).
  
  (** A friendly name for zero list *)
  Definition lzero (T0 : T) n := repeat T0 n.

  (** lzero's length law *)
  Lemma lzero_length (T0 : T) : forall n, length (lzero T0 n) = n.
  Proof.
    intros. apply repeat_length.
  Qed.

  (** append two zero list to a zero list satisfy length relation *)
  Lemma lzero_app (T0 : T) : forall n1 n2,
      lzero T0 n1 ++ lzero T0 n2 == lzero T0 (n1 + n2).
  Proof.
    unfold lzero. intros. rewrite repeat_app. easy.
  Qed.

End lzero.


(* ======================================================================= *)
(** ** Properties of mapping a list *)

Section map_T_U_V.
  Context `{Teq : relation T} `{Ueq : relation U} `{Equiv_Veq : Equivalence V Veq}.
  Infix "==" := (eqlistA Veq).

  (** map_map setoid version *)
  Lemma map_map : forall (f : T -> U) (g : U -> V) (l : list T),
      map g (map f l) == map (fun x : T => g (f x)) l.
  Proof.
    intros f g l. induction l; simpl; try easy.
    apply cons_aeq_mor; auto.
    easy.
  Qed.

End map_T_U_V.


(** map for two types *)
Section map_T_U.

  Context `{Equiv_Teq : Equivalence T Teq}.
  Context `{Equiv_Ueq : Equivalence U Ueq}.
  Infix "==" := (Ueq) : T_scope.
  Infix "==" := (eqlistA Ueq).

  (** map is a proper morphism *)
  Lemma map_aeq_mor : Proper ((Teq ==> Ueq) ==> eqlistA Teq ==> eqlistA Ueq) (@map T U).
  Proof.
    simp_proper.
    intros f1 f2 Hf l1.
    induction l1.
    - intros [|l2]; intros; simpl in *; auto. inv H.
    - intros [|l2]; intros; simpl in *. inv H. inv H.
      constructor; auto.
  Qed.

  Global Existing Instance map_aeq_mor.

  (** map_ext setoid version *)
  Lemma map_ext : forall (f g : T -> U),
      (forall t : T, (f t == g t)%T) -> forall l : list T, map f l == map g l.
  Proof.
    intros f g H l. induction l; intros; try easy.
    simpl. rewrite H,IHl. easy.
  Qed.

  (** map is equal, imply the list is equal *)
  Lemma map_eq_imply_eq : forall (f : T -> U) (l1 l2 : list T),
      map f l1 == map f l2 ->
      Bijective f (Teq:=Teq) (Ueq:=Ueq) ->
      eqlistA Teq l1 l2.
  Proof.
    intros f l1. induction l1; intros; destruct l2; simpl in *; try easy.
    apply cons_eq_iff in H. destruct H.
    constructor; auto.
    destruct H0 as [Hinj Hbij].
    apply inj_pres_eq with (a1:=a)(a2:=t) in Hinj; auto.
  Qed.

  (** map_ext_in_iff setoid version *)
  Lemma map_ext_in_iff : forall (f g : T -> U) (l : list T),
      map f l == map g l <-> (forall t : T, In t l -> (f t == g t)%T).
  Proof.
    intros f g l. induction l; intros; simpl; split; intros; try easy.
    - inversion H; subst. rewrite IHl in H6. destruct H0.
      + subst. easy.
      + apply H6. auto.
    - apply cons_aeq_mor; auto.
      apply IHl. auto.
  Qed.

  (** map and repeat is communtative *)
  Lemma map_repeat (f : T -> U) : forall (t : T) n, 
      (map f (repeat t n)) == (repeat (f t) n).
  Proof. 
    induction n; simpl; auto. constructor; auto. easy.
  Qed.
  
End map_T_U.


(** map for one type *)
Section map_A.

  Context `{Equiv_Teq : Equivalence T Teq}.
  Infix "==" := (Teq) : T_scope.
  Infix "==" := (eqlistA Teq).

  (** Extented map_id lemma, which needn't the function is a exactly format of
     "forall x, x" *)
  Lemma map_id : forall (l : list T) (f : T -> T) (H: forall t, (f t == t)%T),
      (map f l == l)%list.
  Proof.
    induction l; intros; simpl. easy. apply cons_eq_iff; split; auto.
  Qed.

  (** reverse of map_id *)
  Lemma map_id_rev : forall (l : list T) (f : T -> T),
      map f l == l -> (forall x, In x l -> (f x == x)%T).
  Proof. induction l; intros; simpl in *. easy. inv H. destruct H0; subst; auto. Qed.

  (** lzero equal to map to_zero *)
  Lemma map_eq_zero : forall l (T0 : T) (f : T -> T) n,
      (forall x : T, (f x == T0)%T) -> length l = n -> map f l == lzero T0 n.
  Proof.
    induction l; intros; simpl in *. subst. simpl. easy.
    destruct n. easy. inv H0. simpl.
    apply cons_aeq_mor; auto.
  Qed.
    
  (** Mapping is fixpoint, iff f is id *)
  Lemma map_fixpoint_imply_id (f : T -> T) : forall (l : list T), 
      map f l == l -> (forall x, In x l -> (f x == x)%T).
  Proof.
    induction l; intros; simpl in *. easy. inversion H.
    destruct H0. subst; auto. apply IHl; auto.
  Qed.

  (** Simplify of nth+map+seq *)
  Lemma nth_map_seq : forall i f n m (a0 : T),
      i < m -> (nth i (map f (seq n m)) a0 == f (i + n))%T.
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
  Lemma map_nth_seq  : forall n (l : list T) T0,
      length l = n -> map (fun i => nth i l T0) (seq 0 n) == l.
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
  (* Lemma map_seq_eq : forall n (f g : nat -> T), *)
  (*     map f (seq 0 n) == map g (seq 0 n) <-> (forall i, i < n -> (f i == g i)%T). *)
  (* Proof. *)
  (*   intros; split; intros. *)
  (*   - rewrite map_ext_in_iff in H. apply H. apply in_seq. lia. *)
  (*   - apply map_ext_in_iff. intros. apply H. apply in_seq in H0. lia. *)
  (* Qed. *)

  Lemma map_seq_eq : forall a n (f g : nat -> T),
      map f (seq a n) == map g (seq a n) <->
        (forall i, a <= i < (a + n) -> (f i == g i)%T).
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
    Context {T U V : Type}.
    Variable f : T -> U -> V.
    
    (** map operation to two list *)
    Fixpoint map2 (l1 : list T) (l2 : list U) : list V :=
      match l1, l2 with
      | x1 :: t1, x2 :: t2 => (f x1 x2) :: (map2 t1 t2)
      | _, _ => []
      end.
  End defs.

  (** Properties of map2 with three different types *)
  Section props_T_U_V.
    Context {T U V :Type} {Teq : relation T} {Ueq : relation U} {Veq : relation V}.
    Context `{Equiv_Veq : Equivalence V Veq}.
    Context {f : T -> U -> V}.
    Context (fProper : Proper (Teq ==> Ueq ==> Veq) f).
    Infix "==" := (eqlistA Veq).

    Lemma map2_aeq_mor :
      Proper (eqlistA Teq ==> eqlistA Ueq ==> eqlistA Veq) (map2 f).
    Proof.
      simp_proper.
      intros t1. induction t1.
      - intros t2 Ha b1 b2 Hb. destruct b1,t2,b2; try easy.
      - intros t2 Ha b1 b2 Hb. destruct b1,t2,b2; try easy.
        simpl. inversion Ha. inversion Hb. subst.
        apply cons_eq_iff. split.
        + apply fProper; auto.
        + apply IHt1; auto.
    Qed.
    Global Existing Instance map2_aeq_mor.
  
    (** length of map2 *)
    Lemma map2_length : forall (l1 : list T) (l2 : list U) n,
        length l1 = n -> length l2 = n -> length (map2 f l1 l2) = n.
    Proof. 
      induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy.
    Qed.
    
    (** map2 to two lists could be separated by two segments with same length *)
    Lemma map2_app : forall (lt1 lt2 : list T) (lb1 lb2 : list U),
        length lt1 = length lb1 -> length lt2 = length lb2 ->
        map2 f (lt1 ++ lt2) (lb1 ++ lb2) == (map2 f lt1 lb1) ++ (map2 f lt2 lb2).
    Proof.
      induction lt1, lb1; intros; simpl; auto; simpl in H; try easy.
      apply cons_aeq_mor; try easy.
      apply IHlt1; auto.
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
        i < length l1 -> i < length l2 -> Veq (f a b) c ->
        Veq (nth i (map2 f l1 l2) c) (f (nth i l1 a) (nth i l2 b)).
    Proof.
      induction l1; intros; simpl in *; try lia.
      destruct l2; simpl in *; try lia.
      destruct i; try easy.
      apply IHl1; try lia. auto.
    Qed.
    
  End props_T_U_V.

  (**  Properties of map2 with one type *)
  Section props_A.
    Context `{Equiv_Teq : Equivalence T Teq}.
    Context `{Tadd : T -> T -> T} `{Topp : T -> T}.
    Infix "+" := Tadd : T_scope.
    Notation "- a" := (Topp a) : T_scope.
    Notation Tsub := (fun a b => a + (-b)).
    Infix "==" := (Teq) : T_scope.
    Infix "==" := (eqlistA Teq).

    (** l1 . l2 = l2 . l1 *)
    Context {Comm : Commutative Tadd Teq}.
    Lemma map2_comm : forall l1 l2, map2 Tadd l1 l2 == map2 Tadd l2 l1.
    Proof.
      induction l1; destruct l2; simpl; auto.
      f_equiv; auto. apply commutative.
    Qed.
    
    (** (l1 . l2) . l3 = l1 . (l2 . l3) *)
    Context {Assoc:Associative Tadd Teq}.
    Lemma map2_assoc : forall l1 l2 l3,
        map2 Tadd (map2 Tadd l1 l2) l3 == map2 Tadd l1 (map2 Tadd l2 l3).
    Proof.
      induction l1; destruct l2,l3; simpl; auto.
      f_equiv; auto. apply associative.
    Qed.

    (** map2 over map is homorphism *)
    (* In fact, I don't know how to naming this property yet. *)
    Lemma map2_map_hom :
      forall l1 l2 (H : forall a b : T, (Topp (Tadd a b) == Tadd (Topp a) (Topp b))%T),
        map2 Tadd (map Topp l1) (map Topp l2) == map Topp (map2 Tadd l1 l2).
    Proof.
      intros. revert l2.
      induction l1; destruct l2; simpl; try easy.
      apply cons_aeq_mor; auto. easy.
    Qed.

    
    (** *** The properties below, need a monoid structure *)
    Context `{M : Monoid _ Tadd T0 Teq}.

    (** map2 lzero l = l *)
    Lemma map2_zero_l : forall l n, length l = n -> map2 Tadd (lzero T0 n) l == l.
    Proof.
      induction l; intros; subst; simpl in *. easy. rewrite IHl; auto. monoid_simp.
    Qed.

    (** map2 l lzero = l *)
    Lemma map2_zero_r : forall l n, length l = n -> map2 Tadd l (lzero T0 n) == l.
    Proof.
      induction l; intros; subst; simpl in *. easy. rewrite IHl; auto. monoid_simp.
    Qed.

    
    (** *** The properties below, need a group structure *)
    Context `{G : Group T Tadd T0 Topp Teq}.

    (* l1 - l2 = - (l2 - l1) *)
    Lemma map2_sub_comm : forall (l1 l2 : list T),
        map2 Tsub l1 l2 == map Topp (map2 Tsub l2 l1).
    Proof.
      induction l1; destruct l2; intros; simpl in *; auto.
      apply cons_aeq_mor; auto.
      rewrite group_inv_distr. rewrite group_inv_inv. easy.
    Qed.

    (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
    Lemma map2_sub_perm : forall (l1 l2 l3 : list T),
        map2 Tsub (map2 Tsub l1 l2) l3 == map2 Tsub (map2 Tsub l1 l3) l2.
    Proof.
      induction l1,l2,l3; simpl; auto. apply cons_aeq_mor; auto.
      rewrite ?associative.
      apply monoidTaddProper; try easy. apply commutative.
    Qed.
    
    (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
    Lemma map2_sub_assoc : forall (l1 l2 l3 : list T),
        map2 Tsub (map2 Tsub l1 l2) l3 == map2 Tsub l1 (map2 Tadd l2 l3).
    Proof.
      induction l1,l2,l3; simpl; auto. apply cons_aeq_mor; auto.
      rewrite associative. apply monoidTaddProper; try easy.
      rewrite group_inv_distr. apply commutative.
    Qed.

    (** 0 - l = - l *)
    Lemma map2_sub_zero_l : forall l n, 
        length l = n -> map2 Tsub (lzero T0 n) l == map Topp l.
    Proof.
      induction l; simpl; intros. apply map2_nil_r.
      induction n ; simpl. inversion H. apply cons_aeq_mor; auto.
      group_simp.
    Qed.
    
    (** l - 0 = l *)
    Lemma map2_sub_zero_r : forall l n, 
        length l = n -> map2 Tsub l (lzero T0 n) == l.
    Proof.
      induction l; simpl; intros; auto. destruct n; simpl. inversion H.
      apply cons_aeq_mor; auto.
      rewrite group_inv_id. group_simp.
    Qed.
    
    (** l - l = 0 *)
    Lemma map2_sub_self : forall l n, 
        length l = n -> map2 Tsub l l == (lzero T0 n).
    Proof.
      induction l; simpl; intros; subst; try easy.
      apply cons_aeq_mor; auto. group_simp.
    Qed.

  End props_A.

  (** Properties of map2 (other forms) *)
  Section props_others.
    
    Context {T U : Type}.
    Context {Ueq : relation U}.
    Infix "==" := (Ueq) : T_scope.
    Infix "==" := (eqlistA Ueq) : list_scope.

    Lemma map2_map_map : forall (f1 f2 g : T -> U) (h : U -> U -> U)
                           (H : forall x, (h (f1 x) (f2 x) == g x)%T)
                           (l : list T),
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
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq).

  (** fold_right is a Proper morphism *)
  Lemma fold_right_aeq_mor : Proper (Teq ==> eqlistA Teq ==> Teq) (fold_right Tadd).
  Proof.
    simp_proper.
    intros x y H l1. induction l1; intros l2 H2; destruct l2; try easy.
    inv H2. simpl. apply monoidTaddProper; try easy.
    apply IHl1. easy.
  Qed.
  Global Existing Instance fold_right_aeq_mor.

  (** fold_left is a proper relation *)
  Lemma fold_left_aeq_mor :
    Proper (eqlistA Teq ==> Teq ==> Teq) (fold_left Tadd).
  Proof.
    simp_proper.
    intros l1. induction l1; intros l2 Hl t1 t2 Ha.
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
  Lemma concat_length : forall T (l : dlist T),
      length (concat l) = fold_left Nat.add (map (@length T) l) 0.
  Proof.
    intros T l.
    induction l; simpl; auto.
    rewrite app_length. rewrite IHl. rewrite (fold_left_nat_initial _ (length a)).
    lia.
  Qed.

End concat.


(* ======================================================================= *)
(** ** Convert between list and function *)
Section f2l_l2f.
  Context `{Equiv_Teq : Equivalence T Teq} {T0 : T}.
  Infix "==" := (Teq) : T_scope.
  Infix "==" := (eqlistA Teq).

  Definition f2l {n : nat} (f : nat -> T) : list T := map f (seq 0 n).

  Definition l2f {n : nat} (l : list T) : nat -> T := fun i => nth i l T0.

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
  Notation Tsub := (fun a b => Tadd a (Topp b)).
  Infix "==" := (Teq) : T_scope.
  Infix "==" := (eqlistA Teq).

  (** l1 + l2 *)
  Definition ladd (l1 l2 : list T) : list T := map2 Tadd l1 l2.
  Infix "+" := ladd : list_scope.

  Lemma ladd_aeq_mor : Proper (eqlistA Teq ==> eqlistA Teq ==> eqlistA Teq) ladd.
  Proof.
    apply map2_aeq_mor. apply groupTaddProper.
  Qed.
  
  Global Existing Instance ladd_aeq_mor.

  (** - l *)
  Definition lopp (l : list T) : list T := map Topp l.
  Notation "- l" := (lopp l) : list_scope.
  
  Lemma lopp_aeq_mor : Proper (eqlistA Teq ==> eqlistA Teq) lopp.
  Proof.
    apply map_aeq_mor. apply groupToppProper.
  Qed.

  Global Existing Instance lopp_aeq_mor.
  
  (** l1 - l2 *)
  Definition lsub (l1 l2 : list T) : list T := map2 Tsub l1 l2.
  Infix "-" := lsub : list_scope.

  Lemma lsub_aeq_mor : Proper (eqlistA Teq ==> eqlistA Teq ==> eqlistA Teq) lsub.
  Proof.
    apply map2_aeq_mor.
    simp_proper.
    intros. apply monoidTaddProper; try easy. apply groupToppProper. auto.
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
  Lemma ladd_0_l : forall l n, length l = n -> ladd (lzero T0 n) l == l.
  Proof. intros. unfold ladd. apply map2_zero_l; auto. Qed.

  (** l + 0 = l *)
  Lemma ladd_0_r : forall l n, length l = n -> ladd l (lzero T0 n) == l.
  Proof. intros. apply map2_zero_r; auto. Qed.

  (** 0 - l = - l *)
  Lemma lsub_0_l : forall l n, length l = n -> (lzero T0 n) - l == - l.
  Proof. apply map2_sub_zero_l. Qed.
  
  (** l - 0 = l *)
  Lemma lsub_0_r : forall l n, length l = n -> l - (lzero T0 n) == l.
  Proof. apply map2_sub_zero_r. Qed.
  
  (** l - l = 0 *)
  Lemma lsub_self : forall l n, length l = n -> l - l == lzero T0 n.
  Proof. apply map2_sub_self. Qed.


  (** Let's have an abelian group AG *)
  Context `{AG : AGroup T Tadd T0 Topp Teq}.

  (** l1 + l2 = l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, l1 + l2 == l2 + l1.
  Proof. apply map2_comm; auto. Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma lsub_assoc : forall (l1 l2 l3 : list T), (l1 - l2) - l3 == l1 - (l2 + l3).
  Proof. intros. apply map2_sub_assoc. Qed.

  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma lsub_perm : forall (l1 l2 l3 : list T), (l1 - l2) - l3 == (l1 - l3) - l2.
  Proof. apply map2_sub_perm. Qed.

  (** l1 - l2 = - (l2 - l1) *)
  Lemma lsub_comm : forall (l1 l2 : list T), l1 - l2 == - (l2 - l1).
  Proof. intros. apply map2_sub_comm. Qed.
  
End ladd_opp_sub.


(* ======================================================================= *)
(** ** constant multiplication of list *)
Section lcmul_lmulc.
  (** Let's have a ring R *)
  Context `{R:Ring}.
  Add Ring ring_inst : (make_ring_theory R).
  
  Infix "*" := Tmul : T_scope.
  Infix "==" := (Teq) : T_scope.
  Infix "==" := (eqlistA Teq).

  Context `{HDec : Dec T Teq}.
  
  (** t * l *)
  Definition lcmul (t : T) (l : list T) : list T := map (fun x => t * x) l.
  
  (** l * t *)
  Definition lmulc (l : list T) (t : T) : list T := map (fun x => x * t) l.
  
  (** cmul keep its length *)
  Lemma lcmul_length : forall t l n, length l = n -> length (lcmul t l) = n.
  Proof. intros. unfold lcmul. rewrite map_length; auto. Qed.
  
  (** t * l = l * t *)
  Lemma lmulc_lcmul : forall t l, lmulc l t == lcmul t l.
  Proof. induction l; simpl; auto. f_equiv; auto. ring. Qed.
  
  (** t * (x :: l) = (t * x) :: (t * l) *)
  Lemma lcmul_cons : forall t x l, lcmul t (x :: l) == (t * x) :: (lcmul t l).
  Proof. intros. simpl. easy. Qed.

  (** t * [] = [] *)
  Lemma lcmul_nil : forall t, lcmul t [] == [].
  Proof. intros. simpl. easy. Qed.
  
  (** [] * t = [] *)
  Lemma lmulc_nil : forall t, lmulc [] t == [].
  Proof. intros. simpl. easy. Qed.
  
  (** 0 c* l = 0 *)
  Lemma lcmul_0_l : forall l n, length l = n -> lcmul T0 l == lzero T0 n.
  Proof. induction l; intros; subst; simpl in *; auto. f_equiv; auto. ring. Qed.

  (** t * 0 = 0 *)
  Lemma lcmul_0_r : forall t n, lcmul t (lzero T0 n) == lzero T0 n.
  Proof. intros. unfold lcmul,lzero. rewrite map_repeat. f_equiv. ring. Qed.
  
  (** Let's have t field F *)
  Context `{F : Field T Tadd T0 Topp Tmul T1 Tinv Teq}.
  
  (** k * l = l -> k = 1 \/ l = 0 *)
  Lemma lcmul_eq_imply_k1_or_l0 : forall (l : list T) n (k : T),
      length l = n -> lcmul k l == l -> ((k == T1)%T \/ l == lzero T0 n).
  Proof.
    induction l; intros. subst; auto. destruct n; auto. easy. simpl in *.
    injection H. intros H1. apply cons_eq_iff in H0. destruct H0.
    apply IHl with (k:=k) in H1; auto.
    apply field_mul_eq_imply_a1_or_b0 in H0; auto.
    destruct H0,H1; auto.
  Qed.
  
  (** k * l = 0 -> k = 0 \/ l = 0 *)
  Lemma lcmul_eq0_imply_k0_or_lzero : forall (l : list T) {n} (k : T),
      length l = n -> lcmul k l == lzero T0 n ->
      ((k == T0)%T \/ l == lzero T0 n).
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
  Context `{R : Ring}.
  Add Ring ring_inst : (make_ring_theory R).

  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Infix "+" := (ladd (Tadd:=Tadd)) : list_scope.
  Infix "c*" := (lcmul (Tmul:=Tmul)) : list_scope.
  Infix "==" := (Teq) : T_scope.
  Infix "==" := (eqlistA Teq).

  
  (** dot product, marked as l1 ⋅ l2 *)
  Definition ldot (l1 l2 : list T) : T := fold_right Tadd T0 (map2 Tmul l1 l2).
  Infix "⋅" := ldot : list_scope.

  (** map is respect to aeq *)
  Lemma ldot_aeq_mor : Proper (eqlistA Teq ==> eqlistA Teq ==> Teq) ldot.
  Proof.
    simp_proper.
    intros. unfold ldot. rewrite H,H0. easy.
  Qed.

  Global Existing Instance ldot_aeq_mor.

  (** l1 ⋅ l2 = l2 ⋅ l1 *)
  Lemma ldot_comm : forall (l1 l2 : list T), (l1 ⋅ l2 == l2 ⋅ l1)%T.
  Proof. intros. unfold ldot. rewrite map2_comm; auto. apply R. Qed.
  
  (** [] ⋅ l = 0 *)
  Lemma ldot_nil_l : forall (l : list T), (nil ⋅ l == T0)%T.
  Proof. intros. destruct l; simpl; try easy. Qed.
  
  (** l ⋅ [] = 0 *)
  Lemma ldot_nil_r : forall (l : list T), (l ⋅ nil == T0)%T.
  Proof. intros. destruct l; simpl; try easy. Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2,
      ((x1 :: l1) ⋅ (x2 :: l2) == (x1 * x2) + (l1 ⋅ l2))%T.
  Proof. induction l1,l2; simpl; intros; try easy. Qed.
  
  (** 0 ⋅ l = 0 *)
  Lemma ldot_0_l : forall l n, ((lzero T0 n) ⋅ l == T0)%T.
  Proof. induction l,n; simpl; intros; try easy. rewrite ldot_cons.
         rewrite IHl. ring. Qed.
  
  (** l ⋅ 0 = 0 *)
  Lemma ldot_0_r : forall l n, (l ⋅ (lzero T0 n) == T0)%T.
  Proof. intros. rewrite ldot_comm. apply ldot_0_l. Qed.
  
  (** ldot left distributve over map2: l1 ⋅ (map l2 l3) = l1 ⋅ l2 + l1 ⋅ l3 *)
  Lemma ldot_map2_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (l1 ⋅ (map2 Tadd l2 l3) == (l1 ⋅ l2) + (l1 ⋅ l3))%T.
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite !ldot_cons. rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.

  (** ldot right distributve over map2: (map + l1 l2) ⋅ l3 = l1 ⋅ l3 + l2 ⋅ l3 *)
  Lemma ldot_map2_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      ((map2 Tadd l1 l2) ⋅ l3 == (l1 ⋅ l3) + (l2 ⋅ l3))%T.
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite ?ldot_cons. ring_simplify. rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.

  (** ldot left distributive over ladd: l1 ⋅ (l2 + l3) = l1 ⋅ l2 + l1 ⋅ l3 *)
  Lemma ldot_ladd_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (l1 ⋅ (l2 + l3) == (l1 ⋅ l2) + (l1 ⋅ l3))%T.
  Proof. intros. apply ldot_map2_distr_l with (r:=r); auto. Qed.
  
  (** ldot right distributive over ladd: (l1 + l2) ⋅ l3 = l1 ⋅ l3 + l2 ⋅ l3 *)
  Lemma ldot_ladd_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      ((l1 + l2) ⋅ l3 == (l1 ⋅ l3) + (l2 ⋅ l3))%T.
  Proof. intros. apply ldot_map2_distr_r with (r:=r); auto. Qed.
  
  (** ldot left distributive over lcmul and mul: (x * l1) ⋅ l2 = x * (l1 ⋅ l2) *)
  Lemma ldot_lcmul_distr_l : forall l1 l2 x, ((x c* l1) ⋅ l2 == x * (l1 ⋅ l2))%T.
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite !ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot right distributive over lcmul and mul.
      l1 ⋅ (x * l2) = x * (l1 ⋅ l2) *)
  Lemma ldot_lcmul_distr_r : forall l1 l2 x, (l1 ⋅ (x c* l2) == x * (l1 ⋅ l2))%T.
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
  
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Infix "==" := (Teq) : T_scope.
  Infix "==" := (eqlistA Teq).
  
  (** create a list for unit matrix, which length is n and almost all elements 
    are zero except i-th element is one. *)
  Fixpoint list_unit (n i : nat) : list T :=
    match n, i with
    | 0, _ => []
    | S n, 0 => T1 :: (repeat T0 n)
    | S n, S i => T0 :: (list_unit n i)
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
  
  (** list_unit(n,i) [i] = T1, when i < n *)
  Lemma list_unit_T1 : forall n i, i < n -> (nth i (list_unit n i) T0 == T1)%T.
  Proof.
    induction n; intros; auto. easy.
    destruct i; simpl; try easy. apply IHn. lia.
  Qed.
  
  (** list_unit(n,i) [j] = T0, when i < n /\ j <> i *)
  Fact list_unit_spec1 : forall n i j, i < n -> j <> i ->
                                  (nth j (list_unit n i) T0 == T0)%T.
  Proof.
    induction n; intros; auto. easy. destruct i,j; simpl; try easy.
    apply nth_repeat_same. apply IHn; lia.
  Qed.
  
  (** list_unit(n,i) [j] = T0, j <> i *)
  Lemma list_unit_T0 : forall n i j,
      j <> i -> (nth j (list_unit n i) T0 == T0)%T.
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
  Infix "==" := (Teq) : T_scope.
  Infix "==" := (eqlistA Teq).

  (** Get list from a given list and given length, too many data will be ignored 
      and too less data will be filled with T0 *)
  Fixpoint list_to_listN (l : list T) (n : nat) : list T :=
    match n with
    | 0 => []
    | S n' => (hd T0 l) :: (list_to_listN (tl l) n')
    end.
  
  Lemma list_to_listN_length : forall (n : nat) (l : list T), length (list_to_listN l n) = n.
  Proof. induction n; intros; simpl; auto. Qed.
  
  Lemma list_to_listN_eq : forall (n : nat) (l : list T),
      length l = n -> list_to_listN l n == l.
  Proof.
    induction n; intros; simpl.
    - apply (length_zero_iff_nil (Teq:=Teq)) in H; easy.
    - rewrite IHn; destruct l; simpl in *; try easy. auto.
  Qed.

End list_to_listN.


(* ======================================================================= *)
(** ** width of a dlist *)

Section dlist_width.

  Section defs.

    (** A predicate that every list of a dlist has same length *)
    Definition width {T} (dl : dlist T) (n : nat) : Prop :=
      Forall (fun l => length l = n) dl.
    
  End defs.

  Section props.
    Context {T : Type}.

    (** width property should be kept by its child structure *)
    Lemma width_cons : forall (l : list T) dl n,
        width (l :: dl) n <-> length l = n /\ width dl n.
    Proof. intros. split; intros; inversion H; auto. constructor; auto. Qed.

    (** width property should be kept by every child element *)
    Lemma width_in : forall dl (l : list T) n, width dl n -> In l dl -> length l = n.
    Proof.
      induction dl; intros. inv H0.
      apply in_inv in H0. inv H. destruct H0; auto. subst; auto.
    Qed.

    (** app operation won't change width property *)
    Lemma app_width : forall (dl1 : dlist T) dl2 n, 
        width (dl1 ++ dl2) n <-> width dl1 n /\ width dl2 n.
    Proof.
      unfold width in *.
      induction dl1; intros; split; intros; simpl in *; inv H; auto.
      - apply IHdl1 in H3 as []. split; auto.
      - inv H0. constructor; auto. apply IHdl1. auto.
    Qed.

    (** rev operation won't change width property *)
    Lemma rev_width : forall (dl : dlist T) n, width (rev dl) n -> width dl n.
    Proof.
      unfold width in *.
      induction dl; simpl; intros; auto.
      apply app_width in H. destruct H. inv H0. constructor; auto.
    Qed.

    (** dlist generated by repeat will keep width property same as seed element *)
    Lemma repeat_width : forall (l : list T) n k, length l = k -> width (repeat l n) k.
    Proof. unfold width. induction n; intros; simpl; auto. Qed.

    (** width promise i-th row has same length *)
    Lemma width_imply_nth_length : forall i c (dl : dlist T), 
        i < length dl -> width dl c -> length (nth i dl []) = c.
    Proof.
      unfold width. intros i c dl. revert i c.
      induction dl; intros; simpl in *. lia.
      inv H0. destruct i; auto. apply IHdl; auto. lia.
    Qed.

    (** map width law *)
    Lemma width_map : forall (f: nat -> list T) (rowIdxs : list nat) c,
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
      Context {T : Type}.
      
      (** Set element of a dlist with a constant value *)
      Fixpoint dlst_chg (dl : dlist T) (i j : nat) (x : T) : dlist T :=
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
      Context {T : Type}.
      
      (** Length property *)
      Lemma dlst_chg_length : forall dl i r j (x : T),
          length dl = r -> length (dlst_chg dl i j x) = r.
      Proof. induction dl; destruct i; intros; simpl; auto. destruct r; auto. easy.
      Qed.
      
      (** Width property *)
      Lemma dlst_chg_width : forall dl i c j (x : T), 
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
      Context {T : Type}.

      (** Inner version, i0 is given position, i is changed in every loop *)
      Fixpoint dlst_chgf_aux (dl : dlist T) (i0 i j : nat) (f : nat -> nat -> T)
        : dlist T :=
        match dl, i with
        | [], _ => []
        | l :: dl, 0 => (lst_chgf l j (f i0)) :: dl
        | l :: dl, S i' => l :: (dlst_chgf_aux dl i0 i' j f)
        end. 
      
      (** User version that hide i0 parameter *)
      Definition dlst_chgf (dl : dlist T) (i j : nat) (f : nat -> nat -> T) : dlist T :=
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
      Context {T : Type}.
      
      (** Length property *)
      Lemma dlst_chgf_aux_length : forall dl i r i0 j f, 
          length dl = r -> length (@dlst_chgf_aux T dl i0 i j f) = r.
      Proof. induction dl; destruct i; auto; simpl; intros. destruct r; auto. easy.
      Qed.
      
      Lemma dlst_chgf_length : forall dl r i j f, 
          length dl = r -> length (@dlst_chgf T dl i j f) = r.
      Proof. intros. apply dlst_chgf_aux_length. auto. Qed.
      
      (** Width property *)
      Lemma dlst_chgf_aux_width : forall dl i c i0 j f, 
          width dl c -> width (@dlst_chgf_aux T dl i0 i j f) c.
      Proof.
        unfold width. induction dl; auto. 
        induction i; intros; simpl in *; auto; inv H; constructor; auto.
        apply lst_chgf_length; auto.
      Qed.
      
      Lemma dlst_chgf_width : forall dl i c j f, 
          width dl c -> width (@dlst_chgf T dl i j f) c.
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
      Context {T : Type}.
      
      Fixpoint dlst_chgrow (dl : dlist T) (i : nat) (l : list T) : dlist T :=
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
      Context {T : Type}.

      (** Length property *)
      Lemma dlst_chgrow_length : forall dl i r l, 
          length dl = r -> length (@dlst_chgrow T dl i l) = r.
      Proof.
        induction dl; auto. destruct i; auto; intros; simpl in *.
        destruct r; auto. easy.
      Qed.
      
      (** Width property *)
      Lemma dlst_chgrow_width : forall {T} dl i c l,
          length l = c -> width dl c -> width (@dlst_chgrow T dl i l) c.
      Proof.
        unfold width; induction dl; auto. 
        induction i; intros; simpl in *; inv H0; constructor; auto.
      Qed.
    End props.

  End by_constant.

  
  (** *** with a generation function *)
  Section by_function.

    Section defs.
      Context {T : Type}.
      
      (** Inner version, i0 is given position, i is changed in every loop *)
      Fixpoint dlst_chgrowf_aux (dl : dlist T) (i0 i : nat) (f : nat -> list T)
        : dlist T :=
        match dl, i with
        | [], _ => []
        | l :: dl, 0 => (f i0) :: dl
        | l :: dl, S i' => l :: (dlst_chgrowf_aux dl i0 i' f)
        end. 
      
      (** User version that hide i0 parameter *)
      Definition dlst_chgrowf (dl : dlist T) (i : nat) (f : nat -> list T) : dlist T :=
        dlst_chgrowf_aux dl i i f.
      
    End defs.
    
    (* Let f_gen := fun (i : nat) => [i+10;i+11;i+12]. *)
    (* Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 f_gen. *)
    (* Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 f_gen. *)
    (* Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 2 f_gen. *)
    (* Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 3 f_gen.  *)

    Section props.
      Context {T : Type}.
      
      (** Length property *)
      Lemma dlst_chgrowf_aux_length : forall dl i r i0 f, 
          length dl = r -> length (@dlst_chgrowf_aux T dl i0 i f) = r.
      Proof. induction dl; intros; auto. destruct i; auto. simpl. destruct r; auto.
             easy.
      Qed.
      
      Lemma dlst_chgrowf_length : forall dl r i f, 
          length dl = r -> length (@dlst_chgrowf T dl i f) = r.
      Proof. intros. apply dlst_chgrowf_aux_length. auto. Qed.
      
      (** Width property *)
      Lemma dlst_chgrowf_aux_width : forall dl i c i0 f, 
          length (f i0) = c -> width dl c -> width (@dlst_chgrowf_aux T dl i0 i f) c.
      Proof.
        unfold width; induction dl; auto. 
        induction i; intros; simpl in *; auto; inv H0; constructor; auto.
      Qed.
      
      Lemma dlst_chgrowf_width : forall dl i c f, 
          length (f i) = c -> width dl c ->  width (@dlst_chgrowf T dl i f) c.
      Proof. intros. apply dlst_chgrowf_aux_width; auto. Qed.
    End props.
    
  End by_function.
  
End dlst_chgrow.


(* ======================================================================= *)
(** ** Properties of dlist equal *)
Section dlst_eq.

  Context `{Equiv_Teq : Equivalence T Teq}.
  Context `{T0 : T}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).
  Open Scope nat.

  (** Two dlists are equal, iff all corresponded (i,j) elements is equal *)
  Lemma dlist_eq_iff_nth :
    forall r c (dl1 dl2 : dlist T)
           (H1 : length dl1 = r) (H2 : length dl2 = r)
           (H3 : width dl1 c) (H4 : width dl2 c),
      dl1 == dl2 <->
        (forall i j, i < r -> j < c ->
                (nth j (nth i dl1 []) T0 == nth j (nth i dl2 []) T0)%T).
  Proof.
    intros; split; intros.
    - rewrite H. easy.
    - apply (list_eq_iff_nth [] [] _ dl1 dl2 H1 H2). intros. subst.
      rewrite (list_eq_iff_nth) with (n:=c); auto;
        apply width_imply_nth_length; auto. lia.
  Qed.

  (* (** dlist_eq is decidable *) *)
  (* Lemma dlist_eq_dec : forall (dl1 dl2 : dlist T) (HDec:Decidable Teq), *)
  (*     {dl1 == dl2} + {~(dl1 == dl2)}. *)
  (* Proof. intros. apply decidable. Qed. *)

End dlst_eq.


(* ======================================================================= *)
(** ** a dlist with all nil elements *)
Section dnil.
  
  Context `{M:Monoid}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).
  Open Scope nat.
  
  (** a dlist that every list is nil, named as dnil *)
  Fixpoint dnil n : dlist T :=
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
  Lemma dlist_w0_eq_dnil : forall (dl : list (list T)), 
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

  Context {T U C : Type} {Teq : relation T} {Ueq : relation U} {Ceq : relation C}.
  Context {EqEquivA:Equivalence Teq}.
  Context {EqEquivU:Equivalence Ueq}.
  Context {EqEquivC:Equivalence Ceq}.
  Variable f : T -> U -> C.
  
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
  Context `{Equiv_Teq : Equivalence T Teq} {T0 : T}.
  (* Infix "==" := (Teq) : T_scope. *)
  (* Infix "==" := (eqlistA Teq). *)
  (* Infix "==" := (eqlistA (eqlistA Teq)). *)

  Definition f2dl {r c : nat} (f : nat -> nat -> T) : dlist T :=
    map (fun i => f2l (n:=c) (f i)) (seq 0 r).

  Definition dl2f {r c : nat} (dl : dlist T) : nat -> nat -> T :=
    fun i j => nth j (nth i dl []) T0.

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
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).
  
  (** Convert a list to a dlist, it looks like converting a row to a column. *)
  Fixpoint row2col (l : list T) : dlist T :=
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
      i < length l -> (nth i (row2col l) [] == [nth i l T0])%list.
  Proof.
    induction l; intros; simpl in *. lia. destruct i; try easy. apply IHl. lia.
  Qed.
  
  (** Convert a dlist to a list which contain head element, it looks like 
      converting a column to a row. *)
  Fixpoint col2row (dl : dlist T) : list T :=
    match dl with
    | [] => []
    | l :: tl => (hd T0 l) :: (col2row tl)
    end.
  
  (** Convert a dlist to list then convert it to a dlist, equal to original dlist. *)
  Lemma row2col_col2row : forall (dl : list (list T)),
      width dl 1 -> row2col (col2row dl) == dl.
  Proof.
    unfold width; induction dl; simpl; auto; intros. inv H.
    apply cons_aeq_mor; auto.
    destruct a; simpl in *; try easy. inv H2.
    apply List.length_zero_iff_nil in H0. subst. easy.
  Qed.
  
  (** Convert a list to dlist then convert it to a list, equal to original 
      list. *)
  Lemma col2row_row2col : forall (l : list T), 
      (col2row (row2col l) == l)%list.
  Proof. induction l; simpl; auto; intros. rewrite IHl. easy. Qed.

End convert_row_and_col.


(* ======================================================================= *)
(** ** head column of a dlist *)
Section hdc.
  Context {T : Type} (T0 : T).
  
  (** Get head column of a dlist *)
  Fixpoint hdc (dl : dlist T) : list T :=
    match dl with
    | [] => []
    | l :: tl => (hd T0 l) :: (hdc tl)
    end.
  
  (** hdc length law *)
  Lemma hdc_length : forall dl, length (hdc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
End hdc.


(* ======================================================================= *)
(** ** tail columns of a dlist *)
Section tlc.
  Context {T : Type}.
  
  (** Get tail columns of a dlist *)
  Fixpoint tlc (dl : dlist T) : dlist T :=
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

  Context `{Equiv_Teq : Equivalence T Teq} {T0 : T}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).
  
  (** Construct a dlist by column with a list and a dlist.
      If the list and dlist have different length, then only the
      top elements with minimal length will be kept. *)
  Fixpoint consc (l : list T) (dl : dlist T) : dlist T :=
    match l, dl with
    | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
    | _, _ => []
    end.

  Lemma consc_aeq_mor :
    Proper (eqlistA Teq ==> eqlistA (eqlistA Teq) ==> eqlistA (eqlistA Teq)) consc.
  Proof.
    simp_proper.
    induction x; intros.
    - destruct x,y0,y; simpl; try easy.
    - destruct x0,y0,y; simpl; try easy.
      apply cons_eq_iff in H as [->], H0 as [->].
      apply cons_aeq_mor; auto. easy.
  Qed.
  
  Global Existing Instance consc_aeq_mor.

  (** consc_eq, seems like f_equal *)
  Lemma consc_eq_iff : forall (l1 l2 : list T) (dl1 dl2 : list (list T)) n
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
      consc (hdc T0 dl) (tlc dl) == row2col (repeat T0 r).
  Proof.
    unfold width; induction dl; simpl; intros; subst; try easy.
    inv H0. apply List.length_zero_iff_nil in H2. subst. simpl.
    rewrite IHdl; auto. easy.
  Qed.
  
  (** consc with hdc and tlc of a dlist generate itself *)
  Lemma consc_hdc_tlc_widthS : forall dl c, 
      width dl (S c) ->
      consc (hdc T0 dl) (tlc dl) == dl.
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
  Context {T : Type}.
  
  (** dlist append by row *)
  Definition dlappr := @app (list T).
  
  (** dlist apend by column *)
  Fixpoint dlappc (dl1 dl2 : dlist T) : dlist T :=
    match dl1, dl2 with
    | l1 :: tl1, l2 :: tl2 => (app l1 l2) :: (dlappc tl1 tl2)
    | _, _ => []
    end.

End dlist_app.

Notation "l @@ r" := (dlappc l r) (at level 40) : dlist_scope.


(* ======================================================================= *)
(** ** Zero dlist *)
Section dlzero.

  Context `{Equiv_Teq : Equivalence T Teq} (T0 : T).
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).
  
  (** dlist constructed by repeated lzero, named as dlzero *)
  Definition dlzero r c := repeat (repeat T0 c) r.

  (** dlzero rewrite *)
  Lemma dlzero_rw : forall r c, repeat (lzero T0 c) r = dlzero r c.
  Proof. auto. Qed.
  
  (** dlzero with (S r) rows could be splited to two parts *)
  Lemma dlzero_Sr : forall {r c}, dlzero (S r) c == (lzero T0 c) :: (dlzero r c).
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

  Context `{Equiv_Teq : Equivalence T Teq} {T0 : T}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).
  
  (** Transposition of a dlist *)
  (* Note: fetch every row and cons by column one bye one.
     c is the columnu number of the dlist. *)
  Fixpoint dltrans (dl : dlist T) (c : nat) : dlist T :=
    match dl with
    | [] => @dnil T c
    | l :: tl => consc l (dltrans tl c)
    end.

  Lemma dltrans_aeq_mor :
    Proper (eqlistA (eqlistA Teq) ==> eq ==> eqlistA (eqlistA Teq)) dltrans.
  Proof.
    simp_proper.
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
  Lemma dltrans_zero : forall r c, dltrans (dlzero T0 r c ) c == dlzero T0 c r.
  Proof.
    induction r; intros; simpl; auto. rewrite dlzero_dnil; easy.
    unfold dlzero in *; simpl in *. rewrite IHr.
    rewrite repeat_consr. easy.
  Qed.
  
End dltrans.


(* ======================================================================= *)
(** ** dlist unit, like a identity matrix *)
Section dlunit.

  Context `{Equiv_Teq : Equivalence T Teq} {T0 T1 : T}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).
  
  (** Build a identity matrix with dlist. *)
  (* there are 4 parts of a dlunit [n x n]: 
      left top element [1 x 1], 
      right top list [1 x (n-1)], 
      left bottom list [(n-1) x 1],
      right bottom square is another small dlunit [(n-1) x (n-1)] *)
  Fixpoint dlunit (n : nat) : dlist T :=
    match n with
    | O => []
    | S n0 => (T1 :: (repeat T0 n0)) :: (consc (repeat T0 n0) (dlunit n0))
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
    assert ((dltrans (consc (repeat T0 n) (dlunit n)) (S n)) ==
              (repeat T0 n) :: (dltrans (dlunit n) n)).
    { apply dltrans_consc with (r:=n).
      apply repeat_length. apply dlunit_length. apply dlunit_width. }
    destruct (dltrans (consc (repeat T0 n) (dlunit n)) (S n)). easy.
    inv H. rewrite H3,H5,IHn. easy.
  Qed.

End dlunit.


(* ======================================================================= *)
(** ** map of dlist *)

Section dmap.

  Section defs.
    Context {T U : Type}.
    Variable f : T -> U.
    
    (** map operation to dlist *)
    Definition dmap dl := map (map f) dl.
  End defs.
  
  (** properties for map of dlist with f : T -> U *)
  Section props_T_U.
    Context `{Equiv_Teq : Equivalence T Teq}.
    Context `{Equiv_Ueq : Equivalence U Ueq}.
    Variable f : T -> U.
    Infix "==" := Ueq : T_scope.
    Infix "==" := (eqlistA Ueq) : list_scope.
    Infix "==" := (eqlistA (eqlistA Ueq)).
    
    (** dmap is a proper morphism *)
    Context {fProper : (Proper (Teq ==> Ueq) f)}.
    Lemma dmap_aeq_mor :
      Proper (eqlistA (eqlistA Teq) ==> eqlistA (eqlistA Ueq)) (dmap f).
    Proof.
      simp_proper.
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
    Lemma dmap_ext : forall dl (g : T -> U) (H : forall a, (f a == g a)%T),
        dmap f dl == dmap g dl.
    Proof. intros. unfold dmap. apply map_ext. intros. apply map_ext; auto. Qed.

  End props_T_U.

  (** map of dlist with f : T -> T *)
  Section props_AA.
    Context `{Equiv_Teq : Equivalence T Teq}.
    Infix "==" := Teq : T_scope.
    Infix "==" := (eqlistA Teq) : list_scope.
    Infix "==" := (eqlistA (eqlistA Teq)).

    (** dmap (fun x => T0) dl = dlzero T0 r c *)
    Lemma dmap_f0 : forall {r c} dl (T0 : T),
        length dl = r -> width dl c ->
        dmap (fun (x : T) => T0) dl == dlzero T0 r c.
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
    Definition dmap2 {T U V} (f : T -> U -> V) dl1 dl2 := map2 (map2 f) dl1 dl2.
  End defs.

  Section props_T_U_V.
    
    Context {T U : Type} `{Equiv_Veq : Equivalence V Veq}.
    Variable f : T -> U -> V.
    Infix "==" := (eqlistA (eqlistA Veq)).
    
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
    Lemma dmap2_app : forall dlt1 dlt2 dlb1 dlb2,
        length dlt1 = length dlb1 -> length dlt2 = length dlb2 ->
        dmap2 f (dlt1 ++ dlt2) (dlb1 ++ dlb2) ==
          (dmap2 f dlt1 dlb1) ++ (dmap2 f dlt2 dlb2).
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
    
  End props_T_U_V.

  (** dmap2 with same base type *)
  Section props_AAA.

    Context `{Tadd : T -> T -> T}.
    Context `{Equiv_Teq : Equivalence T Teq}.
    Infix "+" := Tadd : T_scope.
    Infix "==" := Teq : T_scope.
    Infix "==" := (eqlistA Teq) : list_scope.
    Infix "==" := (eqlistA (eqlistA Teq)) : dlist_scope.

    (** dmap2 with dmap of two components *)
    Lemma dmap2_dmap_dmap : forall (f1 f2 g : T -> T) (h : T -> T -> T) 
                              (H : forall x, Teq (g x) (h (f1 x) (f2 x))) dl,
        (dmap2 h (dmap f1 dl) (dmap f2 dl) == dmap g dl)%dlist.
    Proof.
      induction dl; simpl; auto. rewrite IHdl. f_equiv. apply map2_map_map. easy.
    Qed.

    Variable Topp : T -> T.
    Notation "- a" := (Topp a) : T_scope.

    (** dmap2 over dmap is homorphism *)
    Lemma dmap2_dmap_hom : forall (H : forall a b : T, (- (a + b) == (- a) + (- b))%T)
                                  d1 d2,
        (dmap2 Tadd (dmap Topp d1) (dmap Topp d2) ==
           dmap Topp (dmap2 Tadd d1 d2))%dlist.
    Proof.
      intros. revert d2. induction d1,d2; simpl; auto.
      rewrite IHd1. f_equiv. rewrite map2_map_hom; auto. easy.
    Qed.
    
    (** dl1 . dl2 = dl2 . dl1 *)
    Lemma dmap2_comm : forall {Comm : Commutative Tadd Teq} (dl1 dl2 : dlist T),
        (dmap2 Tadd dl1 dl2 == dmap2 Tadd dl2 dl1)%dlist.
    Proof. induction dl1,dl2; simpl; auto. f_equiv; auto. apply map2_comm; auto. Qed.

    (** (dl1 . dl2) . dl3 = dl1 . (dl2 . dl3) *)
    Lemma dmap2_assoc : forall {Assoc : Associative Tadd Teq} (dl1 dl2 dl3 : dlist T),
        (dmap2 Tadd (dmap2 Tadd dl1 dl2) dl3 ==
          dmap2 Tadd dl1 (dmap2 Tadd dl2 dl3))%dlist.
    Proof. induction dl1,dl2,dl3; simpl; auto. f_equiv; auto. apply map2_assoc; auto.
    Qed.
    
  End props_AAA.
  
End dmap2.


(* ======================================================================= *)
(** ** Square Zero dlist *)
Section sdlzero.
  Context `{Equiv_Teq : Equivalence T Teq} (T0 : T).
  Infix "==" := (eqlistA (eqlistA Teq)).

  (** Square dlist with element zero *)
  Definition sdlzero n := repeat (repeat T0 n) n.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_r : forall r c, r = c -> sdlzero r == dlzero T0 r c.
  Proof. intros. subst. unfold sdlzero, dlzero. easy. Qed.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_c : forall r c, r = c -> sdlzero c == dlzero T0 r c.
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
  Infix "==" := Teq : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Tsub := (fun a b => a + (-b)). 
  Infix "-" := Tsub : T_scope.

  Infix "==" := (eqlistA (eqlistA Teq)) : dlist_scope.

  (* dladd,dlopp,dlsub are notations *)
  Notation dladd dl1 dl2 := (dmap2 Tadd dl1 dl2).
  Notation dlopp dl := (dmap Topp dl).
  Notation dlsub dl1 dl2 := (dmap2 Tsub dl1 dl2).

  Infix "+" := dladd : dlist_scope.
  Notation "- a" := (dlopp a) : dlist_scope.
  Infix "-" := dlsub : dlist_scope.

  Open Scope dlist_scope.
  
  (** dl + 0 = dl *)
  Lemma dladd_0_l : forall dl r c, 
      length dl = r -> width dl c -> (dlzero T0 r c) + dl == dl.
  Proof.
    unfold width, dlzero in *. induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - destruct r. easy. inv H. inv H0.
      simpl. f_equiv; auto. rewrite map2_zero_l; auto. easy.
  Qed.
  
  (** 0 + dl = dl *)
  Lemma dladd_0_r : forall dl r c, 
      length dl = r -> width dl c -> dl + (dlzero T0 r c) == dl.
  Proof.
    unfold width, dlzero in *. induction dl; simpl; intros; auto.
    destruct r. easy. simpl. inv H. inv H0. f_equiv; auto.
    rewrite map2_zero_r; auto. easy.
  Qed.
  
  (** 0 - dl = - dl *)
  Lemma dlsub_0_l : forall dl r c, 
      length dl = r -> width dl c -> (dlzero T0 r c) - dl == - dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - induction r. easy. inv H. inv H0. simpl.
      unfold dlzero in *. f_equiv; auto. apply lsub_0_l; auto.
  Qed.
  
  (** dl - 0 = dl *)
  Lemma dlsub_zero_r : forall dl r c, 
      length dl = r -> width dl c -> dl - (dlzero T0 r c) == dl.
  Proof.
    induction dl; simpl; intros; auto. destruct r; simpl. easy.
    inv H. inv H0. f_equiv; auto.
    - apply lsub_0_r; auto.
    - apply IHdl; auto. 
  Qed.
  
  (** dl - dl = 0 *)
  Lemma dlsub_self : forall dl r c,
      length dl = r -> width dl c -> dl - dl == (dlzero T0 r c).
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

  (* Let's Tadd is commutative *)
  Context {Comm : Commutative Tadd Teq}.
  
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
  
  Infix "==" := (Teq) : T_scope.
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- b" := (Topp b) : T_scope.
  Notation Tsub := (fun a b => a + (-b)).
  Infix "-" := Tsub : T_scope.

  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).

  Notation ldot := (@ldot _ Tadd T0 Tmul).
  Notation ladd := (@ladd _ Tadd).
  Notation lcmul := (@lcmul _ Tmul).
  Notation dlunit := (@dlunit _ T0 T1).
  
  (** list dot product to dlist *)
  Fixpoint ldotdl (l : list T) (dl : dlist T) : list T :=
    match dl with
    | h :: t => (ldot l h) :: (ldotdl l t)
    | [] => []
    end.

  Lemma ldotdl_aeq_mor :
    Proper (eqlistA Teq ==> eqlistA (eqlistA Teq) ==> eqlistA Teq) ldotdl.
  Proof.
    simp_proper.
    intros l1 l2 H dl1. revert l1 l2 H. induction dl1; simpl; intros.
    - destruct y; try easy.
    - destruct y; try easy. simpl. inv H0. apply cons_eq_iff; split; auto.
      rewrite H,H4. easy.
  Qed.

  Global Existing Instance ldotdl_aeq_mor.
  
  (** ldotdl left with nil *)
  Lemma ldotdl_nil_l : forall dl r,
      length dl = r -> (ldotdl [] dl == lzero T0 r)%list.
  Proof.
    induction dl; simpl; intros; subst; try easy.
    rewrite ldot_nil_l. rewrite IHdl with (r:=length dl); simpl; easy.
  Qed.
  
  (** ldotdl right with nil *)
  Lemma ldotdl_nil_r : forall r l, (ldotdl l (dnil r) == lzero T0 r)%list.
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
      (ldotdl (map2 Tadd l1 l2) dl == map2 Tadd (ldotdl l1 dl) (ldotdl l2 dl))%list.
  Proof.
    induction dl; intros; simpl; auto. inv H1. f_equiv.
    - apply ldot_map2_distr_r with (r:=length l1); auto.
    - apply IHdl with (c:=length dl); auto.
  Qed.

  (** ldotdl right distributve over dmap2 *)
  Lemma ldotdl_dmap2_distr_r : forall l dl1 dl2 {c},
      length l = c ->
      width dl1 c -> width dl2 c ->
      (ldotdl l (dmap2 Tadd dl1 dl2) == map2 Tadd (ldotdl l dl1) (ldotdl l dl2))%list.
  Proof.
    induction dl1,dl2; simpl; intros; auto. inv H0. inv H1. f_equiv.
    - apply ldot_map2_distr_l with (r:=length a); auto. lia.
    - apply IHdl1 with (c:=length l); auto.
  Qed.
  
  (** ldotdl left with zero *)
  Lemma ldotdl_0_l : forall dl r c,
      length dl = r -> width dl c ->
      (ldotdl (lzero T0 c) dl == lzero T0 r)%list.
  Proof.
    induction dl; simpl; intros; auto.
    - subst. easy.
    - inv H0. rewrite IHdl with (r:=length dl); auto. rewrite ldot_0_l. easy.
  Qed.
  
  (** ldotdl right with zero *)
  Lemma ldotdl_0_r : forall l r c,
      length l = c ->
      (ldotdl l (dlzero T0 r c) == lzero T0 r)%list.
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
      (ldot l1 (ldotdl l2 dl) == ldot l2 (ldotdl l1 (dltrans dl c)))%T.
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
  Fixpoint dldotdl (dl1 dl2 : dlist T) : dlist T :=
    match dl1 with
    | h1 :: t1 => (ldotdl h1 dl2) :: (dldotdl t1 dl2)
    | [] => []
    end.

  Lemma dldotdl_aeq_mor :
    let deq := eqlistA (eqlistA Teq) in
    Proper (deq ==> deq ==> deq) dldotdl.
  Proof.
    simp_proper.
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
      dldotdl (dmap2 Tadd dl1 dl2) dl3 == 
        dmap2 Tadd (dldotdl dl1 dl3) (dldotdl dl2 dl3).
  Proof.
    induction dl1; destruct dl2; intros; simpl in *; auto.
    inv H. inv H0. f_equiv.
    - apply ldotdl_map2_distr_l with (c:=length dl3); auto.
    - apply IHdl1 with (c:=length a); auto. 
  Qed.
  
  (** dldotdl right distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_r : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl dl1 (dmap2 Tadd dl2 dl3) ==
        dmap2 Tadd (dldotdl dl1 dl2) (dldotdl dl1 dl3).
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
      width dl c -> dldotdl (dlzero T0 r c) dl == dlzero T0 r (length dl).
  Proof.
    induction r; simpl; intros; simpl; unfold dlzero in *; simpl; auto.
    f_equiv; auto. apply ldotdl_0_l; auto.
  Qed.
  
  (** dldotdl dl zero = zero *)
  Lemma dldotdl_zero_r : forall dl c t,
      width dl c -> dldotdl dl (dlzero T0 t c) == dlzero T0 (length dl) t.
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
  Lemma dldotdl_dlunit_l : forall (dl : dlist T) {c},
      width dl c -> dldotdl (dlunit c) dl == dltrans dl c.
  Proof.
    induction dl; simpl; intros; auto.
    - rewrite dldotdl_nil_r. rewrite dlunit_length. easy.
    - inversion H.
      rewrite dldotdl_consr_r with (c:=c); auto using dlunit_width.
      rewrite IHdl; auto. rewrite ldotdl_dlunit; auto. easy.
  Qed.
  
  (** dldotdl right with dlunit *)
  Lemma dldotdl_dlunit_r : forall (dl : dlist T) {c},
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
  Context {Dec_Teq : Dec Teq}.
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA (eqlistA Teq)).
  
  (** Mapping cmul to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlcmul_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : dlist T) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Tmul k x)) dl == dl ->
      ((k == T1)%T \/ dl == dlzero T0 r c).
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
    forall {r c} k (dl : dlist T) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Tmul k x)) dl == (dlzero T0 r c) ->
      ((k == T0)%T \/ dl == dlzero T0 r c).
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


(* ======================================================================= *)
(** ** Folding of a bool list *)
Section fold_blist.
  
  (** = true && hd l && hd (tl l) && ... *)
  Definition and_blist (l : list bool) : bool := fold_left andb l true.

  (** = false || hd l || hd (tl l) || ... *)
  Definition or_blist (l : list bool) : bool := fold_left orb l false.

End fold_blist.


(* ======================================================================= *)
(** ** Special search algorithm *)
Section search.

  (** Find the minimum element from a list *)
  Section list_min.
    (** Find the minimum element from a list (Auxiliary function).
      Parameters:
      l         the given list
      cmp       compare function, t1 < t2 is true, otherwise false
      val       minimum value, init is the head of l
         
      Return:
      if the given list is empty, return val
      otherwise, return the value we need.
     *)
    Fixpoint list_min_aux {T} (val : T) (l : list T) (cmp : T -> T -> bool) : T :=
      match l with
      | [] => val
      | a :: tl =>
          if cmp a val
          then list_min_aux a tl cmp
          else list_min_aux val tl cmp
      end.

    (** Find the minimum element from a list.

      Parameters:
      T0    default value of A
      cmp   compare function, t1 < t2 is true, otherwise false
      l     the given list
         
      Return:
      if the given list is empty, return T0
      otherwise, return the value we need.
     *)
    Definition list_min {T} (T0 : T) (cmp : T -> T -> bool) (l : list T) : T :=
      list_min_aux (hd T0 l) l cmp.

    Section test.
      
      Open Scope nat.
      (* Compute list_min 9 Nat.ltb []. *)
      (* Compute list_min 0 Nat.ltb [2;3;4;1;5]. *)
      (* Compute list_min 0 Nat.ltb [2;3;4;1;1;5]. (* find the first minimum *) *)
      (* Compute list_min 0 Nat.ltb [1;2;3;4;5]. *)
      (* Compute list_min 0 Nat.ltb [2;3;4;5;1]. *)
      
    End test.

  End list_min.


  (** Find the index of the minimum element from a list *)
  Section list_min_pos.
    (** Find the index of the minimum element from a list (Auxiliary function).

      Parameters:
      l         the given list
      cmp       compare function, t1 < t2 is true, otherwise false
      min_val   minimum value, init is the head of l
      min_pos   record position where the element is minum, init is 0
      cnt       to count the position, init is 0
         
      Return:
      if the given list is empty, return min_pos
      otherwise, return the value we need.
     *)
    Fixpoint list_min_pos_aux {T} (cmp : T -> T -> bool) (l : list T) 
      (min_val : T) (min_pos : nat) (cnt : nat) : nat :=
      match l with
      | [] => min_pos
      | a :: tl =>
          if cmp a min_val 
          then list_min_pos_aux cmp tl a cnt (S cnt)
          else list_min_pos_aux cmp tl min_val min_pos (S cnt)
      end.

    (** Find the index of the minimum element from a list.

      Parameters:
      T0    default value of A, only be used as the parameter of hd, any value is ok.
      cmp   compare function, t1 < t2 is true, otherwise false
      l     the given list
         
      Return:
      if the given list is empty, return 0
      otherwise, return the value we need.
     *)
    Definition list_min_pos {T} (T0 : T) (cmp : T -> T -> bool) (l : list T) : nat :=
      list_min_pos_aux cmp l (hd T0 l) 0 0.

    (** Spec: no any other elements is smaller than the result. *)
    Lemma list_min_pos_spec : forall {T} (T0 : T) (cmp : T -> T -> bool) (l : list T),
        let min_pos :=  list_min_pos T0 cmp l in
        let min_val := nth min_pos l T0 in
        Forall (fun a => negb (cmp a min_val)) l.
    Proof.
      intros T T0 cmp l. simpl. induction l; constructor.
    Abort.

    Section test.
      
      Open Scope nat.
      (* Compute list_min_pos 9 Nat.ltb []. *)
      (* Compute list_min_pos 0 Nat.ltb [2;3;4;1;5]. *)
      (* Compute list_min_pos 0 Nat.ltb [2;3;4;1;1;5]. (* find the first minimum *) *)
      (* Compute list_min_pos 0 Nat.ltb [1;2;3;4;5]. *)
      (* Compute list_min_pos 0 Nat.ltb [2;3;4;5;1]. *)
      
    End test.
  End list_min_pos.

End search.

