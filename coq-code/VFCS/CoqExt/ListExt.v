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
(* Require Export SetoidList. *)
Require Export List. Export ListNotations.

Open Scope nat_scope.
Open Scope A.
Open Scope list.

Generalizable Variables A B C. (* Aeq Beq Ceq. *)
Generalizable Variables Aadd Aopp Amul Ainv.


(* ======================================================================= *)
(** ** Properties of cons *)

Section cons.
  Context {A : Type}.

  (** Equality of cons, iff both components are equal *)
  Lemma cons_eq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      a1 :: l1 = a2 :: l2 <-> (a1 = a2) /\ l1 = l2.
  Proof. intros. split; intros H; inversion H; subst; auto. Qed.

  (** Inequality of cons, iff at least one parts are not equal *)
  Lemma cons_neq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      (a1 :: l1 <> a2 :: l2) <-> (a1 <> a2) \/ (l1 <> l2).
  Proof.
    intros. split; intro H.
    - rewrite cons_eq_iff in H. apply not_and_or in H; auto.
    - intro. inversion H0. subst. destruct H; auto.
  Qed.

End cons.


(* ======================================================================= *)
(** ** Properties of hd and tl *)
Section hd_tl.
  Context {A : Type}.

  (** length of tl. (pred version) *)
  Lemma tl_length : forall (l : list A), length (tl l) = pred (length l).
  Proof. induction l; auto. Qed.

End hd_tl.


(* ======================================================================= *)
(** ** Properties of nth *)

Section nth.
  Context {A : Type}.  

  (** nth [] a = a *)
  Lemma nth_nil : forall (a : A) (i : nat), (nth i [] a = a).
  Proof. intros. destruct i; simpl; auto. Qed.
  
  (** Get from repeat x and default value x always return x *)
  Lemma nth_repeat_same : forall (a : A) (n i : nat), nth i (repeat a n) a = a.
  Proof. intros a n. induction n; destruct i; simpl; auto. Qed.

End nth.


(* ======================================================================= *)
(** ** Properties of length *)
Section length.
  Context {A : Type}.

  (** Re-proof it, end with Defined instead of Qed *)
  Lemma length_zero_iff_nil : forall (l : list A), length l = 0 <-> l = [].
  Proof. induction l; simpl; try easy. Defined.

  (** decompose a list which length is 1 *)
  Lemma list_length_1 : forall (l : list A), length l = 1 -> {x | l = [x]}.
  Proof. 
    destruct l; intros. inversion H. inversion H.
    apply length_zero_iff_nil in H1. subst. exists a. easy.
  Defined.

  (** a list has only one element equal to [hd _ l] *)
  Lemma list_length1_eq_hd : forall (x : A) (l:list A), length l = 1 -> [hd x l] = l.
  Proof.
    intros x l. destruct l; intros; simpl in *; try easy.
    f_equal. apply eq_sym. apply length_zero_iff_nil. lia.
  Qed.

  (** decompose a list which length is S n *)
  Lemma list_length_Sn : forall (l : list A) n, length l = S n -> {x & { t | l = x :: t}}.
  Proof.  destruct l; intros. inversion H. exists a. exists l. easy. Qed.

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
      (length (a :: l) = 1 /\ (a :: l <> [b])) -> (a <> b /\ l = []).
  Proof.
    intros l. induction l; intros; destruct H.
    - simpl in *. split; auto. intro H1; subst. easy.
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
  Context {A : Type}.  

  (** *** Set element with a constant value *)
  Fixpoint lst_chg (l : list A) (i : nat) (x : A) : list A :=
    match l with
    | [] => []
    | a :: l' =>
        match i with
        | 0 => x :: l'
        | S i' => a :: (lst_chg l' i x)
        end
    end.

  (** Length property *)
  Lemma lst_chg_length : forall (l : list A) ni n x, 
      length l = n -> length (lst_chg l ni x) = n.
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
  Context {A : Type}.

  (* (** Induction principle by length of a list *) *)
  (* Lemma list_ind_length : forall (P : list A -> Prop), *)
  (*     (forall n l, length l = n -> P l) -> (forall l, P l). *)
  (* Proof. *)
  (*   intros. apply (H (length l)). auto. *)
  (* Qed. *)

  (** Two step induction principle for list *)
  Theorem list_ind2 : forall (P : list A -> Prop),
      (P []) -> 
      (forall a, P [a]) -> 
      (forall l a b, P l -> P (a :: b :: l)) ->
      (forall l, P l).
  Proof.
    intros P Hx H0 H1 H2. apply ind_nat_list. induction n using nat_ind2. 
    - intros. apply length_zero_iff_nil in H; subst; auto.
    - intros. apply list_length_1 in H. destruct H. subst. auto.
    - destruct l; auto. destruct l; auto.
      intros. apply H1. apply IHn. simpl in H. lia.
  Qed.

End ind.


(* ======================================================================= *)
(** ** list repeat properties *)

Section repeat.
  Context {A : Type}.

  (* (** repeat S n times equal to another form *) *)
  (* Lemma list_repeat_Sn (a : A) : forall n, repeat a (S n) = a :: repeat a n. *)
  (* Proof. intros; auto. Qed. *)

End repeat.


(* ======================================================================= *)
(** ** List with constant value 0 *)
Section lzero.

  Context {A : Type}.
  
  (** A zero list is made by a constant value 0 *)
  Definition lzero (A0 : A) n := repeat A0 n.

  (** lzero's length law *)
  Lemma lzero_length (A0 : A) : forall n, length (lzero A0 n) = n.
  Proof. intros. apply repeat_length. Qed.

  (** append two zero list to a zero list satisfy length relation *)
  Lemma lzero_app (A0 : A) : forall n1 n2, lzero A0 n1 ++ lzero A0 n2 = lzero A0 (n1 + n2).
  Proof. intros. unfold lzero. rewrite repeat_app. auto. Qed.

End lzero.


(* ======================================================================= *)
(** ** Properties of mapping a list *)
Section map.

  (** map and repeat is communtative *)
  Lemma map_repeat: forall {A B} (f : A -> B) (a : A) n,
      map f (repeat a n) = repeat (f a) n.
  Proof. induction n; simpl; auto. f_equal; auto. Qed.
  
  (** map with bijective funciton is equal, imply the list is equal *)
  Lemma map_bij_eq_imply_eq : forall {A B} (f : A -> B) (l1 l2 : list A),
      map f l1 = map f l2 -> Bijective f -> l1 = l2.
  Proof.
    induction l1; intros; destruct l2; simpl in *; try easy.
    apply cons_eq_iff in H. destruct H. f_equal.
    - apply inj_pres_eq with f; auto. apply H0.
    - apply IHl1; auto.
  Qed.

  (** Extended map_id lemma, which needn't the function is a exactly format of
     "forall x, x" *)
  Lemma map_id : forall {A} (l : list A) (f : A -> A) (H: forall a, f a = a), map f l = l.
  Proof. induction l; intros; simpl; auto. f_equal; auto. Qed.

  (** lzero is equal to map with to-zero *)
  Lemma map_eq_zero : forall {A} l (A0 : A) (f : A -> A) n,
      (forall x : A, f x = A0) -> length l = n -> lzero A0 n = map f l.
  Proof. induction l; intros; simpl in *; subst; simpl; auto. f_equal; auto. Qed.
    
  (** reverse of map_id *)
  Lemma map_id_rev : forall {A} (l : list A) (f : A -> A),
      map f l = l -> (forall x, In x l -> f x = x).
  Proof. induction l; intros; simpl in *; try easy. inv H. destruct H0; subst; auto.
  Qed.

  (** Rewrite for (nth (map seq)) *)
  Lemma nth_map_seq : forall {A} (n m i : nat) (f : nat -> A) (a0 : A),
      i < m -> nth i (map f (seq n m)) a0 = f (i + n).
  Proof.
    induction n.
    - induction m; intros; try easy.
      simpl. destruct i; auto.
      rewrite <- seq_shift. rewrite map_map. rewrite IHm; try easy. lia.
    - intros.
      rewrite <- seq_shift. rewrite map_map. rewrite IHn; auto.
  Qed.

  (** Rewrite for (map (nth seq)) *)
  Lemma map_nth_seq  : forall {A} n (l : list A) (A0 : A),
      length l = n -> map (fun i => nth i l A0) (seq 0 n) = l.
  Proof.
    induction n; intros; simpl.
    - apply length_zero_iff_nil in H; auto.
    - destruct l; simpl in *; try easy. f_equal.
      rewrite <- seq_shift. rewrite map_map. auto.
  Qed.

  (** Mapping two functions to same seq is equal, iff the functions are extensional
      equal *)
  Lemma map_seq_eq : forall {A} n (f g : nat -> A),
      map f (seq 0 n) = map g (seq 0 n) <-> (forall i, i < n -> f i = g i).
  Proof.
    intros; split; intros.
    - rewrite map_ext_in_iff in H. apply H. apply in_seq. auto with arith.
    - apply map_ext_in_iff. intros. apply H. apply in_seq in H0. lia.
  Qed.

End map.


(* ======================================================================= *)
(** ** Mapping two lists to a list *)

Section map2.

  (** Definitions *)
  Section defs.
    Context {A B C :Type}.
    Variable (f : A -> B -> C).

    (** map operation to two list *)
    Fixpoint map2 (l1 : list A) (l2 : list B) : list C :=
      match l1, l2 with
      | x1 :: t1, x2 :: t2 => (f x1 x2) :: (map2 t1 t2)
      | _, _ => []
      end.
  End defs.

  (** Properties of map2 with three different types *)
  Section props_ABC.
    Context {A B C : Type}.
    Variable f : A -> B -> C.
    
    (** length of map2 *)
    Lemma map2_length : forall (l1 : list A) (l2 : list B) n,
        length l1 = n -> length l2 = n -> length (map2 f l1 l2) = n.
    Proof. induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy. Qed.
    
    (** map2 with append of same length *)
    Lemma map2_app : forall (la1 la2 : list A) (lb1 lb2 : list B),
        length la1 = length lb1 -> length la2 = length lb2 ->
        map2 f (la1 ++ la2) (lb1 ++ lb2) = (map2 f la1 lb1) ++ (map2 f la2 lb2).
    Proof. induction la1, lb1; intros; simpl; auto; simpl in H; try easy. f_equal; auto.
    Qed.

    (** map2 [] l = [] *)
    Lemma map2_nil_l : forall l, map2 f [] l = [].
    Proof. destruct l; easy. Qed.

    (** map2 l [] = [] *)
    Lemma map2_nil_r : forall l, map2 f l [] = [].
    Proof. destruct l; easy. Qed.

    (** tail of map2, equal to map2 to tail *)
    Lemma tail_map2_dlist : forall l1 l2,
        tl (map2 f l1 l2) = map2 f (tl l1) (tl l2).
    Proof. destruct l1, l2; simpl; try easy. rewrite map2_nil_r; auto. Qed.

    (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *)
    Lemma map2_nth : forall l1 l2 i a b c,
        i < length l1 -> i < length l2 -> c = f a b ->
        nth i (map2 f l1 l2) c = f (nth i l1 a) (nth i l2 b).
    Proof.
      induction l1; intros; simpl in *; try lia.
      destruct l2; simpl in *; try lia.
      destruct i; try easy.
      apply IHl1; try lia. auto.
    Qed.

  End props_ABC.

  (**  Properties of map2 with one type *)
  Section props_A.
    Context {A : Type}.
    Variable Aadd : A -> A -> A.
    Variable Aopp : A -> A.
    Infix "+" := Aadd : A_scope.
    Notation "- a" := (Aopp a) : A_scope.
    Notation Asub := (fun a b => a + (-b)).

    (** l1 . l2 = l2 . l1 *)
    Context {Comm : Commutative Aadd}.
    Lemma map2_comm : forall l1 l2, map2 Aadd l1 l2 = map2 Aadd l2 l1.
    Proof. induction l1; destruct l2; simpl; auto. f_equal; auto. apply commutative.
    Qed.
    
    (** (l1 . l2) . l3 = l1 . (l2 . l3) *)
    Context {Assoc:Associative Aadd}.
    Lemma map2_assoc : forall l1 l2 l3,
        map2 Aadd (map2 Aadd l1 l2) l3 = map2 Aadd l1 (map2 Aadd l2 l3).
    Proof. induction l1; destruct l2,l3; simpl; auto. f_equal; auto. apply associative.
    Qed.

    (** map2 over map is homorphism *)
    (* In fact, I don't know how to naming this property yet. *)
    Lemma map2_map_hom : forall l1 l2 (H : forall a b : A, - (a + b) = (-a) + (-b)),
        map2 Aadd (map Aopp l1) (map Aopp l2) = map Aopp (map2 Aadd l1 l2).
    Proof. induction l1; destruct l2; intros; simpl; auto. f_equal; auto. Qed.

    
    (** *** The properties below, need a monoid structure *)
    Context `{M : Monoid A Aadd A0}.

    (** map2 lzero l = l *)
    Lemma map2_zero_l : forall l n, length l = n -> map2 Aadd (lzero A0 n) l = l.
    Proof. induction l; destruct n; intros; simpl; auto; try easy. f_equal; auto.
           monoid_simp. Qed.

    (** map2 l lzero = l *)
    Lemma map2_zero_r : forall l n, length l = n -> map2 Aadd l (lzero A0 n) = l.
    Proof. induction l; destruct n; intros; simpl; auto; try easy. f_equal; auto.
           monoid_simp. Qed.

    
    (** *** The properties below, need a group structure *)
    Context `{G : Group A Aadd A0 Aopp}.

    (* l1 - l2 = - (l2 - l1) *)
    Lemma map2_sub_comm : forall l1 l2, map2 Asub l1 l2 = map Aopp (map2 Asub l2 l1).
    Proof.
      induction l1; destruct l2; intros; simpl in *; auto. f_equal; auto.
      rewrite group_inv_distr. rewrite group_inv_inv. auto.
    Qed.

    (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
    Lemma map2_sub_perm : forall (l1 l2 l3 : list A),
        map2 Asub (map2 Asub l1 l2) l3 = map2 Asub (map2 Asub l1 l3) l2.
    Proof.
      induction l1,l2,l3; simpl; auto. f_equal; auto.
      monoid_simp. f_equal. apply commutative.
    Qed.
    
    (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
    Lemma map2_sub_assoc : forall (l1 l2 l3 : list A),
        map2 Asub (map2 Asub l1 l2) l3 = map2 Asub l1 (map2 Aadd l2 l3).
    Proof.
      induction l1,l2,l3; simpl; auto. f_equal; auto.
      group_simp. f_equal. rewrite group_inv_distr. apply commutative.
    Qed.

    (** 0 - l = - l *)
    Lemma map2_sub_zero_l : forall l n,
        length l = n -> map2 Asub (lzero A0 n) l = map Aopp l.
    Proof.
      induction l; simpl; intros. apply map2_nil_r.
      destruct n; simpl; try easy. f_equal; auto. group_simp.
    Qed.
    
    (** l - 0 = l *)
    Lemma map2_sub_zero_r : forall l n, length l = n -> map2 Asub l (lzero A0 n) = l.
    Proof.
      induction l; intros; simpl; auto. destruct n; simpl; try easy. f_equal; auto.
      rewrite (group_inv_id (G:=G)). group_simp.
    Qed.
    
    (** l - l = 0 *)
    Lemma map2_sub_self : forall l n, length l = n -> map2 Asub l l = (lzero A0 n).
    Proof. induction l; intros; simpl; subst; auto. simpl. f_equal; auto. group_simp.
    Qed.

  End props_A.

  (** Properties of map2 (other forms) *)
  Section props_others.
    
    (** map2 (map) (map) = map *)
    Lemma map2_map_map : forall {A B} (f1 f2 g : A -> B) (h : B -> B -> B)
                           (H : forall x, (h (f1 x) (f2 x) = g x))
                           (l : list A),
        map2 h (map f1 l) (map f2 l) = map g l.
    Proof. induction l; simpl; auto. f_equal; auto. Qed.

  End props_others.

End map2.


(* ======================================================================= *)
(** ** fold of list *)
Section fold.
  (* Context `{M : Monoid}. *)

  (** fold_left of list nat and add operation with different initial value *)
  Lemma fold_left_nat_initial : forall (l : list nat) n,
      fold_left add l n = fold_left add l 0 + n.
  Proof.
    induction l; intros; auto.
    simpl. rewrite IHl. rewrite (IHl a). lia.
  Qed.

End fold.


(* ======================================================================= *)
(** ** concatenation of list: list (list A) -> list A *)
Section concat.

  (** Length of concat operation *)
  Lemma concat_length : forall A (l : list (list A)),
      length (concat l) = fold_left add (map (@length A) l) 0.
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
  Context {A : Type} {A0 : A}.

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

  (** l1 + l2 *)
  Definition ladd (l1 l2 : list A) : list A := map2 Aadd l1 l2.
  Infix "+" := ladd : list_scope.

  (** - l *)
  Definition lopp (l : list A) : list A := map Aopp l.
  Notation "- l" := (lopp l) : list_scope.
  
  (** l1 - l2 *)
  Definition lsub (l1 l2 : list A) : list A := map2 Asub l1 l2.
  Infix "-" := lsub : list_scope.

  (** length of ladd *)
  Lemma ladd_length : forall l1 l2 n,
      length l1 = n -> length l2 = n -> length (l1 + l2) = n.
  Proof. intros. apply map2_length; auto. Qed.
  
  (** [] + l = [] *)
  Lemma ladd_nil_l : forall l, ladd l [] = [].
  Proof. apply map2_nil_r. Qed.
  
  (** l + [] = [] *)
  Lemma ladd_nil_r : forall l, ladd [] l = [].
  Proof. apply map2_nil_l. Qed.

  (** 0 + l = l *)
  Lemma ladd_zero_l : forall l n, length l = n -> ladd (lzero A0 n) l = l.
  Proof. intros. apply map2_zero_l; auto. apply G. Qed.
  
  (** l + 0 = l *)
  Lemma ladd_zero_r : forall l n, length l = n -> ladd l (lzero A0 n) = l.
  Proof. intros. apply map2_zero_r; auto. apply G. Qed.
  
  (** 0 - l = - l *)
  Lemma lsub_zero_l : forall l n, length l = n -> (lzero A0 n) - l = - l.
  Proof. apply map2_sub_zero_l. apply G. Qed.
  
  (** l - 0 = l *)
  Lemma lsub_zero_r : forall l n, length l = n -> l - (lzero A0 n) = l.
  Proof. apply map2_sub_zero_r. all: apply G. Qed.
  
  (** l - l = 0 *)
  Lemma lsub_self : forall l n, length l = n -> l - l = lzero A0 n.
  Proof. apply map2_sub_self. apply G. Qed.


  (** Let's have an abelian group AG *)
  Context `{AG : AGroup A Aadd A0 Aopp}.

  (** l1 + l2 = l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, l1 + l2 = l2 + l1.
  Proof. apply map2_comm; auto. apply AG. Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma lsub_assoc : forall (l1 l2 l3 : list A), (l1 - l2) - l3 = l1 - (l2 + l3).
  Proof. apply map2_sub_assoc with A0. all: apply AG. Qed.

  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma lsub_perm : forall (l1 l2 l3 : list A), (l1 - l2) - l3 = (l1 - l3) - l2.
  Proof. apply map2_sub_perm. all: apply AG. Qed.

  (** l1 - l2 = - (l2 - l1) *)
  Lemma lsub_comm : forall (l1 l2 : list A), l1 - l2 = - (l2 - l1).
  Proof. intros. unfold lsub. apply (map2_sub_comm) with A0. apply AG. Qed.
  
End ladd_opp_sub.


(* ======================================================================= *)
(** ** constant multiplication of list *)
Section lcmul_lmulc.
  (** Let's have a ring R *)
  Context `{R:Ring}.

  Infix "*" := Amul : A_scope.
  
  (** a * l *)
  Definition lcmul (a : A) (l : list A) : list A := map (fun x => a * x) l.
  
  (** l * a *)
  Definition lmulc (l : list A) (a : A) : list A := map (fun x => x * a) l.
  
  (** cmul keep its length *)
  Lemma lcmul_length : forall a l n, length l = n -> length (lcmul a l) = n.
  Proof. intros. unfold lcmul. rewrite map_length; auto. Qed.
  
  (** a * l = l * a *)
  Lemma lmulc_lcmul : forall a l, lmulc l a = lcmul a l.
  Proof. induction l; simpl; try easy. f_equal; auto. apply commutative. Qed.
  
  (** a * [] = [] *)
  Lemma lcmul_nil : forall a, lcmul a [] = [].
  Proof. intros. auto. Qed.
  
  (** [] * a = [] *)
  Lemma lmulc_nil : forall a, lmulc [] a = [].
  Proof. intros. auto. Qed.
  
  (** Let's have a field F *)
  Context `{F : Field A Aadd A0 Aopp Amul A1 Ainv}.
  
  (** k * l = l -> k = 1 \/ l = 0 *)
  Lemma lcmul_eq_imply_k1_or_l0 : forall (l : list A) n (k : A)
                                    (HDec: @Decidable A) (Hl : length l = n),
      lcmul k l = l -> (k = A1 \/ l = lzero A0 n).
  Proof.
    induction l; intros. subst; auto. destruct n; try easy. simpl in *.
    injection H; intros H1 H2.
    apply IHl with (n:=length l) in H1; auto.
    apply field_mul_eq_imply_a1_or_b0 in H2; auto.
    destruct H1, H2; auto. right. subst. f_equal. rewrite H0. f_equal. lia.
  Qed.
  
  (** k * l = 0 -> k = 0 \/ l = 0 *)
  Lemma lcmul_eq0_imply_k0_or_lzero : forall (l : list A) {n} (k : A)
                                        (HDec: @Decidable A) (Hl : length l = n),
      lcmul k l = lzero A0 n -> (k = A0 \/ l = lzero A0 n).
  Proof.
    induction l; intros. subst; auto.
    destruct n. easy. simpl in *. inversion H. rewrite H1 in *.
    apply IHl in H2; auto; try lia.
    apply field_mul_eq0_imply_a0_or_b0 in H1; auto.
    destruct H1, H2; auto. right. f_equal; auto. inv H. auto.
  Qed.
  
End lcmul_lmulc.


(* ======================================================================= *)
(** ** product of two lists *)
Section ldot.
  (** Let's have a ring R *)
  Context `{R:Ring}.
  Add Ring ring_inst : make_ring_theory.

  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "+" := (ladd (Aadd:=Aadd)) : list_scope.
  Infix "c*" := (lcmul (Amul:=Amul)) : list_scope.
  
  
  (** dot product, marked as l1 ⋅ l2 *)
  Definition ldot (l1 l2 : list A) : A := fold_right Aadd A0 (map2 Amul l1 l2).
  Infix "⋅" := ldot : list_scope.

  (** l1 ⋅ l2 = l2 ⋅ l1 *)
  Lemma ldot_comm : forall (l1 l2 : list A), l1 ⋅ l2 = l2 ⋅ l1.
  Proof. intros. unfold ldot. rewrite map2_comm; auto. apply R. Qed.
  
  (** [] ⋅ l = 0 *)
  Lemma ldot_nil_l : forall (l : list A), nil ⋅ l = A0.
  Proof. intros. destruct l; simpl; try easy. Qed.
  
  (** l ⋅ [] = 0 *)
  Lemma ldot_nil_r : forall (l : list A), l ⋅ nil = A0.
  Proof. intros. destruct l; simpl; try easy. Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2, (x1 :: l1) ⋅ (x2 :: l2) = ((x1 * x2) + (l1 ⋅ l2))%A.
  Proof. induction l1,l2; simpl; intros; try easy. Qed.
  
  (** 0 ⋅ l = 0 *)
  Lemma ldot_zero_l : forall l n, (lzero A0 n) ⋅ l = A0.
  Proof. induction l,n; simpl; intros; auto. rewrite ldot_cons. rewrite IHl. ring.
  Qed.
  
  (** l ⋅ 0 = 0 *)
  Lemma ldot_zero_r : forall l n, l ⋅ (lzero A0 n) = A0.
  Proof. intros. rewrite ldot_comm. apply ldot_zero_l. Qed.
  
  (** ldot left distributve over map2: l1 ⋅ (map l2 l3) = l1 ⋅ l2 + l1 ⋅ l3 *)
  Lemma ldot_map2_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      l1 ⋅ (map2 Aadd l2 l3) = ((l1 ⋅ l2) + (l1 ⋅ l3))%A.
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite ?ldot_cons. rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.

  (** ldot right distributve over map2: (map + l1 l2) ⋅ l3 = l1 ⋅ l3 + l2 ⋅ l3 *)
  Lemma ldot_map2_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (map2 Aadd l1 l2) ⋅ l3 = ((l1 ⋅ l3) + (l2 ⋅ l3))%A.
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite ?ldot_cons. ring_simplify. rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.

  (** ldot left distributive over ladd: l1 ⋅ (l2 + l3) = l1 ⋅ l2 + l1 ⋅ l3 *)
  Lemma ldot_ladd_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      l1 ⋅ (l2 + l3) = ((l1 ⋅ l2) + (l1 ⋅ l3))%A.
  Proof. intros. apply ldot_map2_distr_l with (r:=r); auto. Qed.
  
  (** ldot right distributive over ladd: (l1 + l2) ⋅ l3 = l1 ⋅ l3 + l2 ⋅ l3 *)
  Lemma ldot_ladd_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (l1 + l2) ⋅ l3 = ((l1 ⋅ l3) + (l2 ⋅ l3))%A.
  Proof. intros. apply ldot_map2_distr_r with (r:=r); auto. Qed.
  
  (** ldot left distributive over lcmul and mul: (x * l1) ⋅ l2 = x * (l1 ⋅ l2) *)
  Lemma ldot_lcmul_distr_l : forall l1 l2 x, (x c* l1) ⋅ l2 = x * (l1 ⋅ l2).
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot right distributive over lcmul and mul.
      l1 ⋅ (x * l2) = x * (l1 ⋅ l2) *)
  Lemma ldot_lcmul_distr_r : forall l1 l2 x, l1 ⋅ (x c* l2) = x * (l1 ⋅ l2).
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

End ldot.


(* ======================================================================= *)
(** ** Generate special list *)
Section GenerateSpecialList.
  (** Let's have a ring R *)
  Context `{R:Ring}.
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  
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
  Lemma list_unit_A1 : forall n i, i < n -> nth i (list_unit n i) A0 = A1.
  Proof.
    induction n; try easy. destruct i; simpl; try easy.
    intros; apply IHn.
    (* since Coq_8.16.0, Arith.Lt was deprecated *)
    (* apply Lt.lt_S_n; auto. *)
    apply Nat.succ_lt_mono. auto.
  Qed.
  
  (** list_unit(n,i) [j] = A0, when i < n /\ j <> i *)
  Fact list_unit_spec1 : forall n i j, i < n -> j <> i ->
    nth j (list_unit n i) A0 = A0.
  Proof.
    induction n; try easy. intros. destruct i,j; simpl; try easy.
    - apply nth_repeat_same.
    - apply IHn; lia.
  Qed.
  
  (** list_unit(n,i) [j] = A0, j <> i *)
  Lemma list_unit_A0 : forall n i j, j <> i -> nth j (list_unit n i) A0 = A0.
  Proof.
    induction n; try easy; simpl; intros.
    - destruct j; easy.
    - destruct i,j; simpl; try easy.
      apply nth_repeat_same. apply IHn. auto.
  Qed.
    
End GenerateSpecialList.


(* ======================================================================= *)
(** ** Convert list to fixed-length list *)
Section list_to_listN.
  Context `{M:Monoid}.

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
    length l = n -> list_to_listN l n = l.
  Proof.
    induction n; intros; simpl.
    - apply length_zero_iff_nil in H; easy.
    - rewrite IHn; destruct l; try easy. simpl. inv H. auto.
  Qed.

End list_to_listN.
