(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Basic configuration (Libraries, Notations, Warning, etc.)
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. Basic libraries in whole project
  3. Reserved notations for consistence.
     https://coq.inria.fr/distrib/V8.13.2/refman/language/coq-library.html 
  3. Eliminate some warning.  
     https://coq.inria.fr/distrib/V8.13.2/refman/user-extensions/
     syntax-extensions.html?highlight=warning
  4. Customized tactics.
*)


(* ######################################################################### *)
(** * Basic libraries *) 

Require Export Coq.Classes.Morphisms.     (* respectful, ==> *)
Require Export Coq.Setoids.Setoid.        (*  *)
Require Export Coq.Classes.SetoidTactics. (* add_morphism_tactic *)
Require Export Coq.Relations.Relations.   (* equivalence *)
Require Export Coq.Bool.Sumbool.          (* sumbool_not *)
Require Export Coq.Bool.Bool.             (* reflect *)
Require Export Ring.                      (* ring *)
Require Export Field.                     (* field *)

Require Export Coq.Logic.Classical.
Require Export Coq.Logic.FunctionalExtensionality.

Require Arith ZArith QArith Qcanon Reals List SetoidList.


(* ######################################################################### *)
(** * Reserved Notations *)

(* Reserved Notations, to keep same precedence and associativity *)

(* ****************************************************** *)
(* The precedence ∈ [60,100) are logic operations *)
Reserved Infix    "=="      (at level 70, no associativity).      (* equiv *)
Reserved Infix    "==?"     (at level 65, no associativity).      (* decidable *)
Reserved Infix    "<>?"     (at level 65, no associativity).      (* decidable right *)
Reserved Notation "a != b"  (at level 70, no associativity).      (* not equiv *)
Reserved Infix    "=?"      (at level 70, no associativity).      (* bool equal *)

(* ****************************************************** *)
(* The precedence ∈ [30,60) are vector/matrix operations *)
Reserved Infix    "+"       (at level 50, left associativity).    (* add *)
Reserved Infix    "-"       (at level 50, left associativity).    (* sub *)
Reserved Infix    "*"       (at level 40, left associativity).    (* mul *)
Reserved Infix    "/"       (at level 40, left associativity).    (* div *)
Reserved Infix    "n*"      (at level 40, no associativity).      (* n-times *)
Reserved Infix    "c*"      (at level 40, left associativity).    (* scal left mul *)
Reserved Infix    "*c"      (at level 40, left associativity).    (* scal right mul *)
Reserved Infix    "⦿"      (at level 40, left associativity).    (* hardmard prod *)
Reserved Infix    "\o"      (at level 50, no associativity).
Reserved Infix    "⋅"       (at level 40, no associativity).      (* dot prod *)
Reserved Notation "< a , b >" (at level 60, b at level 55, format "< a , b >"). (* dot prod *)
Reserved Notation "|| v ||"   (at level 60, v at level 45, format "|| v ||").  (* vlen *)
Reserved Infix    "×"       (at level 40, no associativity).      (* cross prod *)
Reserved Infix    "∘"       (at level 40, left associativity).    (* compose *)
Reserved Notation "- a"     (at level 35, right associativity).   (* opp *)
Reserved Notation "/ a"     (at level 35, right associativity).   (* inv *)
Reserved Notation "m \T"    (at level 32, left associativity).    (* transpose *)
Reserved Notation "m ⁻¹"    (at level 20, format "m ⁻¹").         (* minv *)
Reserved Notation "m1 @ m2" (at level 30, no associativity).      (* cons by col *)
Reserved Notation "'tr' m"  (at level 33, no associativity).

(* ****************************************************** *)
(* The precedence ∈ [1,30) are element operations *)

Reserved Notation "| r |"   (at level 30, r at level 25, format "| r |").  (* Rabs *)

(* this level is consistent with Mathcomp.ssreflect.ssrnotations.v *)

(* safe access (any index) *)
Reserved Notation "m ! i ! j"  (at level 20, i at next level).    (* nth of mat *)
Reserved Notation "v ! i"      (at level 20, i at next level).    (* nth of vec *)
(* unsafe access (developer must give valid index) *)
Reserved Notation "m $ i $ j"  (at level 20, i at next level).    (* nth of mat, raw *)
Reserved Notation "v $ i"      (at level 20, i at next level).    (* nth of vec, raw *)

(* index-of-matrix or index-of-nat-nat-function.
 Note, there are two style of start number to count index, 0 or 1.
 Many programming language use 0, but MATLAB and many mathematical textbook use 1.
 Maybe it is a convention problem, we choose 1. *)
Reserved Notation "m .11"      (at level 20, format "m .11").     (* m[1,1] *)
Reserved Notation "m .12"      (at level 20, format "m .12").
Reserved Notation "m .13"      (at level 20, format "m .13").
Reserved Notation "m .14"      (at level 24, format "m .14").
Reserved Notation "m .21"      (at level 20, format "m .21").
Reserved Notation "m .22"      (at level 20, format "m .22").
Reserved Notation "m .23"      (at level 20, format "m .23").
Reserved Notation "m .24"      (at level 20, format "m .24").
Reserved Notation "m .31"      (at level 20, format "m .31").
Reserved Notation "m .32"      (at level 20, format "m .32").
Reserved Notation "m .33"      (at level 20, format "m .33").
Reserved Notation "m .34"      (at level 20, format "m .34").
Reserved Notation "m .41"      (at level 20, format "m .41").
Reserved Notation "m .42"      (at level 20, format "m .42").
Reserved Notation "m .43"      (at level 20, format "m .43").
Reserved Notation "m .44"      (at level 20, format "m .44").

(* index-of-vector or index-of-nat-function. We choose 0 as start number. *)
Reserved Notation "v .1"       (at level 20, format "v .1").      (* v[1] *)
Reserved Notation "v .2"       (at level 20, format "v .2").
Reserved Notation "v .3"       (at level 20, format "v .3").
Reserved Notation "v .4"       (at level 20, format "v .4").
(* Reserved Notation "v .x"       (at level 20, format "v .x").      (* v[0] *) *)
(* Reserved Notation "v .y"       (at level 20, format "v .y"). *)
(* Reserved Notation "v .z"       (at level 20, format "v .z"). *)
(* Reserved Notation "v .w"       (at level 20, format "v .w"). *)


(* this level is consistent with coq.ssr.ssrbool.v *)
(* Notation "~~ b" := (negb b) (at level 35, right associativity) : bool_scope. *)


(* ######################################################################### *)
(** * Eliminate Warning. *)

(* Export Set Warnings "-notation-overridden". *)


(* ######################################################################### *)
(** * Customized tactics *)

(** ** Tactics with a short name *)

Global Ltac gd k := generalize dependent k.

(** repeat split *)
Ltac ssplit := 
  repeat 
  match goal with
  | |- _ /\ _ => split
  end.

(** inversion and subst *)
Ltac inv H :=
  inversion H; clear H; subst.

(** first step of the proof of Proper *)
Ltac simp_proper :=
  unfold Proper; unfold respectful.

(** Use this tactic, the proposition of a comparision relation and the sumbool 
    comparison are connected. 
    We must first register the desired reflection to "bdestruct" database to
    take effect. *)

(* (* original version, which has additional support for natural number *) *)
(* Ltac bdestruct X := *)
(*   let H := fresh in let e := fresh "e" in *)
(*    evar (e: Prop); *)
(*    assert (H: reflect e X); subst e; *)
(*     [eauto with bdestruct *)
(*     | destruct H as [H|H]; *)
(*       [ | try first [apply not_lt in H | apply not_le in H]]]. *)

(* modified version, support any data type which registered a reflection relation *)
Ltac bdestruct X :=
  let H := fresh in
  let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
  [ try eauto with bdestruct
  | destruct H as [H|H]].
(* [ | try first [apply not_lt in H | apply not_le in H]]]. *)


(* ######################################################################### *)
(** * Global coercions *)

(** bool to Prop *)
Definition is_true (b : bool) : Prop := b = true.
Coercion is_true : bool >-> Sortclass.

(* Note that Coq.Bool.Bool.Is_true is another implementation, and I argue that it is 
   a bit complex *)
(* Print Is_true. (* Is_true = fun b : bool => if b then True else False *)
     : bool -> Prop *)

Lemma is_true_and_iff : forall b1 b2 : bool,
    is_true b1 /\ is_true b2 <-> is_true (b1 && b2).
Proof. destruct b1,b2; intros; split; intros; auto; try easy. Qed.

Lemma is_true_or_iff : forall b1 b2 : bool,
    is_true b1 \/ is_true b2 <-> is_true (b1 || b2).
Proof.
  destruct b1,b2; intros; split; intros; auto; try easy.
  simpl. unfold is_true in *. destruct H; auto.
Qed.

(** use reflect to connect bool and proposition equality *)
Example eqnP (n m : nat) : reflect (n = m) (Nat.eqb n m).
Proof.
  gd m. induction n; intros [|m]; simpl; try constructor; auto.
  destruct IHn with m; subst; constructor; auto.
Qed.


(* ######################################################################### *)
(** * A relation is decidable *)

(** ** Class *)

Class Dec {A : Type} (Aeq : relation A) := {
    dec : forall (a b : A), {Aeq a b} + {~(Aeq a b)};
  }.
Infix "==?" := (dec).
Infix "<>?" := (fun a b => sumbool_not _ _ (a ==? b)).

(** ** Instances *)

Section Instances.
  Import Nat Arith ZArith QArith Qcanon Reals SetoidList.
  
  Global Instance Dec_NatEq : Dec (@eq nat).
  Proof. constructor. apply Nat.eq_dec. Defined.

  Global Instance Dec_Z : Dec (@eq Z).
  Proof. constructor. apply Z.eq_dec. Defined.

  Global Instance Dec_Q_Qeq : Dec Qeq.
  Proof. constructor. apply Qeq_dec. Defined.

  Global Instance Dec_Qc : Dec (@eq Qc).
  Proof. constructor. apply Qc_eq_dec. Defined.

  Global Instance Dec_R : Dec (@eq R).
  Proof. constructor. apply Req_EM_T. Defined.

  Global Instance Dec_list `{D:Dec} : Dec (eqlistA Aeq).
  Proof.
  constructor. intros l1. induction l1.
    - intros l2. destruct l2; auto.
      right. intro. easy.
    - intros l2. destruct l2.
      + right. intro. easy.
      + destruct (dec a a0), (IHl1 l2); auto.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
  Defined.

  Global Instance Dec_dlist `{D:Dec} : Dec (eqlistA (eqlistA Aeq)).
  Proof. constructor. intros. apply dec. Defined.

End Instances.

(** ** Extra Theories *)
Section Dec_theory.

  Context `{D : Dec}.
  Infix "==" := Aeq.

  (** Tips: these theories are useful for R type *)
  
  (** Calculate equality to boolean, with the help of equality decidability *)
  Definition Aeqb (a b : A) : bool := if a ==? b then true else false.
  Infix "=?" := Aeqb.

  (** Aeqb is true iff equal. *)
  Lemma Aeqb_true : forall a b, a =? b = true <-> a == b.
  Proof.
    intros. unfold Aeqb. destruct dec; split; intros; easy.
  Qed.

  (** Aeqb is false iff not equal *)
  Lemma Aeqb_false : forall a b, a =? b = false <-> ~(a == b).
  Proof.
    intros. unfold Aeqb. destruct dec; split; intros; easy.
  Qed.

  Lemma Aeq_reflect : forall a b : A, reflect (a == b) (a =? b).
  Proof.
    intros. unfold Aeqb. destruct (dec a b); constructor; auto.
  Qed.

End Dec_theory.

(** ** Examples *)
Goal forall a b : nat, {a = b} + {a <> b}.
  apply dec. Qed.


(* ######################################################################### *)
(** * Usually used scopes *)

(** Scope for matrix/vector/list element type *)
Declare Scope A_scope.
Delimit Scope A_scope with A.
Open Scope A.

(** Scope for list type *)
Declare Scope list_scope.
Delimit Scope list_scope with list.
Open Scope list.

(** Scope for list list type *)
Declare Scope dlist_scope.
Delimit Scope dlist_scope with dlist.
Open Scope dlist.

(** Scope for function (especially for nat-indexed function such as "nat -> A") *)
Declare Scope fun_scope.
Delimit Scope fun_scope with F. (* Note that, Ranalysis1 defined Rfun_scope with F *)
Open Scope fun_scope.

(** Scope for matrix type *)
Declare Scope mat_scope.
Delimit Scope mat_scope with M.
Open Scope mat_scope.

(** Scope for vector type (limited use) *)
(* Declare Scope vec_scope. *)
(* Delimit Scope vec_scope with V. *)
(* Open Scope vec_scope. *)

(** Scope for row-vector type *)
Declare Scope rvec_scope.
Delimit Scope rvec_scope with RV.
Open Scope rvec_scope.

(** Scope for column-vector type *)
Declare Scope cvec_scope.
Delimit Scope cvec_scope with CV.
Open Scope cvec_scope.

(** Scope for linear-space type *)
Declare Scope LinearSpace_scope.
Delimit Scope LinearSpace_scope with LS.
Open Scope LinearSpace_scope.
