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
(* Reserved Infix    "==?"     (at level 65, no associativity).      (* decidable *) *)
(* Reserved Infix    "<>?"     (at level 65, no associativity).      (* decidable right *) *)
(* Reserved Infix    "=="      (at level 70, no associativity).      (* equiv *) *)
(* Reserved Notation "a != b"  (at level 70, no associativity).      (* not equiv *) *)
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
Reserved Notation "M \T"    (at level 32, left associativity).    (* transpose *)
(* Reserved Notation "M ⁻¹"    (at level 20, format "M ⁻¹").         (* minv *) *)
Reserved Notation "M \-1"    (at level 20, format "M \-1").         (* minv *)
Reserved Notation "M1 @ M2" (at level 30, no associativity).      (* cons by col *)
Reserved Notation "'tr' M"  (at level 33, no associativity).

Reserved Notation "'\sum' f" (at level 10).       (* sum of a fin-function *)


(* ****************************************************** *)
(* The precedence ∈ [1,30) are element operations *)

Reserved Notation "| r |"   (at level 30, r at level 25, format "| r |").  (* Rabs *)

(* this level is consistent with Mathcomp.ssreflect.ssrnotations.v *)

(* get element of list or dlist *)
(* Reserved Notation "l ! i"      (at level 20, i at next level, format "l ! i" ). *)
(* Reserved Notation "dl ! i ! j" (at level 20, i, j at next level, format "dl ! i ! j"). *)
Reserved Notation "l ! i"      (at level 25, left associativity, i at next level, format "l ! i" ).
Reserved Notation "dl ! i ! j" (at level 25, left associativity, i,j at next level, format "dl ! i ! j").

(* get element of vector or matrix *)
Reserved Notation "V $ i"      (at level 25, left associativity, i at next level, format "V $ i" ).
(* Reserved Notation "M $ i $ j"  (at level 20, i, j at next level, format "M $ i $ j"). *)

(* index-of-matrix or index-of-nat-nat-function.
 Note, there are two style of start number to count index, 0 or 1.
 Many programming language use 0, but MATLAB and many mathematical textbook use 1.
 Maybe it is a convention problem, we choose 1. *)
Reserved Notation "M .11"      (at level 25, format "M .11").     (* m[1,1] *)
Reserved Notation "M .12"      (at level 25, format "M .12").
Reserved Notation "M .13"      (at level 25, format "M .13").
Reserved Notation "M .14"      (at level 25, format "M .14").
Reserved Notation "M .21"      (at level 25, format "M .21").
Reserved Notation "M .22"      (at level 25, format "M .22").
Reserved Notation "M .23"      (at level 25, format "M .23").
Reserved Notation "M .24"      (at level 25, format "M .24").
Reserved Notation "M .31"      (at level 25, format "M .31").
Reserved Notation "M .32"      (at level 25, format "M .32").
Reserved Notation "M .33"      (at level 25, format "M .33").
Reserved Notation "M .34"      (at level 25, format "M .34").
Reserved Notation "M .41"      (at level 25, format "M .41").
Reserved Notation "M .42"      (at level 25, format "M .42").
Reserved Notation "M .43"      (at level 25, format "M .43").
Reserved Notation "M .44"      (at level 25, format "M .44").

(* index-of-vector or index-of-nat-function. We choose 0 as start number. *)
Reserved Notation "V .1"       (at level 25, format "V .1").      (* v[1] *)
Reserved Notation "V .2"       (at level 25, format "V .2").
Reserved Notation "V .3"       (at level 25, format "V .3").
Reserved Notation "V .4"       (at level 25, format "V .4").

(* only for 3D vector, the "w" component has two conventions, we won't use it *)
Reserved Notation "V .x"       (at level 25, format "V .x").      (* v[1] *)
Reserved Notation "V .y"       (at level 25, format "V .y").
Reserved Notation "V .z"       (at level 25, format "V .z").
(* Reserved Notation "V .w"       (at level 25, format "V .w"). *)


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
(** * Extension for option type *)

(** Convert option type to base type  *)
Definition option_get {A} (o : option A) (def : A) : A :=
  match o with
  | Some a => a
  | _ => def
  end.


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
(* Open Scope fun_scope. *)

(** Scope for vector type *)
Declare Scope vec_scope.
Delimit Scope vec_scope with V.
Open Scope vec_scope.

(** Scope for matrix type *)
Declare Scope mat_scope.
Delimit Scope mat_scope with M.
Open Scope mat_scope.

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
