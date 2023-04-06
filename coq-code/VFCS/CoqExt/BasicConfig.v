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
Require Export Coq.Bool.Bool.             (* reflect *)
Require Export Ring.                      (* ring *)
Require Export Field.                     (* field *)

Require Export Coq.Logic.Classical.
Require Export Coq.Logic.FunctionalExtensionality.


(* ######################################################################### *)
(** * Reserved Notations *)

(** Reserved Notations, to keep same precedence and associativity *)
Reserved Infix    "=="      (at level 70, no associativity).      (* equiv *)
Reserved Notation "a != b"  (at level 70, no associativity).      (* not equiv *)
Reserved Infix    "=?"      (at level 70, no associativity).      (* bool equal *)
Reserved Infix    "+"       (at level 50, left associativity).    (* add *)
Reserved Infix    "-"       (at level 50, left associativity).    (* sub *)
Reserved Infix    "*"       (at level 40, left associativity).    (* mul *)
Reserved Infix    "/"       (at level 40, left associativity).    (* div *)
Reserved Infix    "c*"      (at level 40, left associativity).    (* scal left mul *)
Reserved Infix    "*c"      (at level 40, left associativity).    (* scal right mul *)
Reserved Infix    "\o"      (at level 50, no associativity).
Reserved Infix    "⋅"       (at level 40, no associativity).      (* dot product *)
Reserved Infix    "∘"       (at level 40, left associativity).    (* compose *)
Reserved Notation "- a"     (at level 35, right associativity).   (* opp *)
Reserved Notation "/ a"     (at level 35, right associativity).   (* inv *)
Reserved Notation "a \T"    (at level 34, left associativity).    (* transpose *)
Reserved Notation "m1 @ m2" (at level 30, no associativity).      (* cons by col *)

(* this level is consistent with Mathcomp.ssreflect.ssrnotations.v *)

(* safe access (any index) *)
Reserved Notation "m ! i ! j"  (at level 20, i at next level).    (* nth of mat *)
Reserved Notation "v ! i"      (at level 20, i at next level).    (* nth of vec *)
(* unsafe access (developer must give valid index) *)
Reserved Notation "m $ i $ j"  (at level 20, i at next level).    (* nth of mat, raw *)
Reserved Notation "v $ i"      (at level 20, i at next level).    (* nth of vec, raw *)

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
  [eauto with bdestruct
  | destruct H as [H|H]].
(* [ | try first [apply not_lt in H | apply not_le in H]]]. *)



(* ######################################################################### *)
(** * Global coercions *)

(** bool to Prop *)
Definition is_true (b : bool) : Prop := b = true.
Coercion is_true : bool >-> Sortclass.

Goal true.
apply eq_refl. Qed.

Goal negb false.
simpl. apply eq_refl. Qed.

Example eqnP (n m : nat) : reflect (n = m) (Nat.eqb n m).
Proof.
  gd m. induction n; intros [|m]; simpl; try constructor; auto.
  destruct IHn with m; subst; constructor; auto.
Qed.


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

(** Scope for matrix type *)
Declare Scope mat_scope.
Delimit Scope mat_scope with mat.
Open Scope mat.

(** Scope for vector type *)
Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Open Scope vec_scope.

