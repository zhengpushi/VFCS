(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       Basic.v
  by:         ZhengPu Shi
  purpose:    common code.
  
  remark:
  1. Support of polymorphic data types.
  2. Functions and Tactics of tuple
  
*)

Require Export ZArith.
Require Export Reals.

(* --------------------------------------------------------------- *)
(** Some useful datatypes *)

(* Function of n parameters with T type and return type is U *)
Fixpoint Fn (n : nat) (T U : Set) : Set :=
  match n with
  | O => U
  | S n => T -> Fn n T U
  end.

(*
Compute Fn 3 nat bool.
*)

(* --------------------------------------------------------------- *)
(** Support of polymorphic data types *)

(** abstract element type *)
Module Type EType.
  Parameter T : Set.
  Parameter Zero : T.               (* 0 *)
  Parameter One : T.                (* 1 *)
  Parameter Two : T.                (* 2 *)
  Parameter neg : T -> T.           (* negation of a number *)
  Parameter add : T -> T -> T.     (* a + b *)
  Definition sub (a b : T) := add a (neg b).
  Parameter mul : T -> T -> T.     (* a * b *)
  Definition NOne := neg One.      (* -1 *)

  Declare Scope element_scope.
  Bind Scope element_scope with T.
  Bind Scope element_scope with Zero.
  Bind Scope element_scope with One.
  Bind Scope element_scope with NOne.
  Bind Scope element_scope with add.
  Bind Scope element_scope with sub.
  Bind Scope element_scope with mul.
  Delimit Scope element_scope with element.
  Open Scope element_scope.

  Notation "0" := Zero.
  Notation "1" := One.
  Notation " - b" := (neg b) : element_scope.
  Infix "*" := mul : element_scope.
  Infix "+" := add : element_scope.
  Infix "-" := sub : element_scope.

  Parameter add_comm : forall a b, a + b = b + a.
  Parameter add_0_l : forall a, 0 + a = a.
  Parameter add_0_r : forall a, a + 0 = a.
  Parameter add_assoc: forall a b c, a + (b + c) = a + b + c.

  Parameter mul_neg_l : forall a b, (-a) * b = -(a*b).
  Parameter mul_neg_r : forall a b, a * (-b) = -(a*b).
  Parameter mul_1_l: forall a, 1 * a = a.
  Parameter mul_1_r: forall n, n * 1 = n.
  Parameter mul_comm: forall a b, a * b = b * a.
  Parameter mul_assoc: forall a b c, a * (b * c) = a * b * c.
  Parameter mul_add_distr_r : forall a b c, (a + b) * c = a * c + b * c.
  
  Parameter sub_def : forall a b, a - b = a + (-b).
  Parameter add_neg_l : forall a, a + (-a) = 0.
  (* --------- ring ------------- *)
  (* Check ring_theory.
  Print ring_theory. *)
  Add Ring ring_th : (mk_rt 0 1 add mul sub neg eq 
    add_0_l add_comm add_assoc 
    mul_1_l mul_comm mul_assoc mul_add_distr_r 
    sub_def  
    add_neg_l).
  
  (*
  Lemma ex1 a b : b * a = a * b.
  ring. Qed.
  
  Lemma ring_ex : forall a b, (a + b) * (a - b) = a * a - b * b.
  intros. ring. Qed.
  *)
  
End EType.

(** element type based on integer numbers *)
Open Scope Z.
Module ETypeZ : EType 
    with Definition T := Z
    with Definition Zero := 0
    with Definition One := 1
    with Definition neg := Z.opp
    with Definition add := Z.add
    with Definition sub := Z.sub
    with Definition mul := Z.mul.
  Definition T := Z.
  Definition Zero := 0.
  Definition One := 1.
  Definition Two := 2.
  Definition neg := Z.opp.
  Definition add := Z.add.
  Definition sub := Z.sub.
  Definition mul := Z.mul.
  Definition NOne := -1.
  
  Definition add_comm : forall a b, a + b = b + a.
    intros. rewrite Z.add_comm; trivial. Defined.
  Definition add_0_l := Z.add_0_l.
  Definition add_0_r := Z.add_0_r.
  Definition add_assoc := Z.add_assoc.


  Definition mul_neg_l := Z.mul_opp_l.
  Definition mul_neg_r := Z.mul_opp_r.
  Definition mul_1_l := Z.mul_1_l.
  Definition mul_1_r := Z.mul_1_r.
  Definition mul_comm := Z.mul_comm.
  Definition mul_assoc := Z.mul_assoc.
  Definition mul_add_distr_r := Z.mul_add_distr_r.

  Definition sub_def : forall a b, a - b = a + (-b).
    intros. reflexivity. Defined.
  Definition add_neg_l := Z.add_opp_diag_r.

  Add Ring ring_th : (mk_rt 0 1 add mul sub neg eq 
    add_0_l add_comm add_assoc 
    mul_1_l mul_comm mul_assoc mul_add_distr_r 
    sub_def  
    add_neg_l).
    
End ETypeZ.


(** element type based on real numbers *)
Open Scope R.
Definition Rsub := fun a b => Rplus a (Ropp b).
Module ETypeR : EType 
    with Definition T := R
    with Definition Zero := 0
    with Definition One := 1
    with Definition neg := Ropp
    with Definition add := Rplus
    with Definition sub := Rsub
    with Definition mul := Rmult.
  Definition T := R.
  Definition Zero := 0.
  Definition One := 1.
  Definition Two := 2.
  Definition neg := Ropp.
  Definition add := Rplus.
  Definition sub := Rsub.
  Definition mul := Rmult.
  Definition NOne := -1.
  
  Definition add_comm := Rplus_comm.
  Definition add_0_l := Rplus_0_l.
  Definition add_0_r := Rplus_0_r.
  Definition add_assoc : forall a b c, a + (b + c) = a + b + c.
    intros. rewrite Rplus_assoc; trivial. Qed.

  Definition mul_neg_l := Ropp_mult_distr_l_reverse.
  Definition mul_neg_r := Ropp_mult_distr_r_reverse.
  Definition mul_1_l := Rmult_1_l.
  Definition mul_1_r := Rmult_1_r.
  Definition mul_comm := Rmult_comm.
  Definition mul_assoc : forall a b c, a * (b * c) = a * b * c.
    intros. rewrite Rmult_assoc; trivial. Qed.
  Definition mul_add_distr_r := Rmult_plus_distr_r.

  Definition sub_def : forall a b, a - b = a + (-b).
    intros. reflexivity. Defined.
  Definition add_neg_l := Rplus_opp_r.

  Add Ring ring_th : (mk_rt 0 1 add mul sub neg eq 
    add_0_l add_comm add_assoc 
    mul_1_l mul_comm mul_assoc mul_add_distr_r 
    sub_def  
    add_neg_l).
    
End ETypeR.


(* --------------------------------------------------------------- *)
(** Functions and Tactics for tuple *)

(** equality of two tuples, iff corresponding elements are equal. *)

Lemma tuple2_equality {T1 T2} (a1 a2 : T1) (b1 b2 : T2) :
  (a1,b1) = (a2,b2) <-> (a1 = a2 /\ b1 = b2).
Proof.
  split.
  - intros. inversion H. split; reflexivity.
  - intros. destruct H. f_equal; assumption.
Qed.

(** tactic for simplify the equality of two tuples *)

(* (a1,a2,...) = (b1,b2,...) *)
Ltac simpl_equal_of_tuples :=
  repeat (apply tuple2_equality; split; auto).


Example ex_simpl_tuple2_equal : (1,2) = (2 - 1, 1 + 1).
  simpl_equal_of_tuples; ring. Qed.

Example ex_simpl_tuple3_equal : (4,5,6) = (1 + 3, 7 - 2, 2 * 3).
  simpl_equal_of_tuples; ring. Qed.

Example ex_simpl_tuple4_equal : (4,5,6,7) = (1 + 3, 7 - 2, 2 * 3, 3+(1+3)).
  simpl_equal_of_tuples; ring. Qed.

