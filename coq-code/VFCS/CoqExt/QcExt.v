(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Qc (canonical rational number).
  author    : ZhengPu Shi
  date      : 2022.07
*)


Require Import Basic.
Require Export QExt Qcanon.
Open Scope Qc.


(* ######################################################################### *)
(** ** Understanding the Qc type *)

(* Why Qc is better than Q *)
Section eq.
  (* Why 1#2 and 2#4 could be equal? *)
  
  (* Compute Q2Qc (1#2). *)
  (* = {| this := 1 # 2; canon := Qred_involutive (1 # 2) |} *)
  (* Compute Q2Qc (2#4). *)
  (* = {| this := 1 # 2; canon := Qred_involutive (2 # 4) |} *)

  (* Answer: because the Qc type.

     Record Qc : Set := Qcmake { 
       this : Q;  
       canon : Qred this = this }.

     Here, canon is a proof of equality, so its unique by the help of UIP.
     Then, only need the "this" component equal.
   *)
  Goal Q2Qc (1#2) = Q2Qc (2#4).
  Proof. cbv. f_equal. apply UIP. Qed.
End eq.


(* ######################################################################### *)
(** ** Convertion between Qc and other types *)

(** Qc to Q *)
Definition Qc2Q (qc : Qc) : Q := this qc.

(** Z to Qc *)
Definition Z2Qc (z : Z) : Qc := Q2Qc (Z2Q z).

(** nat to Qc *)
Definition nat2Qc (n : nat) : Qc := Q2Qc (nat2Q n).

(** Qc to Z *)
Definition Qc2Z_ceiling (q : Qc) : Z := Q2Z_ceiling (Qc2Q q).
Definition Qc2Z_floor (q : Qc) : Z := Q2Z_floor (Qc2Q q).

(** list Q to list Qc *)
Definition Q2Qc_list l := List.map (fun q => Q2Qc q) l.

(** list (list Q) to list (list Qc) *)
Definition Q2Qc_dlist dl := List.map Q2Qc_list dl.


(* ######################################################################### *)
(** ** Properties for Qeqb and Qeq *)

Notation Qceqdec := Qc_eq_dec.

Notation Qceqb := Qc_eq_bool.

Infix     "=?"          := Qceqb          : Qc_scope.

(** Reflection of (=) and (=?) *)
Lemma Qceqb_true_iff : forall x y, x =? y = true <-> x = y.
Proof.
  intros; split; intros.
  - apply Qc_eq_bool_correct; auto.
  - subst. unfold Qceqb, Qc_eq_bool.
    unfold Qceqdec.
    destruct (Qeq_dec y y) eqn: E1; auto.
    destruct n. apply Qeq_refl.
Qed.

Lemma Qceqb_false_iff : forall x y, x =? y = false <-> x <> y.
Proof. 
  intros; split; intros.
  - intro. apply Qceqb_true_iff in H0. rewrite H in H0. easy.
  - destruct (Qceqb x y) eqn:E1; auto. apply Qceqb_true_iff in E1. easy.
Qed.


(* ######################################################################### *)
(** ** Well-defined (or compatible, or proper morphism) of operations on Qc. *)

Lemma Qcplus_wd : Proper (eq ==> eq ==> eq) Qcplus.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcopp_wd : Proper (eq ==> eq) Qcopp.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcminus_wd : Proper (eq ==> eq ==> eq) Qcminus.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcmult_wd : Proper (eq ==> eq ==> eq) Qcmult.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcinv_wd : Proper (eq ==> eq) Qcinv.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcdiv_wd : Proper (eq ==> eq ==> eq) Qcdiv.
Proof. simp_proper. intros; subst; ring. Qed.

Hint Resolve
  Qcplus_wd Qcopp_wd Qcminus_wd Qcmult_wd Qcinv_wd Qcdiv_wd
  : wd.


(* ######################################################################### *)
(** ** Others *)


(** ** sqrt of Q *)

(* Definition Qsqrt (q : Q) := Qmake (Z.sqrt (Qnum q)) (Pos.sqrt (Qden q)). *)

(* Example *)
(* Compute Qsqrt 1.21. *)
