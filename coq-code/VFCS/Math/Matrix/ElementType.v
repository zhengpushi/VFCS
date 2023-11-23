(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Type of Matrix Element
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. Element type is orgainized to several levels
  (1) ElementType
      EqElementType, Aeq is eq.
  (2) DecidableElementType, based on ElementType.
  (3) RingElementType, based on ElementType.
  (4) FieldElementType, based on RingEementType.
  (5) DecidableFieldElementType, based on FieldElementType, and 
      satisfy Decidable relation.
*)

Require NatExt ZExt QExt QcExt RExt RealFunction Complex.
Require Export Hierarchy.


(* ######################################################################### *)
(** * Base type *)

(** ** Type of base type *)
Module Type BaseType.
  Parameter T : Type.
End BaseType.

(** ** Instances *)

Module BaseTypeNat <: BaseType.
  Export NatExt.
  Definition T := nat.
  Hint Unfold T : T.
End BaseTypeNat.

Module BaseTypeZ <: BaseType.
  Export ZExt.
  Definition T := Z.
  Hint Unfold T : T.
End BaseTypeZ.

Module BaseTypeQ <: BaseType.
  Export QExt.
  Definition T := Q.
  Hint Unfold T : T.
End BaseTypeQ.

Module BaseTypeQc <: BaseType.
  Export QcExt.
  Definition T := Qc.
  Hint Unfold T : T.
End BaseTypeQc.

Module BaseTypeR <: BaseType.
  Export RExt.
  Definition T := R.
  Hint Unfold T : T.
End BaseTypeR.

Module BaseTypeC <: BaseType.
  Export Complex.
  Definition T := C.
  Hint Unfold T : T.
End BaseTypeC.

Module BaseTypeRFun <: BaseType.
  Export RealFunction.
  Definition T := tpRFun.
  Hint Unfold T : T.
End BaseTypeRFun.

Module BaseTypeFun (A B : BaseType) <: BaseType.
  (* Import Reals. *)
  Definition T := A.T -> B.T.
  Hint Unfold T : T.
End BaseTypeFun.


(* ######################################################################### *)
(** * Element with setoid equality *)

(** ** Type of element *)
Module Type ElementType <: BaseType.
  Parameter T : Type.
  Parameter Teq : relation T.
  Parameter T0 : T.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.

  Axiom Equiv_Teq : Equivalence Teq.
  #[export] Existing Instance Equiv_Teq.
End ElementType.


(** ** Type of element which specify the Teq is eq, used in lots of cases *)
Module Type EqElementType (B : BaseType)
<: ElementType
   with Definition T := B.T
   with Definition Teq := @eq B.T.
  Definition T := B.T.
  Definition Teq := @eq B.T.
  
  Parameter T0 : T.
  Axiom Equiv_Teq : Equivalence Teq.
  #[export] Existing Instance Equiv_Teq.
End EqElementType.  

(* ToDo: these code only works in Coq-8.16, but failed at Coq-8.13,8.14,
   I'm not sure why? *)
(* Module Type EqElementType (B : BaseType) *)
(* <: BaseType *)
(*   := ElementType *)
(*      with Definition T := B.T *)
(*      with Definition Teq := @eq B.T. *)


(** ** Instances *)
Module ElementTypeNat <: EqElementType BaseTypeNat.
  Export BaseTypeNat.

  Definition T : Type := nat.
  Definition Teq : relation T := eq.
  Definition T0 : T := 0.
  Hint Unfold T Teq T0 : T.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.

  #[export] Instance Equiv_Teq : Equivalence Teq.
  Proof. apply eq_equivalence. Qed.
  
End ElementTypeNat.

Module ElementTypeZ <: EqElementType BaseTypeZ.
  Export BaseTypeZ.
  
  Definition T : Type := Z.
  Definition Teq : relation T := eq.
  Definition T0 : T := 0.
  Hint Unfold T Teq T0 : T.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.

  #[export] Instance Equiv_Teq : Equivalence Teq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeZ.

(** Tips, this module cannot be a EqElementType *)
Module ElementTypeQ <: ElementType.
  Export BaseTypeQ.
  
  Definition T : Type := Q.
  Definition Teq : relation T := Qeq.
  Definition T0 : T := 0.
  Hint Unfold T Teq T0 : T.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.

  #[export] Instance Equiv_Teq : Equivalence Teq.
  Proof. apply Q_Setoid. Qed.
End ElementTypeQ.

Module ElementTypeQc <: EqElementType BaseTypeQc.
  Export BaseTypeQc.
  
  Definition T : Type := Qc.
  Definition Teq : relation T := eq.
  Definition T0 : T := 0.
  Hint Unfold T Teq T0 : T.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.

  #[export] Instance Equiv_Teq : Equivalence Teq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeQc.

Module ElementTypeR <: EqElementType BaseTypeR.
  Export BaseTypeR.

  Definition T : Type := R.
  Definition Teq : relation T := eq.
  Definition T0 : T := 0%R.
  Hint Unfold T Teq T0 : T.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.

  #[export] Instance Equiv_Teq : Equivalence Teq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeR.

Module ElementTypeC <: EqElementType BaseTypeC.
  Export BaseTypeC.

  Definition T : Type := C.
  Definition Teq : relation T := eq.
  Definition T0 : T := 0.
  Hint Unfold T Teq T0 : T.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.

  #[export] Instance Equiv_Teq : Equivalence Teq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeC.

Module ElementTypeRFun <: EqElementType BaseTypeRFun.
  Export BaseTypeRFun.

  Definition T : Type := tpRFun.
  Definition Teq : relation T := eq.
  Definition T0 : T := fzero.
  Hint Unfold T Teq T0 : T.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.

  #[export] Instance Equiv_Teq : Equivalence Teq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeRFun.

Module ElementTypeFun (I O : ElementType) <: ElementType.
  Definition T : Type := {f : I.T -> O.T | Proper (I.Teq ==> O.Teq) f}.
  Definition Teq : relation T :=
    fun (f g : T) => forall (a : I.T),
        O.Teq (proj1_sig f a) (proj1_sig g a).
  Infix "=I=" := I.Teq (at level 20).
  Infix "=O=" := O.Teq (at level 20).

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b : T => ~(a == b)) : T_scope.
  
  Definition T0 : T.
    refine (exist _ (fun _ => O.T0) _).
    simp_proper. intros. destruct (O.Equiv_Teq). reflexivity.
  Defined.
  
  #[export] Instance Equiv_Teq : Equivalence Teq.
  Proof.
    destruct (I.Equiv_Teq), (O.Equiv_Teq).
    constructor; cbv; intros; try easy.
    destruct x. specialize (H a). specialize (H0 a). rewrite H0 in H. auto.
  Qed.
End ElementTypeFun.

Module ElementType_Test.
  
  Import ElementTypeNat ElementTypeR.
  Module Import ElementTypeFunEx1 := ElementTypeFun ElementTypeNat ElementTypeR.

  Definition f : T.
    refine (exist _ (fun i => match i with 0%nat => 1 | 1%nat => 2 | _ => 1 end) _).
    simp_proper. intros. rewrite H. reflexivity.
  Defined.
  Definition g : T.
    refine (exist _ (fun i => match i with 1%nat => 2 | _ => 1 end) _ ).
    simp_proper. intros. rewrite H. reflexivity.
  Defined.

  Goal f == g.
  Proof. cbv. intros. auto. Qed.
End ElementType_Test.


(* ######################################################################### *)
(** * Element with decidable relation *)

(** ** Type of element with decidable relation *)
Module Type DecidableElementType <: ElementType.
  Include ElementType.

  Axiom Dec_Teq : Dec Teq.
  #[export] Existing Instance Dec_Teq.
End DecidableElementType.

Module Type EqDecidableElementType (B : BaseType)
<: EqElementType B
  := DecidableElementType
     with Definition T := B.T
     with Definition Teq := @eq B.T.


(** ** Instances *)
Module DecidableElementTypeNat
<: DecidableElementType.
  Include ElementTypeNat.

  #[export] Instance Dec_Teq : Dec Teq.
  Proof. constructor. apply Nat.eq_dec. Qed.
End DecidableElementTypeNat.

Module DecidableElementTypeZ
<: DecidableElementType.
  Include ElementTypeZ.

  #[export] Instance Dec_Teq : Dec Teq.
  Proof. constructor. apply Z.eq_dec. Qed.
End DecidableElementTypeZ.

Module DecidableElementTypeQ
<: DecidableElementType.
  Include ElementTypeQ.

  #[export] Instance Dec_Teq : Dec Teq.
  Proof. constructor. apply Qeq_dec. Qed.
End DecidableElementTypeQ.

Module DecidableElementTypeQc
<: DecidableElementType.
  Include ElementTypeQc.

  #[export] Instance Dec_Teq : Dec Teq.
  Proof. constructor. apply Qc_eq_dec. Qed.
End DecidableElementTypeQc.

Module DecidableElementTypeR
<: DecidableElementType.
  Include ElementTypeR.

  #[export] Instance Dec_Teq : Dec Teq.
  Proof. constructor. apply Req_EM_T. Qed.
End DecidableElementTypeR.

Module DecidableElementTypeC
<: DecidableElementType.
  Include ElementTypeC.

  #[export] Instance Dec_Teq : Dec Teq.
  Proof. apply Dec_Complex. Qed.
End DecidableElementTypeC.


(* ######################################################################### *)
(** * Element with ring structure *)

(** ** Type of Element with ring structure *)
Module Type RingElementType <: ElementType.
  Include ElementType.
  Open Scope T_scope.

  Parameter T1 : T.
  Parameter Tadd Tmul : T -> T -> T.
  Parameter Topp : T -> T.

  Notation Tsub := (fun x y => Tadd x (Topp y)).
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := Tsub : T_scope.

  (** Use these lemmas, we can replace "Add Morphism ..." with "Existing Morphism" *)
  Axiom Tadd_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tadd).
  Axiom Topp_aeq_mor : Proper (Teq ==> Teq) (Topp).
  Axiom Tmul_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tmul).

  #[export] Existing Instance Tadd_aeq_mor.
  #[export] Existing Instance Topp_aeq_mor.
  #[export] Existing Instance Tmul_aeq_mor.

  Axiom Ring_thy : ring_theory T0 T1 Tadd Tmul Tsub Topp Teq.

  (** A Group structure can be derived from the context *)
  Axiom AGroup_inst : AGroup Tadd T0 Topp Teq.
  #[export] Existing Instance AGroup_inst.

  (** A Ring structure can be derived from the context *)
  Axiom Ring_inst : Ring Tadd T0 Topp Tmul T1 Teq.
  #[export] Existing Instance Ring_inst.

End RingElementType.

Module Type EqRingElementType (B : BaseType)
<: EqElementType B
  := RingElementType
     with Definition T := B.T
     with Definition Teq := @eq B.T.


(** ** Instances *)

Module RingElementTypeZ
<: RingElementType.
  Include ElementTypeZ.

  Definition T1 : T := 1.
  Definition Tadd := Zplus.
  Definition Topp := Z.opp.
  Definition Tmul := Zmult.
  Hint Unfold T1 Tadd Topp Tmul : T.

  Notation Tsub := (fun x y => Tadd x (Topp y)).
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := Tsub : T_scope.

  #[export] Instance Tadd_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tadd).
  Proof. simp_proper. intros. rewrite H,H0. easy. Qed.

  #[export] Instance Topp_aeq_mor : Proper (Teq ==> Teq) (Topp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Tmul_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tmul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.
  
  Lemma Ring_thy : ring_theory T0 T1 Tadd Tmul Tsub Topp Teq.
  Proof.
    constructor; intros; autounfold with T; auto with zarith.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  #[export] Instance AGroup_inst : AGroup Tadd T0 Topp Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor; try apply Equiv_Teq;
    unfold Tadd,Teq,Topp,T0,T; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Tadd T0 Topp Tmul T1 Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor, Tmul_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,Tmul,T0,T1,T; ring.
  Qed.
  
End RingElementTypeZ.

Module RingElementTypeQ
<: RingElementType.
  Include ElementTypeQ.
  
  Definition T1 : T := 1.
  Definition Tadd := Qplus.
  Definition Topp := Qopp.
  Definition Tmul := Qmult.
  Hint Unfold T1 Tadd Topp Tmul : T.

  Notation Tsub := (fun x y => Tadd x (Topp y)).
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := Tsub : T_scope.

  #[export] Instance Tadd_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Topp_aeq_mor : Proper (Teq ==> Teq) (Topp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Tmul_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tmul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.
  
  Lemma Ring_thy : ring_theory T0 T1 Tadd Tmul Tsub Topp Teq.
  Proof.
    constructor; intros;
      unfold T,Teq,Tadd,Topp,Tmul,T0,T1;
      unfold ElementTypeQ.Teq,ElementTypeQ.T0,ElementTypeQ.T;
      try ring.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  #[export] Instance AGroup_inst : AGroup Tadd T0 Topp Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor; try apply Equiv_Teq;
    unfold Tadd,Teq,Topp,T0,T; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Tadd T0 Topp Tmul T1 Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor, Tmul_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,Tmul,T0,T1,T; ring.
  Qed.
  
End RingElementTypeQ.

Module RingElementTypeQc
<: RingElementType.
  Include ElementTypeQc.

  Definition T1 : T := 1.
  Definition Tadd := Qcplus.
  Definition Topp := Qcopp.
  Definition Tmul := Qcmult.
  Hint Unfold T1 Tadd Topp Tmul : T.
  
  Notation Tsub := (fun x y => Tadd x (Topp y)).
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := Tsub : T_scope.

  #[export] Instance Tadd_aeq_mor : Proper (Teq  ==> Teq ==> Teq) (Tadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Topp_aeq_mor : Proper (Teq ==> Teq) (Topp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Tmul_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tmul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.
  
  Lemma Ring_thy : ring_theory T0 T1 Tadd Tmul Tsub Topp Teq.
  Proof.
    constructor; intros;
      unfold T,Teq,Tadd,Topp,Tmul,T0,T1;
      unfold ElementTypeQc.Teq,ElementTypeQc.T0,ElementTypeQc.T;
      try ring.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  #[export] Instance AGroup_inst : AGroup Tadd T0 Topp Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,T0,T; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Tadd T0 Topp Tmul T1 Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor, Tmul_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,Tmul,T0,T1,T; ring.
  Qed.

End RingElementTypeQc.

Module RingElementTypeR
<: RingElementType.
  Include ElementTypeR.
  
  Definition T1 : T := 1.
  Definition Tadd := Rplus.
  Definition Topp := Ropp.
  Definition Tmul := Rmult.
  Hint Unfold T1 Tadd Topp Tmul : T.
  
  Notation Tsub := (fun x y => Tadd x (Topp y)).
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := Tsub : T_scope.

  #[export] Instance Tadd_aeq_mor : Proper (Teq  ==> Teq ==> Teq) (Tadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Topp_aeq_mor : Proper (Teq ==> Teq) (Topp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Tmul_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tmul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  Lemma Ring_thy : ring_theory T0 T1 Tadd Tmul Tsub Topp Teq.
  Proof.
    constructor; intros;
      unfold T,Teq,Tadd,Topp,Tmul,T0,T1;
      unfold ElementTypeR.Teq,ElementTypeR.T0,ElementTypeR.T;
      try ring.
  Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.
  
  #[export] Instance AGroup_inst : AGroup Tadd T0 Topp Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,T0,T; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Tadd T0 Topp Tmul T1 Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor, Tmul_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,Tmul,T0,T1,T; ring.
  Qed.

End RingElementTypeR.


Module RingElementTypeC
<: RingElementType.
  Include ElementTypeC.

  Definition T1 : T := 1.
  Definition Tadd := Cadd.
  Definition Topp := Copp.
  Definition Tmul := Cmul.
  (** Note that, this explicit annotation is must, 
      otherwise, the ring has no effect. (because C and T are different) *)
  (* Definition Tadd : T -> T -> T := fun a b => Cadd a b. *)
  (* Definition Topp : T -> T := fun a => Copp a. *)
  (* Definition Tmul : T -> T -> T := fun a b => Cmul a b. *)
  Hint Unfold T1 Tadd Topp Tmul : T.
  
  Notation Tsub := (fun x y => Tadd x (Topp y)).
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := Tsub : T_scope.

  #[export] Instance Tadd_aeq_mor : Proper (Teq  ==> Teq ==> Teq) (Tadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Topp_aeq_mor : Proper (Teq ==> Teq) (Topp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Tmul_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tmul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  Lemma Ring_thy : ring_theory T0 T1 Tadd Tmul Tsub Topp Teq.
  Proof.
    constructor; intros; autounfold with T; ring.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  #[export] Instance AGroup_inst : AGroup Tadd T0 Topp Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor; try apply Equiv_Teq;
    autounfold with T; try ring.
  Qed.

  #[export] Instance Ring_inst : Ring Tadd T0 Topp Tmul T1 Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor, Tmul_aeq_mor; try apply Equiv_Teq;
      autounfold with T; ring.
  Qed.

End RingElementTypeC.


Module RingElementTypeRFun
<: RingElementType.
  Include ElementTypeRFun.
  
  Definition T1 : T := fone.
  Definition Tadd := fadd.
  Definition Topp := fopp.
  Definition Tmul := fmul.
  Hint Unfold T1 Tadd Topp Tmul : T.
  
  Notation Tsub := (fun x y => Tadd x (Topp y)).
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := Tsub : T_scope.

  #[export] Instance Tadd_aeq_mor : Proper (Teq  ==> Teq ==> Teq) (Tadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Topp_aeq_mor : Proper (Teq ==> Teq) (Topp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Tmul_aeq_mor : Proper (Teq ==> Teq ==> Teq) (Tmul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  Lemma Ring_thy : ring_theory T0 T1 Tadd Tmul Tsub Topp Teq.
  Proof.
    constructor; intros;
      unfold T,Teq,Tadd,Topp,Tmul,T0,T1;
      unfold ElementTypeRFun.Teq,ElementTypeRFun.T0,ElementTypeRFun.T;
      try ring.
  Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.
  
  #[export] Instance AGroup_inst : AGroup Tadd T0 Topp Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,T0,T; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Tadd T0 Topp Tmul T1 Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor, Tmul_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,Tmul,T0,T1,T; ring.
  Qed.

End RingElementTypeRFun.


Module RingElementTypeFun (I O : RingElementType) <: RingElementType.
  Export I O.
  Add Ring Ring_thy_inst_i : I.Ring_thy.
  Add Ring Ring_thy_inst_o : O.Ring_thy.
  
  Include (ElementTypeFun I O).

  Definition T1 : T.
    refine (exist _ (fun _ => O.T1) _).
    simp_proper. intros. destruct (O.Equiv_Teq). reflexivity.
  Defined.

  Definition Tadd : T -> T -> T.
    cbv. intros [f Pf] [g Pg].
    refine (exist _ (fun x : I.T => O.Tadd (f x) (g x)) _).
    intros.
    pose proof (O.Tadd_aeq_mor). apply H0. apply Pf; easy. apply Pg; easy.
  Defined.
    
  Definition Topp : T -> T.
    cbv. intros [f Pf].
    refine (exist _ (fun x : I.T => O.Topp (f x)) _).
    intros.
    pose proof (O.Topp_aeq_mor). apply H0. apply Pf; easy.
  Defined.

  Definition Tmul : T -> T -> T.
    cbv. intros [f Pf] [g Pg].
    refine (exist _ (fun x : I.T => O.Tmul (f x) (g x)) _).
    intros.
    pose proof (O.Tmul_aeq_mor). apply H0. apply Pf; easy. apply Pg; easy.
  Defined.

  Notation Tsub := (fun x y => Tadd x (Topp y)).

  #[export] Instance Tadd_aeq_mor : Proper (Teq  ==> Teq ==> Teq) (Tadd).
  Proof.
    simp_proper.
    intros [x Px] [y Py] H1 [x0 Px0] [y0 Py0] H2.
    cbv in *. intros. apply O.Tadd_aeq_mor; auto.
  Qed.

  #[export] Instance Topp_aeq_mor : Proper (Teq ==> Teq) (Topp).
  Proof.
    simp_proper. intros [x Px] [y Py] H1.
    cbv in *. intros. apply O.Topp_aeq_mor; auto.
  Qed.

  #[export] Instance Tmul_aeq_mor : Proper (Teq  ==> Teq ==> Teq) (Tmul).
  Proof.
    simp_proper. intros [x Px] [y Py] H1 [x0 Px0] [y0 Py0] H2.
    cbv in *. intros. apply O.Tmul_aeq_mor; auto.
  Qed.

  Lemma Ring_thy : ring_theory T0 T1 Tadd Tmul Tsub Topp Teq.
  Proof.
    destruct (O.Ring_thy).
    constructor; intros; cbv; intros;
      repeat match goal with | x:T |- _ => destruct x end; auto.
  Qed.

  #[export] Instance AGroup_inst : AGroup Tadd T0 Topp Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,T0,T;
      repeat match goal with a : ?A |- _ => destruct a end; intros; simpl; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Tadd T0 Topp Tmul T1 Teq.
  Proof.
    repeat constructor; intros;
      auto using Tadd_aeq_mor, Topp_aeq_mor, Tmul_aeq_mor; try apply Equiv_Teq;
      unfold Tadd,Teq,Topp,Tmul,T0,T1,T;
      repeat match goal with a : ?A |- _ => destruct a end; intros; simpl; ring.
  Qed.

End RingElementTypeFun.


Module RingElementTypeTest.
  Import FunctionalExtensionality.
  Import RingElementTypeQ.
  Import RingElementTypeR.
  
  Module Import RingElementTypeFunEx1 :=
    RingElementTypeFun RingElementTypeQ RingElementTypeR.
  Definition f : T.
    refine (exist _ (fun i:Q => Q2R i + R1) _).
    simp_proper. intros. rewrite H. easy.
  Defined.

  Definition g : T.
    refine (exist _ (fun i:Q => Q2R (i+1)) _).
    simp_proper. intros. rewrite H. easy.
  Defined.

  Goal (f == g)%T.
  Proof.
    unfold f,g,Teq. hnf. cbn. intros. rewrite Qreals.Q2R_plus.
    hnf. f_equal. cbv. auto with real.
  Qed.
  
End RingElementTypeTest.



(* ######################################################################### *)
(** * Element with field structure *)

(** ** Type of Element with field structure *)

Module Type FieldElementType <: RingElementType.
  Include RingElementType.
  Open Scope T_scope.

  Parameter Tinv : T -> T.

  Notation Tdiv := (fun x y => Tmul x (Tinv y)).
  Notation "/ a" := (Tinv a) : T_scope.
  Infix "/" := Tdiv : T_scope.

  Axiom Tinv_aeq_mor : Proper (Teq ==> Teq) Tinv.
  #[export] Existing Instance Tinv_aeq_mor.

  (** 1 <> 0. *)
  Axiom T1_neq_T0 : ~(T1 == T0)%T.
  
  Axiom Field_thy: field_theory T0 T1 Tadd Tmul Tsub Topp Tdiv Tinv Teq.
  (* Add Field Field_thy_inst : Field_thy. *)

  (** A Field structure can be derived from the context *)

  Axiom Field_inst : Field Tadd T0 Topp Tmul T1 Tinv Teq.
  #[export] Existing Instance Field_inst.

End FieldElementType.


(** ** Instances *)

Module FieldElementTypeQ <: FieldElementType.
  Include RingElementTypeQ.

  Definition Tinv := Qinv.
  Hint Unfold Tinv : T.

  Notation Tdiv := (fun x y => Tmul x (Tinv y)).

  #[export] Instance Tinv_aeq_mor : Proper (Teq ==> Teq) Tinv.
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  Lemma T1_neq_T0 : ~(T1 == T0)%T.
  Proof. intro. cbv in *. inv H. Qed.
    
  Lemma Field_thy: field_theory T0 T1 Tadd Tmul Tsub Topp Tdiv Tinv Teq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy.
    unfold Tmul,Tinv,T1,Teq. unfold ElementTypeQ.Teq. field. auto.
  Qed.

  (* Add Field Field_thy_inst : Field_thy. *)
  
  #[export] Instance Field_inst : Field Tadd T0 Topp Tmul T1 Tinv Teq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Tmul,Tinv,Teq,T1,T. field. auto.
    apply T1_neq_T0. apply Tinv_aeq_mor.
  Qed.

End FieldElementTypeQ.

Module FieldElementTypeQc
<: FieldElementType.
  Include RingElementTypeQc.

  Definition Tinv := Qcinv.
  Hint Unfold Tinv : T.
  
  Notation Tdiv := (fun x y => Tmul x (Tinv y)).

  #[export] Instance Tinv_aeq_mor : Proper (Teq ==> Teq) Tinv.
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  Lemma T1_neq_T0 : ~(T1 == T0)%T.
  Proof. intro. cbv in *. inv H. Qed.
  
  Lemma Field_thy: field_theory T0 T1 Tadd Tmul Tsub Topp Tdiv Tinv Teq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy.
    unfold Tmul,Tinv,T1,Teq. unfold ElementTypeQc.Teq,ElementTypeQc.T. field. auto.
  Qed.

  (* Bug: when publish the project to opam, CI report error in ocaml4.07.1 as follows,

Error: Illegal application: 
The term "@fieldTinvProper" of type
 "forall (A : Type) (Tadd : T -> T -> T) (T0 : T) (Topp : T -> T) (Tmul : T -> T -> T) 
    (T1 : T) (Tinv : T -> T) (Teq : T -> T -> Prop),
  Field Tadd T0 Topp Tmul T1 Tinv Teq -> Proper (Teq ==> Teq) Tinv"
cannot be applied to the terms
 "A" : "Type"
 "Qcplus" : "Qc -> Qc -> Qc"
 "Q2Qc 0" : "Qc"
 "Qcopp" : "Qc -> Qc"
 "Qcmult" : "Qc -> Qc -> Qc"
 "1" : "Qc"
 "Tinv" : "Qc -> Qc"
 "Teq" : "relation T"
 "Field_Qc" : "Field Qcplus (Q2Qc 0) Qcopp Qcmult 1 Qcinv eq"
The 1st term has type "Type@{A.u0}" which should be coercible to "Type@{Field.u0}".
    
    But I don't know why?
    just need comment this declaration.
*)
  (* Check @fieldTinvProper Qc Qcplus (Q2Qc (Qmake Z0 xH)) *)
  (*   Qcopp Qcmult (Q2Qc (Qmake (Zpos xH) xH)) Tinv Teq. *)
    
  (* Add Field Field_thy_inst : Field_thy. *)
  
  #[export] Instance Field_inst : Field Tadd T0 Topp Tmul T1 Tinv Teq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Tmul,Tinv,Teq,T1,T. field. auto.
    apply T1_neq_T0. apply Tinv_aeq_mor.
  Qed.

End FieldElementTypeQc.

Module FieldElementTypeR
<: FieldElementType.
  Include RingElementTypeR.
  
  Definition Tinv := Rinv.
  Hint Unfold Tinv : T.
  
  Notation Tdiv := (fun x y => Tmul x (Tinv y)).

  #[export] Instance Tinv_aeq_mor : Proper (Teq ==> Teq) Tinv.
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  Lemma T1_neq_T0 : ~(T1 == T0)%T.
  Proof. cbv in *. auto with real. Qed.

  Lemma Field_thy: field_theory T0 T1 Tadd Tmul Tsub Topp Tdiv Tinv Teq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy. apply T1_neq_T0.
    unfold Tmul,Tinv,T1,Teq. unfold ElementTypeR.Teq,ElementTypeR.T. field. auto.
  Qed.

  (* Add Field Field_thy_inst : Field_thy. *)
  
  #[export] Instance Field_inst : Field Tadd T0 Topp Tmul T1 Tinv Teq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Tmul,Tinv,Teq,T1,T. field. auto.
    apply T1_neq_T0. apply Tinv_aeq_mor.
  Qed.
  
End FieldElementTypeR.

Module FieldElementTypeC
<: FieldElementType.
  Include RingElementTypeC.
  
  Definition Tinv := Cinv.
  Hint Unfold Tinv : T.
  
  Notation Tdiv := (fun x y => Tmul x (Tinv y)).

  #[export] Instance Tinv_aeq_mor : Proper (Teq ==> Teq) Tinv.
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  Lemma T1_neq_T0 : ~(T1 == T0)%T.
  Proof. cbv in *. auto with complex. Qed.

  Lemma Field_thy: field_theory T0 T1 Tadd Tmul Tsub Topp Tdiv Tinv Teq.
  Proof.
    constructor; intros; auto with complex; try easy.
    apply Ring_thy. apply Cmul_inv_l. auto.
  Qed.

  (* Add Field Field_thy_inst : Field_thy. *)
  
  #[export] Instance Field_inst : Field Tadd T0 Topp Tmul T1 Tinv Teq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Tmul,Tinv,Teq,T1,T. field. auto.
    apply T1_neq_T0. apply Tinv_aeq_mor.
  Qed.
  
End FieldElementTypeC.

(* Module FieldElementTypeFun (I O : FieldElementType) <: FieldElementType. *)
(*   Include (RingElementTypeFun I O). *)

(*   Definition Tinv : T -> T. *)
(*     cbv. intros [f Pf]. *)
(*     refine (exist _ (fun x : I.T => O.Tinv (f x)) _). *)
(*     constructor. intros. *)
(*     pose proof (O.Resp_Tinv_Teq). apply respectUnary. apply Pf; easy. *)
(*   Defined. *)
  
(*   Notation Tdiv := (fun x y => Tmul x (Tinv y)). *)

  (* Lemma Tinv_aeq_mor : Proper (Teq ==> Teq) Tinv. *)
  (* Proof. *)
  (*   unfold Proper, respectful. intros [x Px] [y Py] H1. *)
  (*   cbv in *. intros. apply O.Resp_Tinv_Teq; auto. *)
  (* Qed. *)
  
(*   (* Import FunctionalExtensionality. *) *)
(*   Lemma T1_neq_T0 : ~(T1 == T0)%T. *)
(*   Proof. cbv in *. intros. specialize (H I.T0). apply O.T1_neq_T0 in H. auto. Qed. *)

(*   Lemma Field_thy: field_theory T0 T1 Tadd Tmul Tsub Topp Tdiv Tinv Teq. *)
(*   Proof. *)
(*     destruct (I.Field_thy), (O.Field_thy). *)
(*     constructor. *)
(*     - apply Ring_thy. *)
(*     - apply T1_neq_T0. *)
(*     - intros. *)
(*       repeat match goal with | x:A |- _ => destruct x end. *)
(*       cbv in *; intros. *)
(*       pose proof (O.Tmul_aeq_mor). *)
(*       pose proof (O.Equiv_Teq). *)
(*       apply H; easy. *)
(*     - intros. *)
(*       repeat match goal with | x:A |- _ => destruct x end. *)
(*       cbv in *; intros. *)
(*       apply Finv_l0. revert a. *)
(*       (* Note that, this is not true. *)
(*          H means: ~(x a1 = 0 /\ x a2 = 0 /\ ...) *)
(*          but we need: x a1 <> 0 /\ x a2 <> 0 /\ ... *)
(*          !!this is not provable. *)
(*        *) *)
(*       admit. *)
(*   Admitted. *)

(* End FieldElementTypeFun. *)

Module FieldElementTypeTest.
  Import FunctionalExtensionality.
  Import FieldElementTypeQ.
  Import FieldElementTypeR.

  (* Include (FieldElementTypeFun FieldElementTypeQ FieldElementTypeR). *)
End FieldElementTypeTest.



(* ######################################################################### *)
(** * Element with field structure and decidable relation *)

(** ** Type of Element with field structure and decidable relation *)

Module Type DecidableFieldElementType
<: FieldElementType
<: DecidableElementType.
  Include FieldElementType.
  Open Scope T_scope.

  Axiom Dec_Teq : Dec Teq.
  #[export] Existing Instance Dec_Teq.
End DecidableFieldElementType.

Module Type EqDecidableFieldElementType (B : BaseType)
<: EqElementType B
<: DecidableFieldElementType
  := DecidableFieldElementType
     with Definition T := B.T
     with Definition Teq := @eq B.T.

(** ** Instances *)

Module DecidableFieldElementTypeQ
<: DecidableFieldElementType.
  Include FieldElementTypeQ.
  Import DecidableElementTypeQ.
  
  #[export] Instance Dec_Teq : Dec Teq.
  Proof. apply Dec_Teq. Qed.
End DecidableFieldElementTypeQ.

Module DecidableFieldElementTypeQc
<: DecidableFieldElementType.
(* <: EqDecidableFieldElementType BaseTypeQc. *) (* needn't do this *)
  Include FieldElementTypeQc.
  Import DecidableElementTypeQc.
  
  #[export] Instance Dec_Teq : Dec Teq.
  Proof. apply Dec_Teq. Qed.
End DecidableFieldElementTypeQc.

Module DecidableFieldElementTypeR
<: DecidableFieldElementType.
  Include FieldElementTypeR.
  Import DecidableElementTypeR.

  #[export] Instance Dec_Teq : Dec Teq.
  Proof. apply Dec_Teq. Qed.
End DecidableFieldElementTypeR.

Module DecidableFieldElementTypeC
<: DecidableFieldElementType.
  Include FieldElementTypeC.
  Import DecidableElementTypeC.

  #[export] Instance Dec_Teq : Dec Teq.
  Proof. apply Dec_Teq. Qed.
End DecidableFieldElementTypeC.
