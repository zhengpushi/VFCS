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
Require Export AlgebraStructure.


(* ######################################################################### *)
(** * Base type *)

(** ** Type of base type *)
Module Type BaseType.
  Parameter A : Type.
End BaseType.

(** ** Instances *)

Module BaseTypeNat <: BaseType.
  Export NatExt.
  Definition A := nat.
  Hint Unfold A : A.
End BaseTypeNat.

Module BaseTypeZ <: BaseType.
  Export ZExt.
  Definition A := Z.
  Hint Unfold A : A.
End BaseTypeZ.

Module BaseTypeQ <: BaseType.
  Export QExt.
  Definition A := Q.
  Hint Unfold A : A.
End BaseTypeQ.

Module BaseTypeQc <: BaseType.
  Export QcExt.
  Definition A := Qc.
  Hint Unfold A : A.
End BaseTypeQc.

Module BaseTypeR <: BaseType.
  Export RExt.
  Definition A := R.
  Hint Unfold A : A.
End BaseTypeR.

Module BaseTypeC <: BaseType.
  Export Complex.
  Definition A := C.
  Hint Unfold A : A.
End BaseTypeC.

Module BaseTypeRFun <: BaseType.
  Export RealFunction.
  Definition A := tpRFun.
  Hint Unfold A : A.
End BaseTypeRFun.

Module BaseTypeFun (A B : BaseType) <: BaseType.
  (* Import Reals. *)
  Definition A := A.A -> B.A.
  Hint Unfold A : A.
End BaseTypeFun.


(* ######################################################################### *)
(** * Element with setoid equality *)

(** ** Type of element *)
Module Type ElementType <: BaseType.
  Parameter A : Type.
  Parameter Aeq : relation A.
  Parameter Azero : A.

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.

  Axiom Equiv_Aeq : Equivalence Aeq.
  #[export] Existing Instance Equiv_Aeq.
End ElementType.


(** ** Type of element which specify the Aeq is eq, used in lots of cases *)
Module Type EqElementType (B : BaseType)
<: ElementType
   with Definition A := B.A
   with Definition Aeq := @eq B.A.
  Definition A := B.A.
  Definition Aeq := @eq B.A.
  
  Parameter Azero : A.
  Axiom Equiv_Aeq : Equivalence Aeq.
  #[export] Existing Instance Equiv_Aeq.
End EqElementType.  

(* Note, these code only works in Coq-8.16, but failed at Coq-8.13,8.14,
   I'm not sure why? *)
(* Module Type EqElementType (B : BaseType) *)
(* <: BaseType *)
(*   := ElementType *)
(*      with Definition A := B.A *)
(*      with Definition Aeq := @eq B.A. *)


(** ** Instances *)
Module ElementTypeNat <: EqElementType BaseTypeNat.
  Export BaseTypeNat.

  Definition A : Type := nat.
  Definition Aeq : relation A := eq.
  Definition Azero : A := 0.
  Hint Unfold A Aeq Azero : A.

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.

  #[export] Instance Equiv_Aeq : Equivalence Aeq.
  Proof. apply eq_equivalence. Qed.
  
End ElementTypeNat.

Module ElementTypeZ <: EqElementType BaseTypeZ.
  Export BaseTypeZ.
  
  Definition A : Type := Z.
  Definition Aeq : relation A := eq.
  Definition Azero : A := 0.
  Hint Unfold A Aeq Azero : A.

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.

  #[export] Instance Equiv_Aeq : Equivalence Aeq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeZ.

(** Tips, this module cannot be a EqElementType *)
Module ElementTypeQ <: ElementType.
  Export BaseTypeQ.
  
  Definition A : Type := Q.
  Definition Aeq : relation A := Qeq.
  Definition Azero : A := 0.
  Hint Unfold A Aeq Azero : A.

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.

  #[export] Instance Equiv_Aeq : Equivalence Aeq.
  Proof. apply Q_Setoid. Qed.
End ElementTypeQ.

Module ElementTypeQc <: EqElementType BaseTypeQc.
  Export BaseTypeQc.
  
  Definition A : Type := Qc.
  Definition Aeq : relation A := eq.
  Definition Azero : A := 0.
  Hint Unfold A Aeq Azero : A.

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.

  #[export] Instance Equiv_Aeq : Equivalence Aeq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeQc.

Module ElementTypeR <: EqElementType BaseTypeR.
  Export BaseTypeR.

  Definition A : Type := R.
  Definition Aeq : relation A := eq.
  Definition Azero : A := 0%R.
  Hint Unfold A Aeq Azero : A.

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.

  #[export] Instance Equiv_Aeq : Equivalence Aeq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeR.

Module ElementTypeC <: EqElementType BaseTypeC.
  Export BaseTypeC.

  Definition A : Type := C.
  Definition Aeq : relation A := eq.
  Definition Azero : A := 0.
  Hint Unfold A Aeq Azero : A.

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.

  #[export] Instance Equiv_Aeq : Equivalence Aeq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeC.

Module ElementTypeRFun <: EqElementType BaseTypeRFun.
  Export BaseTypeRFun.

  Definition A : Type := tpRFun.
  Definition Aeq : relation A := eq.
  Definition Azero : A := fzero.
  Hint Unfold A Aeq Azero : A.

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.

  #[export] Instance Equiv_Aeq : Equivalence Aeq.
  Proof. apply eq_equivalence. Qed.
End ElementTypeRFun.

Module ElementTypeFun (I O : ElementType) <: ElementType.
  Definition A : Type := {f : I.A -> O.A | Proper (I.Aeq ==> O.Aeq) f}.
  Definition Aeq : relation A :=
    fun (f g : A) => forall (a : I.A),
        O.Aeq (proj1_sig f a) (proj1_sig g a).
  Infix "=I=" := I.Aeq (at level 20).
  Infix "=O=" := O.Aeq (at level 20).

  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun a b : A => ~(a == b)) : A_scope.
  
  Definition Azero : A.
    refine (exist _ (fun _ => O.Azero) _).
    simp_proper. intros. destruct (O.Equiv_Aeq). reflexivity.
  Defined.
  
  #[export] Instance Equiv_Aeq : Equivalence Aeq.
  Proof.
    destruct (I.Equiv_Aeq), (O.Equiv_Aeq).
    constructor; cbv; intros; try easy.
    destruct x. specialize (H a). specialize (H0 a). rewrite H0 in H. auto.
  Qed.
End ElementTypeFun.

Module ElementType_Test.
  
  Import ElementTypeNat ElementTypeR.
  Module Import ElementTypeFunEx1 := ElementTypeFun ElementTypeNat ElementTypeR.

  Definition f : A.
    refine (exist _ (fun i => match i with 0%nat => 1 | 1%nat => 2 | _ => 1 end) _).
    simp_proper. intros. rewrite H. reflexivity.
  Defined.
  Definition g : A.
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

  Axiom Dec_Aeq : Dec Aeq.
  #[export] Existing Instance Dec_Aeq.
End DecidableElementType.

Module Type EqDecidableElementType (B : BaseType)
<: EqElementType B
  := DecidableElementType
     with Definition A := B.A
     with Definition Aeq := @eq B.A.


(** ** Instances *)
Module DecidableElementTypeNat
<: DecidableElementType.
  Include ElementTypeNat.

  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. constructor. apply Nat.eq_dec. Qed.
End DecidableElementTypeNat.

Module DecidableElementTypeZ
<: DecidableElementType.
  Include ElementTypeZ.

  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. constructor. apply Z.eq_dec. Qed.
End DecidableElementTypeZ.

Module DecidableElementTypeQ
<: DecidableElementType.
  Include ElementTypeQ.

  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. constructor. apply Qeq_dec. Qed.
End DecidableElementTypeQ.

Module DecidableElementTypeQc
<: DecidableElementType.
  Include ElementTypeQc.

  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. constructor. apply Qc_eq_dec. Qed.
End DecidableElementTypeQc.

Module DecidableElementTypeR
<: DecidableElementType.
  Include ElementTypeR.

  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. constructor. apply Req_EM_T. Qed.
End DecidableElementTypeR.

Module DecidableElementTypeC
<: DecidableElementType.
  Include ElementTypeC.

  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. apply Dec_Complex. Qed.
End DecidableElementTypeC.


(* ######################################################################### *)
(** * Element with ring structure *)

(** ** Type of Element with ring structure *)
Module Type RingElementType <: ElementType.
  Include ElementType.
  Open Scope A_scope.

  Parameter Aone : A.
  Parameter Aadd Amul : A -> A -> A.
  Parameter Aopp : A -> A.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  (** Use these lemmas, we can replace "Add Morphism ..." with "Existing Morphism" *)
  Axiom Aadd_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Aadd).
  Axiom Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Axiom Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).

  #[export] Existing Instance Aadd_aeq_mor.
  #[export] Existing Instance Aopp_aeq_mor.
  #[export] Existing Instance Amul_aeq_mor.

  Axiom Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.

  (** A Group structure can be derived from the context *)
  Axiom AGroup_inst : AGroup Aadd Azero Aopp Aeq.
  #[export] Existing Instance AGroup_inst.

  (** A Ring structure can be derived from the context *)
  Axiom Ring_inst : Ring Aadd Azero Aopp Amul Aone Aeq.
  #[export] Existing Instance Ring_inst.

End RingElementType.

Module Type EqRingElementType (B : BaseType)
<: EqElementType B
  := RingElementType
     with Definition A := B.A
     with Definition Aeq := @eq B.A.


(** ** Instances *)

Module RingElementTypeZ
<: RingElementType.
  Include ElementTypeZ.

  Definition Aone : A := 1.
  Definition Aadd := Zplus.
  Definition Aopp := Z.opp.
  Definition Amul := Zmult.
  Hint Unfold Aone Aadd Aopp Amul : A.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance Aadd_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Aadd).
  Proof. simp_proper. intros. rewrite H,H0. easy. Qed.

  #[export] Instance Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.
  
  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros; autounfold with A; auto with zarith.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
    unfold Aadd,Aeq,Aopp,Azero,A; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Aadd Azero Aopp Amul Aone Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,Azero,Aone,A; ring.
  Qed.
  
End RingElementTypeZ.

Module RingElementTypeQ
<: RingElementType.
  Include ElementTypeQ.
  
  Definition Aone : A := 1.
  Definition Aadd := Qplus.
  Definition Aopp := Qopp.
  Definition Amul := Qmult.
  Hint Unfold Aone Aadd Aopp Amul : A.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance Aadd_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Aadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.
  
  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      unfold A,Aeq,Aadd,Aopp,Amul,Azero,Aone;
      unfold ElementTypeQ.Aeq,ElementTypeQ.Azero,ElementTypeQ.A;
      try ring.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
    unfold Aadd,Aeq,Aopp,Azero,A; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Aadd Azero Aopp Amul Aone Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,Azero,Aone,A; ring.
  Qed.
  
End RingElementTypeQ.

Module RingElementTypeQc
<: RingElementType.
  Include ElementTypeQc.

  Definition Aone : A := 1.
  Definition Aadd := Qcplus.
  Definition Aopp := Qcopp.
  Definition Amul := Qcmult.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance Aadd_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Aadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.
  
  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      unfold A,Aeq,Aadd,Aopp,Amul,Azero,Aone;
      unfold ElementTypeQc.Aeq,ElementTypeQc.Azero,ElementTypeQc.A;
      try ring.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Azero,A; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Aadd Azero Aopp Amul Aone Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,Azero,Aone,A; ring.
  Qed.

End RingElementTypeQc.

Module RingElementTypeR
<: RingElementType.
  Include ElementTypeR.
  
  Definition Aone : A := 1.
  Definition Aadd := Rplus.
  Definition Aopp := Ropp.
  Definition Amul := Rmult.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance Aadd_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Aadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      unfold A,Aeq,Aadd,Aopp,Amul,Azero,Aone;
      unfold ElementTypeR.Aeq,ElementTypeR.Azero,ElementTypeR.A;
      try ring.
  Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.
  
  #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Azero,A; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Aadd Azero Aopp Amul Aone Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,Azero,Aone,A; ring.
  Qed.

End RingElementTypeR.


Module RingElementTypeC
<: RingElementType.
  Include ElementTypeC.

  Definition Aone : A := 1.
  Definition Aadd := Cadd.
  Definition Aopp := Copp.
  Definition Amul := Cmul.
  (** Note that, this explicit annotation is must, 
      otherwise, the ring has no effect. (because C and A are different) *)
  (* Definition Aadd : A -> A -> A := fun a b => Cadd a b. *)
  (* Definition Aopp : A -> A := fun a => Copp a. *)
  (* Definition Amul : A -> A -> A := fun a b => Cmul a b. *)
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance Aadd_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Aadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros; autounfold with A; ring.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
    autounfold with A; try ring.
  Qed.

  #[export] Instance Ring_inst : Ring Aadd Azero Aopp Amul Aone Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      autounfold with A; ring.
  Qed.

End RingElementTypeC.


Module RingElementTypeRFun
<: RingElementType.
  Include ElementTypeRFun.
  
  Definition Aone : A := fone.
  Definition Aadd := fadd.
  Definition Aopp := fopp.
  Definition Amul := fmul.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance Aadd_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Aadd).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  #[export] Instance Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  #[export] Instance Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof. simp_proper. intros. rewrite H, H0. easy. Qed.

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      unfold A,Aeq,Aadd,Aopp,Amul,Azero,Aone;
      unfold ElementTypeRFun.Aeq,ElementTypeRFun.Azero,ElementTypeRFun.A;
      try ring.
  Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.
  
  #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Azero,A; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Aadd Azero Aopp Amul Aone Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,Azero,Aone,A; ring.
  Qed.

End RingElementTypeRFun.


Module RingElementTypeFun (I O : RingElementType) <: RingElementType.
  Export I O.
  Add Ring Ring_thy_inst_i : I.Ring_thy.
  Add Ring Ring_thy_inst_o : O.Ring_thy.
  
  Include (ElementTypeFun I O).

  Definition Aone : A.
    refine (exist _ (fun _ => O.Aone) _).
    simp_proper. intros. destruct (O.Equiv_Aeq). reflexivity.
  Defined.

  Definition Aadd : A -> A -> A.
    cbv. intros [f Pf] [g Pg].
    refine (exist _ (fun x : I.A => O.Aadd (f x) (g x)) _).
    intros.
    pose proof (O.Aadd_aeq_mor). apply H0. apply Pf; easy. apply Pg; easy.
  Defined.
    
  Definition Aopp : A -> A.
    cbv. intros [f Pf].
    refine (exist _ (fun x : I.A => O.Aopp (f x)) _).
    intros.
    pose proof (O.Aopp_aeq_mor). apply H0. apply Pf; easy.
  Defined.

  Definition Amul : A -> A -> A.
    cbv. intros [f Pf] [g Pg].
    refine (exist _ (fun x : I.A => O.Amul (f x) (g x)) _).
    intros.
    pose proof (O.Amul_aeq_mor). apply H0. apply Pf; easy. apply Pg; easy.
  Defined.

  Notation Asub := (fun x y => Aadd x (Aopp y)).

  #[export] Instance Aadd_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Aadd).
  Proof.
    simp_proper.
    intros [x Px] [y Py] H1 [x0 Px0] [y0 Py0] H2.
    cbv in *. intros. apply O.Aadd_aeq_mor; auto.
  Qed.

  #[export] Instance Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof.
    simp_proper. intros [x Px] [y Py] H1.
    cbv in *. intros. apply O.Aopp_aeq_mor; auto.
  Qed.

  #[export] Instance Amul_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Amul).
  Proof.
    simp_proper. intros [x Px] [y Py] H1 [x0 Px0] [y0 Py0] H2.
    cbv in *. intros. apply O.Amul_aeq_mor; auto.
  Qed.

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.
  Proof.
    destruct (O.Ring_thy).
    constructor; intros; cbv; intros;
      repeat match goal with | x:A |- _ => destruct x end; auto.
  Qed.

  #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Azero,A;
      repeat match goal with a : ?A |- _ => destruct a end; intros; simpl; ring.
  Qed.

  #[export] Instance Ring_inst : Ring Aadd Azero Aopp Amul Aone Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,Azero,Aone,A;
      repeat match goal with a : ?A |- _ => destruct a end; intros; simpl; ring.
  Qed.

End RingElementTypeFun.


Module RingElementTypeTest.
  Import FunctionalExtensionality.
  Import RingElementTypeQ.
  Import RingElementTypeR.
  
  Module Import RingElementTypeFunEx1 :=
    RingElementTypeFun RingElementTypeQ RingElementTypeR.
  Definition f : A.
    refine (exist _ (fun i:Q => Q2R i + R1) _).
    simp_proper. intros. rewrite H. easy.
  Defined.

  Definition g : A.
    refine (exist _ (fun i:Q => Q2R (i+1)) _).
    simp_proper. intros. rewrite H. easy.
  Defined.

  Goal (f == g)%A.
  Proof.
    unfold f,g,Aeq. hnf. cbn. intros. rewrite Qreals.Q2R_plus.
    hnf. f_equal. cbv. auto with real.
  Qed.
  
End RingElementTypeTest.



(* ######################################################################### *)
(** * Element with field structure *)

(** ** Type of Element with field structure *)

Module Type FieldElementType <: RingElementType.
  Include RingElementType.
  Open Scope A_scope.

  Parameter Ainv : A -> A.

  Notation Adiv := (fun x y => Amul x (Ainv y)).
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := Adiv : A_scope.

  Axiom Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  #[export] Existing Instance Ainv_aeq_mor.

  (** 1 <> 0. *)
  Axiom Aone_neq_Azero : ~(Aone == Azero)%A.
  
  Axiom Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Aeq.
  (* Add Field Field_thy_inst : Field_thy. *)

  (** A Field structure can be derived from the context *)

  Axiom Field_inst : Field Aadd Azero Aopp Amul Aone Ainv Aeq.
  #[export] Existing Instance Field_inst.

End FieldElementType.


(** ** Instances *)

Module FieldElementTypeQ <: FieldElementType.
  Include RingElementTypeQ.

  Definition Ainv := Qinv.
  Hint Unfold Ainv : A.

  Notation Adiv := (fun x y => Amul x (Ainv y)).

  #[export] Instance Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  Lemma Aone_neq_Azero : ~(Aone == Azero)%A.
  Proof. intro. cbv in *. inv H. Qed.
    
  Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Aeq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy.
    unfold Amul,Ainv,Aone,Aeq. unfold ElementTypeQ.Aeq. field. auto.
  Qed.

  (* Add Field Field_thy_inst : Field_thy. *)
  
  #[export] Instance Field_inst : Field Aadd Azero Aopp Amul Aone Ainv Aeq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Amul,Ainv,Aeq,Aone,A. field. auto.
    apply Aone_neq_Azero. apply Ainv_aeq_mor.
  Qed.

End FieldElementTypeQ.

Module FieldElementTypeQc
<: FieldElementType.
  Include RingElementTypeQc.

  Definition Ainv := Qcinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  #[export] Instance Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  Lemma Aone_neq_Azero : ~(Aone == Azero)%A.
  Proof. intro. cbv in *. inv H. Qed.
  
  Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Aeq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy.
    unfold Amul,Ainv,Aone,Aeq. unfold ElementTypeQc.Aeq,ElementTypeQc.A. field. auto.
  Qed.

  (* Bug: when publish the project to opam, CI report error in ocaml4.07.1 as follows,

Error: Illegal application: 
The term "@fieldAinvProper" of type
 "forall (A : Type) (Aadd : A -> A -> A) (Azero : A) (Aopp : A -> A) (Amul : A -> A -> A) 
    (Aone : A) (Ainv : A -> A) (Aeq : A -> A -> Prop),
  Field Aadd Azero Aopp Amul Aone Ainv Aeq -> Proper (Aeq ==> Aeq) Ainv"
cannot be applied to the terms
 "A" : "Type"
 "Qcplus" : "Qc -> Qc -> Qc"
 "Q2Qc 0" : "Qc"
 "Qcopp" : "Qc -> Qc"
 "Qcmult" : "Qc -> Qc -> Qc"
 "1" : "Qc"
 "Ainv" : "Qc -> Qc"
 "Aeq" : "relation A"
 "Field_Qc" : "Field Qcplus (Q2Qc 0) Qcopp Qcmult 1 Qcinv eq"
The 1st term has type "Type@{A.u0}" which should be coercible to "Type@{Field.u0}".
    
    But I don't know why?
    just need comment this declaration.
*)
  (* Check @fieldAinvProper Qc Qcplus (Q2Qc (Qmake Z0 xH)) *)
  (*   Qcopp Qcmult (Q2Qc (Qmake (Zpos xH) xH)) Ainv Aeq. *)
    
  (* Add Field Field_thy_inst : Field_thy. *)
  
  #[export] Instance Field_inst : Field Aadd Azero Aopp Amul Aone Ainv Aeq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Amul,Ainv,Aeq,Aone,A. field. auto.
    apply Aone_neq_Azero. apply Ainv_aeq_mor.
  Qed.

End FieldElementTypeQc.

Module FieldElementTypeR
<: FieldElementType.
  Include RingElementTypeR.
  
  Definition Ainv := Rinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  #[export] Instance Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  Lemma Aone_neq_Azero : ~(Aone == Azero)%A.
  Proof. cbv in *. auto with real. Qed.

  Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Aeq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy. apply Aone_neq_Azero.
    unfold Amul,Ainv,Aone,Aeq. unfold ElementTypeR.Aeq,ElementTypeR.A. field. auto.
  Qed.

  (* Add Field Field_thy_inst : Field_thy. *)
  
  #[export] Instance Field_inst : Field Aadd Azero Aopp Amul Aone Ainv Aeq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Amul,Ainv,Aeq,Aone,A. field. auto.
    apply Aone_neq_Azero. apply Ainv_aeq_mor.
  Qed.
  
End FieldElementTypeR.

Module FieldElementTypeC
<: FieldElementType.
  Include RingElementTypeC.
  
  Definition Ainv := Cinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  #[export] Instance Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  Proof. simp_proper. intros. rewrite H. easy. Qed.

  Lemma Aone_neq_Azero : ~(Aone == Azero)%A.
  Proof. cbv in *. auto with complex. Qed.

  Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Aeq.
  Proof.
    constructor; intros; auto with complex; try easy.
    apply Ring_thy. apply Cmul_inv_l. auto.
  Qed.

  (* Add Field Field_thy_inst : Field_thy. *)
  
  #[export] Instance Field_inst : Field Aadd Azero Aopp Amul Aone Ainv Aeq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Amul,Ainv,Aeq,Aone,A. field. auto.
    apply Aone_neq_Azero. apply Ainv_aeq_mor.
  Qed.
  
End FieldElementTypeC.

(* Module FieldElementTypeFun (I O : FieldElementType) <: FieldElementType. *)
(*   Include (RingElementTypeFun I O). *)

(*   Definition Ainv : A -> A. *)
(*     cbv. intros [f Pf]. *)
(*     refine (exist _ (fun x : I.A => O.Ainv (f x)) _). *)
(*     constructor. intros. *)
(*     pose proof (O.Resp_Ainv_Aeq). apply respectUnary. apply Pf; easy. *)
(*   Defined. *)
  
(*   Notation Adiv := (fun x y => Amul x (Ainv y)). *)

  (* Lemma Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv. *)
  (* Proof. *)
  (*   unfold Proper, respectful. intros [x Px] [y Py] H1. *)
  (*   cbv in *. intros. apply O.Resp_Ainv_Aeq; auto. *)
  (* Qed. *)
  
(*   (* Import FunctionalExtensionality. *) *)
(*   Lemma Aone_neq_Azero : ~(Aone == Azero)%A. *)
(*   Proof. cbv in *. intros. specialize (H I.Azero). apply O.Aone_neq_Azero in H. auto. Qed. *)

(*   Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Aeq. *)
(*   Proof. *)
(*     destruct (I.Field_thy), (O.Field_thy). *)
(*     constructor. *)
(*     - apply Ring_thy. *)
(*     - apply Aone_neq_Azero. *)
(*     - intros. *)
(*       repeat match goal with | x:A |- _ => destruct x end. *)
(*       cbv in *; intros. *)
(*       pose proof (O.Amul_aeq_mor). *)
(*       pose proof (O.Equiv_Aeq). *)
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
  Open Scope A_scope.

  Axiom Dec_Aeq : Dec Aeq.
  #[export] Existing Instance Dec_Aeq.
End DecidableFieldElementType.

Module Type EqDecidableFieldElementType (B : BaseType)
<: EqElementType B
<: DecidableFieldElementType
  := DecidableFieldElementType
     with Definition A := B.A
     with Definition Aeq := @eq B.A.

(** ** Instances *)

Module DecidableFieldElementTypeQ
<: DecidableFieldElementType.
  Include FieldElementTypeQ.
  Import DecidableElementTypeQ.
  
  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. apply Dec_Aeq. Qed.
End DecidableFieldElementTypeQ.

Module DecidableFieldElementTypeQc
<: DecidableFieldElementType.
(* <: EqDecidableFieldElementType BaseTypeQc. *) (* needn't do this *)
  Include FieldElementTypeQc.
  Import DecidableElementTypeQc.
  
  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. apply Dec_Aeq. Qed.
End DecidableFieldElementTypeQc.

Module DecidableFieldElementTypeR
<: DecidableFieldElementType.
  Include FieldElementTypeR.
  Import DecidableElementTypeR.

  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. apply Dec_Aeq. Qed.
End DecidableFieldElementTypeR.

Module DecidableFieldElementTypeC
<: DecidableFieldElementType.
  Include FieldElementTypeC.
  Import DecidableElementTypeC.

  #[export] Instance Dec_Aeq : Dec Aeq.
  Proof. apply Dec_Aeq. Qed.
End DecidableFieldElementTypeC.
