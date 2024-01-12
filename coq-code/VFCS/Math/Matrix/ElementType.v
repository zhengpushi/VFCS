(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Type of Matrix Element
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. Element type is orgainized to several levels
  * ElementType
  * OrderedElementType
  * MonoidElementType, based on ElementType.
  * RingElementType, based on MonoidElementType.
  * OrderedRingElementType, based on RingElementType + OrderedElementType
  * FieldElementType, based on RingElementType.
  * OrderedFieldElementType, based on FieldElementType + OrderedElementType.

  2. Future plan:
  * SemiRingElementType.
    Because, we can define `add` and `mul` on `nat` type, 
    such that `vcmul` and `vdot` could be defined on natural numbers.
*)

Require NatExt ZExt QExt QcExt RExt RealFunction Complex.
Require Export Hierarchy.



(* ######################################################################### *)
(** * ElementType *)

(** A type with decidable equality and zero element *)
Module Type ElementType.
  Parameter A : Type.
  Parameter Azero : A.

  Axiom AeqDec : Dec (@eq A).
  #[export] Existing Instance AeqDec.
End ElementType.


(** ** Instances *)
Module ElementTypeNat <: ElementType.
  Export NatExt.
  Definition A : Type := nat.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply nat_eq_Dec. Qed.
End ElementTypeNat.

Module ElementTypeZ <: ElementType.
  Export ZExt.
  Definition A : Type := Z.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Z_eq_Dec. Qed.
End ElementTypeZ.

Module ElementTypeQ <: ElementType.
  Export QExt.
  Definition A : Type := Q.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Q_eq_Dec. Qed.
End ElementTypeQ.

Module ElementTypeQc <: ElementType.
  Export QcExt.
  Definition A : Type := Qc.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Qc_eq_Dec. Qed.
End ElementTypeQc.

Module ElementTypeR <: ElementType.
  Export RExt.
  Definition A : Type := R.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply R_eq_Dec. Qed.
End ElementTypeR.

Module ElementTypeC <: ElementType.
  Export Complex.
  Definition A : Type := C.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Complex_eq_Dec. Qed.
End ElementTypeC.

Module ElementTypeRFun <: ElementType.
  Export RealFunction.
  Definition A : Type := tpRFun.
  Definition Azero : A := fzero.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. constructor. intros a b. unfold tpRFun in *.
         (* rewrite (functional_extensionality a b). *)
  Admitted.
End ElementTypeRFun.

Module ElementTypeFun (I O : ElementType) <: ElementType.
  Definition A : Type := I.A -> O.A.
  Definition Azero : A := fun _ => O.Azero.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. constructor. intros a b. unfold A in *.
  Admitted.
End ElementTypeFun.

Module ElementType_Test.
  Import ElementTypeNat ElementTypeR.
  Module Import ElementTypeFunEx1 :=
    ElementTypeFun ElementTypeNat ElementTypeR.

  Definition f : A := fun i => match i with 0%nat => 1 | 1%nat => 2 | _ => 1 end.
  Definition g : A := fun i => match i with 1%nat => 2 | _ => 1 end.

  Goal f = g.
  Proof. cbv. intros. auto. Qed.
End ElementType_Test.



(* ######################################################################### *)
(** * OrderedElementType *)

(** An extended `ElementType` equipped with order relation *)
Module Type OrderedElementType <: ElementType.
  Include ElementType.
  
  Parameter Ale Alt : A -> A -> Prop.

  Axiom AleDec : Dec Ale.
  #[export] Existing Instance AleDec.
  
  Axiom AltDec : Dec Alt.
  #[export] Existing Instance AltDec.

  Axiom Ale_refl : forall a : A, Ale a a.
  
End OrderedElementType.

(** ** Instances *)
Module OrderedElementTypeNat <: OrderedElementType.
  Include ElementTypeNat.

  Definition Ale := Nat.le.
  Definition Alt := Nat.lt.
  Hint Unfold Ale Alt : A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply nat_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply nat_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply nat_le_refl. Qed.
End OrderedElementTypeNat.

Module OrderedElementTypeZ <: OrderedElementType.
  Include ElementTypeZ.

  Definition Ale := Z.le.
  Definition Alt := Z.lt.
  Hint Unfold Ale Alt : A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply Z_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply Z_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply Z_le_refl. Qed.
End OrderedElementTypeZ.

Module OrderedElementTypeQ <: OrderedElementType.
  Include ElementTypeQ.

  Definition Ale := Qle.
  Definition Alt := Qlt.
  Hint Unfold Ale Alt : A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply Q_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply Q_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply Q_le_refl. Qed.
End OrderedElementTypeQ.

Module OrderedElementTypeQc <: OrderedElementType.
  Include ElementTypeQc.

  Definition Ale := Qcle.
  Definition Alt := Qclt.
  Hint Unfold Ale Alt : A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply Qc_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply Qc_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply Qc_le_refl. Qed.
End OrderedElementTypeQc.

Module OrderedElementTypeR <: OrderedElementType.
  Include ElementTypeR.

  Definition Ale := Rle.
  Definition Alt := Rlt.
  Hint Unfold Ale Alt : A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply R_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply R_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply R_le_refl. Qed.
End OrderedElementTypeR.


(* ######################################################################### *)
(** * Element with abelian-monoid structure *)

(** ** Type of Element with abelian-monoid structure *)
(* Note, we won't use `AMonoidElementType` to emphasize the `abelian` property *)
Module Type MonoidElementType <: ElementType.
  Include ElementType.
  Open Scope A_scope.

  Parameter Aadd : A -> A -> A.
  Infix "+" := Aadd : A_scope.

  Axiom Aadd_AMonoid : AMonoid Aadd Azero.
  #[export] Existing Instance Aadd_AMonoid.
End MonoidElementType.

(** ** Instances *)

Module MonoidElementTypeNat <: MonoidElementType.
  Include ElementTypeNat.

  Definition Aadd := Nat.add.
  Hint Unfold Aadd : A.

  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeNat.

Module MonoidElementTypeZ <: MonoidElementType.
  Include ElementTypeZ.

  Definition Aadd := Zplus.
  Hint Unfold Aadd : A.

  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeZ.

Module MonoidElementTypeQc <: MonoidElementType.
  Include ElementTypeQc.

  Definition Aadd := Qcplus.
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeQc.

Module MonoidElementTypeR <: MonoidElementType.
  Include ElementTypeR.
  
  Definition Aadd := Rplus.
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeR.

Module MonoidElementTypeC <: MonoidElementType.
  Include ElementTypeC.

  Definition Aadd := Cadd.
  
  (** Note that, this explicit annotation is must, 
      otherwise, the ring has no effect. (because C and T are different) *)
  (* Definition Aadd : A -> A -> A := fun a b => Cadd a b. *)
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeC.

Module MonoidElementTypeRFun <: MonoidElementType.
  Include ElementTypeRFun.
  
  Definition Aadd := fadd.
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeRFun.

Module MonoidElementTypeFun (I O : MonoidElementType) <: MonoidElementType.
  (* Export I O. *)
  
  Include (ElementTypeFun I O).
  Open Scope A_scope.

  Definition Aadd (f g : A) : A := fun x : I.A => O.Aadd (f x) (g x).
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  Lemma Aadd_Associative : Associative Aadd.
  Proof.
    intros. constructor; intros; autounfold with A.
    extensionality x. apply O.Aadd_AMonoid.
  Qed.
  
  Lemma Aadd_Commutative : Commutative Aadd.
  Proof.
    intros. constructor; intros; autounfold with A.
    extensionality x. apply O.Aadd_AMonoid.
  Qed.
  
  Lemma Aadd_IdentityLeft : IdentityLeft Aadd Azero.
  Proof.
    intros. constructor; intros; autounfold with A.
    extensionality x. apply O.Aadd_AMonoid.
  Qed.
  
  Lemma Aadd_IdentityRight : IdentityRight Aadd Azero.
  Proof.
    intros. constructor; intros; autounfold with A.
    extensionality x. apply O.Aadd_AMonoid.
  Qed.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof.
    intros. constructor; intros; autounfold with A.
    intros. constructor; intros; autounfold with A.
    constructor. apply Aadd_Associative.
    apply Aadd_IdentityLeft. apply Aadd_IdentityRight.
    constructor. apply Aadd_Associative.
    apply Aadd_Commutative.
    constructor. constructor. apply Aadd_Associative.
    apply Aadd_Commutative.
  Qed.
End MonoidElementTypeFun.


Module MonoidElementTypeTest.
  Import MonoidElementTypeQc.
  Import MonoidElementTypeR.
  
  Module Import MonoidElementTypeFunEx1 :=
    MonoidElementTypeFun MonoidElementTypeQc MonoidElementTypeR.

  (* Definition f : A := fun i:Qc => Qc2R i + R1. *)
  (* Definition g : A := fun i:Qc => Qc2R (i+1). *)
  Definition f : A := fun i => 1.
  Definition g : A := fun i => 2.
  Definition h : A := fun i => 3.

  Goal f + g + h = f + (g + h).
  Proof. rewrite associative. auto. Qed.
End MonoidElementTypeTest.


(* ######################################################################### *)
(** * Element with abelian-ring structure *)

(** ** Type of Element with abelian-ring structure *)
(* Note, we won't use `ARingElementType` to emphasize the `abelian` property *)
Module Type RingElementType <: MonoidElementType.
  Include MonoidElementType.
  Open Scope A_scope.

  Parameter Aone : A.
  Parameter Amul : A -> A -> A.
  Parameter Aopp : A -> A.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  Axiom Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.

  (* (** A Abelian-Group structure can be derived from the context *) *)
  (* Axiom AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* #[export] Existing Instance AGroup_inst. *)

  (** A Ring structure can be derived from the context *)
  Axiom ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  #[export] Existing Instance ARing_inst.
End RingElementType.

(** ** Instances *)

Module RingElementTypeZ <: RingElementType.
  Include MonoidElementTypeZ.

  Definition Aone : A := 1.
  Definition Aopp := Z.opp.
  Definition Amul := Zmult.
  Hint Unfold Aone Aopp Amul : A.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.
  
  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. repeat constructor; autounfold with A; intros; ring. Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
End RingElementTypeZ.

Module RingElementTypeQc <: RingElementType.
  Include MonoidElementTypeQc.

  Definition Aone : A := 1.
  Definition Aopp := Qcopp.
  Definition Amul := Qcmult.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.
  
  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. repeat constructor; autounfold with A; intros; ring. Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
End RingElementTypeQc.

Module RingElementTypeR <: RingElementType.
  Include MonoidElementTypeR.
  
  Definition Aone : A := 1.
  Definition Aopp := Ropp.
  Definition Amul := Rmult.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.
  
  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. repeat constructor; autounfold with A; intros; ring. Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
End RingElementTypeR.

Module RingElementTypeC <: RingElementType.
  Include MonoidElementTypeC.

  Definition Aone : A := 1.
  Definition Aopp := Copp.
  Definition Amul := Cmul.
  
  (** Note that, this explicit annotation is must, 
      otherwise, the ring has no effect. (because C and T are different) *)
  (* Definition Aadd : A -> A -> A := fun a b => Cadd a b. *)
  (* Definition Aopp : A -> A := fun a => Copp a. *)
  (* Definition Amul : A -> A -> A := fun a b => Cmul a b. *)
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.

  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. repeat constructor; autounfold with A; intros; ring. Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
End RingElementTypeC.


Module RingElementTypeRFun <: RingElementType.
  Include MonoidElementTypeRFun.
  
  Definition Aone : A := fone.
  Definition Aopp := fopp.
  Definition Amul := fmul.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof.
    repeat constructor; intros;  autounfold with A;
      apply functional_extensionality; intros; cbv; ring.
  Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.
  
  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. *)
  (*   repeat constructor; intros;  autounfold with A; *)
  (*     apply functional_extensionality; intros; cbv; ring. *)
  (* Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof.
    repeat constructor; intros;  autounfold with A;
      apply functional_extensionality; intros; cbv; ring.
  Qed.
End RingElementTypeRFun.


Module RingElementTypeFun (I O : RingElementType) <: RingElementType.
  (* Export I O. *)
  (* Add Ring Ring_thy_inst_i : I.Ring_thy. *)
  Add Ring Ring_thy_inst_o : O.Ring_thy.
  
  Include (MonoidElementTypeFun I O).

  Definition Aone : A := fun _ => O.Aone.
  Definition Aopp (f : A) : A := fun x : I.A => O.Aopp (f x).
  Definition Amul (f g : A) : A := fun x : I.A => O.Amul (f x) (g x).
  Notation Asub := (fun x y => Aadd x (Aopp y)).

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof.
    repeat constructor; autounfold with A; intros;
      apply functional_extensionality; intros; cbv; ring.
  Qed.

  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. *)
  (*   repeat constructor; autounfold with A; intros; *)
  (*     apply functional_extensionality; intros; cbv; ring. *)
  (* Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof.
    repeat constructor; autounfold with A; intros;
      apply functional_extensionality; intros; cbv; ring.
  Qed.
End RingElementTypeFun.


Module RingElementTypeTest.
  Import RingElementTypeQc.
  Import RingElementTypeR.
  
  Module Import RingElementTypeFunEx1 :=
    RingElementTypeFun RingElementTypeQc RingElementTypeR.
  
  Definition f : A := fun i:Qc => (Qc2R i + R1)%R.
  Definition g : A := fun i:Qc => Qc2R (i+1).

  Goal f = g.
  Proof. Abort.
End RingElementTypeTest.



(* ######################################################################### *)
(** * Element with abelian-ring structure and ordered relation *)

(** ** Type of Element with ordered abelian-ring structure *)
Module Type OrderedRingElementType <: RingElementType <: OrderedElementType.
  Include RingElementType.

  Parameter Ale Alt : A -> A -> Prop.

  Axiom AleDec : Dec Ale.
  #[export] Existing Instance AleDec.
  
  Axiom AltDec : Dec Alt.
  #[export] Existing Instance AltDec.

  Axiom Ale_refl : forall a : A, Ale a a.
  Axiom Azero_le_sqr : forall a : A, Ale Azero (Amul a a).
  Axiom Aadd_le_compat : forall a1 b1 a2 b2 : A,
      Ale a1 a2 -> Ale b1 b2 -> Ale (Aadd a1 b1) (Aadd a2 b2).
  Axiom Aadd_eq_0_reg_l : forall a b : A,
      Ale Azero a -> Ale Azero b -> Aadd a b = Azero -> a = Azero.
End OrderedRingElementType.


(** ** Instances *)

Module OrderedRingElementTypeZ <: OrderedRingElementType.
  Include RingElementTypeZ.
  
  (* 注意，多继承时，无法用多个Include语句，需要手动拷贝代码 *)
  Definition Ale := Z.le.
  Definition Alt := Z.lt.
  Hint Unfold Ale Alt : A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply Z_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply Z_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply Z_le_refl. Qed.
  
  Lemma Azero_le_sqr : forall a : A, Ale Azero (Amul a a).
  Proof. apply Z_zero_le_sqr. Qed.
  
  Lemma Aadd_le_compat : forall a1 b1 a2 b2 : A,
      Ale a1 a2 -> Ale b1 b2 -> Ale (Aadd a1 b1) (Aadd a2 b2).
  Proof. apply Z_add_le_compat. Qed.
  
  Lemma Aadd_eq_0_reg_l : forall a b : A,
      Ale Azero a -> Ale Azero b -> Aadd a b = Azero -> a = Azero.
  Proof. intros. apply Z_add_eq_0_reg_l in H1; auto. Qed.
End OrderedRingElementTypeZ.

Module OrderedRingElementTypeQc <: OrderedRingElementType.
  Include RingElementTypeQc.

  Definition Ale := Qcle.
  Definition Alt := Qclt.
  Hint Unfold Ale Alt : A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply Qc_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply Qc_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply Qc_le_refl. Qed.
  
  Lemma Azero_le_sqr : forall a : A, Ale Azero (Amul a a).
  Proof. apply Qc_zero_le_sqr. Qed.
  
  Lemma Aadd_le_compat : forall a1 b1 a2 b2 : A,
      Ale a1 a2 -> Ale b1 b2 -> Ale (Aadd a1 b1) (Aadd a2 b2).
  Proof. apply Qc_add_le_compat. Qed.
  
  Lemma Aadd_eq_0_reg_l : forall a b : A,
      Ale Azero a -> Ale Azero b -> Aadd a b = Azero -> a = Azero.
  Proof. intros. apply Qc_add_eq_0_reg_l in H1; auto. Qed.
End OrderedRingElementTypeQc.

Module OrderedRingElementTypeR <: OrderedRingElementType.
  Include RingElementTypeR.
  
  Definition Ale := Rle.
  Definition Alt := Rlt.
  Hint Unfold Ale Alt: A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply R_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply R_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply R_le_refl. Qed.
  
  Lemma Azero_le_sqr : forall a : A, Ale Azero (Amul a a).
  Proof. apply R_zero_le_sqr. Qed.
  
  Lemma Aadd_le_compat : forall a1 b1 a2 b2 : A,
      Ale a1 a2 -> Ale b1 b2 -> Ale (Aadd a1 b1) (Aadd a2 b2).
  Proof. apply R_add_le_compat. Qed.
  
  Lemma Aadd_eq_0_reg_l : forall a b : A,
      Ale Azero a -> Ale Azero b -> Aadd a b = Azero -> a = Azero.
  Proof. intros. apply R_add_eq_0_reg_l in H1; auto. Qed.
End OrderedRingElementTypeR.



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

  (** 1 <> 0. *)
  Axiom Aone_neq_Azero : Aone <> Azero.
  
  Axiom Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv eq.
  Add Field Field_thy_inst : Field_thy.

  (** A Field structure can be derived from the context *)

  Axiom Field_inst : Field Aadd Azero Aopp Amul Aone Ainv.
  #[export] Existing Instance Field_inst.
End FieldElementType.


(** ** Instances *)

Module FieldElementTypeQc <: FieldElementType.
  Include RingElementTypeQc.

  Definition Ainv := Qcinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. intro. cbv in *. inv H. Qed.
  
  Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv eq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy.
    unfold Amul,Ainv,Aone. unfold ElementTypeQc.A. field. auto.
  Qed.
    
  Add Field Field_thy_inst : Field_thy.
  
  #[export] Instance Field_inst : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing_inst.
    intros. autounfold with A. field. auto.
    apply Aone_neq_Azero.
  Qed.
End FieldElementTypeQc.

Module FieldElementTypeR <: FieldElementType.
  Include RingElementTypeR.
  
  Definition Ainv := Rinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. cbv in *. auto with real. Qed.

  Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv eq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy. apply Aone_neq_Azero.
    autounfold with A. field. auto.
  Qed.

  Add Field Field_thy_inst : Field_thy.
  
  #[export] Instance Field_inst : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing_inst. intros.
    autounfold with A. field. auto.
    apply Aone_neq_Azero.
  Qed.
End FieldElementTypeR.

Module FieldElementTypeC <: FieldElementType.
  Include RingElementTypeC.
  
  Definition Ainv := Cinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. cbv in *. auto with complex. Qed.

  Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv eq.
  Proof.
    constructor; intros; auto with complex; try easy.
    apply Ring_thy.
  Qed.

  Add Field Field_thy_inst : Field_thy.
  
  #[export] Instance Field_inst : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing_inst. intros.
    autounfold with A. field. auto.
    apply Aone_neq_Azero.
  Qed.
End FieldElementTypeC.

(* Module FieldElementTypeFun (I O : FieldElementType) <: FieldElementType. *)
(*   Include (RingElementTypeFun I O). *)

(*   Definition Ainv : A -> A. *)
(*     cbv. intros [f Pf]. *)
(*     refine (exist _ (fun x : I.T => O.Ainv (f x)) _). *)
(*     constructor. intros. *)
(*     pose proof (O.Resp_Ainv_Teq). apply respectUnary. apply Pf; easy. *)
(*   Defined. *)
  
(*   Notation Adiv := (fun x y => Amul x (Ainv y)). *)

  (* Lemma Ainv_aeq_mor : Proper (Teq ==> Teq) Ainv. *)
  (* Proof. *)
  (*   unfold Proper, respectful. intros [x Px] [y Py] H1. *)
  (*   cbv in *. intros. apply O.Resp_Ainv_Teq; auto. *)
  (* Qed. *)
  
(*   (* Import FunctionalExtensionality. *) *)
(*   Lemma Aone_neq_Azero : ~(Aone == Azero)%T. *)
(*   Proof. cbv in *. intros. specialize (H I.Azero). apply O.Aone_neq_Azero in H. auto. Qed. *)

(*   Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Teq. *)
(*   Proof. *)
(*     destruct (I.Field_thy), (O.Field_thy). *)
(*     constructor. *)
(*     - apply Ring_thy. *)
(*     - apply Aone_neq_Azero. *)
(*     - intros. *)
(*       repeat match goal with | x:A |- _ => destruct x end. *)
(*       cbv in *; intros. *)
(*       pose proof (O.Amul_aeq_mor). *)
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
  Import FieldElementTypeQc.
  Import FieldElementTypeR.

  (* Include (FieldElementTypeFun FieldElementTypeQ FieldElementTypeR). *)
End FieldElementTypeTest.


(* ######################################################################### *)
(** * Element with field structure and ordered relation *)

(** ** Type of Element with ordered field structure *)
Module Type OrderedFieldElementType <: FieldElementType <: OrderedElementType.
  Include FieldElementType.

  Parameter Ale Alt : A -> A -> Prop.

  Axiom AleDec : Dec Ale.
  #[export] Existing Instance AleDec.
  
  Axiom AltDec : Dec Alt.
  #[export] Existing Instance AltDec.

  Axiom Ale_refl : forall a : A, Ale a a.
  Axiom Azero_le_sqr : forall a : A, Ale Azero (Amul a a).
  Axiom Aadd_le_compat : forall a1 b1 a2 b2 : A,
      Ale a1 a2 -> Ale b1 b2 -> Ale (Aadd a1 b1) (Aadd a2 b2).
  Axiom Aadd_eq_0_reg_l : forall a b : A,
      Ale Azero a -> Ale Azero b -> Aadd a b = Azero -> a = Azero.
End OrderedFieldElementType.


(** ** Instances *)

Module OrderedFieldElementTypeQc <: OrderedFieldElementType.
  Include FieldElementTypeQc.

  Definition Ale := Qcle.
  Definition Alt := Qclt.
  Hint Unfold Ale Alt : A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply Qc_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply Qc_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply Qc_le_refl. Qed.
  
  Lemma Azero_le_sqr : forall a : A, Ale Azero (Amul a a).
  Proof. apply Qc_zero_le_sqr. Qed.
  
  Lemma Aadd_le_compat : forall a1 b1 a2 b2 : A,
      Ale a1 a2 -> Ale b1 b2 -> Ale (Aadd a1 b1) (Aadd a2 b2).
  Proof. apply Qc_add_le_compat. Qed.
  
  Lemma Aadd_eq_0_reg_l : forall a b : A,
      Ale Azero a -> Ale Azero b -> Aadd a b = Azero -> a = Azero.
  Proof. intros. apply Qc_add_eq_0_reg_l in H1; auto. Qed.
End OrderedFieldElementTypeQc.

Module OrderedFieldElementTypeR <: OrderedFieldElementType.
  Include FieldElementTypeR.
  
  Definition Ale := Rle.
  Definition Alt := Rlt.
  Hint Unfold Ale Alt: A.
  
  Lemma AleDec : Dec Ale.
  Proof. apply R_le_Dec. Qed.
  
  Lemma AltDec : Dec Alt.
  Proof. apply R_lt_Dec. Qed.

  Lemma Ale_refl : forall a : A, Ale a a.
  Proof. apply R_le_refl. Qed.
  
  Lemma Azero_le_sqr : forall a : A, Ale Azero (Amul a a).
  Proof. apply R_zero_le_sqr. Qed.
  
  Lemma Aadd_le_compat : forall a1 b1 a2 b2 : A,
      Ale a1 a2 -> Ale b1 b2 -> Ale (Aadd a1 b1) (Aadd a2 b2).
  Proof. apply R_add_le_compat. Qed.
  
  Lemma Aadd_eq_0_reg_l : forall a b : A,
      Ale Azero a -> Ale Azero b -> Aadd a b = Azero -> a = Azero.
  Proof. intros. apply R_add_eq_0_reg_l in H1; auto. Qed.
End OrderedFieldElementTypeR.
