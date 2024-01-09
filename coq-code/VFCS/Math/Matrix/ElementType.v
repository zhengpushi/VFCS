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
  (2) ARingElementType, based on ElementType.
  (3) FieldElementType, based on RingEementType.
*)

Require NatExt ZExt QExt QcExt RExt RealFunction Complex.
Require Export Hierarchy.



(* ######################################################################### *)
(** * Element with setoid equality *)

(** ** Type of element *)
Module Type ElementType.
  Parameter A : Type.
  Parameter Azero : A.

  Axiom ADec : @Dec A.
  #[export] Existing Instance ADec.
  
End ElementType.


(** ** Instances *)
Module ElementTypeNat <: ElementType.
  Export NatExt.
  Definition A : Type := nat.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma ADec : @Dec nat.
  Proof. constructor. apply Nat.eq_dec. Qed.
End ElementTypeNat.

Module ElementTypeZ <: ElementType.
  Export ZExt.
  Definition A : Type := Z.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma ADec : @Dec Z.
  Proof. constructor. apply Z.eq_dec. Qed.
End ElementTypeZ.

Module ElementTypeQ <: ElementType.
  Export QExt.
  Definition A : Type := Q.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma ADec : @Dec Q.
  Proof. constructor. apply Qeqdec. Qed.
End ElementTypeQ.

Module ElementTypeQc <: ElementType.
  Export QcExt.
  Definition A : Type := Qc.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma ADec : @Dec Qc.
  Proof. constructor. apply Qc_eq_dec. Qed.
End ElementTypeQc.

Module ElementTypeR <: ElementType.
  Export RExt.
  Definition A : Type := R.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma ADec : @Dec R.
  Proof. constructor. apply Req_EM_T. Qed.
End ElementTypeR.

Module ElementTypeC <: ElementType.
  Export Complex.
  Definition A : Type := C.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma ADec : @Dec C.
  Proof. apply Dec_Complex. Qed.
End ElementTypeC.

Module ElementTypeRFun <: ElementType.
  Export RealFunction.
  Definition A : Type := tpRFun.
  Definition Azero : A := fzero.
  Hint Unfold A Azero : A.

  Lemma ADec : @Dec tpRFun.
  Proof. constructor. intros a b. unfold tpRFun in *.
         (* rewrite (functional_extensionality a b). *)
  Admitted.
  
End ElementTypeRFun.

Module ElementTypeFun (I O : ElementType) <: ElementType.
  Definition A : Type := I.A -> O.A.
  Definition Azero : A := fun _ => O.Azero.
  Hint Unfold A Azero : A.

  Lemma ADec : @Dec A.
  Proof. constructor. intros a b. unfold A in *.
  Admitted.
  
End ElementTypeFun.


Module ElementType_Test.
  Import ElementTypeNat ElementTypeR.
  Module Import ElementTypeFunEx1 := ElementTypeFun ElementTypeNat ElementTypeR.

  Definition f : A := fun i => match i with 0%nat => 1 | 1%nat => 2 | _ => 1 end.
  Definition g : A := fun i => match i with 1%nat => 2 | _ => 1 end.

  Goal f = g.
  Proof. cbv. intros. auto. Qed.
End ElementType_Test.


(* ######################################################################### *)
(** * Element with abelian-ring structure *)

(** ** Type of Element with abelian-ring structure *)
(* Note, we won't use `ARingElementType` to emphasize the `abelian` property *)
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
  
  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. repeat constructor; autounfold with A; intros; ring. Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
  
End RingElementTypeZ.

Module RingElementTypeQc <: RingElementType.
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
  
  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. repeat constructor; autounfold with A; intros; ring. Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.

End RingElementTypeQc.

Module RingElementTypeR <: RingElementType.
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

  Lemma Ring_thy : ring_theory Azero Aone Aadd Amul Asub Aopp eq.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.
  
  (* #[export] Instance AGroup_inst : AGroup Aadd Azero Aopp. *)
  (* Proof. repeat constructor; autounfold with A; intros; ring. Qed. *)

  #[export] Instance ARing_inst : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.

End RingElementTypeR.

Module RingElementTypeC <: RingElementType.
  Include ElementTypeC.

  Definition Aone : A := 1.
  Definition Aadd := Cadd.
  Definition Aopp := Copp.
  Definition Amul := Cmul.
  
  (** Note that, this explicit annotation is must, 
      otherwise, the ring has no effect. (because C and T are different) *)
  (* Definition Aadd : A -> A -> A := fun a b => Cadd a b. *)
  (* Definition Aopp : A -> A := fun a => Copp a. *)
  (* Definition Amul : A -> A -> A := fun a b => Cmul a b. *)
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "+" := Aadd : A_scope.
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
  
  Include (ElementTypeFun I O).

  Definition Aone : A := fun _ => O.Aone.
  Definition Aadd (f g : A) : A := fun x : I.A => O.Aadd (f x) (g x).
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
  
  Definition f : A := fun i:Qc => Qc2R i + R1.
  Definition g : A := fun i:Qc => Qc2R (i+1).

  Goal f = g.
  Proof. Abort.
  
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
