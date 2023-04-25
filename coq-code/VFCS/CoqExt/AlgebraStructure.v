(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Algebra Structure
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. This file is come from CoqMatrix, and removed the setoid design.
  2. Mainly use typeclasses.
  3. The motivate of this module is to support development with good organized 
     algebraic hierarchy, instead of scattered def./op./props.
  3. There are three technologies to form a hierarchy: 
     (1) module is a strong specification and too heavy;
     (2) Typeclass is used in Coq standard library;
         Reference:
         a. paper "A Gentle Introduction to Type Classes and Relations in Coq"
         b. the refrence manual of Coq at "https://coq.inria.fr/distrib/V8.13.2/
            refman/addendum/type-classes.html".
     (3) Canonical structure is used in mathematical component.
  4. About Q (rational number), we mainly use Qcanon (Qc) instead of Q, hence 
     the convenient of equality relation. Precisely, Qc use eq that has best 
     built-in support in Coq, rather than Q use Qeq that we should use Setoid 
     and write more code to let it work.
  5. Other references:
     (1) Arkansas Tech University / Dr. Marcel B. Finan /
         MATH 4033: Elementary Modern Algebra
     (2) 5 Definition and Examples of Groups
         https://faculty.atu.edu/mfinan/4033/absalg5.pdf
     (3) 14 Elementary Properties of Groups
         https://faculty.atu.edu/mfinan/4033/absalg14.pdf
     (4) https://math.okstate.edu/people/binegar/3613/3613-l21.pdf
 *)

Require Export BasicConfig.   (* reserved notation *)
Require Export Coq.Classes.RelationClasses. (* binary_relation *)
Require Import Coq.Logic.Description. (* constructive_definite_description *)
Require Export List SetoidList. Import ListNotations.
Require Export Lia Lra.
Require Export Ring Field.

Require Arith ZArith QArith Qcanon Reals.

Set Implicit Arguments.
Unset Strict Implicit.

(* Meanwhile, like A0,A1,... also be availble *)
Generalizable Variables A Aeq Aadd Aopp Amul Ainv Adiv.


(* ######################################################################### *)
(** * Small utilities *)

(** repeat split and intro *)
Ltac split_intro :=
  repeat (try split; try intro).

(** Applicate a unary function for n-times, i.e. f ( .. (f a0) ...) *)
Fixpoint iterate {A} (f : A -> A) (n : nat) (a0 : A) : A :=
  match n with
  | O => a0
  | S n' => f (iterate f n' a0)
  end.

Section test.
  Context {A} {f : A -> A} (A0 : A).
  (* Compute iterate f 3 A0. *)
End test.

(* (** x is an unique element which holds by P. Setoid version *) *)
(* Definition unique_setoid {A : Type} {Aeq: relation A} (P: A -> Prop) (x: A) := *)
(*   P x /\ (forall x' : A, P x' -> Aeq x x'). *)

(* (** constructive_definite_description, setoid version *) *)
(* Axiom constructive_definite_description_setoid : *)
(*   forall (A : Type) (Aeq:relation A) (P : A -> Prop), *)
(*     (exists x : A, (P x /\ unique_setoid (Aeq:=Aeq) P x)) -> {x : A | P x}. *)

(* (** functional_extensionality, setoid version *) *)
(* Axiom functional_extensionality_setoid : *)
(*   forall {A B} {Beq: relation B} (feq: relation (A->B)) (f g : A -> B), *)
(*     (forall a : A, Beq (f a) (g a)) -> feq f g. *)


(* ######################################################################### *)
(** * A relation is equivalence relation *)

(** ** Class *)

(* Global Hint Constructors Equivalence : core. *)

(** ** Instances *)

(** eqlistA is a equivalence relation *)
Global Instance Equivalence_eqlistA `{Equiv_Aeq:Equivalence A Aeq}
  : Equivalence (eqlistA Aeq).
Proof. apply eqlistA_equiv. auto. Defined.

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * A relation is decidable *)

(** ** Class *)

Class Decidable {A : Type} (Aeq : relation A) := {
    decidable : forall (a b : A), {Aeq a b} + {~(Aeq a b)};
  }.
Infix "==?" := (decidable).
Infix "<>?" := (fun a b => sumbool_not _ _ (a ==? b)).


(* Global Hint Constructors Decidable : core. *)

(** ** Instances *)

Section Instances.
  Import Arith ZArith QArith Qcanon Reals.

  Global Instance Decidable_NatEq : Decidable (@eq nat).
  Proof. constructor. apply Nat.eq_dec. Defined.

  Global Instance Decidable_Positive : Decidable (@eq positive).
  Proof. constructor. apply Pos.eq_dec. Defined.

  Global Instance Decidable_Z : Decidable (@eq Z).
  Proof. constructor. apply Z.eq_dec. Defined.

  Global Instance Decidable_Q : Decidable (@eq Q).
  Proof.
    constructor.
    intros [a1 a2] [b1 b2].
    destruct (a1 ==? b1), (a2 ==? b2); subst; auto.
    all: right; intro H; inv H; auto.
  Defined.

  Global Instance Decidable_Q_Qeq : Decidable Qeq.
  Proof. constructor. apply Qeq_dec. Defined.

  Global Instance Decidable_Qc : Decidable (@eq Qc).
  Proof. constructor. apply Qc_eq_dec. Defined.

  Global Instance Decidable_R : Decidable (@eq R).
  Proof. constructor. apply Req_EM_T. Defined.

  Global Instance Decidable_list `{Dec:Decidable} : Decidable (eqlistA Aeq).
  Proof.
    constructor. intros l1. induction l1.
    - intros l2. destruct l2; auto.
      right. intro. easy.
    - intros l2. destruct l2.
      + right. intro. easy.
      + destruct (decidable a a0), (IHl1 l2); auto.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
  Defined.

  Global Instance Decidable_dlist `{Dec:Decidable} : Decidable (eqlistA (eqlistA Aeq)).
  Proof.
    constructor. intros l1. induction l1.
    - intros l2. destruct l2; auto.
      right. intro. easy.
    - intros l2. destruct l2.
      + right. intro. easy.
      + destruct (decidable a l), (IHl1 l2); auto.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
  Defined.

End Instances.

(** ** Extra Theories *)
Section Dec_theory.

  Context `{Dec : Decidable}.
  Infix "==" := Aeq.

  (** Tips: these theories are useful for R type *)
  
  (** Calculate equality to boolean, with the help of equality decidability *)
  Definition Aeqb (a b : A) : bool := if a ==? b then true else false.
  Infix "=?" := Aeqb.

  (** Aeqb is true iff equal. *)
  Lemma Aeqb_true : forall a b, a =? b = true <-> a == b.
  Proof.
    intros. unfold Aeqb. destruct decidable; split; intros; easy.
  Qed.

  (** Aeqb is false iff not equal *)
  Lemma Aeqb_false : forall a b, a =? b = false <-> ~(a == b).
  Proof.
    intros. unfold Aeqb. destruct decidable; split; intros; easy.
  Qed.

  Lemma Aeq_reflect : forall a b : A, reflect (a == b) (a =? b).
  Proof.
    intros. unfold Aeqb. destruct (decidable a b); constructor; auto.
  Qed.

End Dec_theory.

(** ** Examples *)
Goal forall a b : nat, {a = b} + {a <> b}.
  apply decidable. Qed.


(* ######################################################################### *)
(** * Respect: an operation respect a relation *)

(** deprecated, replaced with "Proper" in Coq *)

(* (** ** Class *) *)

(* (** A unary operation is respect to the equality relation *) *)
(* Class RespectUnary {A B:Type} (op:A->B) (Aeq:A -> A->Prop) (Beq:B->B->Prop) := { *)
(*     respectUnary : forall x y : A, *)
(*       Aeq x y -> Beq (op x) (op y) *)
(*   }. *)

(* (** A binary operation is respect to the equality relation *) *)
(* Class RespectBinary {A B C:Type} (op:A->B->C) *)
(*   (Aeq:A -> A->Prop) (Beq:B->B->Prop) (Ceq:C->C->Prop):= { *)
(*     respectBinary : forall x y : A, *)
(*       Aeq x y -> forall x0 y0 : B, Beq x0 y0 -> Ceq (op x x0) (op y y0) *)
(*   }. *)

(* (** ** Instances *) *)

(* (** ** Extra Theories *) *)

(* (** ** Examples *) *)



(* ######################################################################### *)
(** * Associative *)

(** ** Class *)
Class Associative {A : Type} (Aop : A -> A -> A) (Aeq : relation A) := {
    associative : forall a b c, Aeq (Aop (Aop a b) c) (Aop a (Aop b c));
  }.

(** ** Instances *)
Global Instance Assoc_NatAdd : Associative Nat.add eq.
Proof. constructor. auto with arith. Qed.

(** ** Extra Theories *)
(* Lemma associative_inv : forall `{Assoc : Associative} a b c, *)
(*     Aop a (Aop b c) = Aop (Aop a b) c. *)
(* Proof. intros. rewrite -> associative. auto. Qed. *)

(** ** Examples *)
Goal forall a b c : nat, a + (b + c) = (a + b) + c.
  intros. rewrite associative. auto. Qed.

Goal forall a b c : nat, (a + b) + c = a + (b + c).
  apply associative. Qed.


(* ######################################################################### *)
(** * Commutative *)

(** ** Class *)
Class Commutative {A : Type} (Aop : A -> A -> A) (Aeq : relation A) := {
    commutative : forall a b, Aeq (Aop a b) (Aop b a)
  }.

(** ** Instances *)
Global Instance Comm_NatAdd : Commutative Nat.add eq.
constructor. auto with arith. Qed.

Global Instance Comm_NatMul : Commutative Nat.mul eq.
constructor. auto with arith. Qed.

(** ** Extra Theories *)

(** ** Examples *)
Goal forall a b : nat, a + b = b + a.
  apply commutative. Qed.

Goal forall a b : nat, a * b = b * a.
  apply commutative. Qed.


(* ######################################################################### *)
(** * Identity Left/Right *)

(** ** Class *)
Class IdentityLeft {A : Type} (Aop : A -> A -> A) (Ae : A) (Aeq : relation A) := {
    identityLeft : forall a, Aeq (Aop Ae a) a
  }.

Class IdentityRight {A : Type} (Aop : A -> A -> A) (Ae : A) (Aeq : relation A) := {
    identityRight : forall a, Aeq (Aop a Ae) a
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Inverse Left/Right *)

(** ** Class *)
Class InverseLeft {A : Type} (Aop : A -> A -> A) (Ae : A) (Aopinv : A -> A)
  (Aeq : relation A) := {
    inverseLeft : forall a, Aeq (Aop (Aopinv a) a) Ae
  }.

Class InverseRight {A : Type} (Aop : A -> A -> A) (Ae : A) (Aopinv : A -> A)
  (Aeq : relation A) := {
    inverseRight : forall a, Aeq (Aop a (Aopinv a)) Ae
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Distributive *)

(** ** Class *)

(* Class DistributiveUnary {A : Type} (Aadd:A -> A -> A) (Aopp : A -> A) := { *)
(*     distributiveUnary : forall a b, *)
(*       Aopp (Aadd a b) = Aadd (Aopp a) (Aopp b) *)
(*   }. *)

Class DistributiveLeft {A : Type} (Aadd Amul : A -> A -> A) (Aeq : relation A) := {
    distributiveLeft : forall a b c,
      Aeq (Amul a (Aadd b c)) (Aadd (Amul a b) (Amul a c))
  }.

Class DistributiveRight {A : Type} (Aadd Amul : A -> A -> A) (Aeq : relation A) := {
    distributiveRight : forall a b c,
      Aeq (Amul (Aadd a b) c) (Aadd (Amul a c) (Amul b c))
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Involution Law *)

(** ** Class *)

(* Class Involution {A : Type} (Aopp : A -> A) := { *)
(*     involution : forall a, Aeq (Aopp (Aopp a)) a *)
(*   }. *)

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Injective *)

(** ** Class *)

Class Injective {A B : Type} {Aeq: relation A} {Beq: relation B} (phi: A -> B) := {
    injective : forall a1 a2 : A, ~(Aeq a1 a2) -> ~(Beq (phi a1) (phi a2))
  }.
  
(** ** Instances *)

(** ** Extra Theories *)
Section theory.

  Context {A B : Type} {Aeq: relation A} {Beq: relation B}.

  Notation Injective := (Injective (Aeq:=Aeq) (Beq:=Beq)).
  
  (** Second form of injective *)
  Definition injective_form2 (phi: A -> B) :=
    forall (a1 a2 : A), Beq (phi a1) (phi a2) -> Aeq a1 a2.

  (** These two forms are equal *)
  Lemma injective_eq_injective_form2 (phi: A -> B) :
    Injective phi <-> injective_form2 phi.
  Proof.
    split; intros.
    - hnf. destruct H as [H]. intros.
      specialize (H a1 a2). apply imply_to_or in H. destruct H.
      + apply NNPP in H. auto.
      + easy.
    - hnf in H. constructor. intros. intro. apply H in H1. easy.
  Qed.

  (** Injective function preserve equal relation *)
  Lemma inj_pres_eq : forall (f : A -> B),
      Injective f -> (forall a1 a2 : A, Beq (f a1) (f a2) -> Aeq a1 a2).
  Proof.
    intros. apply injective_eq_injective_form2 in H. apply H. auto.
  Qed.

End theory.

(** ** Examples *)



(* ######################################################################### *)
(** * Surjective *)

(** ** Class *)

Class Surjective {A B : Type} {Beq: relation B} (phi: A -> B) := {
    surjective : forall (b : B), (exists (a : A), Beq (phi a) b)
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Bijective *)

(** ** Class *)

Class Bijective {A B : Type} {Aeq: relation A} {Beq: relation B} (phi: A -> B) := {
    bijInjective :> Injective (Aeq:=Aeq) (Beq:=Beq) phi;
    bijSurjective :> Surjective (Beq:=Beq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)
Section theory.
  Context {A B: Type} {Aeq:relation A} {Beq:relation B}.
  Context {Equiv_Aeq:Equivalence Aeq} {Equiv_Beq:Equivalence Beq}.
  Notation Bijective := (Bijective (Aeq:=Aeq) (Beq:=Beq)).
  Infix "=A=" := Aeq (at level 70).
  Infix "=B=" := Beq (at level 70).
  
  (** There exist inverse function from a bijective function.

      ref: https://stackoverflow.com/questions/62464821/
      how-to-make-an-inverse-function-in-coq

      Tips: there are two methods to formalize "existential", sig and ex.
      ex makes a Prop, sig makes a Type. 
      Here, we proof the ex version. the sig version could be derived by an axiom:
      [constructive_definite_description : 
      forall (A : Type) (P : A -> Prop), (exists ! x : A, P x) -> {x : A | P x} ]
   *)

  (** x is an unique element which holds by P. Setoid version *)
  Local Definition unique_setoid {A: Type} {Aeq: relation A} (P: A -> Prop) (x: A) :=
    P x /\ (forall x' : A, P x' -> Aeq x x').

  (** constructive_definite_description, setoid version *)
  Local Axiom constructive_definite_description_setoid :
    forall (A : Type) (Aeq:relation A) (P : A -> Prop),
      (exists x : A, (P x /\ unique_setoid (Aeq:=Aeq) P x)) -> {x : A | P x}.

  (** functional_extensionality, setoid version *)
  Local Axiom functional_extensionality_setoid :
    forall {A B} {Beq: relation B} (feq: relation (A->B)) (f g : A -> B),
      (forall a : A, Beq (f a) (g a)) -> feq f g.

  Lemma bij_inverse_exist : forall (phi : A -> B) (Hbij: Bijective phi),
    {psi : B -> A | (forall a : A, (psi (phi a)) =A= a) /\  (forall b : B, phi (psi b) =B= b)}.
  Proof.
    intros. destruct Hbij as [Hinj [Hsurj]].
    apply injective_eq_injective_form2 in Hinj. hnf in *.
    (* Tips, unique is eq version, we need setoid version *)
    (* assert (H : forall b, exists! a, phi a =B= b). *)
    assert (H: forall b, exists a, phi a =B= b /\ unique_setoid (Aeq:=Aeq) (fun x => phi x =B= b) a).
    { intros b.
      destruct (Hsurj b) as [a Ha]. exists a. unfold unique_setoid. repeat split; auto.
      intros a' Ha'. apply Hinj. rewrite Ha. rewrite Ha'. easy. }
    eapply constructive_definite_description_setoid.
    exists (fun b => proj1_sig (constructive_definite_description_setoid (H b))).
    split.
    - split.
      + intros a. destruct (constructive_definite_description_setoid). simpl.
        apply Hinj. auto.
      + intros b. destruct (constructive_definite_description_setoid). simpl. auto.
    - hnf. split.
      + split.
        * intros. destruct (constructive_definite_description_setoid). simpl.
          apply Hinj. auto.
        * intros. destruct (constructive_definite_description_setoid). simpl. auto.
      + intros psi [H1 H2].
        eapply functional_extensionality_setoid.
        intros b. destruct (constructive_definite_description_setoid). simpl.
        assert (phi (psi b) =B= b); auto using H2.
        rewrite <- H0 in b0. apply Hinj in b0. exact b0.
        Unshelve. exact eq.
  Defined.

  (** A bijective function preserve equal relation *)
  (* Lemma bij_pres_eq_forward : forall (f : A -> B), *)
  (*     Bijective f -> (forall (a1 a2 : A), Aeq a1 a2 -> Beq (f a1) (f a2)). *)
  (* Proof. *)
  (*   intros. destruct H as [H1 H2]. *)
  (*   (* I can't prove now. *) *)
  (*   Abort. *)
    

End theory.

(** ** Examples *)



(* ######################################################################### *)
(** * Homomorphic  *)

(** ** Class *)

Class Homomorphic {A B : Type} {Beq: relation B}
  (fa : A -> A -> A) (fb : B -> B -> B) (phi: A -> B) := {
    homomorphic : forall (a1 a2 : A), Beq (phi (fa a1 a2)) (fb (phi a1) (phi a2))
  }.

(** ** Instances *)

(** ** Extra Theories *)

(* Definition homo_inj {A B} (ϕ : A -> B) : Prop := *)
(*   homomorphic ϕ /\ injective ϕ. *)

(* (** ϕ is a homomorphic and surjective mapping *) *)
(* Definition homo_surj (ϕ : A -> B) : Prop := *)
(*   homomorphic ϕ /\ surjective ϕ. *)

(** ** Examples *)



(* ######################################################################### *)
(** * Homomorphism *)

(** ** Class *)

(** If there exist a homomorphic and surjective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is homomorphism *)
Class Homomorphism {A B : Type} {Aeq: relation A} {Beq: relation B}
  (fa : A -> A -> A) (fb : B -> B -> B) := {
    homomorphism : exists (phi: A -> B),
      Homomorphic fa fb phi (Beq:=Beq)
      /\ Surjective phi (Beq:=Beq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Aeq ==> Beq) phi
  }.

(** If there exist two homomorphic and surjective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is homomorphism *)
Class Homomorphism2 {A B : Type} {Aeq: relation A} {Beq: relation B}
  (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    homomorphism2 : exists (phi: A -> B),
      Homomorphic fa fb phi (Beq:=Beq)
      /\ Homomorphic ga gb phi (Beq:=Beq)
      /\ Surjective phi (Beq:=Beq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Aeq ==> Beq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Isomorphism *)

(** ** Class *)

(** If there exist a homomorphic and bijective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is isomorphism *)
Class Isomorphism {A B : Type} {Aeq: relation A} {Beq: relation B}
  (fa : A -> A -> A) (fb : B -> B -> B) := {
    isomorphism : exists (phi: A -> B),
      Homomorphic fa fb phi (Beq:=Beq)
      /\ Bijective phi (Aeq:=Aeq) (Beq:=Beq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Aeq ==> Beq) phi
  }.

(** If there exist two homomorphic and bijective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is isomorphism *)
Class Isomorphism2 {A B : Type} {Aeq: relation A} {Beq: relation B}
  (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    isomorphism2 : exists (phi: A -> B),
      Homomorphic fa fb phi (Beq:=Beq)
      /\ Homomorphic ga gb phi (Beq:=Beq)
      /\ Bijective phi (Aeq:=Aeq) (Beq:=Beq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Aeq ==> Beq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Monoid *)

(** ** Class *)
Class Monoid {A:Type} (Aadd : A -> A -> A) (A0 : A) (Aeq:A->A->Prop) := {
    monoidAaddProper :> Proper (Aeq ==> Aeq ==> Aeq) Aadd;
    monoidEquiv :> Equivalence Aeq;
    monoidAssoc :> Associative Aadd Aeq;
    monoidIdL :> IdentityLeft Aadd A0 Aeq;
    monoidIdR :> IdentityRight Aadd A0 Aeq;
  }.

(** Get parameter of a monoid *)
Definition monoidAadd `{M:Monoid} : A -> A -> A := Aadd.
Definition monoidA0 `{M:Monoid} : A := A0.

(** ** Instances *)
Section Instances.
  Import Arith ZArith QArith Qcanon Reals.
  
  Global Instance Monoid_NatAdd : Monoid Nat.add 0%nat eq.
  repeat constructor; intros; auto with arith.
  simp_proper; intros; subst; auto. apply eq_equivalence. Qed.

  Global Instance Monoid_NatMul : Monoid Nat.mul 1%nat eq.
  repeat constructor; intros; auto with arith.
  simp_proper; intros; subst; auto. apply eq_equivalence. Qed.

  Global Instance Monoid_ZAdd : Monoid Z.add 0%Z eq.
  repeat constructor; intros; auto with zarith.
  simp_proper; intros; subst; auto. Qed.

  Global Instance Monoid_ZMul : Monoid Z.mul 1%Z eq.
  repeat constructor; intros; auto with zarith.
  simp_proper; intros; subst; auto. Qed.

  Global Instance Monoid_QAdd : Monoid Qplus 0 Qeq.
  repeat constructor; intros; simpl; try ring.
  simp_proper; intros. f_equiv; auto. all: apply Q_Setoid. Qed.

  Global Instance Monoid_QMul : Monoid Qmult 1 Qeq.
  repeat constructor; intros; simpl; try ring.
  simp_proper; intros. f_equiv; auto. all: apply Q_Setoid. Qed.

  Global Instance Monoid_QcAdd : Monoid Qcplus 0 eq.
  repeat constructor; intros; try ring.
  simp_proper; intros; subst; auto. all: apply eq_equivalence. Qed.

  Global Instance Monoid_QcMul : Monoid Qcmult 1 eq.
  repeat constructor; intros; try ring.
  simp_proper; intros; subst; auto. all: apply eq_equivalence. Qed.

  Global Instance Monoid_RAdd : Monoid Rplus 0%R eq.
  repeat constructor; intros; try ring.
  simp_proper; intros; subst; auto. all: apply eq_equivalence. Qed.

  Global Instance Monoid_RMul : Monoid Rmult 1%R eq.
  repeat constructor; intros; try ring.
  simp_proper; intros; subst; auto. all: apply eq_equivalence. Qed.
  
End Instances.

(** ** Extra Theories *)

(** monoid rewriting, automatic inference the Instance. But sometimes it will fail *)
Ltac monoid_rw :=
  repeat (try rewrite identityLeft;
          try rewrite identityRight;
          try rewrite associative).

Ltac monoid_simp := intros; monoid_rw; try reflexivity; auto.

(** monoid rewriting with given monoid-instance-name.
    It is strict and powerful (such as "a + (e + b)" could be solved), 
    but less automated. *)
Ltac monoid_rw_strict M :=
  repeat (try rewrite (@identityLeft _ _ _ _ (@monoidIdL _ _ _ _ M));
          try rewrite (@identityRight _ _ _ _ (@monoidIdR _ _ _ _ M));
          try rewrite (@associative _ _ _ (@monoidAssoc _ _ _ _ M))).

Ltac monoid_simp_strict M := intros; monoid_rw_strict M; auto.

Section tac_example.
  Import Reals.
  Open Scope R.
  Goal forall a b c : R, a + (0 + b + 0) = a + b.
    intros.
    monoid_rw.
    monoid_rw_strict Monoid_RAdd. auto.
  Qed.
End tac_example.
  

(** ** Examples *)

Section Examples.
  Import Reals.
  Open Scope R.

  Goal forall a b c : R, (a * b) * c = a * (b * c).
  Proof.
    apply associative.
  Qed.
  
  Goal forall a b : R, a + ((b + 0) + 0) = a + b.
  Proof.
    intros. monoid_simp.
Qed.

End Examples.


(* ######################################################################### *)
(** * Abelian monoid *)

(** ** Class *)
Class AMonoid {A} Aadd A0 Aeq := {
    amonoidMonoid :> @Monoid A Aadd A0 Aeq;
    amonoidComm :> Commutative Aadd Aeq;
  }.

(** ** Instances *)
Section Instances.
  Import Qcanon Reals.
  
  Global Instance AMonoid_QcAdd : AMonoid Qcplus 0 eq.
  split_intro; subst; ring. Defined.

  Global Instance AMonoid_QcMul : AMonoid Qcmult 1 eq.
  split_intro; subst; ring. Defined.

  Global Instance AMonoid_RAdd : AMonoid Rplus 0%R eq.
  split_intro; subst; ring. Defined.

  Global Instance AMonoid_RMul : AMonoid Rmult 1%R eq.
  split_intro; subst; ring. Defined.

End Instances.

  
(** ** Extra Theories *)

Ltac amonoid_simp :=
  monoid_simp;
  apply commutative.


(** 交换幺半群中，将任意单个元素移动到整个表达式的头部
    转换 a1 + (... + (... + c) ...)
    到   c + (a1 + (... + ...) ...) *)
Ltac am_move2h c :=
  rewrite <- ?associative;
  try rewrite (commutative _ c);
  rewrite ?associative.

(* 在 Kalmanfilter 中，我还多加了一些策略，能够调用上面的策略来自动化简表达式，
   有需要时可移植到这里来 *)

Section Theory.

  Context `(AM : AMonoid).
  Infix "+" := Aadd.
  Infix "==" := Aeq.

  (* 如何证明这类复杂表达式（表示很复杂时，不方便使用结合律、交换律）*)
  Goal forall a b c d e : A, a + (b + c) + (d + e) == (c + e) + (d + a + b).
  Proof.
    intros.
    am_move2h a; f_equiv.
    am_move2h b; f_equiv.
    am_move2h c; f_equiv.
    am_move2h d; f_equiv.
  Qed.
  
(*   Lemma amonoid_comm : forall a b, a * b = b * a. *)
(*   Proof. apply comm. Qed. *)

(*   Lemma amonoid_comm' : forall a b, a * b = b * a. *)
(*   Proof. destruct AM. auto. Qed. *)

End Theory.

(** ** Examples *)
Section Examples.

  Import Qcanon.
  
  Goal forall a b : Qc, a * b = b * a.
  Proof.
    amonoid_simp.
  Qed.

End Examples.



(* ######################################################################### *)
(** * Group *)

(** ** Class *)
Class Group {A} Aadd A0 (Aopp : A -> A) Aeq := {
    groupMonoid :> @Monoid A Aadd A0 Aeq;
    groupInvL :> InverseLeft Aadd A0 Aopp Aeq;
    groupInvR :> InverseRight Aadd A0 Aopp Aeq;
    groupAaddProper :> Proper (Aeq ==> Aeq ==> Aeq) Aadd;
    groupAoppProper :> Proper (Aeq ==> Aeq) Aopp;
    (* groupDistrAinv :> DistributiveUnary Aop Ainv Aeq; *)
    (* groupInvoAinv :> Involution Ainv Aeq; *)
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance Group_QcAdd : Group Qcplus 0 Qcopp eq.
  split_intro; subst; ring. Defined.

  Global Instance Group_RAdd : Group Rplus 0%R Ropp eq.
  split_intro; subst; ring. Defined.

End Instances.


(** ** Extra Theories *)

(** group rewriting, automatic inference the Instance. But sometimes it will fail *)
Ltac group_rw :=
  repeat (try rewrite inverseLeft;
          try rewrite inverseRight).

(** group rewriting with given group-instance-name.
    It is strict and powerful (such as "a + (-b + b)" could be solved), 
    but less automated. *)
Ltac group_rw_strict G :=
  repeat (try rewrite (@inverseLeft _ _ _ _ _ (@groupInvL _ _ _ _ _ G));
          try rewrite (@inverseRight _ _ _ _ _ (@groupInvR _ _ _ _ _ G))).

Ltac group_simp :=
  intros;
  repeat (group_rw || monoid_rw || group_rw);
  try reflexivity;
  auto.

Ltac group_simp_strict G :=
  intros;
  repeat (group_rw_strict G ||
            monoid_simp_strict (@groupMonoid _ _ _ _ _ G) ||
              group_rw_strict G);
  try reflexivity;
  auto.

Section tac_example.
  Import Reals.
  Open Scope R_scope.
  
  Goal forall a b : R, a + (b + (a + (-a))) = a + b.
    group_simp. (* a bit complex expression cannot be solved automatically *)
  Qed.
End tac_example.

(*
  Group Theory

  1.  Arkansas Tech University / Dr. Marcel B. Finan /
      MATH 4033: Elementary Modern Algebra
  
  (a) 5 Definition and Examples of Groups
  https://faculty.atu.edu/mfinan/4033/absalg5.pdf
  (b) 14 Elementary Properties of Groups
  https://faculty.atu.edu/mfinan/4033/absalg14.pdf
 *)
Section GroupTheory.
  
  Context `{G:Group}.
  Infix "==" := Aeq.
  Infix "+" := Aadd.
  Notation "0" := A0.
  Notation "- a" := (Aopp a).
  Notation Asub := (fun x y => x + (-y)).
  Infix "-" := Asub.
  
  (** Theorem 5.1 *)
  (* Note that, I give two theorem rather than one. *)
  Theorem group_id_uniq_l : forall e', (forall a, e' + a == a) -> e' == 0.
  Proof.
    intros.
    (* e = e' + e = e' *)
    assert (e' == e' + 0) by monoid_simp.
    assert (e' + 0 == 0); auto.
    rewrite H0. rewrite <- H1 at 2. easy.
  Qed.

  Theorem group_id_uniq_r : forall e', (forall a, a + e' == a) -> e' == 0.
  Proof.
    intros.
    (* e = e + e' = e' *)
    assert (0 == 0 + e'). { rewrite H. easy. }
    assert (0 + e' == e') by group_simp.
    apply transitivity with (0 + e'); auto. group_simp.
  Qed.

  (* Note that, I give two theorem rather than one. *)
  Theorem group_inv_uniq_l : forall x1 x2 y, x1 + y == 0 /\ y + x2 == 0 -> x1 == x2.
  Proof.
    intros. destruct H as [Ha Hb].
    (* x1 = x1+e = x1+(y+x2) = (x1+y)+x2 = e+x2 = x2 *)
    assert (x1 == x1 + 0) by group_simp.
    rewrite H. rewrite <- Hb. rewrite <- associative.
    rewrite Ha. group_simp.
  Qed.

  Theorem group_inv_uniq_r : forall x y1 y2, x + y1 == 0 /\ y2 + x == 0 -> y1 == y2.
  Proof.
    intros. destruct H as [Ha Hb].
    (* y1 = e+y1 = (y2+x)+y1 = y2+(x+y1) = y2+e = y2 *)
    assert (y1 == 0 + y1) by group_simp.
    rewrite H. rewrite <- Hb. rewrite associative.
    rewrite Ha. group_simp.
  Qed.

  (** Theorem 14.1 *)
  Theorem group_cancel_l : forall x y1 y2, x + y1 == x + y2 -> y1 == y2.
  Proof.
    intros.
    (* y1 = e+y1 = (-x+x)+y1 = (-x)+(x+y1) = (-x) + (x+y2) = e+y2 = y2 *)
    rewrite <- identityLeft.
    setoid_replace 0 with (-x + x) by group_simp.
    rewrite associative. rewrite H. rewrite <- associative.
    group_simp.
  Qed.

  Theorem group_cancel_r : forall x1 x2 y, x1 + y == x2 + y -> x1 == x2.
  Proof.
    intros.
    (* x1 = x1+e = x1+(y+ -y) = (x1+y)+(-y) = (x2+y)+(-y) = x2+e = x2 *)
    rewrite <- identityRight.
    setoid_replace 0 with (y + (-y)) by group_simp.
    rewrite <- associative. rewrite H. rewrite associative.
    group_simp.
  Qed.

  Theorem group_inv_inv : forall x,  - - x == x.
  Proof.
    intros. apply group_cancel_l with (- x). group_simp.
  Qed.

  Theorem group_inv_distr : forall x y, - (x + y) == (- y) + (- x).
  Proof.
    intros.
    (* (x+y)+ -(x+y) = e = x+ -x = x+e+ -x = x+(y+ -y)+ -x
      = (x+y)+(-y+ -x), by cancel_l, got it *)
    apply group_cancel_l with (x + y).
    rewrite inverseRight. rewrite <- associative. rewrite (associative x y).
    (* group_simp. (* Tips: it is not so smart to solve "0 + -x" automatically *) *)
    group_simp_strict G.
  Qed.
    
  (** Theorem 14.2 *)
  (* a + x = b -> x = (-a) + b *)
  Theorem group_equation_sol_l : forall a b x, a + x == b -> x == (- a) + b.
  Proof.
    intros.
    (* left add a at two side *)
    apply group_cancel_l with (a).
    rewrite <- associative.
    (* group_simp. (* Tips: not finished yet. *) *)
    group_simp_strict G.
  Qed.

  (* a + x = b /\ a + y = b -> x = -a + b /\ y = -a + b *)
  Theorem group_equation_sol_l_uniq : 
    forall a b x y, (a + x == b /\ a + y == b) -> (x == -a + b /\ y == -a + b).
  Proof.
    intros. destruct H. split.
    apply group_equation_sol_l; auto.
    apply group_equation_sol_l; auto.
  Qed.

  (* x + a = b -> x = b + (-a) *)
  Theorem group_equation_sol_r : forall a b x, x + a == b -> x == b + (- a).
  Proof.
    intros.
    (* right mult a *)
    apply group_cancel_r with (a).
    (* group_simp. (* Tips: not finished yet. *) *)
    group_simp_strict G.
  Qed.

  (* (x + a = b /\ y + a = b) -> (x = b + -a /\ y = b + -a) *)
  Theorem group_equation_sol_r_uniq : 
    forall a b x y, (x + a == b /\ y + a == b) -> (x == b + (- a) /\ y == b + (- a)).
  Proof.
    intros; destruct H. split.
    apply group_equation_sol_r; auto.
    apply group_equation_sol_r; auto.
  Qed.

  (** Definition 14.1 (multiple operations) *)
  (* batch : list A -> A
    [] = e
    [a1] = a1
    [a1;a2] = a1 * a2
    [a1;a2;a3] = (a1*a2)*a3
    [a1;a2;...;a_n-1;an] = ((...(a1*a2)* ... )*a_n-1)*an *)
  Definition group_batch (l:list A) :=
    match l with
    | [] => 0
    | x :: l' => fold_left Aadd l' x
    end.
  
  Section test.
    Variable (a1 a2 a3 a4 : A).
    
    (* Compute group_batch []. *)
    (* Compute group_batch [a1]. *)
    (* Compute group_batch [a1;a2]. *)
    (* Compute group_batch [a1;a2;a3]. *)
    (* Compute group_batch [a1;a2;a3;a4]. *)

  End test.

  (** Theorem 14.3 (Generalized Associative Law) *)
  Section th14_3.

    Notation "'Σ' a '&' l " := (fold_left Aadd l a) (at level 10).

    (** (a1+...+as) + (b1+...+bt) = a1+...+as + b1+...+bt *)
    Theorem group_assoc_general (l1 l2 : list A) :
      (group_batch l1) + (group_batch l2) == group_batch (l1 ++ l2).
    Proof.
      (* reduct to fold_left *)
      destruct l1,l2; simpl; group_simp.
      - rewrite app_nil_r. group_simp.
      - rename a into a1, a0 into a2.
        (* H1. forall a l1 l2, Σ a & (l1 ++ l2) = Σ (Σ a & l1) & l2
           H2. forall a b l, a + Σ b & l = Σ (a + b) & l
           H3. forall a b l, Σ a & (b :: l) = Σ (a + b) & l
           by H1, right = Σ (Σ a1 & l1) & (a2 :: l2).
           by H2, left  = Σ ((Σ a1 & l1) + a2) & l2).
           remember (Σ a1 & l1) as c, then goal become to
              Σ (c + a2) & l2 = Σ c & (a2 :: l2)
           by H3, we got it. *)
        assert (forall a l1 l2, Σ a & (l1 ++ l2) == Σ (Σ a & l1) & l2) as H1.
        { intros a l0. gd a. induction l0; intros; try reflexivity.
          simpl. rewrite IHl0. reflexivity. }
        assert (forall a b l, a + Σ b & l == Σ (a + b) & l) as H2.
        { intros. gd b. gd a. induction l; simpl; intros; try reflexivity.
          simpl. rewrite IHl.
          (** fold_left preveres the aeq *)
          assert (forall l a1 a2, a1 == a2 -> Σ a1 & l == Σ a2 & l).
          { induction l0; intros; simpl in *; auto.
            apply IHl0. rewrite H. easy. }
          apply H. group_simp. }
        assert (forall a b l, Σ a & (b :: l) == Σ (a + b) & l) as H3.
        { intros. gd b. gd a. induction l; intros; auto. easy. easy. }
        rewrite H1. rewrite H2. rewrite H3. easy.
    Qed.
    
  End th14_3.

  Section th14_4.

    Import ZArith.

    (** Definition 14.2 (power)
      a ^ 0      = e
      a ^ n      = a ^ (n-1) * a, for n >= 1
      a ^ (-n)   = (-a) ^ n,  for n >= 1
     *)
    Definition group_power (a : A) (n : Z) : A :=
      match n with
      | Z0 => 0
      | Zpos m => iterate (fun x => Aadd x a) (Pos.to_nat m) 0
      | Z.neg m => iterate (fun x => Aadd x (Aopp a)) (Pos.to_nat m) 0
      end.
    Infix "^" := group_power.
    
    Section test.
      Variable (a1 a2 a3 a4 : A).
      (* Compute group_power a1 3. *)
      (* Compute group_power a1 (-3). *)

    End test.

    (** Remark 14.2 *)
    Lemma group_power_eq1 (n : Z) :
      match n with
      | Z0 => forall a, a ^ n = 0
      | Zpos m => forall a, a ^ n = group_batch (repeat a (Z.to_nat n))
      | Zneg m => forall a, a ^ n = group_batch (repeat (-a) (Z.to_nat (-n)))
      end.
    Proof.
      destruct n; intros; auto.
    Admitted.

    (** Theorem 14.4 *)
    Theorem group_power_inv : forall a n, (a^n) + (a^(- n)) = 0.
    Admitted.

    Theorem group_power_plus : forall a m n, (a^m) + (a^n) = a^(m+n).
    Admitted.

    Theorem group_power_mul : forall a m n, (a^m)^n = a^(m*n).
    Admitted.

  End th14_4.

  
  (** *** Below, these properties are not in textbook *)
  Section additional_props.
  
    Theorem group_inv_id : - 0 == 0.
    Proof.
      (* -e = -e + e = e *)
      rewrite <- identityRight at 1. group_simp.
    Qed.

  End additional_props.

End GroupTheory.

(** ** Examples *)
Section Examples.
  
  Import Reals.
  Open Scope R.

  Goal (- 0 = 0).
    rewrite group_inv_id. auto. Qed.
  
  Goal forall x1 x2 y : R, (x1 + y = 0 /\ y + x2 = 0 -> x1 = x2)%R.
    apply group_inv_uniq_l. Qed.

End Examples.


(* ######################################################################### *)
(** * Abelian Group *)
(* ######################################################################### *)
(** ** Class *)
(** ** Instances *)
(** ** Extra Theories *)
(** ** Examples *)

(* ======================================================================= *)
(** ** Definition and theory *)

Class AGroup {A} Aadd A0 Aopp Aeq := {
    agroupGroup :> @Group A Aadd A0 Aopp Aeq;
    agroupAM :> @AMonoid A Aadd A0 Aeq;
    agroupComm :> Commutative Aadd Aeq;
  }.

Global Coercion agroupGroup : AGroup >-> Group.

Ltac agroup_simp :=
  group_simp;
  try apply commutative.

Section Theory.
  
  Context `{AG : AGroup}.
  Infix "==" := Aeq.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation "a - b" := (a + (-b)).

  (** a - b = - (b - a) *)
  Lemma agroup_sub_comm : forall a b, a - b == - (b - a).
  Proof. intros. rewrite (group_inv_distr). rewrite (group_inv_inv). easy. Qed.

  (** (a - b) - c = (a - c) - b *)
  Lemma agroup_sub_perm : forall a b c, (a - b) - c == (a - c) - b.
  Proof. intros. rewrite ?associative. rewrite (commutative (-b)). easy. Qed.

  (** - (a + b) = (-a) + (-b) *)
  Lemma agroup_sub_distr : forall a b, - (a + b) == -a + (-b).
  Proof. intros. rewrite (group_inv_distr). agroup_simp. Qed.

  (** (a - b) - c = a - (b + c) *)
  Lemma agroup_sub_assoc : forall a b c, (a - b) - c == a - (b + c).
  Proof. intros. rewrite ?associative. rewrite agroup_sub_distr. easy. Qed.
  
End Theory.

(* ======================================================================= *)
(** ** Instances *)
Section Instances.

  Import ZArith QArith Qcanon Reals.
  
  Global Instance AGroup_ZAdd : AGroup Z.add 0%Z Z.opp eq.
  split_intro; subst; ring. Qed.

  Global Instance AGroup_QAdd : AGroup Qplus 0 Qopp Qeq.
  split_intro; try rewrite ?H,?H0; simpl; try easy; try ring. Qed.

  Global Instance AGroup_QcAdd : AGroup Qcplus 0 Qcopp eq.
  split_intro; subst; ring. Qed.

  Global Instance AGroup_RAdd : AGroup Rplus 0%R Ropp eq.
  split_intro; subst; ring. Qed.

End Instances.

Section example.
  Import Reals.
  Open Scope R.
  
  Goal forall a b c : R, ((a - b) - c = a - (b + c))%R.
    intros. apply agroup_sub_assoc. Qed.
  
  Goal forall a , a + - 0 = a.
    intros. rewrite group_inv_id. group_simp. Qed.
  
End example.


(* ######################################################################### *)
(** * Ring*)

(** ** Class *)

(* Note that, in mathematics, mul needn't commutative, but ring_theory in Coq 
   need it. Because we want use ring tactic, so add this properties. *)
Class Ring {A} Aadd A0 Aopp Amul A1 Aeq := {
    ringAddAG :> @AGroup A Aadd A0 Aopp Aeq;
    ringMulAM :> @AMonoid A Amul A1 Aeq;
    ringDistrL :> DistributiveLeft Aadd Amul Aeq;
    ringDistrR :> DistributiveRight Aadd Amul Aeq;
  }.

(** ** Instances *)
Section Instances.

  Import ZArith QArith Qcanon Reals.
  
  Global Instance Ring_Z : Ring Z.add 0%Z Z.opp Z.mul 1%Z eq.
  split_intro; subst; ring. Qed.

  Global Instance Ring_Q : Ring Qplus 0 Qopp Qmult 1 Qeq.
  split_intro; rewrite ?H, ?H0; simpl; try ring. Qed.

  Global Instance Ring_Qc : Ring Qcplus 0 Qcopp Qcmult 1 eq.
  split_intro; subst; ring. Qed.

  Global Instance Ring_R : Ring Rplus R0 Ropp Rmult R1 eq.
  split_intro; subst; ring. Qed.

End Instances.

(** ** Extra Theories *)

(** make a coq ring object from our Ring object *)
Lemma make_ring_theory `(R : Ring) :
  ring_theory A0 A1 Aadd Amul (fun a b => Aadd a (Aopp b)) Aopp Aeq.
Proof.
  constructor; intros;
    try (rewrite ?identityLeft,?associative; reflexivity);
    try (rewrite commutative; reflexivity).
  rewrite distributiveRight; reflexivity.
  rewrite inverseRight; reflexivity.
Qed.

Section Theory.

  Context `(R:Ring).

  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + -b).
  Infix "*" := Amul : A_scope.

  Add Ring ring_inst : (make_ring_theory R).

End Theory.

(** ** Examples *)

Section Examples.

  Import Reals.
  
  Goal forall a b c : R, (a * (b + c) = a * b + a * c)%R.
    apply distributiveLeft. Qed.

End Examples.


(** This example declares an abstract ring structure, and shows how to use fewer code 
    to enable "ring" tactic. *)
Module Demo_AbsRing.
  Context `{R : Ring}.
  Infix "==" := Aeq.
  Infix "+" := Aadd.
  Infix "*" := Amul.
  Notation "0" := A0.
  Notation "1" := A1.

  Add Ring ring_thy_inst : (make_ring_theory R).

  Goal forall a b c : A, (a + b) * c == 0 + b * c * 1 + 0 + 1 * c * a.
  Proof. intros. ring. Qed.
  
End Demo_AbsRing.

(** This is a concrete ring structure *)
Module Demo_ConcrateRing.
  (*
A={a b e}.
+ 0 1 2 3
0 0 1 2 3
1 1 2 3 0
2 2 3 0 1

* 0 1 2 3
0 0 0 0 0
1 0 1 2 3
2 0 2 0 2
3 0 3 2 1
   *)
  Inductive A := A0 | A1 | A2 | A3.
  Notation "0" := A0. Notation "1" := A1.
  Notation "2" := A2. Notation "3" := A3.

  Definition add  (a b : A) :=
    match a,b with
    | 0,_ => b
    | 1,0 => 1 | 1,1 => 2 | 1,2 => 3 | 1,3 => 0
    | 2,0 => 2 | 2,1 => 3 | 2,2 => 0 | 2,3 => 1
    | 3,0 => 3 | 3,1 => 0 | 3,2 => 1 | 3,3 => 2
    end.
  Infix "+" := add.

  Definition opp (a:A) :=
    match a with
    | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1
    end.
  Notation "- a" := (opp a).
  Notation "a - b" := (a + (-b)).
  
  Definition mul  (a b : A) :=
    match a,b with
    | 0,_ => 0
    | 1,_ => b
    | 2,0 => 0 | 2,1 => 2 | 2,2 => 0 | 2,3 => 2
    | 3,0 => 0 | 3,1 => 3 | 3,2 => 2 | 3,3 => 1
    end.
  Infix "*" := mul.

  Lemma add_comm : forall a b, a + b = b + a.
  Proof. destruct a,b; auto. Qed.

  Lemma ring_thy : ring_theory 0 1 add mul (fun x y => add x (opp y)) opp eq.
  Proof.
    constructor; auto;
      try (destruct x,y; auto); try destruct z; auto.
    intros. destruct x; auto.
  Qed.

  Add Ring ring_thy_inst : ring_thy.

  Goal forall a b c : A, a + b + c - b = a + c.
  Proof.
    (* Tips, the proof is simple *)
    intros. ring.
  Qed.
  
End Demo_ConcrateRing.
  

(* ######################################################################### *)
(** * Field *)

(** ** Class *)
Class Field {A} Aadd A0 Aopp Amul A1 Ainv Aeq := {
    (** Field: Ring + mult inversion + (1≠0) *)
    fieldRing :> @Ring A Aadd A0 Aopp Amul A1 Aeq;
    field_mulInvL : forall a, ~(Aeq a A0) -> Aeq (Amul (Ainv a) a) A1;
    field_1_neq_0 : ~(Aeq A1 A0);
    (** additional: Ainv is proper morphism *)
    fieldAinvProper :> Proper (Aeq ==> Aeq) Ainv
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance Field_Qc : Field Qcplus 0 Qcopp Qcmult 1 Qcinv eq.
  split_intro; subst; (try (field; reflexivity)); try easy. field. auto. Qed.

  Global Instance Field_R : Field Rplus R0 Ropp Rmult R1 Rinv eq.
  split_intro; subst; try (field; reflexivity); auto. field; auto.
  auto with real. Qed.

End Instances.


(** ** Extra Theories *)

(** make a coq field object from our Field object *)
Lemma make_field_theory `(F : Field):
  field_theory A0 A1 Aadd Amul
               (fun a b => Aadd a (Aopp b)) Aopp
               (fun a b => Amul a (Ainv b)) Ainv Aeq.
Proof.
  constructor; intros;
    try (rewrite ?identityLeft,?associative; reflexivity);
    try (rewrite commutative; reflexivity).
  apply (make_ring_theory fieldRing).
  apply field_1_neq_0.
  apply field_mulInvL. auto.
Qed.

Section Theory.

  Context `{F:Field}.
  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun x y => ~ x == y)%A : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + -b).
  Notation "0" := A0 : A_scope.
  Notation "1" := A1 : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/b)).
  Infix "/" := Adiv : A_scope.

  Add Field field_inst : (make_field_theory F).

  (** a <> 0 -> /a * a = 1 *)
  Lemma field_mul_inv_l : forall a : A, (a != 0) -> /a * a == 1.
  Proof. intros. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> a * /a = 1 *)
  Lemma field_mul_inv_r : forall a : A, (a != 0) -> a * /a == 1.
  Proof. intros. rewrite commutative. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> (1/a) * a = 1 *)
  Lemma field_mul_inv1_l : forall a : A, (a != 0) -> (1/a) * a == 1.
  Proof. intros. simpl. group_simp. apply field_mul_inv_l. auto. Qed.
  
  (** a <> 0 -> a * (1/a) = 1 *)
  Lemma field_mul_inv1_r : forall a : A, (a != 0) -> a * (1/a) == 1.
  Proof. intros. simpl. group_simp. apply field_mul_inv_r. auto. Qed.
  
  (** a <> 0 -> a * b = a * c -> b = c *)
  Lemma field_mul_cancel_l : forall a b c : A, (a != 0) -> a * b == a * c -> b == c.
  Proof.
    intros.
    assert (/a * (a * b) == /a * (a * c)).
    { rewrite H0. easy. }
    rewrite <- ?associative in H1.
    rewrite field_mulInvL in H1; auto.
    rewrite ?identityLeft in H1. easy.
  Qed.

  (** c <> 0 -> a * c = b * c -> a = b *)
  Lemma field_mul_cancel_r : forall a b c : A, (c != 0) -> a * c == b * c -> a == b.
  Proof.
    intros.
    assert ((a * c) * /c == (b * c) * /c).
    { rewrite H0. easy. }
    rewrite ?associative in H1.
    rewrite field_mul_inv_r in H1; auto.
    rewrite ?identityRight in H1. easy.
  Qed.

  (** a * b = 0 -> a = 0 \/ b = 0 *)
  Lemma field_mul_eq0_imply_a0_or_b0 : forall (a b : A) (HDec : Decidable Aeq),
      a * b == 0 -> (a == 0) \/ (b == 0).
  Proof.
    intros.
    destruct (a ==? 0), (b ==? 0); auto.
    assert (/a * a * b == 0).
    { rewrite associative. rewrite H. field. auto. }
    rewrite field_mulInvL in H0; auto.
    rewrite identityLeft in H0. easy.
  Qed.

  (** a * b = b -> a = 1 \/ b = 0 *)
  Lemma field_mul_eq_imply_a1_or_b0 : forall (a b : A) (HDec : Decidable Aeq),
      a * b == b -> (a == 1) \/ (b == 0).
  Proof.
    intros. destruct (a ==? 1), (b ==? 0); auto.
    (* auto. left; auto. *)
    (* apply symmetry in H. *)
    setoid_replace b with (1 * b) in H at 2 by group_simp.
    apply field_mul_cancel_r in H; auto. 
  Qed.

End Theory.

(** ** Examples *)
Section Examples.

  Import Reals.
  
  Goal forall a b : R, ((a <> 0) -> /a * a = 1)%R.
    intros. apply field_mulInvL. auto. Qed.

End Examples.


(* ######################################################################### *)
(** * Linear Space *)

(** ** Class *)
Class LinearSpace `{F : Field} {V : Type}
  (Vadd : V -> V -> V) (V0 : V) (Vopp : V -> V) (Vcmul : A -> V -> V)
  (Veq : relation V) := {
    ls_addC : Commutative Vadd Veq;
    ls_addA : Associative Vadd Veq;
    ls_add_0_r : IdentityRight Vadd V0 Veq;
    ls_add_inv_r : InverseRight Vadd V0 Vopp Veq;
    ls_cmul_1_l : forall u : V, Veq (Vcmul A1 u) u;
    lc_cmul_assoc : forall a b u, Veq (Vcmul (Amul a b) u) (Vcmul a (Vcmul b u));
    lc_cmul_aadd_distr : forall a b u,
      Veq (Vcmul (Aadd a b) u) (Vadd (Vcmul a u) (Vcmul b u));
    lc_cmul_vadd_distr : forall a u v,
      Veq (Vcmul a (Vadd u v)) (Vadd (Vcmul a u) (Vcmul a v));
  }.

(** ** Instances *)
Section Instances.

  (** A field itself is a liner space *)
  Section field_is_linearspace.
    Context `{F : Field}.
    Add Field field_inst : (make_field_theory F).
    
    Global Instance LinearSpace_Field : LinearSpace Aadd A0 Aopp Amul Aeq.
    split_intro; try field. Qed.
    
  End field_is_linearspace.

End Instances.


(** ** Extra Theories *)

Section Theory.

  Context `{LS : LinearSpace}.
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/b)).
  Infix "/" := Adiv : A_scope.

  Infix "==" := Veq : LinearSpace_scope.
  Infix "+" := Vadd : LinearSpace_scope.
  Notation "- a" := (Vopp a) : LinearSpace_scope.
  Notation Vsub := (fun a b => a + -b).
  Infix "-" := Vsub : LinearSpace_scope.
  Infix "c*" := Vcmul : LinearSpace_scope.

  (** V中零元是唯一的。已内置 *)

  (** V中每个元素的负元是唯一的。已内置 *)

  (** 0 * v = 0 *)
  Theorem LS_cmul_0_l : forall v : V, A0 c* v == V0.
  Proof. Abort.
  
End Theory.

(** ** Examples *)
Section Examples.

End Examples.

