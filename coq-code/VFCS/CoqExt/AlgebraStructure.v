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
Generalizable Variables A Aadd Aopp Amul Ainv Adiv.


(* ######################################################################### *)
(** * Small utilities *)

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

(* (** eqlistA is a equivalence relation *) *)
(* Global Instance Equivalence_eqlistA `{Equiv_Aeq:Equivalence A Aeq} *)
(*   : Equivalence (eqlistA Aeq). *)
(* Proof. apply eqlistA_equiv. auto. Defined. *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * A relation is decidable *)

(** ** Class *)

Class Decidable {A : Type} := {
    decidable : forall (a b : A), {a = b} + {a <> b};
  }.
(* Global Hint Constructors Decidable : core. *)

(** ** Instances *)

Section Instances.
  Import Arith ZArith Reals.

  Global Instance Decidable_NatEq : @Decidable nat.
  Proof. constructor. apply Nat.eq_dec. Qed.

  Global Instance Decidable_Z : @Decidable Z.
  Proof. constructor. apply Z.eq_dec. Qed.

  Global Instance Decidable_R : @Decidable R.
  Proof. constructor. apply Req_EM_T. Qed.
  
  Global Instance Decidable_list `{Dec:Decidable} : @Decidable (list A).
  Proof. constructor. apply list_eq_dec. apply decidable. Qed.

  Global Instance Decidable_dlist `{Dec:Decidable} : @Decidable (list (list A)).
  Proof. constructor. apply decidable. Qed.

End Instances.

(** ** Extra Theories *)
Section Dec_theory.

  Context `{Dec : Decidable}.

  (** Tips: these theories are useful for R type *)
  
  (** Calculate equality to boolean, with the help of equality decidability *)
  Definition Aeqb (a b : A) : bool := if decidable a b then true else false.

  (** Aeqb is true iff equal. *)
  Lemma Aeqb_true : forall a b, Aeqb a b = true <-> a = b.
  Proof.
    intros. unfold Aeqb. destruct decidable; split; intros; easy.
  Qed.

  (** Aeqb is false iff not equal *)
  Lemma Aeqb_false : forall a b, Aeqb a b = false <-> a <> b.
  Proof.
    intros. unfold Aeqb. destruct decidable; split; intros; easy.
  Qed.

  Lemma Aeq_reflect : forall a b : A, reflect (a =  b) (Aeqb a b).
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
Class Associative {A : Type} (Aop : A -> A -> A) := {
    associative : forall a b c, Aop (Aop a b) c = Aop a (Aop b c);
  }.

(** ** Instances *)
Global Instance Assoc_NatAdd : Associative Nat.add.
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
Class Commutative {A : Type} (Aop : A -> A -> A) := {
    commutative : forall a b, Aop a b = Aop b a
  }.

(** ** Instances *)
Global Instance Comm_NatAdd : Commutative Nat.add.
constructor. auto with arith. Qed.

Global Instance Comm_NatMul : Commutative Nat.mul.
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
Class IdentityLeft {A : Type} (Aop : A -> A -> A) (Ae : A) := {
    identityLeft : forall a, Aop Ae a = a
  }.

Class IdentityRight {A : Type} (Aop : A -> A -> A) (Ae : A) := {
    identityRight : forall a, Aop a Ae = a
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Inverse Left/Right *)

(** ** Class *)
Class InverseLeft {A : Type} (Aop : A -> A -> A) (Ae : A) (Aopinv : A -> A) := {
    inverseLeft : forall a, Aop (Aopinv a) a = Ae
  }.

Class InverseRight {A : Type} (Aop : A -> A -> A) (Ae : A) (Aopinv : A -> A) := {
    inverseRight : forall a, Aop a (Aopinv a) = Ae
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

Class DistributiveLeft {A : Type} (Aadd Amul : A -> A -> A) := {
    distributiveLeft : forall a b c,
      Amul a (Aadd b c) = Aadd (Amul a b) (Amul a c)
  }.

Class DistributiveRight {A : Type} (Aadd Amul : A -> A -> A) := {
    distributiveRight : forall a b c,
      Amul (Aadd a b) c = Aadd (Amul a c) (Amul b c)
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

Class Injective {A B : Type} (ϕ : A -> B) := {
    injective : forall a1 a2 : A, a1 <> a2 -> ϕ a1 <> ϕ a2
  }.
  
(** ** Instances *)

(** ** Extra Theories *)
Section theory.
  Context {A B : Type}.
  
  (** Second form of injective *)
  Definition injective_form2 (ϕ : A -> B) :=
    forall (a1 a2 : A), ϕ a1 = ϕ a2 -> a1 = a2.

  (** These two forms are equal *)
  Lemma injective_eq_injective_form2 (ϕ: A -> B) :
    Injective ϕ <-> injective_form2 ϕ.
  Proof.
    split; intros.
    - hnf. destruct H as [H]. intros.
      specialize (H a1 a2). apply imply_to_or in H. destruct H; try easy.
      apply NNPP in H. auto.
    - hnf in H. constructor. intros. intro. apply H in H1. easy.
  Qed.

  (** Injective function preserve equal relation *)
  Lemma inj_pres_eq : forall (ϕ : A -> B),
      Injective ϕ -> (forall a1 a2 : A, ϕ a1 = ϕ a2 -> a1 = a2).
  Proof.
    intros. apply injective_eq_injective_form2 in H. apply H. auto.
  Qed.

End theory.

(** ** Examples *)



(* ######################################################################### *)
(** * Surjective *)

(** ** Class *)

Class Surjective {A B : Type} (ϕ: A -> B) := {
    surjective : forall (b : B), (exists (a : A), ϕ a = b)
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Bijective *)

(** ** Class *)

Class Bijective {A B : Type} (ϕ: A -> B) := {
    bijInjective :> Injective ϕ;
    bijSurjective :> Surjective ϕ
  }.

(** ** Instances *)

(** ** Extra Theories *)
Section theory.
  Context {A B: Type}.
  
  (** There exist inverse function from a bijective function.

      ref: https://stackoverflow.com/questions/62464821/
      how-to-make-an-inverse-function-in-coq

      Tips: there are two methods to formalize "existential", sig and ex.
      ex makes a Prop, sig makes a Type. 
      Here, we proof the ex version. the sig version could be derived by an axiom:
      [constructive_definite_description : 
      forall (A : Type) (P : A -> Prop), (exists ! x : A, P x) -> {x : A | P x} ]
   *)

  Lemma bij_inverse_exist : forall (ϕ : A -> B) (Hbij: Bijective ϕ),
    {ψ : B -> A | (forall a : A, (ψ (ϕ a)) = a) /\  (forall b : B, ϕ (ψ b) = b)}.
  Proof.
    intros. destruct Hbij as [Hinj [Hsurj]].
    apply injective_eq_injective_form2 in Hinj. hnf in *.
    apply constructive_definite_description.
    assert (H : forall b, exists! a, ϕ a = b).
    { intros b.
      destruct (Hsurj b) as [a Pa].
      exists a; split; trivial.
      intros a' Pa'. apply Hinj. rewrite Pa, Pa'. auto. }
    exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
    split.
    - split.
      + intros a.
        destruct (constructive_definite_description _ _). simpl.
        apply Hinj. auto.
      + intros b.
        destruct (constructive_definite_description _ _). simpl. auto.
    - intros g' [H1 H2].
      apply functional_extensionality.
      intros b.
      destruct (constructive_definite_description _ _) as [a Ha].
      simpl. rewrite <- Ha, H1. auto.
  Qed.    

End theory.

(** ** Examples *)



(* ######################################################################### *)
(** * Homomorphic  *)

(** ** Class *)

Class Homomorphic {A B : Type} (fa : A -> A -> A) (fb : B -> B -> B) (ϕ : A -> B) := {
    homomorphic : forall (a1 a2 : A), ϕ (fa a1 a2) = fb (ϕ a1) (ϕ a2)
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
Class Homomorphism {A B : Type} (fa : A -> A -> A) (fb : B -> B -> B) := {
    homomorphism : exists (ϕ: A -> B), Homomorphic fa fb ϕ /\ Surjective ϕ
  }.

(** If there exist two homomorphic and surjective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is homomorphism *)
Class Homomorphism2 {A B : Type} (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    homomorphism2 : exists (ϕ: A -> B),
      Homomorphic fa fb ϕ /\ Homomorphic ga gb ϕ /\ Surjective ϕ
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Isomorphism *)

(** ** Class *)

(** If there exist a homomorphic and bijective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is isomorphism *)
Class Isomorphism {A B : Type} (fa : A -> A -> A) (fb : B -> B -> B) := {
    isomorphism : exists (ϕ: A -> B), Homomorphic fa fb ϕ /\ Bijective ϕ
  }.

(** If there exist two homomorphic and bijective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is isomorphism *)
Class Isomorphism2 {A B : Type} (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    isomorphism2 : exists (ϕ: A -> B),
      Homomorphic fa fb ϕ /\ Homomorphic ga gb ϕ /\ Bijective ϕ
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Monoid *)

(** ** Class *)
Class Monoid {A : Type} (Aadd : A -> A -> A) (A0 : A) := {
    monoidAssoc :> Associative Aadd;
    monoidIdL :> IdentityLeft Aadd A0;
    monoidIdR :> IdentityRight Aadd A0;
  }.

(** Get parameter of a monoid *)
Definition monoidAadd `{M:Monoid} : A -> A -> A := Aadd.
Definition monoidA0 `{M:Monoid} : A := A0.

(** ** Instances *)
Section Instances.
  Import Arith ZArith Qcanon Reals.
  
  Global Instance Monoid_NatAdd : Monoid Nat.add 0%nat.
  repeat constructor; intros; auto with arith. Qed.

  Global Instance Monoid_NatMul : Monoid Nat.mul 1%nat.
  repeat constructor; intros; auto with arith. Qed.

  Global Instance Monoid_ZAdd : Monoid Z.add 0%Z.
  repeat constructor; intros; auto with zarith. Qed.

  Global Instance Monoid_ZMul : Monoid Z.mul 1%Z.
  repeat constructor; intros; auto with zarith. Qed.

  Global Instance Monoid_QcAdd : Monoid Qcplus 0.
  repeat constructor; intros; ring. Qed.

  Global Instance Monoid_QcMul : Monoid Qcmult 1.
  repeat constructor; intros; ring. Qed.

  Global Instance Monoid_RAdd : Monoid Rplus 0%R.
  repeat constructor; intros; ring. Qed.

  Global Instance Monoid_RMul : Monoid Rmult 1%R.
  repeat constructor; intros; ring. Qed.
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
  repeat (try rewrite (@identityLeft _ _ _ (@monoidIdL _ _ _ M));
          try rewrite (@identityRight _ _ _ (@monoidIdR _ _ _ M));
          try rewrite (@associative _ _ (@monoidAssoc _ _ _ M))).

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
    intros.
    Fail rewrite identityRight. (* fail here *)
    monoid_simp. (* no expected effect *)
    monoid_simp_strict Monoid_RAdd. (* it succeed *)
Qed.

End Examples.


(* ######################################################################### *)
(** * Abelian monoid *)

(** ** Class *)
Class AMonoid {A} Aadd A0 := {
    amonoidMonoid :> @Monoid A Aadd A0;
    amonoidComm :> Commutative Aadd;
  }.

(** ** Instances *)
Section Instances.
  Import Qcanon Reals.
  
  Global Instance AMonoid_QcAdd : AMonoid Qcplus 0.
  repeat constructor; intros; ring. Qed.

  Global Instance AMonoid_QcMul : AMonoid Qcmult 1.
  repeat constructor; intros; ring. Qed.

  Global Instance AMonoid_RAdd : AMonoid Rplus 0%R.
  repeat constructor; intros; ring. Qed.

  Global Instance AMonoid_RMul : AMonoid Rmult 1%R.
  repeat constructor; intros; ring. Qed.

End Instances.

  
(** ** Extra Theories *)

Ltac amonoid_simp :=
  monoid_simp;
  apply commutative.

(* Section Theory. *)

(*   Context `(AM : AMonoid). *)
(*   Infix "*" := op. *)

(*   Lemma amonoid_comm : forall a b, a * b = b * a. *)
(*   Proof. apply comm. Qed. *)

(*   Lemma amonoid_comm' : forall a b, a * b = b * a. *)
(*   Proof. destruct AM. auto. Qed. *)

(* End Theory. *)

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
Class Group {A} Aadd A0 (Aopp : A -> A) := {
    groupMonoid :> @Monoid A Aadd A0;
    groupInvL :> InverseLeft Aadd A0 Aopp;
    groupInvR :> InverseRight Aadd A0 Aopp;
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance Group_QcAdd : Group Qcplus 0 Qcopp.
  repeat constructor; intros; ring. Qed.

  Global Instance Group_RAdd : Group Rplus 0%R Ropp.
  repeat constructor; intros; ring. Qed.

End Instances.


(** ** Extra Theories *)

Ltac group_rw :=
  rewrite inverseLeft ||
    rewrite inverseRight.

Ltac group_rw_strict G :=
  rewrite inverseLeft ||
    rewrite inverseRight.

Ltac group_simp :=
  repeat (group_rw || monoid_rw || group_rw);
  try reflexivity;
  auto.

Ltac group_simp_strict G :=
  repeat (group_rw ||
            monoid_simp_strict (@groupMonoid _ _ _ _ G) ||
              group_rw);
  try reflexivity;
  auto.

Section tac_example.
  Import Reals.
  Open Scope R_scope.
  
  Goal forall a b : R, a + (b + (a + (-a))) = a + b.
    group_simp. (* a bit complex expression cannot be solved automatically *)
    group_simp_strict Group_RAdd.
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
  Infix "+" := Aadd.
  Notation "0" := A0.
  Notation "- a" := (Aopp a).
  Notation Asub := (fun x y => x + (-y)).
  Infix "-" := Asub.
  
  (** Theorem 5.1 *)
  (* Note that, I give two theorem rather than one. *)
  Theorem group_id_uniq_l : forall e', (forall a, e' + a = a) -> e' = 0.
  Proof.
    intros.
    (* e = e' + e = e' *)
    assert (e' = e' + 0) by monoid_simp.
    assert (e' + 0 = 0); auto.
    rewrite H0. rewrite <- H1 at 2. auto.
  Qed.

  Theorem group_id_uniq_r : forall e', (forall a, a + e' = a) -> e' = 0.
  Proof.
    intros.
    (* e = e + e' = e' *)
    assert (0 = 0 + e'). { rewrite H. auto. }
    assert (0 + e' = e') by group_simp.
    apply transitivity with (0 + e'); auto.
  Qed.

  (* Note that, I give two theorem rather than one. *)
  Theorem group_inv_uniq_l : forall x1 x2 y, x1 + y = 0 /\ y + x2 = 0 -> x1 = x2.
  Proof.
    intros. destruct H as [Ha Hb].
    (* x1 = x1+e = x1+(y+x2) = (x1+y)+x2 = e+x2 = x2 *)
    assert (x1 = x1 + 0) by group_simp.
    rewrite H. rewrite <- Hb. rewrite <- associative.
    rewrite Ha. group_simp.
  Qed.

  Theorem group_inv_uniq_r : forall x y1 y2, x + y1 = 0 /\ y2 + x = 0 -> y1 = y2.
  Proof.
    intros. destruct H as [Ha Hb].
    (* y1 = e+y1 = (y2+x)+y1 = y2+(x+y1) = y2+e = y2 *)
    assert (y1 = 0 + y1) by group_simp.
    rewrite H. rewrite <- Hb. rewrite associative.
    rewrite Ha. group_simp.
  Qed.

  (** Theorem 14.1 *)
  Theorem group_cancel_l : forall x y1 y2, x + y1 = x + y2 -> y1 = y2.
  Proof.
    intros.
    (* y1 = e+y1 = (-x+x)+y1 = (-x)+(x+y1) = (-x) + (x+y2) = e+y2 = y2 *)
    rewrite <- identityLeft.
    replace 0 with (-x + x) by group_simp.
    rewrite associative. rewrite <- H. rewrite <- associative.
    group_simp.
  Qed.

  Theorem group_cancel_r : forall x1 x2 y, x1 + y = x2 + y -> x1 = x2.
  Proof.
    intros.
    (* x1 = x1+e = x1+(y+ -y) = (x1+y)+(-y) = (x2+y)+(-y) = x2+e = x2 *)
    rewrite <- identityRight.
    replace 0 with (y + (-y)) by group_simp.
    rewrite <- associative. rewrite <- H. rewrite associative.  
    group_simp.
  Qed.

  Theorem group_inv_inv : forall x,  - - x = x.
  Proof.
    intros. apply group_cancel_l with (- x). group_simp.
  Qed.

  Theorem group_inv_distr : forall x y, - (x + y) = (- y) + (- x).
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
  Theorem group_equation_sol_l : forall a b x, a + x = b -> x = (- a) + b.
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
    forall a b x y, (a + x = b /\ a + y = b) -> (x = -a + b /\ y = -a + b).
  Proof.
    intros. destruct H. split.
    apply group_equation_sol_l; auto.
    apply group_equation_sol_l; auto.
  Qed.

  (* x + a = b -> x = b + (-a) *)
  Theorem group_equation_sol_r : forall a b x, x + a = b -> x = b + (- a).
  Proof.
    intros.
    (* right mult a *)
    apply group_cancel_r with (a).
    (* group_simp. (* Tips: not finished yet. *) *)
    group_simp_strict G.
  Qed.

  (* (x + a = b /\ y + a = b) -> (x = b + -a /\ y = b + -a) *)
  Theorem group_equation_sol_r_uniq : 
    forall a b x y, (x + a = b /\ y + a = b) -> (x = b + (- a) /\ y = b + (- a)).
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
      (group_batch l1) + (group_batch l2) = group_batch (l1 ++ l2).
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
        assert (forall a l1 l2, Σ a & (l1 ++ l2) = Σ (Σ a & l1) & l2) as H1.
        { intros a l0. gd a. induction l0; intros; try reflexivity.
          simpl. rewrite IHl0. reflexivity. }
        assert (forall a b l, a + Σ b & l = Σ (a + b) & l) as H2.
        { intros. gd b. gd a. induction l; simpl; intros; try reflexivity.
          simpl. rewrite IHl. group_simp. }
        assert (forall a b l, Σ a & (b :: l) = Σ (a + b) & l) as H3.
        { intros. gd b. gd a. induction l; auto. }
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
  
    Theorem group_inv_id : - 0 = 0.
    Proof.
      intros.
      (* -e = -e + e = e *)
      rewrite <- identityRight at 1. group_simp.
    Qed.

  End additional_props.

End GroupTheory.

(** ** Examples *)
Section Examples.
  
  Import Reals.
  
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

Class AGroup {A} Aadd A0 Aopp := {
    agroupGroup :> @Group A Aadd A0 Aopp;
    agroupAM :> @AMonoid A Aadd A0;
    agroupComm :> Commutative Aadd;
  }.

Section Theory.
  
  Context `{AG : AGroup}.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation "a - b" := (a + (-b)).

  (** a - b = - (b - a) *)
  Lemma agroup_sub_comm : forall a b, a - b = - (b - a).
  Proof.
    intros.
    rewrite (group_inv_distr). rewrite (group_inv_inv). easy.
  Qed.

  (** (a - b) - c = (a - c) - b *)
  Lemma agroup_sub_perm : forall a b c, (a - b) - c = (a - c) - b.
  Proof.
    intros.
    rewrite ?associative. rewrite (commutative (-b)). easy.
  Qed.

  (** - (a + b) = (-a) + (-b) *)
  Lemma agroup_sub_distr : forall a b, - (a + b) = -a + (-b).
  Proof.
    intros. rewrite (group_inv_distr). apply commutative.
  Qed.

  (** (a - b) - c = a - (b + c) *)
  Lemma agroup_sub_assoc : forall a b c, (a - b) - c = a - (b + c).
  Proof.
    intros. rewrite ?associative. rewrite agroup_sub_distr. easy.
  Qed.
  
End Theory.

(* ======================================================================= *)
(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance AGroup_QcAdd : AGroup Qcplus 0 Qcopp.
  repeat constructor; intros; ring. Qed.

  Global Instance AGroup_RAdd : AGroup Rplus 0%R Ropp.
  repeat constructor; intros; ring. Qed.

End Instances.

Section example.
  Import Reals.
  
  Goal forall a b c : R, ((a - b) - c = a - (b + c))%R.
    intros. apply agroup_sub_assoc. Qed.
End example.


(* ######################################################################### *)
(** * Ring*)

(** ** Class *)

(* Note that, in mathematics, mul needn't commutative, but ring_theory in Coq 
   need it. Because we want use ring tactic, so add this properties. *)
Class Ring {A} Aadd A0 Aopp Amul A1 := {
    ringAddAG :> @AGroup A Aadd A0 Aopp;
    ringMulAM :> @AMonoid A Amul A1;
    ringDistrL :> DistributiveLeft Aadd Amul;
    ringDistrR :> DistributiveRight Aadd Amul;
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance Ring_Qc : Ring Qcplus 0 Qcopp Qcmult 1.
  repeat constructor; intros; ring. Qed.

  Global Instance Ring_R : Ring Rplus R0 Ropp Rmult R1.
  repeat constructor; intros; ring. Qed.

End Instances.

(** ** Extra Theories *)
Section Theory.

  Context `{R:Ring}.

  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + -b).
  Infix "*" := Amul : A_scope.

  Lemma make_ring_theory : ring_theory A0 A1 Aadd Amul Asub Aopp eq.
  Proof.
    constructor; intros;
      try (rewrite ?identityLeft,?associative; reflexivity);
      try (rewrite commutative; reflexivity).
    rewrite distributiveRight; reflexivity.
    rewrite inverseRight; reflexivity.
  Qed.

  Add Ring ring_inst : make_ring_theory.

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
  Infix "+" := Aadd.
  Infix "*" := Amul.
  Notation "0" := A0.
  Notation "1" := A1.

  Add Ring ring_thy_inst : make_ring_theory.

  Goal forall a b c : A, (a + b) * c = 0 + b * c * 1 + 0 + 1 * c * a.
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
Class Field {A} Aadd A0 Aopp Amul A1 Ainv := {
    (** Field: Ring + mult inversion + (1≠0) *)
    fieldRing :> @Ring A Aadd A0 Aopp Amul A1;
    field_mulInvL : forall a, a <> A0 -> Amul (Ainv a) a = A1;
    field_1_neq_0 : A1 <> A0;
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance Field_Qc : Field Qcplus 0 Qcopp Qcmult 1 Qcinv.
  repeat constructor; intros; try field; auto.
  apply Q_apart_0_1. Qed.

  Global Instance Field_R : Field Rplus R0 Ropp Rmult R1 Rinv.
  repeat constructor; intros; try field; auto.
  apply R1_neq_R0. Qed.

End Instances.


(** ** Extra Theories *)
Section Theory.

  Context `{F:Field}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + -b).
  Notation "0" := A0 : A_scope.
  Notation "1" := A1 : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/b)).
  Infix "/" := Adiv : A_scope.

  Lemma make_field_theory :
    field_theory A0 A1 Aadd Amul Asub Aopp Adiv Ainv eq.
  Proof.
    constructor; intros;
      try (rewrite ?identityLeft,?associative; reflexivity);
      try (rewrite commutative; reflexivity).
    apply make_ring_theory.
    apply field_1_neq_0.
    apply field_mulInvL. auto.
  Qed.

  Add Field field_inst : make_field_theory.

  (** a <> 0 -> /a * a = 1 *)
  Lemma field_mul_inv_l : forall a : A, a <> 0 -> /a * a = 1.
  Proof. intros. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> a * /a = 1 *)
  Lemma field_mul_inv_r : forall a : A, a <> 0 -> a * /a = 1.
  Proof. intros. rewrite commutative. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> (1/a) * a = 1 *)
  Lemma field_mul_inv1_l : forall a : A, a <> 0 -> (A1/a) * a = 1.
  Proof. intros. simpl. group_simp. apply field_mul_inv_l. auto. Qed.
  
  (** a <> 0 -> a * (1/a) = 1 *)
  Lemma field_mul_inv1_r : forall a : A, a <> 0 -> a * (A1/a) = 1.
  Proof. intros. simpl. group_simp.
         replace (1 * /a) with (/a) by monoid_simp. (* Tips: this manual work
                                                       should be avoid in future *)
         apply field_mul_inv_r. auto. Qed.
  
  (** a <> 0 -> a * b = a * c -> b = c *)
  Lemma field_mul_cancel_l : forall a b c : A, a <> 0 -> a * b = a * c -> b = c.
  Proof.
    intros.
    assert (/a * (a * b) = /a * (a * c)).
    { rewrite H0. easy. }
    rewrite <- ?associative in H1.
    rewrite field_mulInvL in H1; auto.
    rewrite ?identityLeft in H1. easy.
  Qed.

  (** c <> 0 -> a * c = b * c -> a = b *)
  Lemma field_mul_cancel_r : forall a b c : A, c <> 0 -> a * c = b * c -> a = b.
  Proof.
    intros.
    assert ((a * c) * /c = (b * c) * /c).
    { rewrite H0. easy. }
    rewrite ?associative in H1.
    rewrite field_mul_inv_r in H1; auto.
    rewrite ?identityRight in H1. easy.
  Qed.

  (** a * b = 0 -> a = 0 \/ b = 0 *)
  Lemma field_mul_eq0_imply_a0_or_b0 : forall (a b : A) (HDec : @Decidable A),
      a * b = 0 -> (a = 0) \/ (b = 0).
  Proof.
    intros.
    destruct (decidable a 0), (decidable b 0);
      try (left; easy); try (right; easy).
    assert (/a * a * b = 0).
    { rewrite associative. rewrite H. field. auto. }
    rewrite field_mulInvL in H0; auto.
    rewrite identityLeft in H0. easy.
  Qed.

End Theory.

(** ** Examples *)
Section Examples.

  Import Reals.
  
  Goal forall a b : R, (a <> 0 -> /a * a = 1)%R.
    intros. apply field_mulInvL. auto. Qed.

End Examples.

