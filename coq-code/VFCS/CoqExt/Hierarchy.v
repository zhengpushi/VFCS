(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Algebraic Hierarchy (Leibniz Equality version)
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. The motivate of this module is to support development with good organized 
    algebraic hierarchy, instead of scattered def./op./props.
  2. There are three technologies to form a hierarchy: module is a strong 
    specification and too heavy; type classes is used in Coq standard library;
    canonical structure is used in mathematical component.
  3. For type classes, ref to this paper "A Gentle Introduction to Type Classes 
    and Relations in Coq" and the refrence manual of Coq at 
    "https://coq.inria.fr/distrib/V8.13.2/refman/addendum/type-classes.html".
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

Require Export Coq.Classes.RelationClasses. (* binary_relation *)
Require Import Coq.Logic.Description. (* constructive_definite_description *)
Require Export Basic.   (* reserved notation *)
Require Export BoolExt.
Require Export List. Import ListNotations.
Require Export Lia Lra.
Require Export Ring Field.
Require Import Arith ZArith QArith Qcanon Reals.

Open Scope nat_scope.
Open Scope A_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Adiv Alt.


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
  Context {A} {f : A -> A} (Azero : A).
  (* Compute iterate f 3 Azero. *)
End test.



(* ######################################################################### *)
(** * <TEMPLATE structures> *)

(** ** Class *)

(** ** Instances *)
Section Instances.
End Instances.

(** ** Extra Theories *)
Section Theory.
End Theory.

(** ** Examples *)
Section Examples.
End Examples.



(* ######################################################################### *)
(** * A relation is equivalence relation *)

(** ** Class *)

(* Global Hint Constructors Equivalence : core. *)

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * A relation is decidable *)

(** ** Class *)

Class Dec {A:Type} (Acmp:A->A->Prop) := {
    dec : forall (a b : A), {Acmp a b} + {~(Acmp a b)};
  }.

(* We prefer don't simpl `dec` *)
Arguments dec {A} _ {_} : simpl never.

(* Global Hint Constructors Dec : core. *)

(* equality relation is decidable *)
Definition Aeqdec {A} {AeqDec:Dec (@eq A)} := @dec _ (@eq A) AeqDec.


(** ** Instances *)
Section Instances.
  Import Arith ZArith Reals.

  #[export] Instance Dec_list `{Dec _ (@eq A)} : Dec (@eq (list A)).
  Proof. constructor. intros. apply list_eq_dec. apply Aeqdec. Defined.

  (** Equality of two pairs, iff their corresponding components are all equal. *)
  Lemma prod_eq_iff : forall {A B} (z1 z2 : A * B),
      z1 = z2 <-> fst z1 = fst z2 /\ snd z1 = snd z2.
  Proof.
    intros A B (a1,b1) (a2,b2). split; intros H; inv H; auto.
    simpl in *; subst. auto.
  Qed.

  (** Inequality of two pairs, iff at least one of components are not equal. *)
  Lemma prod_neq_iff : forall {A B} {AeqDec:Dec (@eq A)} {BeqDec:Dec (@eq B)}
                         (z1 z2 : A * B),
      z1 <> z2 <-> fst z1 <> fst z2 \/ snd z1 <> snd z2.
  Proof.
    intros. rewrite prod_eq_iff. split; intros.
    apply not_and_or in H; auto.
    apply or_not_and in H; auto.
  Qed.  

End Instances.

(** ** Extra Theories *)
Section Dec_theory.

  Context `(Dec).

  (** Tips: these theories are useful for R type *)
  
  (** Calculate equality to boolean, with the help of equality decidability *)
  Definition Acmpb (a b : A) : bool := if dec Acmp a b then true else false.

  (** Acmpb is true iff Acmp hold. *)
  Lemma Acmpb_true : forall a b, Acmpb a b = true <-> Acmp a b.
  Proof.
    intros. unfold Acmpb. destruct dec; split; intros; auto. easy.
  Qed.
  
  (** Acmpb is false iff Acmp not hold *)
  Lemma Acmpb_false : forall a b, Acmpb a b = false <-> ~(Acmp a b).
  Proof. intros. rewrite <- Acmpb_true. split; solve_bool. Qed.

  Lemma Acmp_reflect : forall a b : A, reflect (Acmp a b) (Acmpb a b).
  Proof. intros. unfold Acmpb. destruct (dec Acmp a b); constructor; auto. Qed.

End Dec_theory.

(** ** Examples *)


(* ######################################################################### *)
(** * Respect: an operation respect a relation (also known as "well-defined") *)

(** deprecated, replaced with "Proper" in Coq *)
(** Note that, the naming could be any of them:
    1. "add_wd", means "add" is well defined.
    2. "add_aeq_mor", means "add" is a proper morphism about "aeq".
    3. "Qplus_comp", means "Qplus" is compatible to "Qeq".
*)

(* (** ** Class *) *)

(* (** A unary operation is respect to the equality relation *) *)
(* Class RespectUnary {A B:Type} (op:A->B) (Aeq:A->A->Prop) (Beq:B->B->Prop) := { *)
(*     respectUnary : forall x y : A, *)
(*       Aeq x y -> Beq (op x) (op y) *)
(*   }. *)

(* (** A binary operation is respect to the equality relation *) *)
(* Class RespectBinary {A B C:Type} (op:A->B->C) *)
(*   (Aeq:A->A->Prop) (Beq:B->B->Prop) (Ceq:C->C->Prop):= { *)
(*     respectBinary : forall x y : A, *)
(*       Aeq x y -> forall x0 y0 : B, Beq x0 y0 -> Ceq (op x x0) (op y y0) *)
(*   }. *)

(** ** Instances *)
Hint Resolve
  Nat.add_wd Nat.mul_wd  (* nat *)
  : wd.

(* (** ** Extra Theories *) *)

(* (** ** Examples *) *)



(* ######################################################################### *)
(** * Injective *)

(** ** Class *)

Class Injective {A B} (phi: A -> B) := {
    injective : forall a1 a2 : A, a1 <> a2 -> phi a1 <> phi a2
  }.
  
(** ** Instances *)

(** ** Extra Theories *)
Section theory.
  Context {A B : Type}.
  
  (** Second form of injective *)
  Definition injective_form2 (phi: A -> B) :=
    forall a1 a2, phi a1 = phi a2 -> a1 = a2.

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
  Lemma injective_preserve_eq : forall (f : A -> B),
      Injective f -> (forall a1 a2, f a1 = f a2 -> a1 = a2).
  Proof.
    intros. apply injective_eq_injective_form2 in H. apply H. auto.
  Qed.

End theory.

(** ** Examples *)



(* ######################################################################### *)
(** * Surjective *)

(** ** Class *)

Class Surjective {A B} (phi: A -> B) := {
    surjective : forall b, (exists a, phi a = b)
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Bijective *)

(** ** Class *)

Class Bijective {A B} (phi: A -> B) := {
    bijInjective :: Injective phi;
    bijSurjective :: Surjective phi
  }.
Coercion bijInjective : Bijective >-> Injective.
Coercion bijSurjective : Bijective >-> Surjective.

(** ** Instances *)

(** ** Extra Theories *)
Section theory.
  Context {A B : Type}.
  
  (** There exist inverse function from a bijective function.

      ref: https://stackoverflow.com/questions/62464821/
      how-to-make-an-inverse-function-in-coq

      Tips: there are two methods to formalize "existential", sig and ex.
      ex makes a Prop, sig makes a Type. 
      Here, we proof the ex version. the sig version could be derived by an axiom:
      [constructive_definite_description : 
      forall (A : Type) (P : A -> Prop), (exists ! x : A, P x) -> {x : A | P x} ]
   *)

  Lemma bij_inverse_exist : forall (phi : A -> B) (Hbij: Bijective phi),
    {psi : B -> A | (forall a : A, psi (phi a) = a) /\  (forall b : B, phi (psi b) = b)}.
  Proof.
    intros. destruct Hbij as [Hinj [Hsurj]].
    apply injective_eq_injective_form2 in Hinj. hnf in *.
    assert (H : forall b, exists! a, phi a = b).
    { intros b.
      destruct (Hsurj b) as [a Ha]. exists a. repeat split; auto.
      intros a' Ha'. apply Hinj. rewrite Ha. auto. }
    apply constructive_definite_description.
    exists (fun b => proj1_sig (constructive_definite_description _ (H b))). split. 
    - split.
      + intros a. destruct (constructive_definite_description). simpl. auto.
      + intros b. destruct (constructive_definite_description). simpl. auto.
    - intro psi; intros. apply functional_extensionality.
      intros b. destruct (constructive_definite_description). simpl.
      destruct H0. rewrite <- e. auto.
  Defined.

  (** A bijective function preserve equal relation *)
  Lemma bijective_preserve_eq : forall (f : A -> B),
      Bijective f -> (forall (a1 a2 : A), f a1 = f a2 -> a1 = a2).
  Proof.
    intros. destruct H as [Hinj Hsurj].
    apply injective_preserve_eq in H0; auto.
  Qed.

End theory.

(** ** Examples *)



(* ######################################################################### *)
(** * Homomorphic  *)

(** ** Class *)

Class Homomorphic {A B}
  (fa : A -> A -> A) (fb : B -> B -> B) (phi: A -> B) := {
    homomorphic : forall (a1 a2 : A), phi (fa a1 a2) = fb (phi a1) (phi a2)
  }.

(** ** Instances *)

(** ** Extra Theories *)

(* Definition homo_inj (phi : A -> B) : Prop := *)
(*   homomorphic phi /\ injective phi. *)

(* (** phi is a homomorphic and surjective mapping *) *)
(* Definition homo_surj (phi : A -> B) : Prop := *)
(*   homomorphic phi /\ surjective phi. *)

(** ** Examples *)



(* ######################################################################### *)
(** * Homomorphism *)

(** ** Class *)

(** If there exist a homomorphic and surjective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is homomorphism *)
Class Homomorphism {A B} (fa : A -> A -> A) (fb : B -> B -> B) := {
    homomorphism : exists (phi: A -> B), Homomorphic fa fb phi /\ Surjective phi
  }.

(** If there exist two homomorphic and surjective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is homomorphism *)
Class Homomorphism2 {A B} (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    homomorphism2 : exists (phi: A -> B),
      Homomorphic fa fb phi /\ Homomorphic ga gb phi /\ Surjective phi
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Isomorphism *)

(** ** Class *)

(** If there exist a homomorphic and bijective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is isomorphism *)
Class Isomorphism {A B} (fa : A -> A -> A) (fb : B -> B -> B) := {
    isomorphism : exists (phi: A -> B), Homomorphic fa fb phi /\ Bijective phi
  }.

(** If there exist two homomorphic and bijective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is isomorphism *)
Class Isomorphism2 {A B} (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    isomorphism2 : exists (phi: A -> B),
      Homomorphic fa fb phi /\ Homomorphic ga gb phi /\ Bijective phi
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Subset *)

(** ** Class *)
(* C is subset of P *)
Class Subset (C P : Type) := {
    sub_phi : C -> P;
    sub_phi_inj : Injective sub_phi
  }.

(** ** Instances *)
Section Instances.

  Instance nat_Z_Subset : Subset nat Z.
  Proof.
    refine (@Build_Subset _ _ Z.of_nat _).
    rewrite injective_eq_injective_form2. hnf. apply Nat2Z.inj.
  Qed.
    
End Instances.

(** ** Extra Theories *)
Section Theory.
End Theory.

(** ** Examples *)
Section Examples.
End Examples.


(* ######################################################################### *)
(** * Associative *)

(** ** Class *)
Class Associative {A} (Aop : A -> A -> A) := {
    associative : forall a b c, Aop (Aop a b) c = Aop a (Aop b c);
  }.

(** ** Instances *)
#[export] Instance Assoc_NatAdd : Associative Nat.add.
constructor. auto with arith. Defined.

(** ** Extra Theories *)

(** ** Examples *)
Goal forall a b c : nat, (a + (b + c) = (a + b) + c).
  intros. rewrite associative; auto. Qed.

Goal forall a b c : nat, ((a + b) + c = a + (b + c)).
  apply associative. Qed.


(* ######################################################################### *)
(** * Commutative *)

(** ** Class *)
Class Commutative {A} (Aop : A -> A -> A) := {
    commutative : forall a b, Aop a b = Aop b a
  }.

(** ** Instances *)
#[export] Instance Comm_NatAdd : Commutative Nat.add.
constructor. auto with arith. Defined.

#[export] Instance Comm_NatMul : Commutative Nat.mul.
constructor. auto with arith. Defined.

(** ** Extra Theories *)

(** ** Examples *)
Goal forall a b : nat, (a + b = b + a)%nat.
  apply commutative. Qed.

Goal forall a b : nat, (a * b = b * a)%nat.
  apply commutative. Qed.


(* ######################################################################### *)
(** * Identity Left/Right *)

(** ** Class *)
Class IdentityLeft {A} (Aop : A -> A -> A) (Ae : A) := {
    identityLeft : forall a, Aop Ae a = a
  }.

Class IdentityRight {A} (Aop : A -> A -> A) (Ae : A) := {
    identityRight : forall a, Aop a Ae = a
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Inverse Left/Right *)

(** ** Class *)
Class InverseLeft {A} (Aop : A -> A -> A) (Ae : A) (Aopinv : A -> A)
  := {
    inverseLeft : forall a, Aop (Aopinv a) a = Ae
  }.

Class InverseRight {A} (Aop : A -> A -> A) (Ae : A) (Aopinv : A -> A)
  := {
    inverseRight : forall a, Aop a (Aopinv a) = Ae
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Distributive *)

(** ** Class *)

(* Class DistributiveUnary {A} (Tadd:A -> A -> A) (Aopp : A -> A) := { *)
(*     distributiveUnary : forall a b, *)
(*       Aopp (Tadd a b) = Tadd (Aopp a) (Aopp b) *)
(*   }. *)

Class DistributiveLeft {A} (Aadd Amul : A -> A -> A) := {
    distributiveLeft : forall a b c,
      Amul a (Aadd b c) = Aadd (Amul a b) (Amul a c)
  }.

Class DistributiveRight {A} (Aadd Amul : A -> A -> A) := {
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
(*     involution : forall a, Aopp (Aopp a) = a *)
(*   }. *)

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Total order relations *)

(* ref : 
   https://en.wikipedia.org/wiki/Construction_of_the_real_numbers
   https://en.wikipedia.org/wiki/Partially_ordered_set
 *)
(* 
   Remark :
   1. The difference of total order relation and partial order relation is the 
      "total" propertity (forall a b, a <= b \/ b <= a).
   2. Four forms "<=, <, >, >=" are mutually derived. We will define "<" and "<="
      here, with the consistent law.
 *)

(** ** Class *)
Class Order {A} (Alt Ale : A -> A -> Prop) (Altb Aleb : A -> A -> bool) := {
    (* Lt and Le are consistent *)
    lt_le_cong : forall a b : A, Ale a b <-> (Alt a b \/ a = b);
    (* Lt is anti-reflexivi *)
    lt_irrefl : forall a : A, ~ (Alt a a);
    (* Lt is anti-symmetric *)
    lt_antisym : forall a b : A, Alt a b -> Alt b a -> a = b;
    (* Lt is transitive *)
    lt_trans : forall a b c : A, Alt a b -> Alt b c -> Alt a c;
    (* Lt three cases *)
    lt_cases : forall a b : A, {Alt a b} + {Alt b a} + {a = b};
    (* Lt and Ltb are reflect *)
    ltb_reflect : forall a b : A, reflect (Alt a b) (Altb a b);
    (* Le and Leb are reflect *)
    leb_reflect : forall a b : A, reflect (Ale a b) (Aleb a b);
  }.

(** ** Instances *)

(** ** Extra Theories *)
Section theories.
  Context `{HOrder : Order}.

  (* Note the sequence of the notations, the newer has more priority than older *)
  Notation "a > b" := (Alt b a).
  Notation "a >= b" := (Ale b a).
  Infix "<" := Alt.
  Infix "<=" := Ale.
  Infix "<?" := Altb.
  Infix "<=?" := Aleb.

  (* Lt is decidable *)
  Lemma lt_dec : forall a b, {a < b} + {~(a < b)}.
  Proof.
    intros. destruct (lt_cases a b) as [[H1|H1]|H1]; auto.
    - right. intro. pose proof (lt_trans H1 H). apply lt_irrefl in H0; auto.
    - right. subst. apply lt_irrefl.
  Qed.

  #[export] Instance lt_Dec : Dec Alt.
  Proof. constructor. intro. apply lt_dec. Qed.

  (* Hint Resolve ltb_reflect : bdestruct. *)

  (* eq is decidable can be derived from `Order` *)
  #[export] Instance order_EqDec : Dec (@eq A).
  Proof.
    constructor.
    intros; destruct (lt_cases a b) as [[H1|H1]|H1]; auto.
    - right; intro; subst. apply lt_irrefl in H1; auto.
    - right; intro; subst. apply lt_irrefl in H1; auto.
  Qed.

  (* Lt is connected *)
  Lemma lt_connected : forall a b : A, Alt a b \/ Alt b a \/ a = b.
  Proof. intros. destruct (lt_cases a b) as [[H1|H1]|H1]; auto. Qed.
  
  (* a < b -> a <= b *)
  Lemma le_if_lt : forall a b : A, a < b -> a <= b.
  Proof. intros. apply lt_le_cong. auto. Qed.
  
  (* a <= b -> a <> b -> a < b *)
  Lemma lt_if_le_and_neq : forall a b : A, a <= b -> a <> b -> a < b.
  Proof. intros. apply lt_le_cong in H. destruct H; auto. easy. Qed.

  (** a < b -> a <> b *)
  Lemma lt_not_eq : forall a b : A, a < b -> a <> b.
  Proof. intros. intro. subst. apply lt_irrefl in H; auto. Qed.

  (** a <= a *)
  Lemma le_refl : forall a : A, a <= a.
  Proof. intros. apply lt_le_cong. right. auto. Qed.
  
  (** a <= b -> b <= a -> a = b *)
  Lemma le_antisym : forall a b : A, a <= b -> b <= a -> a = b.
  Proof.
    intros. apply lt_le_cong in H, H0. destruct H, H0; subst; auto.
    apply lt_antisym; auto.
  Qed.
  
  (** a <= b -> b <= c -> a <= c *)
  Lemma le_trans : forall a b c : A, a <= b -> b <= c -> a <= c.
  Proof.
    intros. apply lt_le_cong in H, H0. apply lt_le_cong.
    destruct H, H0; subst; auto. left. apply lt_trans with b; auto.
  Qed.
  
  (** a < b -> b <= c -> a < c *)
  Lemma lt_trans_lt_le : forall a b c : A, a < b -> b <= c -> a < c.
  Proof.
    intros. pose proof (le_if_lt H). pose proof (le_trans H1 H0).
    apply lt_if_le_and_neq; auto.
    intro. subst. pose proof (le_antisym H0 H1). subst. apply lt_irrefl in H; auto.
  Qed.
  
  (** a <= b -> b < c -> a < c *)
  Lemma lt_trans_le_lt : forall a b c : A, a <= b -> b < c -> a < c.
  Proof.
    intros. pose proof (le_if_lt H0). pose proof (le_trans H H1).
    apply lt_if_le_and_neq; auto.
    intro. subst. pose proof (le_antisym H H1). subst. apply lt_irrefl in H0; auto.
  Qed.

  (** a < b -> b < a -> False *)
  Lemma lt_gt_contr : forall a b : A, a < b -> b < a -> False.
  Proof.
    intros. apply lt_trans with (a:=a) in H0; auto. apply lt_irrefl in H0; auto.
  Qed.

  (** a < b -> a <> b *)
  Lemma lt_imply_neq : forall a b : A, a < b -> a <> b.
  Proof. intros. intro. subst. apply lt_irrefl in H. auto. Qed.

(* Qclt_not_le: forall x y : Qc, x < y -> ~ y <= x *)
(* Qcnot_le_lt: forall x y : Qc, ~ x <= y -> y < x *)
  
  (** a < b -> ~ (b < a) *)
  Lemma lt_not_lt : forall a b : A, a < b -> ~ (b < a).
  Proof. intros. intro. apply lt_gt_contr in H; auto. Qed.
  
  (** a < b -> ~ (b <= a) *)
  Lemma lt_not_le : forall a b : A, a < b -> ~ (b <= a).
  Proof.
    intros. rewrite lt_le_cong. apply and_not_or. split.
    apply lt_not_lt; auto. symmetry. apply lt_not_eq; auto.
  Qed.
  
  (** ~ (a <= b) -> b < a *)
  Lemma not_le_lt : forall a b : A, ~ (a <= b) -> b < a.
  Proof.
    intros. rewrite lt_le_cong in H. apply not_or_and in H. destruct H.
    destruct (lt_cases a b) as [[H1|H1]|H1]; try easy.
  Qed.
  
  (** a <= b -> ~ (b < a) *)
  Lemma le_not_lt : forall a b : A, a <= b -> ~ (b < a).
  Proof.
    intros. rewrite lt_le_cong in H. destruct H.
    apply lt_not_lt; auto. subst. apply lt_irrefl.
  Qed.
  
  (** ~ (a < b) -> b <= a *)
  Lemma not_lt_le : forall a b : A, ~ (a < b) -> b <= a.
  Proof.
    intros. apply lt_le_cong.
    destruct (lt_cases a b) as [[H1|H1]|H1]; auto; try easy.
  Qed.

  (** a <= b -> b <= a -> a = b *)
  Lemma le_ge_eq : forall a b : A, a <= b -> b <= a -> a = b.
  Proof.
    intros. apply le_not_lt in H,H0.
    destruct (lt_cases a b) as [[H1|H1]|H1]; easy.
  Qed.

  (** {a <= b} + {~(a <= b)} *)
  Lemma le_dec : forall a b : A, {a <= b} + {~(a <= b)}.
  Proof.
    intros. destruct (lt_dec b a); auto.
    - right. apply lt_not_le; auto.
    - left. apply not_lt_le; auto.
  Qed.

  #[export] Instance le_Dec : Dec Ale.
  Proof. constructor; intros. apply le_dec. Qed.
  
  (** a <= b \/ b < a *)
  Lemma le_connected : forall a b : A, a <= b \/ b < a.
  Proof. intros. destruct (le_dec a b); auto. apply not_le_lt in n. auto. Qed.

  (* Boolean version of "<=" *)
  (* Hint Resolve leb_reflect : bdestruct. *)

  Lemma leb_refl : forall a : A, a <=? a = true.
  Proof. intros. destruct (leb_reflect a a); auto. destruct n. apply le_refl. Qed.

End theories.

(* #[export] Hint Resolve ltb_reflect leb_reflect : bdestruct. *)


(** ** Examples *)


(* ######################################################################### *)
(** * Semigroup 半群 *)

(** ** Class *)
Class SGroup {A} (Aadd : A -> A -> A) := {
    sgroupAssoc :: Associative Aadd;
  }.

(** Get parameter of this structure *)
Definition sgroupAadd `{SG:SGroup} : A -> A -> A := Aadd.

(** ** Instances *)
Section Instances.
  
  #[export] Instance nat_add_SGroup : SGroup Nat.add.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  #[export] Instance nat_mul_SGroup : SGroup Nat.mul.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.
  
End Instances.

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Abelian semigroup 交换半群 *)

(** ** Class *)
Class ASGroup {A} (Aadd : A -> A -> A) := {
    asgroupSGroup :: SGroup Aadd;
    asgroupComm :: Commutative Aadd
  }.

(** Get parameter of this structure *)
Definition asgroupAadd `{ASG : ASGroup} : A -> A -> A := Aadd.

(** ** Instances *)
Section Instances.
  
  #[export] Instance nat_add_ASGroup : ASGroup Nat.add.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  #[export] Instance nat_mul_ASGroup : SGroup Nat.mul.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.
  
End Instances.

(** ** Extra Theories *)

(** In a commutative semigroup, adjust a term in the equation to the head,
    and use full right associative form for next step of elimination.
    From: a1 + ... + c + ... + an    (with parentheses of any form)
    To  : c + (a1 + (... + an))
 *)
(** 在交换半群中，将等式里的一个项调整到头部，并使用完全的右结合形式以便下一步消去。 *)
Ltac move2h c :=
  rewrite <- ?associative;
  try rewrite (commutative _ c);
  rewrite ?associative.

(** In a commutative semigroup, adjust a term in the equation to the tail,
    and use full left associative form for next step of elimination.
    From: a1 + ... + c + ... + an    (with parentheses of any form)
    To  : (...(a1 + ... + an)...) + c 
*)
(** 在交换半群中，将等式里的一个项调整到尾部，并使用完全的左结合形式以便下一步消去。 *)
Ltac move2t c :=
  rewrite ?associative;
  try rewrite (commutative c);
  rewrite <- ?associative.

(** In a commutative semigroup, eliminate first common head.
    From: c + a1 + ... + an = c + b1 + ... + bm   (with parentheses of any form)
    To  : a1 + (a2 + (... + an)) = b1 + (b2 + (... + bm))
 *)
(** 在交换半群中，消去第一个相同的头部。 *)
Ltac elimh1 :=
  rewrite ?associative; (* assure fully right-associative form *)
  match goal with
  | |- ?aeq (?f ?c ?a) (?f ?c ?b) => f_equiv (* elim head on setoid *)
  end.

(** In a commutative semigroup, eliminate first common tail.
    From: c + a1 + ... + an = c + b1 + ... + bm   (with parentheses of any form)
    To  : ((a1 + a2) + ...) + an = ((b1 + b2) + ...) + bm
 *)
(** 在交换半群中，消去第一个相同的尾部。 *)
Ltac elimt1 :=
  rewrite <- ?associative; (* assure fullly left-associative form *)
  match goal with
  | |- ?aeq (?f ?a ?c) (?f ?b ?c) => f_equiv (* elim tail on setoid *)
  end.

(** In a commutative semigroup, automatically simplify and prove equality.
    An example shoing the detail process:
    a0 + a1 + a2 + a3 = a3 + a0 + a2 + a1
    => a0 + a1 + a2 + a3 = a0 + a3 + a2 + a1
    => a1 + a2 + a3 = a3 + a2 + a1
    => a1 + a2 + a3 = a1 + a3 + a2
    => a2 + a3 = a3 + a2
    => a2 + a3 = a2 + a3
    => a3 + a3
    => True
 *)
(** 在交换半群中，自动消去左式中所有可能相同的头部 *)
Ltac elimh :=
  rewrite ?associative; (* assure fully right-associative form *)
  repeat match goal with
    | |- ?aeq (?f ?c _) (?f _ _) => move2h c; elimh1
    end.

(** 在交换半群中，自动消去左式中所有可能相同的尾部 *)
Ltac elimt :=
  rewrite <- ?associative; (* assure fully left-associative form *)
  repeat match goal with
    | |- ?aeq (?f _ ?c) (?f _ _) => move2t c; elimt1
    end.

(** 在交换半群中，自动消去左式和右式中所有可能相同的头部和尾部 *)
Ltac asemigroup :=
  elimh; elimt; (* 消去左式的头部和尾部 *)
  symmetry;
  elimh; elimt. (* 消去右式的头部和尾部 *)

Section test.
  Context `{ASG : ASGroup}. Infix "+" := Aadd.
  Variable a0 a1 a2 a3 a4 a5 a6 : A.

  (** 第一种情形，等式两侧完全相同 *)
  Let eq1 : Prop := a0 + (a1 + a2) + a3 = a3 + (a0 + a2) + a1.

  (* 这个例子表明，任何的项都可以调整到头部，多步调整后得到了相同形式 *)
  Goal eq1.
    unfold eq1. move2h a0. move2h a0. move2h a1. move2h a1.
    move2h a2. move2h a2.  move2h a3. move2h a3. easy. Qed.
  
  (* 这个例子表明，任何的项都可以调整到尾部，多步调整后得到了相同形式 *)
  Goal eq1.
    unfold eq1. move2t a0. move2t a0. move2t a1. move2t a1.
    move2t a2. move2t a2.  move2t a3. move2t a3. easy. Qed.

  (* 这个例子表明，调整到头部+消去头部，可确保化简能够进行 *)
  Goal eq1.
    unfold eq1.
    do 2 move2h a0; elimh1.
    do 2 move2h a1; elimh1.
    do 2 move2h a2; elimh1.
  Qed.

  (* 这个例子表明，调整到尾部+消去尾部，可确保化简能够进行 *)
  Goal eq1.
    unfold eq1.
    do 2 move2t a0; elimt1.
    do 2 move2t a1; elimt1.
    do 2 move2t a2; elimt1.
  Qed.

  (* 这个例子表明，可自动化（以左式头部消除为例） *)
  Goal eq1. Proof. unfold eq1. elimh. Qed.
  (* 这个例子表明，可自动化（以左式尾部消除为例） *)
  Goal eq1. Proof. unfold eq1. elimt. Qed.
  (* 这个例子表明，可自动化（以右式头部消除为例） *)
  Goal eq1. Proof. unfold eq1. symmetry. elimh. Qed.
  (* 这个例子表明，可自动化（以右式尾部消除为例） *)
  Goal eq1. Proof. unfold eq1. symmetry. elimt. Qed.

  (** 第二种情形，等式两侧不完全相同，因为可能需要额外的证明 *)
  Let eq2 : Prop := a0 + (a1 + a2 + a3) + a4 + a5 = a2 + a0 + a6 + a4.

  (* 自动消去所有左式中可能的头部 *)
  Goal eq2. unfold eq2. elimh. Abort.
  (* 自动消去所有左式中可能的尾部 *)
  Goal eq2. unfold eq2. elimt. Abort.
  (* 自动消去所有右式中可能的头部 *)
  Goal eq2. unfold eq2. symmetry. elimh. Abort.
  (* 自动消去所有右式中可能的尾部 *)
  Goal eq2. unfold eq2. symmetry. elimt. Abort.

  (** 在不确定左右两侧中哪一侧更“合适”时，可以两侧都做一遍。
      而且需要同时处理头部和尾部。*)
  Goal eq2. unfold eq2. asemigroup. Abort.

  (** 还有一种可能，某个相同的项出现中中间，既不在头部，也不在尾部 *)
  Let eq3 : Prop := a1 + a0 + a2 = a3 + a0 + a4.

  (* 可以发现，上面的方法不能处理这种情况 *)
  Goal eq3. unfold eq3. asemigroup. Abort.

  (* 也许能够设计一种方法来遍历左侧或右侧的所有的项，但暂时可以手工来做。
     比如，可以手工调用 move2h 或 move2t 来移动一个项，然后调用 elimh 或
     elimt 或 asemigroup 来消除它 *)
  Goal eq3. unfold eq3. move2h a0. asemigroup. Abort.
  Goal eq3. unfold eq3. move2t a0. asemigroup. Abort.
  
End test.

(** ** Examples *)


(* ######################################################################### *)
(** * Monoid 幺半群、独异点 *)

(** ** Class *)
Class Monoid {A} (Aadd : A -> A -> A) (Azero : A) := {
    monoidAssoc :: Associative Aadd;
    monoidIdL :: IdentityLeft Aadd Azero;
    monoidIdR :: IdentityRight Aadd Azero;
    monoidSGroup :: SGroup Aadd
  }.

(** Get parameter of a monoid *)
Definition monoidAadd `{M:Monoid} : A -> A -> A := Aadd.
Definition monoidAzero `{M:Monoid} : A := Azero.

(** ** Instances *)
Section Instances.

  Import Arith ZArith Qcanon Reals.
  
  #[export] Instance Monoid_NatAdd : Monoid Nat.add 0%nat.
  repeat constructor; intros; ring. Qed.

  #[export] Instance Monoid_NatMul : Monoid Nat.mul 1%nat.
  repeat constructor; intros; ring. Qed.

  #[export] Instance Monoid_ZAdd : Monoid Z.add 0%Z.
  repeat constructor; intros; ring. Qed.

  #[export] Instance Monoid_ZMul : Monoid Z.mul 1%Z.
  repeat constructor; intros; ring. Qed.

  #[export] Instance Monoid_QcAdd : Monoid Qcplus 0.
  repeat constructor; intros; ring. Qed.

  #[export] Instance Monoid_QcMul : Monoid Qcmult 1.
  repeat constructor; intros; ring. Qed.

  #[export] Instance Monoid_RAdd : Monoid Rplus 0%R.
  repeat constructor; intros; ring. Qed.

  #[export] Instance Monoid_RMul : Monoid Rmult 1%R.
  repeat constructor; intros; ring. Qed.

End Instances.

(** ** Extra Theories *)
(* What' a theory? a group of properties related to this sturcture *)

(* deprecated *)
(** monoid rewriting with given monoid-instance-name.
    It is strict and powerful (such as "a + (e + b)" could be solved), 
    but less automated. *)
Ltac monoid_rw_old M :=
  rewrite (@associative _ _ _ (@monoidAssoc _ _ _ M)) ||
    rewrite (@identityLeft _ _ _ _ (@monoidIdL _ _ _ M)) ||
    rewrite (@identityRight _ _ _ _ (@monoidIdR _ _ _ M)).

Ltac monoid_simpl_old M := intros; repeat monoid_rw_old M; auto.

(** monoid rewriting, automatic inference the Instance. But sometimes it will fail *)
(* Ltac monoid_rw := *)
(*   rewrite identityLeft || *)
(*     rewrite identityRight || *)
(*     rewrite associative. *)

(* One problem, identityLeft will fail! *)
Section problem.
  Context `{M : Monoid A Aadd Azero}.
  Infix "+" := Aadd.
  Notation "0" := Azero.

  Goal forall x : A, x + (0 + x) = x + x.
    intros.
    Fail rewrite identityLeft.  (* Why this fail? *)
    rewrite identityLeft at 1.  (* We need explicit "position" annotation *)
    Abort.
End problem.

(* So, a newer tactic to automatically use "rewrite identityLeft" *)
Ltac monoid_rw :=
  rewrite identityLeft at 1 ||
  rewrite identityLeft at 2 ||
  rewrite identityLeft at 3 ||
    rewrite identityRight at 1||
    rewrite identityRight at 2||
    rewrite identityRight at 3||
    rewrite associative.

Ltac monoid := intros; repeat monoid_rw; try reflexivity; auto.

Section Theory.
  Context `{M:Monoid}.
  Infix "+" := Aadd : A_scope.

End Theory.

(** ** Examples *)

Section Examples.
  
  Import Reals.

  Goal forall a b c : R, ((a * b) * c = a * (b * c))%R.
  Proof. 
    apply associative.
  Qed.

End Examples.


(* ######################################################################### *)
(** * Abelian monoid *)

(** ** Class *)
Class AMonoid {A} Aadd Azero := {
    amonoidMonoid :: @Monoid A Aadd Azero;
    amonoidComm :: Commutative Aadd;
    amonoidASGroup :: ASGroup Aadd
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  #[export] Instance AMonoid_QcAdd : AMonoid Qcplus 0.
  split_intro; subst; ring. Defined.

  #[export] Instance AMonoid_QcMul : AMonoid Qcmult 1.
  split_intro; subst; ring. Defined.

  #[export] Instance AMonoid_RAdd : AMonoid Rplus 0%R.
  split_intro; subst; ring. Defined.

  #[export] Instance AMonoid_RMul : AMonoid Rmult 1%R.
  split_intro; subst; ring. Defined.

End Instances.

  
(** ** Extra Theories *)

Ltac amonoid :=
  monoid;
  try apply commutative.

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
    amonoid.
  Qed.

End Examples.



(* ######################################################################### *)
(** * Group *)

(** ** Class *)
(* Notice that, this is a one-sided definition, it is equivalence to double-sided *)
Class Group {A} Aadd Azero (Aopp : A -> A) := {
    groupMonoid :: Monoid Aadd Azero;
    groupInvL :: InverseLeft Aadd Azero Aopp;
    groupInvR :: InverseRight Aadd Azero Aopp;
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  #[export] Instance Qc_add_Group : Group Qcplus 0 Qcopp.
  split_intro; subst; ring. Defined.

  #[export] Instance R_add_Group : Group Rplus 0%R Ropp.
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

Ltac group :=
  intros;
  repeat (group_rw || monoid_rw || group_rw);
  try reflexivity;
  auto.

(*
  Group Theory

  1.  Arkansas Aech University / Dr. Marcel B. Finan /
      MATH 4033: Elementary Modern Algebra
  
  (a) 5 Definition and Examples of Groups
  https://faculty.atu.edu/mfinan/4033/absalg5.pdf
  (b) 14 Elementary Properties of Groups
  https://faculty.atu.edu/mfinan/4033/absalg14.pdf
 *)
Section GroupTheory.
  
  Context `{G:Group}.
  Infix "+" := Aadd.
  Notation "0" := Azero.
  Notation "- a" := (Aopp a).
  Notation Asub a b := (a + -b).
  Infix "-" := Asub.

  (** - 0 = 0 *)
  Theorem group_opp_0 : - 0 = 0.
  Proof.
    (* -e = -e + e = e *)
    pose proof (inverseLeft 0). rewrite identityRight in H. auto.
  Qed.
  
  (* Theorem 5.1 *)
  
  (** left identity element is unique  *)
  Theorem group_id_uniq_l : forall e',
      (forall a, e' + a = a) -> e' = 0.
  Proof.
    (* e = e' + e = e' *)
    intros. rewrite <- H. rewrite identityRight; auto.
  Qed.

  (** right identity element is unique  *)
  Theorem group_id_uniq_r : forall e', (forall a, a + e' = a) -> e' = 0.
  Proof.
    (* e = e + e' = e' *)
    intros. rewrite <- H. rewrite identityLeft; auto.
  Qed.

  (** left inverse element is unique *)
  (* a + b = 0 -> - a = b *)
  Theorem group_opp_uniq_l : forall a b : A, a + b = 0 -> -a = b.
  Proof.
    (* -a = -a + 0 = -a + a + b = 0 + b = b *)
    intros.
    replace (-a) with (-a + 0) by apply G.
    replace 0 with (a + b) by apply G.
    rewrite <- associative. rewrite inverseLeft. amonoid.
  Qed.
  
  (** right inverse element is unique *)
  (* a + b = 0 -> -b = a *)
  Theorem group_opp_uniq_r : forall a b : A, a + b = 0 -> -b = a.
  Proof.
    (* -b = 0 + -b = a + b + b = a + 0 = a *)
    intros.
    replace (-b) with (0 + -b) by apply G.
    replace 0 with (a + b) by apply G.
    rewrite associative. rewrite inverseRight. amonoid.
  Qed.

  (* Theorem 14.1 *)
  (** c + a = c + b -> a = b *)
  Theorem group_cancel_l : forall a b c, c + a = c + b -> a = b.
  Proof.
    intros.
    (* a = e+a = (-c+c)+a = (-c)+(c+a) = (-c)+(c+b) = (-c+c)+b = e+b = b*)
    rewrite <- identityLeft at 1.
    assert (0 = -c + c). group.
    rewrite H0. rewrite associative. rewrite H.
    rewrite <- associative. group.
  Qed.

  (** a + c = b + c -> a = b *)
  Theorem group_cancel_r : forall a b c, a + c = b + c -> a = b.
  Proof.
    intros.
    (* a = a+e = a+(c+ -c) = (a+c)+(-c) = (b+c)+(-c) = b+(c+ -c) = b+e = b *)
    rewrite <- identityRight at 1.
    assert (0 = c + (-c)). group.
    rewrite H0. rewrite <- associative. rewrite H.
    rewrite associative. group.
  Qed.

  (** - - a = a *)
  Theorem group_opp_opp : forall a,  - - a = a.
  Proof.
    intros. apply group_cancel_l with (- a). group.
  Qed.

  (** a - a = 0 *)
  Theorem group_sub_self : forall a, a - a = 0.
  Proof. intros. group. Qed.
    
  (** - a = - b -> a = b *)
  Lemma group_opp_inj : forall a b : A, - a = - b -> a = b.
  Proof.
    intros. rewrite <- group_opp_opp. rewrite <- H. rewrite group_opp_opp. auto.
  Qed.

  (** - (a + b) = (- b) + (- a) *)
  Theorem group_opp_distr : forall a b, - (a + b) = (- b) + (- a).
  Proof.
    intros.
    (* (a+b)+ -(a+b) = e = a+ -a = a+e+ -a = a+(b+ -b)+ -a
      = (a+b)+(-b+ -a), by cancel_l, got it *)
    apply group_cancel_l with (a + b).
    rewrite inverseRight. rewrite <- associative. rewrite (associative a b). group.
  Qed.

  (** a <> 0 -> - a <> 0 *)
  Lemma group_opp_neq0 : forall a : A, a <> 0 -> - a <> 0.
  Proof.
    intros. intro. destruct H.
    rewrite <- group_opp_opp at 1. rewrite H0. apply group_opp_0.
  Qed.
    
  (* Theorem 14.2 *)
  (** a + b = c -> a = c + (-b) *)
  Theorem group_sol_l : forall a b c, a + b = c -> a = c + (- b).
  Proof. intros. apply group_cancel_r with (b). group. Qed.

  (** a + b = c -> b = (-a) + c *)
  Theorem group_sol_r : forall a b c, a + b = c -> b = (- a) + c.
  Proof. intros. apply group_cancel_l with (a). rewrite <- associative. group. Qed.

  (** a - b = 0 <-> a = b *)
  Theorem group_sub_eq0_iff_eq : forall a b, a - b = 0 <-> a = b.
  Proof.
    intros. split; intros.
    - apply group_cancel_r with (-b). group.
    - subst. group.
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
    
    Theorem group_assoc_general (l1 l2 : list A) :
      (group_batch l1) + (group_batch l2) =  group_batch (l1 ++ l2).
    Proof.
      (* reduct to fold_left *)
      destruct l1,l2; simpl; group.
      - rewrite app_nil_r. group.
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
        { intros a l0. revert a. induction l0; intros; try reflexivity.
          simpl. rewrite IHl0. reflexivity. }
        assert (forall a b l, a + Σ b & l = Σ (a + b) & l) as H2.
        { intros. revert a b. induction l; simpl; intros; try reflexivity.
          simpl. rewrite IHl.
          (** fold_left preveres the aeq *)
          assert (forall l a1 a2, a1 = a2 -> Σ a1 & l = Σ a2 & l).
          { induction l0; intros; simpl in *; auto.
            apply IHl0. rewrite H. easy. }
          apply H. group. }
        assert (forall a b l, Σ a & (b :: l) = Σ (a + b) & l) as H3.
        { intros. revert a b. induction l; auto. }
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
    Abort.

    (** Theorem 14.4 *)
    Theorem group_power_inv : forall a n, (a^n) + (a^(- n)) = 0.
    Abort.

    Theorem group_power_plus : forall a m n, (a^m) + (a^n) = a^(m+n).
    Abort.

    Theorem group_power_mul : forall a m n, (a^m)^n = a^(m*n).
    Abort.

  End th14_4.

End GroupTheory.

(** ** Examples *)
Section Examples.
  
  Import Reals.
  
  Goal forall a b c : R, (a + c = 0 /\ c + b = 0 -> a = b)%R.
  Proof.
    intros. destruct H.
    apply group_opp_uniq_r in H.
    apply group_opp_uniq_l in H0.
    rewrite <- H, <- H0. auto.
  Qed.

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

Class AGroup {A} Aadd (Azero:A) Aopp := {
    agroupGroup :: Group Aadd Azero Aopp;
    agroupAM :: AMonoid Aadd Azero;
    agroupComm :: Commutative Aadd;
  }.

Section Theory.
  
  Context `{AG : AGroup}.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation "a - b" := (a + (-b)).

  (** a - b = - (b - a) *)
  Lemma agroup_sub_comm : forall a b, a - b = - (b - a).
  Proof.
    intros. rewrite group_opp_distr. rewrite group_opp_opp. easy.
  Qed.

  (** - (a + b) = -a + (-b) *)
  Lemma agroup_sub_distr : forall a b, - (a + b) = -a + (-b).
  Proof.
    intros. rewrite group_opp_distr. apply commutative.
  Qed.

  (** (a - b) - c = (a - c) - b *)
  Lemma agroup_sub_perm : forall a b c, (a - b) - c = (a - c) - b.
  Proof.
    intros. rewrite ?associative. rewrite (commutative (-b)). easy.
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
  
  #[export] Instance Qc_add_AGroup : AGroup Qcplus 0 Qcopp.
  split_intro; subst; ring. Defined.

  #[export] Instance R_add_AGroup : AGroup Rplus 0%R Ropp.
  split_intro; subst; ring. Defined.

  Goal forall a b c : R, ((a - b) - c = a - (b + c))%R.
  Proof. intros. apply agroup_sub_assoc. Qed.

End Instances.


(* ######################################################################### *)
(** * SemiRing *)
(* 区分半环与环：半环加法不需要逆元。比如<nat,+,*>是半环，但不是环 *)

(** ** Class *)

Class SemiRing {A} Aadd (Azero:A) Amul Aone := {
    sringAddAM :: AMonoid Aadd Azero; (* 不确定交换性是否必要，姑且先留下 *)
    sringMulAM :: AMonoid Amul Aone; (* 不确定交换性是否必要，姑且先留下 *)
    sringDistrL :: DistributiveLeft Aadd Amul;
    sringDistrR :: DistributiveRight Aadd Amul;
  }.

(** ** Instances *)
Section Instances.

  Import Nat ZArith Qcanon Reals.

  #[export] Instance nat_SRing : SemiRing Nat.add 0%nat Nat.mul 1%nat.
  repeat constructor; intros; ring. Qed.
  
  #[export] Instance Z_SRing : SemiRing Z.add 0%Z Z.mul 1%Z.
  repeat constructor; intros; ring. Qed.
  
  #[export] Instance Qc_SRing : SemiRing Qcplus 0 Qcmult 1.
  repeat constructor; intros; ring. Qed.

  #[export] Instance R_SRing : SemiRing Rplus R0 Rmult R1.
  split_intro; subst; ring. Defined.

End Instances.

(** ** Extra Theories *)
Section Theory.

  Context `{SR:SemiRing}.

  Infix "+" := Aadd.
  Infix "*" := Amul.

End Theory.

(** ** Examples *)

Section Examples.

End Examples.


(* ######################################################################### *)
(** * Ring *)

(** ** Class *)

(* Note that, the ring theory in mathematics needn't commutative of `mul` operation,
   but ring theory in Coq need it.
   We will distinguish ring and abelian ring with class name Ring and ARing.  *)

Class Ring {A} Aadd (Azero:A) Aopp Amul Aone := {
    ringAddAG :: AGroup Aadd Azero Aopp;
    ringMulM :: Monoid Amul Aone;
    ringDistrL :: DistributiveLeft Aadd Amul;
    ringDistrR :: DistributiveRight Aadd Amul;
  }.

(** ** Instances *)
Section Instances.

  Import ZArith Qcanon Reals.

  #[export] Instance Z_Ring : Ring Z.add 0%Z Z.opp Z.mul 1%Z.
  repeat constructor; intros; ring. Qed.
  
  #[export] Instance Qc_Ring : Ring Qcplus 0 Qcopp Qcmult 1.
  repeat constructor; intros; ring. Qed.

  #[export] Instance R_Ring : Ring Rplus R0 Ropp Rmult R1.
  repeat constructor; intros; ring. Qed.

End Instances.

(** ** Extra Theories *)
Section Theory.

  Context `{R:Ring}.

  Infix "+" := Aadd : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "*" := Amul : A_scope.

End Theory.

(** ** Examples *)

Section Examples.

  Import Reals.
  
  Goal forall a b c : R, (a * (b + c) = a * b + a * c)%R.
  Proof. apply distributiveLeft. Qed.

End Examples.
  

(* ######################################################################### *)
(** * ARing *)

(** ** Class *)

Class ARing {A} Aadd Azero Aopp Amul Aone := {
    aringRing :: @Ring A Aadd Azero Aopp Amul Aone;
    aringMulComm :: Commutative Amul;
    aringASGroup :: ASGroup Amul
  }.

(** ** Instances *)
Section Instances.

  Import ZArith Qcanon Reals.

  #[export] Instance Z_ARing : ARing Z.add 0%Z Z.opp Z.mul 1%Z.
  repeat constructor; intros; ring. Qed.
  
  #[export] Instance Ac_ARing : ARing Qcplus 0 Qcopp Qcmult 1.
  repeat constructor; intros; ring. Qed.

End Instances.

(** ** Extra Theories *)

Lemma make_ring_theory `(H:ARing)
  : ring_theory Azero Aone Aadd Amul (fun x y => Aadd x (Aopp y)) Aopp eq.
Proof.
  constructor; intros;
    try (rewrite ?identityLeft,?associative; reflexivity);
    try (rewrite commutative; reflexivity).
  rewrite distributiveRight; reflexivity.
  rewrite inverseRight; reflexivity.
Qed.

Section Theory.
  Context `{HARing: ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "+" := Aadd.
  Notation "0" := Azero.
  Notation "- a" := (Aopp a).
  Notation Asub a b := (a + -b).
  Infix "*" := Amul.
    
  (** 0 * a = 0 *)
  (* 证明思路：a*0 + 0 = a*0 = a*(0+0) = a*0 + a*0，然后消去律 *)
  Lemma ring_mul_0_r : forall a : A, a * 0 = 0.
  Proof. intros. ring. Qed.

  (** a * 0 = 0 *)
  Lemma ring_mul_0_l : forall a : A, 0 * a = 0.
  Proof. intros. ring. Qed.

  (** a * a = 1, then a = 1 or a = -1 *)
  (* Tips: I can't prove it now..., and this is used in `OrthogonalMatrix` *)
  Lemma ring_sqr_eq1_imply_1_neg1 : forall (a : A),
      a * a = Aone -> a = Aone \/ a = (- Aone).
  Proof.
  Admitted.

  (** (- a) * b = - (a * b) *)
  Theorem ring_mul_opp_l : forall a b, (- a) * b = - (a * b).
  Proof.
    intros.
    assert (a * b + (-a) * b = 0).
    - rewrite <- distributiveRight. rewrite inverseRight. apply ring_mul_0_l.
    - symmetry. apply group_opp_uniq_l. auto.
  Qed.

  (** a * (- b) = - (a * b) *)
  Theorem ring_mul_opp_r : forall a b, a * (- b) = - (a * b).
  Proof.
    intros. rewrite commutative. rewrite ring_mul_opp_l. rewrite commutative; auto.
  Qed.
    
  (** (- a) * (- b) = a * b *)
  Theorem ring_mul_opp_opp : forall a b, (- a) * (- b) = a * b.
  Proof.
    intros. rewrite ring_mul_opp_l, ring_mul_opp_r. apply group_opp_opp.
  Qed.
  
End Theory.

(** ** Examples *)

(** This example declares an abstract abelian-ring structure, and shows how to use
    fewer code to enable "ring" tactic. *)
Module Demo_AbsARing.
  Context `{HARing:ARing}.
  Infix "+" := Aadd. Infix "*" := Amul.
  Notation "0" := Azero. Notation "1" := Aone.

  Add Ring ring_inst : (make_ring_theory HARing).

  Goal forall a b c : A, (a + b) * c = 0 + b * c * 1 + 0 + 1 * c * a.
  Proof. intros. ring. Qed.
  
End Demo_AbsARing.

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
  Inductive A := Azero | A1 | A2 | A3.
  Notation "0" := Azero. Notation "1" := A1.
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

  (* 声明 Coq 中的  Ring 结构，需要一个 ring_theory 类型的证明，有两种方式 *)

  (* 方式1：直接构造一个证明 *)
  Lemma ring_thy : ring_theory 0 1 add mul (fun x y => add x (opp y)) opp eq.
  Proof.
    constructor; auto; intros;
      destruct x; auto; destruct y; auto; destruct z; auto.
  Qed.
  Add Ring ring_thy_inst1 : ring_thy.
  
  (* 方式二，先构造 ARing 结构 *)
  Local Instance ARing_inst : ARing add 0 opp mul 1.
  Proof.
    repeat constructor; intros;
      destruct a; auto; destruct b; auto; destruct c; auto.
  Qed.
  (* Add Ring ring_thy_inst2 : (make_ring_theory ARing_inst). *)

  Goal forall a b c : A, a + b + c - b = a + c.
  Proof.
    (* Tips, the proof is simple *)
    intros. ring.
  Qed.
  
End Demo_ConcrateRing.



(* ######################################################################### *)
(** * Abelian-ring with total order *)

Class OrderedARing {A} Aadd Azero Aopp Amul Aone Alt Ale Altb Aleb := {
    or_Ring :: ARing Aadd Azero Aopp Amul Aone;
    or_Order :: Order Alt Ale Altb Aleb;
    
    (* Lt is compatible with addition operation: a < b -> a + c < a + c *)
    lt_add_compat_r : forall a b c : A,
      Alt a b -> Alt (Aadd a c) (Aadd b c);
    (* Lt is compatible with multiply operation: a < b -> 0 < c -> a * c < b * c *)
    lt_mul_compat_r : forall a b c : A,
      Alt a b -> Alt Azero c -> Alt (Amul a c) (Amul b c);
  }.

Coercion or_Ring : OrderedARing >-> ARing.

(** ** Instances *)

(** ** Extra Theories *)
Section theories.
  Context `{HOrderedARing : OrderedARing}.
  Add Ring ring_inst : (make_ring_theory HOrderedARing).

  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + - b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "2" := (1 + 1) : A_scope.
  Notation "a ²" := (a * a) : A_scope.
  
  Notation "a > b" := (Alt b a) : A_scope.
  Notation "a >= b" := (Ale b a) : A_scope.
  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.
  Infix "<?" := Altb : A_scope.
  Infix "<=?" := Aleb : A_scope.
  

  (** *** Properties for "lt" *)

  (** **** About "add" *)

  (* a < b -> c + a < c + b *)
  Lemma lt_add_compat_l : forall a b c : A, a < b -> c + a < c + b.
  Proof. intros. rewrite !(commutative c _). apply lt_add_compat_r; auto. Qed.
  
  (* a < b -> c < d -> a + c < b + d *)
  Lemma lt_add_compat : forall a b c d : A, a < b -> c < d -> a + c < b + d.
  Proof.
    intros. apply lt_trans with (a + d).
    apply lt_add_compat_l; auto. apply lt_add_compat_r; auto.
  Qed.

  (* c + a < c + b -> a < b *)
  Lemma lt_add_reg_l : forall a b c, c + a < c + b -> a < b.
  Proof.
    intros. apply lt_add_compat_l with (c:=-c) in H.
    rewrite <- !associative in H. rewrite inverseLeft in H.
    rewrite !identityLeft in H. auto.
  Qed.

  (* a + c < b + c -> a < b *)
  Lemma lt_add_reg_r : forall a b c, a + c < b + c -> a < b.
  Proof.
    intros.
    apply lt_add_compat_r with (c:=-c) in H.
    rewrite !associative in H. rewrite inverseRight in H.
    rewrite !identityRight in H. auto.
  Qed.
  
  (* a < b <-> - b < - a *)
  Lemma lt_opp_iff : forall a b : A, a < b <-> - b < - a.
  Proof.
    (* a < b <-> -b + a + -a < -b + b + -a <-> -b < -a *)
    intros. split; intros.
    - apply lt_add_compat_l with (c:=-b) in H.
      apply lt_add_compat_r with (c:=-a) in H.
      replace (-b + a + -a) with (-b) in H; [|group].
      replace (-b + b + -a) with (-a) in H; [|group]. auto.
    - apply lt_add_reg_l with (c:=-b).
      apply lt_add_reg_r with (c:=-a).
      replace (-b + a + -a) with (-b); [|group].
      replace (-b + b + -a) with (-a); [|group]. auto.
  Qed.

  (* a < b <-> a - b < 0 *)
  Lemma lt_sub_iff : forall a b : A, a < b <-> a - b < 0.
  Proof.
    (* a < b <-> a + (- b) < b + (- b) -> a - b < 0 *)
    intros. split; intros.
    - apply lt_add_reg_r with (c := b). rewrite identityLeft at 1.
      rewrite associative. rewrite inverseLeft. rewrite identityRight. auto.
    - apply lt_add_compat_r with (c := b) in H.
      rewrite identityLeft in H at 1.
      rewrite associative in H. rewrite inverseLeft in H.
      rewrite identityRight in H. auto.
  Qed.

  (** a < 0 <-> 0 < - a *)
  Lemma lt0_iff_neg : forall a : A, a < 0 <-> 0 < - a.
  Proof. intros. rewrite lt_opp_iff. rewrite group_opp_0 at 1. easy. Qed.

  (** 0 < a <-> - a < 0 *)
  Lemma gt0_iff_neg : forall a : A, 0 < a <-> - a < 0.
  Proof. intros. rewrite lt_opp_iff. rewrite group_opp_0 at 1. easy. Qed.

  (** 0 < a -> 0 < b -> 0 < a + b *)
  Lemma add_gt0_if_gt0_gt0 : forall a b : A, 0 < a -> 0 < b -> 0 < a + b.
  Proof.
    intros. replace 0 with (0 + 0) by ring. apply lt_add_compat; auto.
  Qed.
    
  (** a < 0 -> b < 0 -> a + b < 0 *)
  Lemma add_lt0_if_lt0_lt0 : forall a b : A, a < 0 -> b < 0 -> a + b < 0.
  Proof.
    intros. replace 0 with (0 + 0) by ring. apply lt_add_compat; auto.
  Qed.
  
  (** a < 0 -> 0 < b -> a < b *)
  Lemma lt_if_lt0_gt0 : forall a b : A, a < 0 -> 0 < b -> a < b.
  Proof. intros. apply lt_trans with 0; auto. Qed.
  
  (** a <= 0 -> 0 < b -> a < b *)
  Lemma lt_if_le0_gt0 : forall a b : A, a <= 0 -> 0 < b -> a < b.
  Proof.
    intros. destruct (Aeqdec a 0). subst; auto.
    apply lt_trans with 0; auto. apply lt_le_cong in H. destruct H; easy.
  Qed.
  
  (** a < 0 -> 0 <= b -> a < b *)
  Lemma lt_if_lt0_ge0 : forall a b : A, a < 0 -> 0 <= b -> a < b.
  Proof.
    intros. destruct (Aeqdec b 0). subst; auto.
    apply lt_trans with 0; auto. apply lt_le_cong in H0. destruct H0; auto.
    symmetry in H0. easy.
  Qed.

  (** a < 0 -> a < - a *)
  Lemma lt_neg_r_if_lt0 : forall a : A, a < 0 -> a < - a.
  Proof. intros. apply lt_if_lt0_gt0; auto. apply lt0_iff_neg; auto. Qed.

  (** 0 < a -> - a < a *)
  Lemma gt_neg_l_if_gt0 : forall a : A, 0 < a -> - a < a.
  Proof. intros. apply lt_if_lt0_gt0; auto. apply gt0_iff_neg; auto. Qed.

  
  (** **** About "mul" *)
  
  (* a < b -> 0 < c -> c * a < c * b *)
  Lemma lt_mul_compat_l : forall a b c : A, a < b -> 0 < c -> c * a < c * b.
  Proof. intros. rewrite !(commutative c _). apply lt_mul_compat_r; auto. Qed.

  (* a < b -> c < 0 -> c * b < c * a *)
  Lemma lt_mul_compat_l_neg : forall a b c : A, a < b -> c < 0 -> c * b < c * a.
  Proof.
    intros. apply lt_opp_iff in H0. rewrite group_opp_0 in H0.
    apply lt_opp_iff. ring_simplify. apply lt_mul_compat_l; auto.
  Qed.

  (* a < b -> c < 0 -> b * c < a * c *)
  Lemma lt_mul_compat_r_neg : forall a b c : A, a < b -> c < 0 -> b * c < a * c.
  Proof. intros. rewrite !(commutative _ c). apply lt_mul_compat_l_neg; auto. Qed.

  (** 0 < a -> 0 < b -> 0 < a * b *)
  Lemma mul_gt0_if_gt0_gt0 : forall a b : A, 0 < a -> 0 < b -> 0 < a * b.
  Proof.
    intros. replace 0 with (a * 0). apply lt_mul_compat_l; auto. ring.
  Qed.
  
  (** a < 0 -> b < 0 -> 0 < a * b *)
  Lemma mul_gt0_if_lt0_lt0 : forall a b : A, a < 0 -> b < 0 -> 0 < a * b.
  Proof.
    intros. replace (a * b) with ((- a) * (- b)) by ring. apply mul_gt0_if_gt0_gt0.
    apply lt0_iff_neg; auto. apply lt0_iff_neg; auto.
  Qed.
  
  (** 0 < a -> b < 0 -> a * b < 0 *)
  Lemma mul_lt0_if_gt0_lt0 : forall a b : A, 0 < a -> b < 0 -> a * b < 0.
  Proof.
    intros. replace 0 with (a * 0). apply lt_mul_compat_l; auto. ring.
  Qed.
  
  (** a < 0 -> 0 < b -> a * b < 0 *)
  Lemma mul_lt0_if_lt0_gt0 : forall a b : A, a < 0 -> 0 < b -> a * b < 0.
  Proof.
    intros. replace 0 with (0 * b). apply lt_mul_compat_r; auto. ring.
  Qed.

  (** 0 < a * b -> 0 < a -> 0 < b *)
  Lemma gt0_mul_reg_gt0 : forall a b : A, 0 < a * b -> 0 < a -> 0 < b.
  Proof.
    intros. destruct (lt_cases 0 b) as [[H1|H1]|H1]; auto.
    - apply lt0_iff_neg in H1.
      pose proof (mul_gt0_if_gt0_gt0 H0 H1).
      replace (a * - b) with (- (a * b)) in H2 by ring.
      apply lt0_iff_neg in H2. apply lt_gt_contr in H; easy.
    - rewrite <- H1 in *. ring_simplify in H. apply lt_irrefl in H; easy.
  Qed.
  
  (** 0 < a * b -> a < 0 -> b < 0 *)
  Lemma gt0_mul_reg_lt0 : forall a b : A, 0 < a * b -> a < 0 -> b < 0.
  Proof.
    intros. replace (a * b) with ((- a) * (- b)) in H by ring.
    apply lt0_iff_neg. apply lt0_iff_neg in H0.
    apply (gt0_mul_reg_gt0 H) in H0; auto.
  Qed.
  
  
  (** *** Properties for "le" *)

  (** **** About "add" *)
  
  (* a <= b -> a + c <= a + c *)
  Lemma le_add_compat_r : forall a b c : A, a <= b -> a + c <= b + c.
  Proof.
    intros. apply lt_le_cong. apply lt_le_cong in H. destruct H; subst; auto.
    left. apply lt_add_compat_r; auto.
  Qed.
  
  (* a <= b -> c + a <= c + b *)
  Lemma le_add_compat_l : forall a b c : A, a <= b -> c + a <= c + b.
  Proof. intros. rewrite !(commutative c _). apply le_add_compat_r; auto. Qed.
  
  (* a <= b -> c <= d -> a + c <= b + d *)
  Lemma le_add_compat : forall a b c d : A, a <= b -> c <= d -> a + c <= b + d.
  Proof.
    intros. apply le_trans with (a + d).
    apply le_add_compat_l; auto. apply le_add_compat_r; auto.
  Qed.

  (* c + a <= c + b -> a <= b *)
  Lemma le_add_reg_l : forall a b c, c + a <= c + b -> a <= b.
  Proof.
    intros. apply le_add_compat_l with (c:=-c) in H.
    rewrite <- !associative in H. rewrite inverseLeft in H.
    rewrite (identityLeft a) in H. rewrite (identityLeft b) in H. auto.
  Qed.

  (* a + c <= b + c -> a <= b *)
  Lemma le_add_reg_r : forall a b c, a + c <= b + c -> a <= b.
  Proof.
    intros. apply le_add_compat_r with (c:=-c) in H.
    rewrite !associative in H. rewrite inverseRight in H.
    rewrite (identityRight a) in H. rewrite (identityRight b) in H. auto.
  Qed.

  (** 0 <= a -> 0 <= b -> 0 <= a + b *)
  Lemma add_ge0_if_ge0_ge0 : forall a b : A, 0 <= a -> 0 <= b -> 0 <= a + b.
  Proof.
    intros. replace 0 with (0 + 0) by ring. apply le_add_compat; auto.
  Qed.
    
  (** a <= 0 -> b <= 0 -> a + b <= 0 *)
  Lemma add_le0_if_le0_le0 : forall a b : A, a <= 0 -> b <= 0 -> a + b <= 0.
  Proof.
    intros. replace 0 with (0 + 0) by ring. apply le_add_compat; auto.
  Qed.
  
  (* a <= b <-> - b <= - a *)
  Lemma le_opp_iff : forall a b : A, a <= b <-> - b <= - a.
  Proof.
    intros. rewrite !lt_le_cong. split; intros; destruct H; subst; auto.
    - apply lt_opp_iff in H; auto.
    - apply lt_opp_iff in H; auto.
    - apply group_opp_inj in H. auto.
  Qed.

  (** a <= 0 <-> 0 <= - a *)
  Lemma le0_iff_neg : forall a : A, a <= 0 <-> 0 <= - a.
  Proof. intros. rewrite le_opp_iff. rewrite group_opp_0 at 1. easy. Qed.

  (** 0 <= a <-> - a <= 0 *)
  Lemma ge0_iff_neg : forall a : A, 0 <= a <-> - a <= 0.
  Proof. intros. rewrite le_opp_iff. rewrite group_opp_0 at 1. easy. Qed.
  
  (** a <= 0 -> 0 <= b -> a <= b *)
  Lemma le_if_le0_ge0 : forall a b : A, a <= 0 -> 0 <= b -> a <= b.
  Proof. intros. apply le_trans with 0; auto. Qed.
  
  (** a < 0 -> 0 < b -> a <= b *)
  Lemma le_if_lt0_gt0 : forall a b : A, a < 0 -> 0 < b -> a <= b.
  Proof. intros. apply le_if_lt. apply lt_if_lt0_gt0; auto. Qed.
  
  (** a <= 0 -> 0 < b -> a <= b *)
  Lemma le_if_le0_gt0 : forall a b : A, a <= 0 -> 0 < b -> a <= b.
  Proof. intros. apply le_if_lt. apply lt_if_le0_gt0; auto. Qed.
  
  (** a < 0 -> 0 <= b -> a <= b *)
  Lemma le_if_lt0_ge0 : forall a b : A, a < 0 -> 0 <= b -> a <= b.
  Proof. intros. apply le_if_lt. apply lt_if_lt0_ge0; auto. Qed.

  (** a <= 0 -> a <= - a *)
  Lemma le_neg_r_if_le0 : forall a : A, a <= 0 -> a <= - a.
  Proof. intros. apply le_if_le0_ge0; auto. apply le0_iff_neg; auto. Qed.

  (** a < 0 -> a <= - a *)
  Lemma le_neg_r_if_lt0 : forall a : A, a < 0 -> a <= - a.
  Proof. intros. apply le_neg_r_if_le0. apply le_if_lt; auto. Qed.

  (** 0 <= a -> - a <= a *)
  Lemma ge_neg_l_if_ge0 : forall a : A, 0 <= a -> - a <= a.
  Proof. intros. apply le_if_le0_ge0; auto. apply ge0_iff_neg; auto. Qed.

  (** 0 < a -> - a <= a *)
  Lemma ge_neg_l_if_gt0 : forall a : A, 0 < a -> - a <= a.
  Proof. intros. apply ge_neg_l_if_ge0. apply le_if_lt; auto. Qed.

  
  (** **** About "mul" *)
  
  (* a <= b -> 0 <= c -> a * c <= b * c *)
  Lemma le_mul_compat_r : forall a b c : A, a <= b -> 0 <= c -> a * c <= b * c.
  Proof.
    intros. apply lt_le_cong. apply lt_le_cong in H, H0. destruct H,H0; auto.
    - left. apply lt_mul_compat_r; auto.
    - rewrite <- H0. rewrite (ring_mul_0_r a). rewrite (ring_mul_0_r b). auto.
    - subst; auto.
    - subst; auto.
  Qed.

  (* a <= b -> 0 <= c -> c * a <= c * b *)
  Lemma le_mul_compat_l : forall a b c : A, a <= b -> 0 <= c -> c * a <= c * b.
  Proof. intros. rewrite !(commutative c _). apply le_mul_compat_r; auto. Qed.

  (* a <= b -> c < 0 -> c * b <= c * a *)
  Lemma le_mul_compat_l_neg : forall a b c : A, a <= b -> c < 0 -> c * b <= c * a.
  Proof.
    intros. apply lt_le_cong in H. destruct H.
    - apply lt_mul_compat_l_neg with (c:=c) in H; auto. apply le_if_lt; auto.
    - subst. apply le_refl.
  Qed.

  (* a <= b -> c < 0 -> b * c <= a * c *)
  Lemma le_mul_compat_r_neg : forall a b c : A, a <= b -> c < 0 -> b * c <= a * c.
  Proof. intros. rewrite !(commutative _ c). apply le_mul_compat_l_neg; auto. Qed.

  (** 0 <= a -> 0 <= b -> 0 <= a * b *)
  Lemma mul_ge0_if_ge0_ge0 : forall a b : A, 0 <= a -> 0 <= b -> 0 <= a * b.
  Proof.
    intros. replace 0 with (a * 0). apply le_mul_compat_l; auto. ring.
  Qed.
  
  (** a <= 0 -> b <= 0 -> 0 <= a * b *)
  Lemma mul_ge0_if_le0_le0 : forall a b : A, a <= 0 -> b <= 0 -> 0 <= a * b.
  Proof.
    intros.
    intros. replace (a * b) with ((- a) * (- b)) by ring. apply mul_ge0_if_ge0_ge0.
    apply le0_iff_neg; auto. apply le0_iff_neg; auto.
  Qed.
    
  (** 0 <= a -> b <= 0 -> a * b <= 0 *)
  Lemma mul_le0_if_ge0_le0 : forall a b : A, 0 <= a -> b <= 0 -> a * b <= 0.
  Proof.
    intros. replace 0 with (a * 0). apply le_mul_compat_l; auto. ring.
  Qed.

  (** a <= 0 -> 0 <= b -> a * b <= 0 *)
  Lemma mul_le0_if_le0_ge0 : forall a b : A, a <= 0 -> 0 <= b -> a * b <= 0.
  Proof.
    intros. replace 0 with (0 * b). apply le_mul_compat_r; auto. ring.
  Qed.

  (** 0 <= a * b -> 0 < a -> 0 <= b *)
  Lemma ge0_mul_reg_ge0 : forall a b : A, 0 <= a * b -> 0 < a -> 0 <= b.
  Proof.
    intros. destruct (le_dec 0 b) as [H1|H1]; auto.
    destruct (Aeqdec b 0) as [H2|H2].
    - rewrite H2 in *. apply le_refl.
    - exfalso. apply not_le_lt in H1.
      pose proof (mul_lt0_if_gt0_lt0 H0 H1).
      apply lt_not_le in H3. easy.
  Qed.
  
  (** 0 <= a * b -> a < 0 -> b <= 0 *)
  Lemma ge0_mul_reg_le0 : forall a b : A, 0 <= a * b -> a < 0 -> b <= 0.
  Proof.
    intros. replace (a * b) with ((- a) * (- b)) in H by ring.
    apply lt0_iff_neg in H0. apply ge0_mul_reg_ge0 in H; auto.
    apply le0_iff_neg; auto.
  Qed.

  
  (** **** More properties  *)
  
  (* 0 <= a * a *)
  Lemma sqr_ge0 : forall a : A, a * a >= 0.
  Proof.
    intros.
    pose proof (lt_connected 0 a). destruct H as [H|[H|H]].
    - apply le_if_lt.
      pose proof (lt_mul_compat_r H H). rewrite ring_mul_0_l in H0; auto.
    - apply le_if_lt. rewrite lt_opp_iff in H. rewrite group_opp_0 in H.
      rewrite <- (group_opp_opp a). rewrite ring_mul_opp_opp.
      pose proof (lt_mul_compat_r H H). rewrite ring_mul_0_l in H0. auto.
    - rewrite <- H. rewrite (ring_mul_0_l 0). apply le_refl.
  Qed.
  
  (* 0 <= a -> 0 <= b -> a + b = 0 -> a = 0 *)
  Lemma add_eq0_imply_0_l : forall a b : A, 0 <= a -> 0 <= b -> a + b = 0 -> a = 0.
  Proof.
    intros. apply lt_le_cong in H, H0.
    destruct H as [H|H], H0 as [H0|H0]; auto.
    - assert (a + b > 0 + 0).
      + apply lt_add_compat; auto.
      + rewrite H1 in H2. rewrite identityLeft in H2. apply lt_irrefl in H2. easy.
    - rewrite <- H0 in *. rewrite identityRight in H1. auto.
  Qed.

  (* 0 <= a -> 0 <= b -> a + b = 0 -> b = 0 *)
  Lemma add_eq0_imply_0_r : forall a b : A, 0 <= a -> 0 <= b -> a + b = 0 -> b = 0.
  Proof.
    intros. rewrite commutative in H1. apply add_eq0_imply_0_l in H1; auto.
  Qed.

  (** 0 <= a + b -> a >= - b *)
  Lemma sub_ge0_imply_ge : forall a b : A, 0 <= a - b -> a >= b.
  Proof.
    intros. apply le_add_compat_r with (c:= b) in H. ring_simplify in H. auto.
  Qed.

  (** 2 * a * b <= a² + b² *)
  Lemma mul_le_add_sqr : forall a b : A, 2 * a * b <= a² + b².
  Proof.
    intros.
    assert (0 <= (a - b)²). apply sqr_ge0.
    ring_simplify in H.
    replace (a ² + - (2 * a * b) + b ²)
      with (a ² + b ² - (2 * a * b)) in H by ring.
    apply sub_ge0_imply_ge in H. auto.
  Qed.


  (** *** Abs of a term of A type *)
  
  Definition Aabs (a : A) : A := if 0 <=? a then a else - a.
  Notation "| a |" := (Aabs a) : A_scope.

  (** 0 <= a -> | a | = a *)
  Lemma Aabs_right : forall a : A, 0 <= a -> | a | = a.
  Proof. intros. unfold Aabs. destruct (leb_reflect 0 a); auto. easy. Qed.
    
  (** a < 0 -> | a | = - a *)
  Lemma Aabs_left : forall a : A, a < 0 -> | a | = - a.
  Proof.
    intros. unfold Aabs. destruct (leb_reflect 0 a); auto.
    apply lt_not_le in H. easy.
  Qed.

  (** | a * b | = | a | * | b | *)
  Lemma Aabs_mul : forall a b : A, | a * b | = | a | * | b |.
  Proof.
    intros. unfold Aabs.
    destruct (leb_reflect 0 (a*b)), (leb_reflect 0 a), (leb_reflect 0 b); try ring.
    - apply not_le_lt in n.
      rewrite commutative in a0. apply ge0_mul_reg_le0 in a0; auto.
      apply le_ge_eq in a1; auto. subst. ring.
    - apply not_le_lt in n. apply ge0_mul_reg_le0 in a0; auto.
      apply le_ge_eq in a1; auto. subst. ring.
    - pose proof (mul_ge0_if_ge0_ge0 a0 a1). easy.
    - apply not_le_lt in n,n0,n1. pose proof (mul_gt0_if_lt0_lt0 n0 n1).
      exfalso. apply (lt_gt_contr n H).
  Qed.

  (** | a + b | <= | a | + | b | *)
  Lemma Aabs_add_le : forall a b : A, | a + b | <= | a | + | b |.
  Proof.
    intros. unfold Aabs.
    destruct (leb_reflect 0 a), (leb_reflect 0 b), (leb_reflect 0 (a + b));
      ring_simplify.
    - apply le_refl.
    - apply le_add_compat; apply ge_neg_l_if_ge0; auto.
    - apply le_add_compat_l. apply le_neg_r_if_lt0; auto. apply not_le_lt; auto.
    - apply le_add_compat_r. apply ge_neg_l_if_ge0; auto.
    - apply le_add_compat_r. apply le_neg_r_if_lt0. apply not_le_lt; auto.
    - apply le_add_compat_l. apply ge_neg_l_if_ge0; auto.
    - apply not_le_lt in n,n0. pose proof (add_lt0_if_lt0_lt0 n n0).
      apply le_not_lt in a0. easy.
    - apply le_refl.
  Qed.

End theories.

(** ** Examples *)



(* ######################################################################### *)
(** * Field *)

(** ** Class *)
Class Field {A} Aadd (Azero:A) Aopp Amul Aone Ainv := {
    fieldRing :: ARing Aadd Azero Aopp Amul Aone;
    field_mulInvL : forall a, a <> Azero -> Amul (Ainv a) a = Aone;
    field_1_neq_0 : Aone <> Azero;
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  #[export] Instance Field_Qc : Field Qcplus 0 Qcopp Qcmult 1 Qcinv.
  split_intro; subst; (try (field; reflexivity)); try easy.
  field. auto.
  Defined.

  #[export] Instance Field_R : Field Rplus R0 Ropp Rmult R1 Rinv.
  split_intro; subst; try (field; reflexivity); auto.
  field; auto. auto with real.
  Defined.

End Instances.


(** ** Extra Theories *)

Lemma make_field_theory `(H:Field)
  : field_theory Azero Aone Aadd Amul
      (fun a b => Aadd a (Aopp b)) Aopp
      (fun a b => Amul a (Ainv b)) Ainv eq.
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
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation Asub a b := (a + -b).
  Notation "0" := Azero.
  Notation "1" := Aone.
  Infix "*" := Amul.
  Notation "/ a" := (Ainv a).
  Notation Adiv a b := (a * (/b)).
  Infix "/" := Adiv.

  Add Field field_inst : (make_field_theory F).

  (** a <> 0 -> a * / a = 1 *)
  Lemma field_mulInvR : forall a : A, a <> 0 -> a * /a = 1.
  Proof. intros. rewrite commutative. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> (1/a) * a = 1 *)
  Lemma field_mulInvL_inv1 : forall a : A, a <> 0 -> (1/a) * a = 1.
  Proof. intros. simpl. group. apply field_mulInvL. auto. Qed.
  
  (** a <> 0 -> a * (1/a) = 1 *)
  Lemma field_mulInvR_inv1 : forall a : A, a <> 0 -> a * (1/a) = 1.
  Proof. intros. simpl. group. apply field_mulInvR. auto. Qed.

  (** a <> 0 -> / a <> 0 *)
  Lemma field_inv_neq0 : forall a : A, a <> 0 -> / a <> 0.
  Proof.
    intros. intro.
    pose proof (field_mulInvL H). rewrite H0 in H1. rewrite ring_mul_0_l in H1.
    apply field_1_neq_0. auto.
  Qed.

  (* / a <> 0 -> a <> 0 *)
  Lemma field_inv_neq0_rev : forall a : A, / a <> 0 -> a <> 0.
  Proof.
    intros. intro. Abort.

  (** - 1 <> 0 *)
  Lemma field_neg1_neq_0 : - (1) <> 0.
  Proof.
    intro. rewrite <- group_opp_0 in H at 1. apply group_opp_inj in H.
    apply field_1_neq_0; auto.
  Qed.
  
  (** a <> 0 -> a * b = a * c -> b = c *)
  Lemma field_mul_cancel_l : forall a b c : A,
      a <> 0 -> a * b = a * c -> b = c.
  Proof.
    intros.
    assert (/a * (a * b) = /a * (a * c)).
    { rewrite H0. easy. }
    rewrite <- ?associative in H1.
    rewrite field_mulInvL in H1; auto.
    rewrite ?identityLeft in H1. easy.
  Qed.

  (** c <> 0 -> a * c = b * c -> a = b *)
  Lemma field_mul_cancel_r : forall a b c : A,
      c <> 0 -> a * c = b * c -> a = b.
  Proof.
    intros.
    assert ((a * c) * /c = (b * c) * /c).
    { rewrite H0. easy. }
    rewrite ?associative in H1.
    rewrite field_mulInvR in H1; auto.
    rewrite ?identityRight in H1. easy.
  Qed.

  (** a * b = 1 -> / a = b *)
  Lemma field_inv_eq_l : forall a b : A, a <> 0 -> a * b = 1 -> / a = b.
  Proof.
    intros. apply (@field_mul_cancel_l a (/ a) b); auto.
    rewrite field_mulInvR; auto.
  Qed.

  (** a * b = 1 -> / b = a *)
  Lemma field_inv_eq_r : forall a b : A, b <> 0 -> a * b = 1 -> / b = a.
  Proof.
    intros. apply (@field_mul_cancel_r (/ b) a b); auto.
    rewrite field_mulInvL; auto.
  Qed.

  (** / / a = a *)
  Lemma field_inv_inv : forall a : A, a <> 0 -> / / a = a.
  Proof.
    intros. pose proof (field_inv_neq0 H).
    apply field_mul_cancel_l with (/ a); auto.
    rewrite field_mulInvL; auto. rewrite field_mulInvR; auto.
  Qed.

  (** / a = / b -> a = b *)
  Lemma field_inv_inj : forall a b : A, a <> 0 -> b <> 0 -> / a = / b -> a = b.
  Proof.
    intros. rewrite <- field_inv_inv; auto. rewrite <- H1.
    rewrite field_inv_inv; auto.
  Qed.

  (** / (- a) = - (/ a) *)
  Lemma field_inv_opp : forall a : A, a <> 0 -> / (- a) = - (/ a).
  Proof.
    intros. apply field_inv_eq_l. apply group_opp_neq0; auto.
    rewrite ring_mul_opp_opp. apply field_mulInvR; auto.
  Qed.

  
  Context {AeqDec : Dec (@eq A)}.
  
  (** a * b = 0 -> a = 0 \/ b = 0 *)
  Lemma field_mul_eq0_reg : forall a b : A, a * b = 0 -> a = 0 \/ b = 0.
  Proof.
    intros. destruct (Aeqdec b 0); auto.
    assert (a * b * /b = 0 * /b). rewrite H. auto.
    assert (0 * /b = 0). apply ring_mul_0_l. rewrite H1 in H0.
    rewrite associative in H0. rewrite field_mulInvR in H0; auto.
    rewrite identityRight in H0. auto.
  Qed.
  
  (** a <> 0 -> b <> 0 -> a * b <> 0 *)
  Lemma field_mul_neq0_if_neq0_neq0 : forall a b : A, a <> 0 -> b <> 0 -> a * b <> 0.
  Proof. intros. intro. apply field_mul_eq0_reg in H1. destruct H1; auto. Qed.

  (* a * a = 0 -> a = 0 *)
  Lemma field_sqr_eq0_reg : forall a : A, a * a = 0 -> a = 0.
  Proof. intros. apply field_mul_eq0_reg in H. destruct H; auto. Qed.

  (** a * b = b -> a = 1 \/ b = 0 *)
  Lemma field_mul_eq_imply_a1_or_b0 : forall (a b : A),
      a * b = b -> (a = 1) \/ (b = 0).
  Proof.
    intros. destruct (Aeqdec a 1), (Aeqdec b 0); auto.
    replace b with (1 * b) in H at 2 by group.
    apply field_mul_cancel_r in H; auto.
  Qed.

End Theory.

(** ** Examples *)
Section Examples.

  Import Reals.
  
  Goal forall a b : R, (a <> 0 -> /a * a = 1)%R.
    intros. apply field_mulInvL. auto. Qed.

End Examples.



(* ######################################################################### *)
(** * Field with total order *)

Class OrderedField {A} Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb := {
    of_Field :: @Field A Aadd Azero Aopp Amul Aone Ainv;
    of_OrderedRing :: @OrderedARing _ Aadd Azero Aopp Amul Aone Alt Ale Altb Aleb;
  }.

Coercion of_Field : OrderedField >-> Field.
(* Coercion of_Order : OrderedField >-> Order. *)

(** ** Instances *)

(** ** Extra Theories *)
Section Theory.
  Context `{HOrderedField : OrderedField}.
  Add Field field_inst : (make_field_theory HOrderedField).

  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation "0" := Azero.
  Infix "*" := Amul.
  Notation "1" := Aone.
  Notation "/ a" := (Ainv a).
  Notation Adiv a b := (a * / b).
  Infix "/" := Adiv.
  
  Notation "a > b" := (Alt b a).
  Notation "a >= b" := (Ale b a).
  Infix "<" := Alt.
  Infix "<=" := Ale.
  Infix "<?" := Altb.
  Infix "<=?" := Aleb.
    
  (** a <> 0 -> 0 < a * a *)
  Lemma sqr_gt0 : forall a : A, a <> 0 -> 0 < a * a.
  Proof.
    intros. apply lt_if_le_and_neq.
    - apply sqr_ge0.
    - intro. symmetry in H0. apply field_sqr_eq0_reg in H0. easy.
  Qed.
  
  (** 0 < 1 *)
  Lemma lt_0_1 : 0 < 1.
  Proof.
    (* 0 < a*a -> 0 < 1*1 -> 0 < 1 *)
    assert (1 <> 0). apply field_1_neq_0.
    pose proof (sqr_gt0 H). rewrite identityLeft in H0. auto.
  Qed.
  
  (** 0 <= 1 *)
  Lemma le_0_1 : 0 <= 1.
  Proof. apply le_if_lt. apply lt_0_1. Qed.
  
  (** 0 < a -> 0 < / a *)
  Lemma inv_gt0 : forall a : A, 0 < a -> 0 < / a.
  Proof.
    intros.
    assert (0 < a * / a).
    { field_simplify. apply lt_0_1. symmetry. apply lt_not_eq; auto. }
    apply (gt0_mul_reg_gt0 H0); auto.
  Qed.
  
  (** a < 0 -> / a < 0 *)
  Lemma inv_lt0 : forall a : A, a < 0 -> / a < 0.
  Proof.
    intros. pose proof (lt_imply_neq H).
    rewrite lt_opp_iff in H. rewrite group_opp_0 in H.
    apply inv_gt0 in H. rewrite field_inv_opp in H; auto. apply lt0_iff_neg; auto.
  Qed.
  
  (** 0 < a -> 0 < b -> a < b -> / b < / a *)
  Lemma lt_inv : forall a b : A, 0 < a -> 0 < b -> a < b -> / b < / a.
  Proof.
    (* a < b -> /b * a * /a < /b * b * /a -> /b < /a *)
    intros.
    apply lt_mul_compat_l with (c:=/b) in H1.
    apply lt_mul_compat_r with (c:=/a) in H1.
    rewrite field_mulInvL in H1. rewrite identityLeft in H1 at 1.
    rewrite associative in H1. rewrite field_mulInvR, identityRight in H1. auto.
    symmetry; apply lt_imply_neq; auto.
    symmetry; apply lt_imply_neq; auto.
    apply inv_gt0; auto.
    apply inv_gt0; auto.
  Qed.

  (** 0 < c -> c * a < c * b -> a < b *)
  Lemma lt_mul_reg_l : forall a b c, 0 < c -> c * a < c * b -> a < b.
  Proof.
    intros. apply lt_mul_compat_l with (c:=/c) in H0.
    - rewrite <- !associative in H0. rewrite field_mulInvL in H0.
      + rewrite !identityLeft in H0; auto.
      + symmetry. apply lt_imply_neq; auto.
    - apply inv_gt0; auto.
  Qed.
  
  (** 0 < c -> a * c < b * c -> a < b *)
  Lemma lt_mul_reg_r : forall a b c, 0 < c -> a * c < b * c -> a < b.
  Proof.
    intros. rewrite !(commutative _ c) in H0. apply lt_mul_reg_l in H0; auto.
  Qed.
  
  (** 0 < a -> a < b -> a / b < 1 *)
  Lemma lt_imply_div_lt_1 : forall a b : A, 0 < a -> a < b -> a / b < 1.
  Proof.
    intros. replace 1 with (b / b).
    apply lt_mul_compat_r; auto. apply inv_gt0. apply lt_trans with a; auto.
    apply field_mulInvR. symmetry. apply lt_imply_neq. apply lt_trans with a; auto.
  Qed.
  
  (** 0 < a -> a <= b -> a / b <= 1 *)
  Lemma le_imply_div_le_1 : forall a b : A, 0 < a -> a <= b -> a / b <= 1.
  Proof.
    intros. apply lt_le_cong in H0. destruct H0.
    - apply le_if_lt. apply lt_imply_div_lt_1; auto.
    - subst. rewrite field_mulInvR. apply le_refl.
      symmetry. apply lt_imply_neq; auto.
  Qed.
    
End Theory.


(* ######################################################################### *)
(** * Convert to R type *)

Class ConvertToR {A} Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb
  (a2r : A -> R) := {
    a2r_add : forall a b : A, a2r (Aadd a b) = (a2r a + a2r b)%R;
    a2r_0 : a2r Azero = 0%R;
    a2r_opp : forall a : A, a2r (Aopp a) = (- (a2r a))%R;
    a2r_mul : forall a b : A, a2r (Amul a b) = (a2r a * a2r b)%R;
    a2r_1 : a2r Aone = 1%R;
    a2r_inv : forall a : A, a <> Azero -> a2r (Ainv a) = (/ (a2r a))%R;
    a2r_Order :: Order Alt Ale Altb Aleb;
    a2r_eq_iff : forall a b : A, a2r a = a2r b <-> a = b;
    a2r_lt_iff : forall a b : A, (a2r a < a2r b)%R <-> Alt a b;
    a2r_le_iff : forall a b : A, (a2r a <= a2r b)%R <-> Ale a b
  }.

(** ** Instances *)

(** ** Extra Theories *)
Section Theory.
  Context `{ConvertToR}.
  Context {AeqDec : Dec (@eq A)}.
  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.

  (** a2r a = 0 <-> a = 0 *)
  Lemma a2r_eq0_iff : forall a : A, (a2r a = 0)%R <-> (a = Azero)%A.
  Proof. intros. rewrite <- a2r_0. apply a2r_eq_iff. Qed.

  (** a2r a = 1 <-> a = 1 *)
  Lemma a2r_eq1_iff : forall a : A, (a2r a = 1)%R <-> (a = Aone)%A.
  Proof. intros. rewrite <- a2r_1. apply a2r_eq_iff. Qed.
  
  (** 0 <= a2r a <-> 0 <= a *)
  Lemma a2r_ge0_iff : forall a : A, (0 <= a2r a)%R <-> (Azero <= a)%A.
  Proof. intros. rewrite <- a2r_0. apply a2r_le_iff. Qed.

  (** 0 < a2r a <-> 0 < a *)
  Lemma a2r_gt0_iff : forall a : A, (0 < a2r a)%R <-> (Azero < a)%A.
  Proof. intros. rewrite <- a2r_0. apply a2r_lt_iff. Qed.

  Section OrderedARing.
    Context `{HOrderedARing :
        OrderedARing A Aadd Azero Aopp Amul Aone Alt Ale Altb Aleb}.
    Notation "| a |" := (Rabs a) : R_scope.
    Notation "| a |" := (@Aabs _ Azero Aopp Aleb a) : A_scope.

    (** a2r | a | = | a2r a | *)
    Lemma a2r_Aabs : forall a : A, a2r (| a |) = | a2r a|%R.
    Proof.
      intros. unfold Aabs. destruct (leb_reflect Azero a).
      - rewrite Rabs_right; auto. rewrite <- a2r_0.
        apply Rle_ge. apply a2r_le_iff; auto.
      - rewrite Rabs_left. rewrite a2r_opp. auto.
        rewrite <- a2r_0. apply a2r_lt_iff. apply not_le_lt; auto.
    Qed.
    
  End OrderedARing.
  
End Theory.
