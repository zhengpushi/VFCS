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

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Adiv.


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

Arguments dec {A} _ {_}.
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
    bijInjective :> Injective phi;
    bijSurjective :> Surjective phi
  }.

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
(** * Semigroup 半群 *)

(** ** Class *)
Class SGroup {A} (Aadd : A -> A -> A) := {
    sgroupAssoc :> Associative Aadd;
  }.

(** Get parameter of this structure *)
Definition sgroupAadd `{SG:SGroup} : A -> A -> A := Aadd.

(** ** Instances *)
Section Instances.
  
  #[export] Instance SGroup_NatAdd : SGroup Nat.add.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  #[export] Instance SGroup_NatMul : SGroup Nat.mul.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.
  
End Instances.

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Abelian semigroup 交换半群 *)

(** ** Class *)
Class ASGroup {A} (Aadd : A -> A -> A) := {
    asgroupSGroup :> SGroup Aadd;
    asgroupComm :> Commutative Aadd
  }.

(** Get parameter of this structure *)
Definition asgroupAadd `{ASG : ASGroup} : A -> A -> A := Aadd.

(** ** Instances *)
Section Instances.
  
  #[export] Instance ASGroup_NatAdd : ASGroup Nat.add.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  #[export] Instance ASGroup_NatMul : SGroup Nat.mul.
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
    monoidAssoc :> Associative Aadd;
    monoidIdL :> IdentityLeft Aadd Azero;
    monoidIdR :> IdentityRight Aadd Azero;
    monoidSGroup :> SGroup Aadd
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
    amonoidMonoid :> @Monoid A Aadd Azero;
    amonoidComm :> Commutative Aadd;
    amonoidASGroup :> ASGroup Aadd
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
    groupMonoid :> Monoid Aadd Azero;
    groupInvL :> InverseLeft Aadd Azero Aopp;
    groupInvR :> InverseRight Aadd Azero Aopp;
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  #[export] Instance Group_QcAdd : Group Qcplus 0 Qcopp.
  split_intro; subst; ring. Defined.

  #[export] Instance Group_RAdd : Group Rplus 0%R Ropp.
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
  Notation Asub := (fun x y => x + (-y)).
  Infix "-" := Asub.

  (** *** Additional properties. *)
  Section additional_props.

    (** - 0 = 0 *)
    Theorem group_inv_zero : - 0 = 0.
    Proof.
      pose proof (inverseLeft 0). rewrite identityRight in H. auto.
    Qed.

  End additional_props.
  
  (** Theorem 5.1 *)
  Theorem group_id_uniq_l : forall e',
      (forall a, e' + a = a) -> e' = 0.
  Proof.
    (* e = e' + e = e' *)
    intros. rewrite <- H. rewrite identityRight; auto.
  Qed.

  Theorem group_id_uniq_r : forall e', (forall a, a + e' = a) -> e' = 0.
  Proof.
    (* e = e + e' = e' *)
    intros. rewrite <- H. rewrite identityLeft; auto.
  Qed.

  Theorem group_inv_uniq_l : forall x1 x2 y,
      x1 + y = 0 /\ y + x2 = 0 -> x1 = x2.
  Proof.
    intros. destruct H as [Ha Hb].
    (* x1 = x1+e = x1+(y+x2) = (x1+y)+x2 = e+x2 = x2 *)
    assert (x1 = x1 + 0) by group.
    rewrite H. rewrite <- Hb. rewrite <- associative.
    rewrite Ha. group.
  Qed.

  Theorem group_inv_uniq_r :
    (forall x y1 y2, x + y1 = 0 /\ y2 + x = 0 -> y1 = y2).
  Proof.
    intros. destruct H as [Ha Hb].
    (* y1 = e+y1 = (y2+x)+y1 = y2+(x+y1) = y2+e = y2 *)
    assert (y1 = 0 + y1). group.
    rewrite H. rewrite <- Hb. rewrite associative.
    rewrite Ha. group.
  Qed.

  (* 2023.12 新的表述，也许更适合 *)
  Theorem group_inv_uniq_l' : forall x, (forall x', x' + x = 0 -> x' = -x).
  Proof.
    (* x' = x' + 0 = x' + x + -x = 0 + -x = -x *)
    intros.
    replace x' with (x' + 0); try apply G.
    replace 0 with (x + -x); try apply G.
    rewrite <- associative. rewrite H. apply G.
  Qed.

  Theorem group_inv_uniq_r' : forall x, (forall x', x + x' = 0 -> x' = -x).
  Proof.
    (* x' = 0 + x' = -x + x + x' = -x + 0 = -x *)
    intros.
    replace x' with (0 + x'); try apply G.
    replace 0 with (-x + x); try apply G.
    rewrite associative. rewrite H. apply G.
  Qed.

  (** Theorem 14.1 *)
  Theorem group_cancel_l : forall x y1 y2, x + y1 = x + y2 -> y1 = y2.
  Proof.
    intros.
    (* y1 = e+y1 = (-x+x)+y1 = (-x)+(x+y1) = (-x)+(x+y1) 
      = (-x+x)+y1 = e+y1 = y1*)
    rewrite <- identityLeft at 1.
    assert (0 = (-x) + x). group.
    rewrite H0. rewrite associative. rewrite H.
    rewrite <- associative. group.
  Qed.

  Theorem group_cancel_r : forall x1 x2 y, x1 + y = x2 + y -> x1 = x2.
  Proof.
    intros.
    (* x1 = x1+e = x1+(y+ -y) = (x1+y)+(-y) = (x2+y)+(-y)
      = x2+(y+ -y) = x2+e = x2 *)
    rewrite <- identityRight at 1.
    assert (0 = y + (-y)). group.
    rewrite H0. rewrite <- associative. rewrite H.
    rewrite associative. group.
  Qed.

  Theorem group_inv_inv : forall x,  - - x = x.
  Proof.
    intros. apply group_cancel_l with (- x). group.
  Qed.

  Theorem group_inv_distr : forall x y, - (x + y) = (- y) + (- x).
  Proof.
    intros.
    (* (x+y)+ -(x+y) = e = x+ -x = x+e+ -x = x+(y+ -y)+ -x
      = (x+y)+(-y+ -x), by cancel_l, got it *)
    apply group_cancel_l with (x + y).
    rewrite inverseRight. rewrite <- associative. rewrite (associative x y).
    group.
  Qed.
    
  (** Theorem 14.2 *)
  (* a + x = b -> x = (-a) + b *)
  Theorem group_equation_sol_l : forall a b x, a + x = b -> x = (- a) + b.
  Proof.
    intros.
    (* left mult a *)
    apply group_cancel_l with (a).
    rewrite <- associative. group.
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
    apply group_cancel_r with (a). group.
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
  
  Theorem group_inv_id : - 0 = 0.
  Proof.
    intros.
    (* -e = -e + e = e *)
    rewrite <- identityRight at 1.  group.
  Qed.

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

Class AGroup {A} Aadd (Azero:A) Aopp := {
    agroupGroup :> Group Aadd Azero Aopp;
    agroupAM :> AMonoid Aadd Azero;
    agroupComm :> Commutative Aadd;
  }.

Section Theory.
  
  Context `{AG : AGroup}.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation "a - b" := (a + (-b)).

  Lemma agroup_sub_comm : forall a b, a - b = - (b - a).
  Proof.
    intros.
    rewrite (group_inv_distr). rewrite (group_inv_inv). easy.
  Qed.
  
  Lemma agroup_sub_perm : forall a b c, (a - b) - c = (a - c) - b.
  Proof.
    intros.
    rewrite ?associative. rewrite (commutative (-b)). easy.
  Qed.
  
  Lemma agroup_sub_distr : forall a b, - (a + b) = -a + (-b).
  Proof.
    intros. rewrite (group_inv_distr). apply commutative.
  Qed.
  
  Lemma agroup_sub_assoc : forall a b c, (a - b) - c = a - (b + c).
  Proof.
    intros. rewrite ?associative. rewrite agroup_sub_distr. easy.
  Qed.
  
End Theory.

(* ======================================================================= *)
(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  #[export] Instance AGroup_QcAdd : AGroup Qcplus 0 Qcopp.
  split_intro; subst; ring. Defined.

  #[export] Instance AGroup_RAdd : AGroup Rplus 0%R Ropp.
  split_intro; subst; ring. Defined.

  Goal forall a b c : R, ((a - b) - c = a - (b + c))%R.
    intros.
    apply agroup_sub_assoc. Qed.

End Instances.


(* ######################################################################### *)
(** * SemiRing *)
(* 区分半环与环：半环加法不需要逆元。比如<nat,+,*>是半环，但不是环 *)

(** ** Class *)

Class SemiRing {A} Aadd (Azero:A) Amul Aone := {
    sringAddAM :> AMonoid Aadd Azero; (* 不确定交换性是否必要，姑且先留下 *)
    sringMulAM :> AMonoid Amul Aone; (* 不确定交换性是否必要，姑且先留下 *)
    sringDistrL :> DistributiveLeft Aadd Amul;
    sringDistrR :> DistributiveRight Aadd Amul;
  }.

(** ** Instances *)
Section Instances.

  Import Nat ZArith Qcanon Reals.

  #[export] Instance SRing_nat : SemiRing Nat.add 0%nat Nat.mul 1%nat.
  repeat constructor; intros; ring. Qed.
  
  #[export] Instance SRing_Z : SemiRing Z.add 0%Z Z.mul 1%Z.
  repeat constructor; intros; ring. Qed.
  
  #[export] Instance SRing_Qc : SemiRing Qcplus 0 Qcmult 1.
  repeat constructor; intros; ring. Qed.

  #[export] Instance SRing_R : SemiRing Rplus R0 Rmult R1.
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
    ringAddAG :> AGroup Aadd Azero Aopp;
    ringMulM :> Monoid Amul Aone;
    ringDistrL :> DistributiveLeft Aadd Amul;
    ringDistrR :> DistributiveRight Aadd Amul;
  }.

(** ** Instances *)
Section Instances.

  Import ZArith Qcanon Reals.

  #[export] Instance Ring_Z : Ring Z.add 0%Z Z.opp Z.mul 1%Z.
  repeat constructor; intros; ring. Qed.
  
  #[export] Instance Ring_Qc : Ring Qcplus 0 Qcopp Qcmult 1.
  repeat constructor; intros; ring. Qed.

  #[export] Instance Ring_R : Ring Rplus R0 Ropp Rmult R1.
  repeat constructor; intros; ring. Qed.

End Instances.

(** ** Extra Theories *)
Section Theory.

  Context `{R:Ring}.

  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation Asub := (fun a b => a + -b).
  Infix "*" := Amul.

End Theory.

(** ** Examples *)

Section Examples.

  Import Reals.
  
  Goal forall a b c : R, (a * (b + c) = a * b + a * c)%R.
    apply distributiveLeft. Qed.

End Examples.
  

(* ######################################################################### *)
(** * ARing *)

(** ** Class *)

Class ARing {A} Aadd Azero Aopp Amul Aone := {
    aringRing :> @Ring A Aadd Azero Aopp Amul Aone;
    aringMulComm :> Commutative Amul;
    aringASGroup :> ASGroup Amul
  }.

(** ** Instances *)
Section Instances.

  Import ZArith Qcanon Reals.

  #[export] Instance ARing_Z : ARing Z.add 0%Z Z.opp Z.mul 1%Z.
  repeat constructor; intros; ring. Qed.
  
  #[export] Instance ARing_Qc : ARing Qcplus 0 Qcopp Qcmult 1.
  repeat constructor; intros; ring. Qed.

  #[export] Instance ARing_R : ARing Rplus R0 Ropp Rmult R1.
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
  Notation "- a" := (Aopp a).
  Notation Asub := (fun a b => a + -b).
  Infix "*" := Amul.
    
  (** 0 * a = 0 *)
  (* 证明思路：a*0 + 0 = a*0 = a*(0+0) = a*0 + a*0，然后消去律 *)
  Lemma ring_mul_0_r : forall a : A, a * Azero = Azero.
  Proof. intros. ring. Qed.

  (** a * 0 = 0 *)
  Lemma ring_mul_0_l : forall a : A, Azero * a = Azero.
  Proof. intros. ring. Qed.

  (* a * a = 1, then a = 1 or a = -1 *)
  (* Tips: I can't prove it now..., and this is used in `OrthogonalMatrix` *)
  Lemma ring_sqr_eq1_imply_1_neg1 : forall (a : A),
      a * a = Aone -> a = Aone \/ a = (- Aone).
  Proof.
  Admitted.

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
(** * Field *)

(** ** Class *)
Class Field {A} Aadd (Azero:A) Aopp Amul Aone Ainv := {
    (** Field: ARing + mult inversion + (1≠0) *)
    fieldRing :> ARing Aadd Azero Aopp Amul Aone;
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
      (fun x y => Aadd x (Aopp y)) Aopp
      (fun x y => Amul x (Ainv y)) Ainv eq.
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
  Notation Asub := (fun a b => a + -b).
  Notation "0" := Azero.
  Notation "1" := Aone.
  Infix "*" := Amul.
  Notation "/ a" := (Ainv a).
  Notation Adiv := (fun a b => a * (/b)).
  Infix "/" := Adiv.

  Add Field field_inst : (make_field_theory F).

  (** a <> 0 -> /a * a = 1 *)
  Lemma field_mul_inv_l : forall a : A, a <> 0 -> /a * a = 1.
  Proof. intros. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> a * /a = 1 *)
  Lemma field_mul_inv_r : forall a : A, a <> 0 -> a * /a = 1.
  Proof. intros. rewrite commutative. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> (1/a) * a = 1 *)
  Lemma field_mul_inv1_l : forall a : A, a <> 0 -> (1/a) * a = 1.
  Proof. intros. simpl. group. apply field_mul_inv_l. auto. Qed.
  
  (** a <> 0 -> a * (1/a) = 1 *)
  Lemma field_mul_inv1_r : forall a : A, a <> 0 -> a * (1/a) = 1.
  Proof. intros. simpl. group. apply field_mul_inv_r. auto. Qed.
  
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
    rewrite field_mul_inv_r in H1; auto.
    rewrite ?identityRight in H1. easy.
  Qed.

  (** a * b = 0 -> a = 0 \/ b = 0 *)
  Lemma field_mul_eq0_imply_a0_or_b0 : forall (a b : A) (AeqDec:Dec (@eq A)),
      a * b = 0 -> a = 0 \/ b = 0.
  Proof.
    intros.
    destruct (dec eq a 0), (dec eq b 0);
      try (left; easy); try (right; easy).
    assert (/a * a * b = 0).
    { rewrite associative. rewrite H. field. auto. }
    rewrite field_mulInvL in H0; auto.
    rewrite identityLeft in H0. easy.
  Qed.

  (* a * a = 0 -> a = 0 *)
  Lemma field_sqr_eq0_imply_eq0 : forall (a : A) (AeqDec:Dec (@eq A)),
      a * a = Azero -> a = Azero.
  Proof. intros. apply field_mul_eq0_imply_a0_or_b0 in H; auto. destruct H; auto. Qed.

  (** a * b = b -> a = 1 \/ b = 0 *)
  Lemma field_mul_eq_imply_a1_or_b0 : forall (a b : A) (AeqDec:Dec (@eq A)),
      a * b = b -> (a = 1) \/ (b = 0).
  Proof.
    intros. destruct (dec eq a 1), (dec eq b 0); auto.
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
(** * Linear Space *)

(** ** Class *)
Class LinearSpace `{F : Field} {V : Type}
  (Vadd : V -> V -> V) (Vzero : V) (Vopp : V -> V) (Vcmul : A -> V -> V) := {
    ls_addC :> Commutative Vadd;
    ls_addA :> Associative Vadd;
    ls_add_0_r :> IdentityRight Vadd Vzero;
    ls_add_inv_r :> InverseRight Vadd Vzero Vopp;
    ls_cmul_1_l : forall u : V, Vcmul Aone u = u;
    ls_cmul_assoc : forall a b u, Vcmul (Amul a b) u = Vcmul a (Vcmul b u);
    ls_cmul_aadd_distr : forall a b u,
      Vcmul (Aadd a b) u = Vadd (Vcmul a u) (Vcmul b u);
    ls_cmul_vadd_distr : forall a u v,
      Vcmul a (Vadd u v) = Vadd (Vcmul a u) (Vcmul a v);
  }.

(** ** Instances *)
Section Instances.

  (** A field itself is a liner space *)
  Section field_is_linearspace.
    Context `{F : Field}.
    Add Field field_inst : (make_field_theory F).
    
    #[export] Instance LinearSpace_Field : LinearSpace Aadd Azero Aopp Amul.
    split_intro; try field. Qed.
    
  End field_is_linearspace.

End Instances.


(** ** Extra Theories *)

Section Theory.
  (* Open Scope A_scope. *)
  
  Context `{LS : LinearSpace}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/b)).
  Infix "/" := Adiv : A_scope.

  Infix "+" := Vadd : LinearSpace_scope.
  Notation "- a" := (Vopp a) : LinearSpace_scope.
  Notation Vsub := (fun a b => a + -b).
  Infix "-" := Vsub : LinearSpace_scope.
  Infix "c*" := Vcmul : LinearSpace_scope.


  (* 0 + v = v  *)
  #[export] Instance ls_add_0_l : IdentityLeft Vadd Vzero.
  Proof.
    (* 0 + v = v + 0 = v *)
    constructor; intros. rewrite commutative, identityRight; auto.
  Qed.
  
  (* -v + v = 0  *)
  #[export] Instance ls_add_inv_l : InverseLeft Vadd Vzero Vopp.
  Proof.
    (* -v + v = v + -v = 0 *)
    constructor; intros. rewrite commutative, inverseRight; auto.
  Qed.
  
  (** Vzero is unique *)
  Theorem ls_vzero_uniq_l : forall v0, (forall v, (v0 + v)%LS = v) -> v0 = Vzero.
  Proof. intros. rewrite <- H. rewrite identityRight; auto. Qed.
  
  Theorem ls_vzero_uniq_r : forall v0, (forall v, (v + v0)%LS = v) -> v0 = Vzero.
  Proof. intros. rewrite <- H. rewrite identityLeft; auto. Qed.

  (** (-v) is unique *)
  Theorem ls_vopp_uniq_l : forall v, (forall v', (v' + v)%LS = Vzero -> v' = Vopp v).
  Proof.
    (* v' = v' + 0 = v' + v + -v = 0 + -v = -v *)
    intros. rewrite <- identityRight at 1. rewrite <- (inverseRight v) at 1.
    rewrite <- associative. rewrite H. apply identityLeft.
  Qed.

  Theorem ls_vopp_uniq_r : forall v, (forall v', v + v' = Vzero -> v' = -v)%LS.
  Proof.
    (* v' = 0 + v' = -v + v + v' = -v + 0 = -v *)
    intros. rewrite <- identityLeft at 1. rewrite <- (inverseLeft v) at 1.
    rewrite associative. rewrite H. apply identityRight.
  Qed.

  (* (-1) v = -v *)
  Theorem LS_cmul_opp1 : forall v : V, (-Aone)%A c* v = (-v)%LS.
  Proof.
    (* -v is unique *)
    intros.
    rewrite <- (ls_vopp_uniq_r (v':=(- Aone)%A c* v)); auto.
    rewrite <- (ls_cmul_1_l v) at 1. rewrite <- ls_cmul_aadd_distr.
    rewrite inverseRight.
    (* 用到下面的定理 *)
  Admitted.
  
  (** 0 * v = 0 *)
  Theorem LS_cmul_0_l : forall v : V, Azero c* v = Vzero.
  Proof.
    (* 0 * v = (1 - 1) * v = v + (-v) = 0 *)
    intros. replace Azero with (Aone + (-Aone))%A.
    rewrite ls_cmul_aadd_distr. rewrite (ls_cmul_1_l v). rewrite LS_cmul_opp1.
    destruct LS. apply inverseRight. 
    apply inverseRight.
  Qed.

  (* a 0 = 0 *)
  Theorem LS_cmul_0_r : forall a : A, a c* Vzero = Vzero.
  Proof.
  Abort.

  (* a<>0 -> v<>0 -> a v <> 0 *)
  Theorem LS_cmul_neq0 : forall (a : A) (v : V), a <> Azero -> v <> Vzero -> a c* v <> Vzero.
  Proof.
  Abort.
  
End Theory.

(** ** Examples *)
Section Examples.

End Examples.

