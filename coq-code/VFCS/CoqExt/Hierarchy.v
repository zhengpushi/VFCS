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

Require Export Basic.   (* reserved notation, etc. *)
Require Export Coq.Classes.RelationClasses. (* binary_relation *)
Require Import Coq.Logic.Description. (* constructive_definite_description *)
Require Export List SetoidList. Import ListNotations.
Require Export Lia Lra.
Require Export Ring Field.

Require Import Arith ZArith QArith QcExt RExt.

Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables T Teq Tadd Topp Tmul Tinv Tdiv.


(* ######################################################################### *)
(** * Small utilities *)

(** repeat split and intro *)
Ltac split_intro :=
  repeat (try split; try intro).

(** Applicate a unary function for n-times, i.e. f ( .. (f a0) ...) *)
Fixpoint iterate {T} (f : T -> T) (n : nat) (a0 : T) : T :=
  match n with
  | O => a0
  | S n' => f (iterate f n' a0)
  end.

Section test.
  Context {T} {f : T -> T} (T0 : T).
  (* Compute iterate f 3 T0. *)
End test.

(* (** x is an unique element which holds by P. Setoid version *) *)
(* Definition unique_setoid {T : Type} {Teq: relation T} (P: T -> Prop) (x: T) := *)
(*   P x /\ (forall x' : T, P x' -> Teq x x'). *)

(* (** constructive_definite_description, setoid version *) *)
(* Axiom constructive_definite_description_setoid : *)
(*   forall (T : Type) (Teq:relation T) (P : T -> Prop), *)
(*     (exists x : T, (P x /\ unique_setoid (Teq:=Teq) P x)) -> {x : T | P x}. *)

(* (** functional_extensionality, setoid version *) *)
(* Axiom functional_extensionality_setoid : *)
(*   forall {T U} {Ueq: relation U} (feq: relation (T->U)) (f g : T -> U), *)
(*     (forall a : T, Ueq (f a) (g a)) -> feq f g. *)


(* ######################################################################### *)
(** * A relation is equivalence relation *)

(** ** Class *)

(* Global Hint Constructors Equivalence : core. *)

(** ** Instances *)

(** eqlistA is a equivalence relation *)
Global Instance Equivalence_eqlistA `{Equiv_Teq:Equivalence T Teq}
  : Equivalence (eqlistA Teq).
Proof. apply eqlistA_equiv. auto. Defined.

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Respect: an operation respect a relation (also known as "well-defined") *)

(** deprecated, replaced with "Proper" in Coq *)
(** Note that, the naming could be any of them:
    1. "add_wd", means "add" is well defined.
    2. "add_aeq_mor", means "add" is a proper morphism about "aeq".
    3. "Qplus_comp", means "Qplus" is compatible to "Qeq".
*)

(** ** Class *)

(* (** A unary operation is respect to the equality relation *) *)
(* Class RespectUnary {T U:Type} (op:T->U) (Teq:T -> T->Prop) (Ueq:U->U->Prop) := { *)
(*     respectUnary : forall x y : T, *)
(*       Teq x y -> Ueq (op x) (op y) *)
(*   }. *)

(* (** A binary operation is respect to the equality relation *) *)
(* Class RespectBinary {T U V:Type} (op:T->U->V) *)
(*   (Teq:T -> T->Prop) (Ueq:U->U->Prop) (Veq:V->V->Prop):= { *)
(*     respectBinary : forall x y : T, *)
(*       Teq x y -> forall x0 y0 : U, Ueq x0 y0 -> Veq (op x x0) (op y y0) *)
(*   }. *)

(** ** Instances *)

(** Prove the "Proper" property, method 1 *)
#[global] Instance NatAdd_wd : Proper (eq ==> eq ==> eq) Nat.add.
Proof. simp_proper. intros; subst; auto. Qed.

(** Prove the "Proper" property, method 2, come from Coq.Arith.PeanoNat *)
Local Obligation Tactic := simpl_relation.
#[global] Program Instance add_wd : Proper (eq==>eq==>eq) plus.

(** The "Respect" properties on common operations have been provided by StdLib,
    so we can use them.
    1. add needed properties to Hint database "wd" to automate the proof.
    2. register them to Coq, to enable rewrite. (maybe needn't to do it). *)

Hint Resolve
  Nat.add_wd Nat.mul_wd  (* nat *)
  Z.add_wd Z.opp_wd Z.sub_wd Z.mul_wd (* Z *)
  Qplus_comp Qopp_comp Qminus_comp Qmult_comp Qinv_comp Qdiv_comp (* Q *)
  Qcplus_wd Qcopp_wd Qcminus_wd Qcmult_wd Qcinv_wd Qcdiv_wd (* Qc *)
  Rplus_wd Ropp_wd Rminus_wd Rmult_wd Rinv_wd Rdiv_wd (* R *)
  : wd.

(* Search Proper. ? *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Associative *)

(** ** Class *)
Class Associative {T : Type} (Top : T -> T -> T) (Teq : relation T) := {
    associative : forall a b c, Teq (Top (Top a b) c) (Top a (Top b c));
  }.

(** ** Instances *)
Global Instance Assoc_NatAdd : Associative Nat.add eq.
Proof. constructor. auto with arith. Qed.

(** ** Extra Theories *)
(* Lemma associative_inv : forall `{Assoc : Associative} a b c, *)
(*     Top a (Top b c) = Top (Top a b) c. *)
(* Proof. intros. rewrite -> associative. auto. Qed. *)

(** ** Examples *)
Goal forall a b c : nat, a + (b + c) = (a + b) + c.
  intros. rewrite associative. auto. Qed.

Goal forall a b c : nat, (a + b) + c = a + (b + c).
  apply associative. Qed.


(* ######################################################################### *)
(** * Commutative *)

(** ** Class *)
Class Commutative {T : Type} (Top : T -> T -> T) (Teq : relation T) := {
    commutative : forall a b, Teq (Top a b) (Top b a)
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
Class IdentityLeft {T : Type} (Top : T -> T -> T) (Te : T) (Teq : relation T) := {
    identityLeft : forall a, Teq (Top Te a) a
  }.

Class IdentityRight {T : Type} (Top : T -> T -> T) (Te : T) (Teq : relation T) := {
    identityRight : forall a, Teq (Top a Te) a
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Inverse Left/Right *)

(** ** Class *)
Class InverseLeft {T : Type} (Top : T -> T -> T) (Te : T) (Topinv : T -> T)
  (Teq : relation T) := {
    inverseLeft : forall a, Teq (Top (Topinv a) a) Te
  }.

Class InverseRight {T : Type} (Top : T -> T -> T) (Te : T) (Topinv : T -> T)
  (Teq : relation T) := {
    inverseRight : forall a, Teq (Top a (Topinv a)) Te
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Distributive *)

(** ** Class *)

(* Class DistributiveUnary {T : Type} (Tadd:T -> T -> T) (Topp : T -> T) := { *)
(*     distributiveUnary : forall a b, *)
(*       Topp (Tadd a b) = Tadd (Topp a) (Topp b) *)
(*   }. *)

Class DistributiveLeft {T : Type} (Tadd Tmul : T -> T -> T) (Teq : relation T) := {
    distributiveLeft : forall a b c,
      Teq (Tmul a (Tadd b c)) (Tadd (Tmul a b) (Tmul a c))
  }.

Class DistributiveRight {T : Type} (Tadd Tmul : T -> T -> T) (Teq : relation T) := {
    distributiveRight : forall a b c,
      Teq (Tmul (Tadd a b) c) (Tadd (Tmul a c) (Tmul b c))
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Involution Law *)

(** ** Class *)

(* Class Involution {T : Type} (Topp : T -> T) (Teq : relation T) := { *)
(*     involution : forall a, Teq (Topp (Topp a)) a *)
(*   }. *)

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Injective *)

(** ** Class *)

Class Injective {T U : Type} {Teq: relation T} {Ueq: relation U} (phi: T -> U) := {
    injective : forall a1 a2 : T, ~(Teq a1 a2) -> ~(Ueq (phi a1) (phi a2))
  }.
  
(** ** Instances *)

(** ** Extra Theories *)
Section theory.

  Context {T U : Type} {Teq: relation T} {Ueq: relation U}.

  Notation Injective := (Injective (Teq:=Teq) (Ueq:=Ueq)).
  
  (** Second form of injective *)
  Definition injective_form2 (phi: T -> U) :=
    forall (a1 a2 : T), Ueq (phi a1) (phi a2) -> Teq a1 a2.

  (** These two forms are equal *)
  Lemma injective_eq_injective_form2 (phi: T -> U) :
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
  Lemma inj_pres_eq : forall (f : T -> U),
      Injective f -> (forall a1 a2 : T, Ueq (f a1) (f a2) -> Teq a1 a2).
  Proof.
    intros. apply injective_eq_injective_form2 in H. apply H. auto.
  Qed.

End theory.

(** ** Examples *)


(* ######################################################################### *)
(** * Surjective *)

(** ** Class *)

Class Surjective {T U : Type} {Ueq: relation U} (phi: T -> U) := {
    surjective : forall (b : U), (exists (a : T), Ueq (phi a) b)
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Bijective *)

(** ** Class *)

Class Bijective {T U : Type} {Teq: relation T} {Ueq: relation U} (phi: T -> U) := {
    bijInjective :> Injective (Teq:=Teq) (Ueq:=Ueq) phi;
    bijSurjective :> Surjective (Ueq:=Ueq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)
Section theory.
  Context {T U: Type} {Teq:relation T} {Ueq:relation U}.
  Context {Equiv_Teq:Equivalence Teq} {Equiv_Ueq:Equivalence Ueq}.
  Notation Bijective := (Bijective (Teq:=Teq) (Ueq:=Ueq)).
  Infix "=T=" := Teq (at level 70).
  Infix "=U=" := Ueq (at level 70).
  
  (** There exist inverse function from a bijective function.

      ref: https://stackoverflow.com/questions/62464821/
      how-to-make-an-inverse-function-in-coq

      Tips: there are two methods to formalize "existential", sig and ex.
      ex makes a Prop, sig makes a Type. 
      Here, we proof the ex version. the sig version could be derived by an axiom:
      [constructive_definite_description : 
      forall (T : Type) (P : T -> Prop), (exists ! x : T, P x) -> {x : T | P x} ]
   *)

  (** x is an unique element which holds by P. Setoid version *)
  Local Definition unique_setoid {T: Type} {Teq: relation T} (P: T -> Prop) (x: T) :=
    P x /\ (forall x' : T, P x' -> Teq x x').

  (** constructive_definite_description, setoid version *)
  Local Axiom constructive_definite_description_setoid :
    forall (T : Type) (Teq:relation T) (P : T -> Prop),
      (exists x : T, (P x /\ unique_setoid (Teq:=Teq) P x)) -> {x : T | P x}.

  (** functional_extensionality, setoid version *)
  Local Axiom functional_extensionality_setoid :
    forall {T U} {Ueq: relation U} (feq: relation (T->U)) (f g : T -> U),
      (forall a : T, Ueq (f a) (g a)) -> feq f g.

  Lemma bij_inverse_exist : forall (phi : T -> U) (Hbij: Bijective phi),
    {psi : U -> T | (forall a : T, (psi (phi a)) =T= a) /\  (forall b : U, phi (psi b) =U= b)}.
  Proof.
    intros. destruct Hbij as [Hinj [Hsurj]].
    apply injective_eq_injective_form2 in Hinj. hnf in *.
    (* Tips, unique is eq version, we need setoid version *)
    (* assert (H : forall b, exists! a, phi a =U= b). *)
    assert (H: forall b, exists a, phi a =U= b /\ unique_setoid (Teq:=Teq) (fun x => phi x =U= b) a).
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
        assert (phi (psi b) =U= b); auto using H2.
        rewrite <- H0 in u. apply Hinj in u. exact u.
        Unshelve. exact eq.
  Defined.

  (** A bijective function preserve equal relation *)
  (* Lemma bij_pres_eq_forward : forall (f : T -> U), *)
  (*     Bijective f -> (forall (a1 a2 : T), Teq a1 a2 -> Ueq (f a1) (f a2)). *)
  (* Proof. *)
  (*   intros. destruct H as [H1 H2]. *)
  (*   (* I can't prove now. *) *)
  (*   Abort. *)

End theory.

(** ** Examples *)


(* ######################################################################### *)
(** * Homomorphic  *)

(** ** Class *)

Class Homomorphic {T U : Type} {Ueq: relation U}
  (fa : T -> T -> T) (fb : U -> U -> U) (phi: T -> U) := {
    homomorphic : forall (a1 a2 : T), Ueq (phi (fa a1 a2)) (fb (phi a1) (phi a2))
  }.

(** ** Instances *)

(** ** Extra Theories *)

(* Definition homo_inj {T U} (ϕ : T -> U) : Prop := *)
(*   homomorphic ϕ /\ injective ϕ. *)

(* (** ϕ is a homomorphic and surjective mapping *) *)
(* Definition homo_surj (ϕ : T -> U) : Prop := *)
(*   homomorphic ϕ /\ surjective ϕ. *)

(** ** Examples *)


(* ######################################################################### *)
(** * Homomorphism *)

(** ** Class *)

(** If there exist a homomorphic and surjective mapping from <T,+> to <U,⊕>,
    then we said <T,+> and <U,⊕> is homomorphism *)
Class Homomorphism {T U : Type} {Teq: relation T} {Ueq: relation U}
  (fa : T -> T -> T) (fb : U -> U -> U) := {
    homomorphism : exists (phi: T -> U),
      Homomorphic fa fb phi (Ueq:=Ueq)
      /\ Surjective phi (Ueq:=Ueq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Teq ==> Ueq) phi
  }.

(** If there exist two homomorphic and surjective mapping from <T,+> to <U,⊕>
    and from <T,*> to <U,⊗>, then we said <T,+,*> and <U,⊕,⊗> is homomorphism *)
Class Homomorphism2 {T U : Type} {Teq: relation T} {Ueq: relation U}
  (fa ga : T -> T -> T) (fb gb : U -> U -> U) := {
    homomorphism2 : exists (phi: T -> U),
      Homomorphic fa fb phi (Ueq:=Ueq)
      /\ Homomorphic ga gb phi (Ueq:=Ueq)
      /\ Surjective phi (Ueq:=Ueq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Teq ==> Ueq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Isomorphism *)

(** ** Class *)

(** If there exist a homomorphic and bijective mapping from <T,+> to <U,⊕>,
    then we said <T,+> and <U,⊕> is isomorphism *)
Class Isomorphism {T U : Type} {Teq: relation T} {Ueq: relation U}
  (fa : T -> T -> T) (fb : U -> U -> U) := {
    isomorphism : exists (phi: T -> U),
      Homomorphic fa fb phi (Ueq:=Ueq)
      /\ Bijective phi (Teq:=Teq) (Ueq:=Ueq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Teq ==> Ueq) phi
  }.

(** If there exist two homomorphic and bijective mapping from <T,+> to <U,⊕>
    and from <T,*> to <U,⊗>, then we said <T,+,*> and <U,⊕,⊗> is isomorphism *)
Class Isomorphism2 {T U : Type} {Teq: relation T} {Ueq: relation U}
  (fa ga : T -> T -> T) (fb gb : U -> U -> U) := {
    isomorphism2 : exists (phi: T -> U),
      Homomorphic fa fb phi (Ueq:=Ueq)
      /\ Homomorphic ga gb phi (Ueq:=Ueq)
      /\ Bijective phi (Teq:=Teq) (Ueq:=Ueq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Teq ==> Ueq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Semigroup 半群 *)

(** ** Class *)
Class SGroup {T:Type} (Tadd : T -> T -> T) (Teq:T->T->Prop) := {
    sgroupTaddProper :> Proper (Teq ==> Teq ==> Teq) Tadd;
    sgroupEquiv :> Equivalence Teq;
    sgroupAssoc :> Associative Tadd Teq;
  }.

(** Get parameter of this structure *)
Definition sgroupTadd `{SG:SGroup} : T -> T -> T := Tadd.

(** ** Instances *)
Section Instances.
  
  Global Instance SGroup_NatAdd : SGroup Nat.add eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance SGroup_NatMul : SGroup Nat.mul eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.
  
End Instances.

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Abelian semigroup 交换半群 *)

(** ** Class *)
Class ASGroup {T:Type} (Tadd : T -> T -> T) (Teq:T->T->Prop) := {
    asgroup_sgroup :> SGroup Tadd Teq;
    asgroupComm :> Commutative Tadd Teq
  }.

(** Get parameter of this structure *)
Definition asgroupTadd `{ASG : ASGroup} : T -> T -> T := Tadd.

(** ** Instances *)
Section Instances.
  
  Global Instance ASGroup_NatAdd : ASGroup Nat.add eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance ASGroup_NatMul : SGroup Nat.mul eq.
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
Ltac elim_auto :=
  elimh; elimt; (* 消去左式的头部和尾部 *)
  symmetry;
  elimh; elimt. (* 消去右式的头部和尾部 *)

Section test.
  Context `{ASG : ASGroup}. Infix "+" := Tadd. Infix "==" := Teq.
  Variable a0 a1 a2 a3 a4 a5 a6 : T.

  (** 第一种情形，等式两侧完全相同 *)
  Let eq1 : Prop := a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.

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
  Let eq2 : Prop := a0 + (a1 + a2 + a3) + a4 + a5 == a2 + a0 + a6 + a4.

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
  Goal eq2. unfold eq2. elim_auto. Abort.

  (** 还有一种可能，某个相同的项出现中中间，既不在头部，也不在尾部 *)
  Let eq3 : Prop := a1 + a0 + a2 == a3 + a0 + a4.

  (* 可以发现，上面的方法不能处理这种情况 *)
  Goal eq3. unfold eq3. elim_auto. Abort.

  (* 也许能够设计一种方法来遍历左侧或右侧的所有的项，但暂时可以手工来做。
     比如，可以手工调用 move2h 或 move2t 来移动一个项，然后调用 elimh 或
     elimt 或 elim_auto 来消除它 *)
  Goal eq3. unfold eq3. move2h a0. elim_auto. Abort.
  Goal eq3. unfold eq3. move2t a0. elim_auto. Abort.
  
End test.

(** ** Examples *)


(* ######################################################################### *)
(** * Monoid 幺半群、独异点 *)

(** ** Class *)
Class Monoid {T:Type} (Tadd : T -> T -> T) (T0 : T) (Teq:T->T->Prop) := {
    monoidTaddProper :> Proper (Teq ==> Teq ==> Teq) Tadd;
    monoidEquiv :> Equivalence Teq;
    monoidAssoc :> Associative Tadd Teq;
    monoidIdL :> IdentityLeft Tadd T0 Teq;
    monoidIdR :> IdentityRight Tadd T0 Teq;
  }.

(** Get parameter of a monoid *)
Definition monoidTadd `{M:Monoid} : T -> T -> T := Tadd.
Definition monoidT0 `{M:Monoid} : T := T0.

(** ** Instances *)
Section Instances.
  Global Instance Monoid_NatAdd : Monoid Nat.add 0%nat eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_NatMul : Monoid Nat.mul 1%nat eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_ZAdd : Monoid Z.add 0%Z eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_ZMul : Monoid Z.mul 1%Z eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_QAdd : Monoid Qplus 0%Q Qeq.
  repeat constructor; auto with wd; try apply Q_Setoid; intros; ring. Qed.

  Global Instance Monoid_QMul : Monoid Qmult 1%Q Qeq.
  repeat constructor; auto with wd; try apply Q_Setoid; intros; ring. Qed.

  Global Instance Monoid_QcAdd : Monoid Qcplus 0%Qc eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_QcMul : Monoid Qcmult 1%Qc eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_RAdd : Monoid Rplus 0%R eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_RMul : Monoid Rmult 1%R eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.
  
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
  Open Scope R.
  Goal forall a b c : R, a + (0 + b + 0) = a + b.
    intros.
    monoid_rw.
    monoid_rw_strict Monoid_RAdd. auto.
  Qed.
End tac_example.
  

(** ** Examples *)

Section Examples.
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
Class AMonoid {T} Tadd T0 Teq := {
    amonoidMonoid :> @Monoid T Tadd T0 Teq;
    amonoidComm :> Commutative Tadd Teq;
  }.

(** ** Instances *)
Section Instances.
  Global Instance AMonoid_QcAdd : AMonoid Qcplus 0%Qc eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance AMonoid_QcMul : AMonoid Qcmult 1%Qc eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance AMonoid_RAdd : AMonoid Rplus 0%R eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance AMonoid_RMul : AMonoid Rmult 1%R eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

End Instances.

  
(** ** Extra Theories *)

Ltac amonoid_simp :=
  monoid_simp;
  apply commutative.

Section Theory.

  Context `(AM : AMonoid).
  Infix "+" := Tadd.
  Infix "==" := Teq.

  (* 如何证明这类复杂表达式（表示很复杂时，不方便使用结合律、交换律）*)
  Goal forall a b c d e : T, a + (b + c) + (d + e) == (c + e) + (d + a + b).
  Proof. intros. elim_auto. Qed.
  
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
Class Group {T} Tadd T0 (Topp : T -> T) Teq := {
    groupMonoid :> @Monoid T Tadd T0 Teq;
    groupInvL :> InverseLeft Tadd T0 Topp Teq;
    groupInvR :> InverseRight Tadd T0 Topp Teq;
    groupTaddProper :> Proper (Teq ==> Teq ==> Teq) Tadd;
    groupToppProper :> Proper (Teq ==> Teq) Topp;
    (* groupDistrTinv :> DistributiveUnary Top Tinv Teq; *)
    (* groupInvoTinv :> Involution Tinv Teq; *)
  }.

(** ** Instances *)
Section Instances.

  Global Instance Group_QcAdd : Group Qcplus 0%Qc Qcopp eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Group_RAdd : Group Rplus 0%R Ropp eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

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
  Infix "==" := Teq.
  Infix "+" := Tadd.
  Notation "0" := T0.
  Notation "- a" := (Topp a).
  Notation Tsub := (fun x y => x + (-y)).
  Infix "-" := Tsub.
  
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
  (* batch : list T -> T
    [] = e
    [a1] = a1
    [a1;a2] = a1 * a2
    [a1;a2;a3] = (a1*a2)*a3
    [a1;a2;...;a_n-1;an] = ((...(a1*a2)* ... )*a_n-1)*an *)
  Definition group_batch (l:list T) :=
    match l with
    | [] => 0
    | x :: l' => fold_left Tadd l' x
    end.
  
  Section test.
    Variable (a1 a2 a3 a4 : T).
    
    (* Compute group_batch []. *)
    (* Compute group_batch [a1]. *)
    (* Compute group_batch [a1;a2]. *)
    (* Compute group_batch [a1;a2;a3]. *)
    (* Compute group_batch [a1;a2;a3;a4]. *)

  End test.

  (** Theorem 14.3 (Generalized Associative Law) *)
  Section th14_3.

    Notation "'Σ' a '&' l " := (fold_left Tadd l a) (at level 10).

    (** (a1+...+as) + (b1+...+bt) = a1+...+as + b1+...+bt *)
    Theorem group_assoc_general (l1 l2 : list T) :
      (group_batch l1) + (group_batch l2) == group_batch (l1 ++ l2).
    Proof.
      (* reduct to fold_left *)
      destruct l1,l2; simpl; group_simp.
      - rewrite app_nil_r. group_simp.
      - rename t into t1, t0 into t2.
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
    Definition group_power (a : T) (n : Z) : T :=
      match n with
      | Z0 => 0
      | Zpos m => iterate (fun x => Tadd x a) (Pos.to_nat m) 0
      | Z.neg m => iterate (fun x => Tadd x (Topp a)) (Pos.to_nat m) 0
      end.
    Infix "^" := group_power.
    
    Section test.
      Variable (a1 a2 a3 a4 : T).
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

Class AGroup {T} Tadd T0 Topp Teq := {
    agroupGroup :> @Group T Tadd T0 Topp Teq;
    agroupAM :> @AMonoid T Tadd T0 Teq;
    agroupComm :> Commutative Tadd Teq;
  }.

Global Coercion agroupGroup : AGroup >-> Group.

Ltac agroup_simp :=
  group_simp;
  try apply commutative.

Section Theory.
  
  Context `{AG : AGroup}.
  Infix "==" := Teq.
  Infix "+" := Tadd.
  Notation "- a" := (Topp a).
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

  Global Instance AGroup_ZAdd : AGroup Z.add 0%Z Z.opp eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance AGroup_QAdd : AGroup Qplus 0%Q Qopp Qeq.
  repeat constructor; auto with wd; try apply Q_Setoid; intros; ring. Qed.

  Global Instance AGroup_QcAdd : AGroup Qcplus 0%Qc Qcopp eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance AGroup_RAdd : AGroup Rplus 0%R Ropp eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

End Instances.

Section example.
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
   need it. Because we want use ring tactic, so add this properties.
 *)
Class Ring {T} Tadd T0 Topp Tmul T1 Teq := {
    ringAddAG :> @AGroup T Tadd T0 Topp Teq;
    ringMulAM :> @AMonoid T Tmul T1 Teq;
    ringDistrL :> DistributiveLeft Tadd Tmul Teq;
    ringDistrR :> DistributiveRight Tadd Tmul Teq;
  }.

(** ** Instances *)
Section Instances.
  Global Instance Ring_Z : Ring Z.add 0%Z Z.opp Z.mul 1%Z eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Ring_Q : Ring Qplus 0%Q Qopp Qmult 1%Q Qeq.
  repeat constructor; auto with wd; try apply Q_Setoid; intros; ring. Qed.

  Global Instance Ring_Qc : Ring Qcplus 0%Qc Qcopp Qcmult 1%Qc eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Ring_R : Ring Rplus R0 Ropp Rmult R1 eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

End Instances.

(** ** Extra Theories *)

(** make a coq ring object from our Ring object *)
Lemma make_ring_theory `(R : Ring) :
  ring_theory T0 T1 Tadd Tmul (fun a b => Tadd a (Topp b)) Topp Teq.
Proof.
  constructor; intros;
    try (rewrite ?identityLeft,?associative; reflexivity);
    try (rewrite commutative; reflexivity).
  rewrite distributiveRight; reflexivity.
  rewrite inverseRight; reflexivity.
Qed.

Section Theory.

  Context `(R:Ring).

  Infix "==" := Teq : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "1" := T1 : T_scope.
  Notation "0" := T0 : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Tsub := (fun a b => a + -b).
  Infix "*" := Tmul : T_scope.
  Open Scope T_scope.

  Add Ring ring_inst : (make_ring_theory R).

  (** 0 * a = 0 *)
  Lemma ring_mul_0_l : forall (a : T), 0 * a == 0.
  Proof. intros. ring. Qed.

  (** a * 0 = 0 *)
  Lemma ring_mul_0_r : forall (a : T), a * 0 * a == 0.
  Proof. intros. ring. Qed.

End Theory.

(** ** Examples *)

Section Examples.

  Goal forall a b c : R, (a * (b + c) = a * b + a * c)%R.
    apply distributiveLeft. Qed.

End Examples.

(** This example declares an abstract ring structure, and shows how to use fewer code 
    to enable "ring" tactic. *)
Module Demo_AbsRing.
  Context `{R : Ring}.
  Infix "==" := Teq.
  Infix "+" := Tadd.
  Infix "*" := Tmul.
  Notation "0" := T0.
  Notation "1" := T1.

  Add Ring ring_thy_inst : (make_ring_theory R).

  Goal forall a b c : T, (a + b) * c == 0 + b * c * 1 + 0 + 1 * c * a.
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
Class Field {T} Tadd T0 Topp Tmul T1 Tinv Teq := {
    (** Field: Ring + mult inversion + (1≠0) *)
    fieldRing :> @Ring T Tadd T0 Topp Tmul T1 Teq;
    field_mulInvL : forall a, ~(Teq a T0) -> Teq (Tmul (Tinv a) a) T1;
    field_1_neq_0 : ~(Teq T1 T0);
    (** additional: Tinv is proper morphism *)
    fieldTinvProper :> Proper (Teq ==> Teq) Tinv
  }.

(** ** Instances *)
Section Instances.
  
  Global Instance Field_Qc : Field Qcplus 0%Qc Qcopp Qcmult 1%Qc Qcinv eq.
  split_intro; subst; (try (field; reflexivity)); try easy. field. auto. Qed.

  Global Instance Field_R : Field Rplus R0 Ropp Rmult R1 Rinv eq.
  split_intro; subst; try (field; reflexivity); auto. field; auto.
  auto with real. Qed.

End Instances.

(** ** Extra Theories *)

(** make a coq field object from our Field object *)
Lemma make_field_theory `(F : Field):
  field_theory T0 T1 Tadd Tmul
               (fun a b => Tadd a (Topp b)) Topp
               (fun a b => Tmul a (Tinv b)) Tinv Teq.
Proof.
  constructor; intros;
    try (rewrite ?identityLeft,?associative; reflexivity);
    try (rewrite commutative; reflexivity).
  apply (make_ring_theory fieldRing).
  apply field_1_neq_0.
  apply field_mulInvL. auto.
Qed.

Section Theory.

  Open Scope T_scope.

  Context `{F:Field}.
  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun x y => ~ x == y)%T : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Tsub := (fun a b => a + -b).
  Notation "0" := T0 : T_scope.
  Notation "1" := T1 : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "/ a" := (Tinv a) : T_scope.
  Notation Tdiv := (fun a b => a * (/b))%T.
  Infix "/" := Tdiv : T_scope.

  Add Ring ring_inst : (make_ring_theory fieldRing).
  Add Field field_inst : (make_field_theory F).

  (** a <> 0 -> /a * a = 1 *)
  Lemma field_mul_inv_l : forall a : T, (a != 0) -> /a * a == 1.
  Proof. intros. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> a * /a = 1 *)
  Lemma field_mul_inv_r : forall a : T, (a != 0) -> a * /a == 1.
  Proof. intros. rewrite commutative. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> (1/a) * a = 1 *)
  Lemma field_mul_inv1_l : forall a : T, (a != 0) -> (1/a) * a == 1.
  Proof. intros. simpl. group_simp. apply field_mul_inv_l. auto. Qed.
  
  (** a <> 0 -> a * (1/a) = 1 *)
  Lemma field_mul_inv1_r : forall a : T, (a != 0) -> a * (1/a) == 1.
  Proof. intros. simpl. group_simp. apply field_mul_inv_r. auto. Qed.
  
  (** a <> 0 -> a * b = a * c -> b = c *)
  Lemma field_mul_cancel_l : forall a b c : T, (a != 0) -> a * b == a * c -> b == c.
  Proof.
    intros.
    assert (/a * (a * b) == /a * (a * c)).
    { rewrite H0. easy. }
    rewrite <- ?associative in H1.
    rewrite field_mulInvL in H1; auto.
    rewrite ?identityLeft in H1. easy.
  Qed.

  (** c <> 0 -> a * c = b * c -> a = b *)
  Lemma field_mul_cancel_r : forall a b c : T, (c != 0) -> a * c == b * c -> a == b.
  Proof.
    intros.
    assert ((a * c) * /c == (b * c) * /c).
    { rewrite H0. easy. }
    rewrite ?associative in H1.
    rewrite field_mul_inv_r in H1; auto.
    rewrite ?identityRight in H1. easy.
  Qed.

  (** a * b = 0 -> a = 0 \/ b = 0 *)
  Lemma field_mul_eq0_imply_a0_or_b0 : forall (a b : T) (HDec : Dec Teq),
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
  Lemma field_mul_eq_imply_a1_or_b0 : forall (a b : T) (HDec : Dec Teq),
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

  Goal forall a b : R, ((a <> 0) -> /a * a = 1)%R.
    intros. apply field_mulInvL. auto. Qed.

End Examples.


(* ######################################################################### *)
(** * Linear Space *)

(** ** Class *)
Class LinearSpace `{F : Field} {V : Type}
  (Vadd : V -> V -> V) (Vzero : V) (Vopp : V -> V) (Vcmul : T -> V -> V)
  (Veq : relation V) := {
    ls_addC : Commutative Vadd Veq;
    ls_addA : Associative Vadd Veq;
    ls_add_0_r : IdentityRight Vadd Vzero Veq;
    ls_add_inv_r : InverseRight Vadd Vzero Vopp Veq;
    ls_cmul_1_l : forall u : V, Veq (Vcmul T1 u) u;
    lc_cmul_assoc : forall a b u, Veq (Vcmul (Tmul a b) u) (Vcmul a (Vcmul b u));
    lc_cmul_aadd_distr : forall a b u,
      Veq (Vcmul (Tadd a b) u) (Vadd (Vcmul a u) (Vcmul b u));
    lc_cmul_vadd_distr : forall a u v,
      Veq (Vcmul a (Vadd u v)) (Vadd (Vcmul a u) (Vcmul a v));
  }.

(** ** Instances *)
Section Instances.

  (** A field itself is a liner space *)
  Section field_is_linearspace.
    Context `{F : Field}.
    Add Field field_inst : (make_field_theory F).
    
    Global Instance LinearSpace_Field : LinearSpace Tadd T0 Topp Tmul Teq.
    split_intro; try field. Qed.
    
  End field_is_linearspace.

End Instances.


(** ** Extra Theories *)

Section Theory.

  Open Scope T_scope.
  
  Context `{LS : LinearSpace}.
  Infix "==" := Teq : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Notation Tsub := (fun a b => a + -b).
  Infix "-" := Tsub : T_scope.
  Infix "*" := Tmul : T_scope.
  Notation "/ a" := (Tinv a) : T_scope.
  Notation Tdiv := (fun a b => a * (/b)).
  Infix "/" := Tdiv : T_scope.

  Infix "==" := Veq : LinearSpace_scope.
  Infix "+" := Vadd : LinearSpace_scope.
  Notation "- a" := (Vopp a) : LinearSpace_scope.
  Notation Vsub := (fun a b => a + -b).
  Infix "-" := Vsub : LinearSpace_scope.
  Infix "c*" := Vcmul : LinearSpace_scope.

  (** V中零元是唯一的。已内置 *)

  (** V中每个元素的负元是唯一的。已内置 *)

  (** 0 * v = 0 *)
  Theorem LS_cmul_0_l : forall v : V, (T0 c* v == Vzero)%LS.
  Proof. Abort.
  
End Theory.

(** ** Examples *)
Section Examples.

End Examples.

