(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Spaces
  author    : ZhengPu Shi
  date      : 2023.03

  reference :
  1. Handbook of Linear Algebra, Leslie Hogben

  remark    :
  1. use matrix theory in CoqMatrix.SafeNatFun, and typeclass in HierarchySetoid.

 *)

Require Import List. Import ListNotations.
Require Import AlgebraStructure.
Require Complex QExt.
Require Vector.
Require VectorR.


Generalizable Variables A Aadd Aopp Amul Ainv Adiv.

(** * Preliminaries *)

(** field *)

(** We should develop our theory on an abstract context *)
Section field.
  Context `{F : Field}.
  Add Field field_inst : make_field_theory.

  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  
  Example ExTheorem1 : forall a b c : A, a + b + c = c + b + a.
  Proof. intros. field. Qed.

End field.

(** The developped theories could be reused on an abstract context *)
Section field.
  Context `{F:Field}.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).

  Goal forall a b c, a + b + c = c + b + a.
  Proof. apply ExTheorem1. Qed.
End field.

(** The developped theories could be reused on an concrete context *)
Section field.
  Import Qcanon.
  Goal forall a b c : Qc, a + b + c = c + b + a.
  Proof. apply ExTheorem1. Qed.

  Import Complex.
  Goal forall a b c : C, a + b + c = c + b + a.
  Proof. apply ExTheorem1. Qed.
End field.


(** * 1.1 Vector Spaces *)

(** ** Definitions *)

(* (** vector *) *)
(* Section vector. *)
(*   Context {A : Type} {f : @field A}. *)
(*   Inductive vector (n : nat) : Type := *)
(*     mk_vec (f : nat -> A). *)

(*   (** get function of a vector *) *)
(*   Definition vecf {n} (v : vector n) : nat -> A := *)
(*     let '(mk_vec _ f) := v in f. *)

(*   Definition vec_add {n} (x y : vector n) : vector n := *)
(*     mk_vec _ (fun i => Fadd f (vecf x i) (vecf y i)). *)

(*   Definition vec_scal {n} (c : A) (x : vector n) : vector n := *)
(*     mk_vec _ (fun i => Fmul f c (vecf x i)). *)

(*   Definition vec_ith {n} (x : vector n) (i : nat) := *)
(*     if leb i n then vecf x i else F0 f. *)

(*   Definition l2v n (l : list A) : vector n := *)
(*     mk_vec _ (fun i => nth i l (F0 f)). *)

(*   Definition v2l n (x : vector n) : list A := *)
(*     map (fun i => vecf x i) (seq 0 n). *)
    
(*     mk_vec _ (fun i => nth i l (F0 f)). *)

(* End vector. *)

(* Arguments mk_vec {A n}. *)


(* (** vector space *) *)
(* Section vector_space. *)

(*   Import Vector. *)
  
(*   Context `{F : Field}. *)
(*   (* Notation veq := (meq (Aeq:=Aeq)). *) *)
(*   (* Infix "==" := veq : vec_scope. *) *)
(*   (* Check meq. *) *)
(*   Class VectorSpace {n} (VS0 : @vec A n) *)
(*     (VSadd : @vec A n -> @vec A n -> @vec A n) *)
(*     (VSscal : A -> @vec A n -> @vec A n) *)
(*     (VSopp : @vec A n -> @vec A n) *)
(*     := { *)
(*       VSadd_comm :> Commutative VSadd meq; *)
(*       VSadd_assoc :> Associative VSadd veq; *)
(*       VSadd_id_l :> IdentityLeft VSadd VS0 veq; *)
(*       VSadd_inv_l :> InverseLeft VSadd VS0 VSopp veq; *)
(*       VSscal_id_l : forall x, VSscal A1 x == x; *)
(*       VSscal_assoc : forall a b x, VSscal (Amul a b) x == VSscal a (VSscal b x); *)
(*       VSscal_distr_r : forall a b x, VSscal (Aadd a b) x == VSadd (VSscal a x) (VSscal b x); *)
(*       VSscal_distr_l : forall a x y, VSscal a (VSadd x y) == VSadd (VSscal a x) (VSscal a y); *)
(*     }. *)

(*   (** real/complex vector space *) *)
(*   (* Import VectorR. *) *)
(*   (* Print vec0. *) *)
(*   (* Print vec. *) *)
(*   (* Check vec0 : vec 3. *) *)
(*   (* Variable n : nat. *) *)
(*   (* Check vec0 : SafeNatFun.Vector.vec n. *) *)

(* End vector_space. *)

(* Import VectorR. *)
(* Global Instance real_vector_space (n : nat) : *)
(*   @VectorSpace R Rplus Rmult R1 eq n vec0 vadd vcmul vopp. *)
(* Proof. *)
(*   constructor; try (constructor); intros. *)
(*   apply vadd_comm. apply vadd_assoc. apply vadd_0_l. apply vadd_opp_l. *)
(*   apply vcmul_1_l. rewrite vcmul_assoc; easy. *)
(*   apply vcmul_add_distr_l. apply vcmul_add_distr_r. *)
(* Defined. *)

(* Import VectorC. *)
(* Global Instance complex_vector_space (n : nat) : *)
(*   @VectorSpace C Cadd Cmul C1 eq n vec0 vadd vcmul vopp. *)
(* Proof. *)
(*   constructor; try (constructor); intros. *)
(*   apply vadd_comm. apply vadd_assoc. apply vadd_0_l. apply vadd_opp_l. *)
(*   apply vcmul_1_l. rewrite vcmul_assoc; easy. *)
(*   apply vcmul_add_distr_l. apply vcmul_add_distr_r. *)
(* Defined. *)

(* ? *)

(* (** n-tuples *) *)
(* Section ntuples. *)
(*   Context {A} {f : @field A}. *)
(*   Definition ntuples (n : nat) := @vector A n. *)

(*   Definition ntuples_add {n} (x y : ntuples n) : ntuples n := *)
(*     @vec_add A f n x y. *)

(*   (** coordinate *) *)
(*   Definition ntuples_coordinate {n} (x : ntuples n) (i : nat) : A := *)
(*     @vec_ith A f n x i. *)
  
(* End ntuples. *)


(* (** subspace *) *)


(* (** ** Facts *) *)

(* (** ** Examples *) *)

(* Section examples. *)

(*   Open Scope R_scope. *)
(*   Let ex1_x := *)

(* End examples. *)

