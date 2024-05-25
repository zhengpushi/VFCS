(*
  Copyright 2024 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 2nd-order homogeneous linear differential equation
              二阶常系数齐次线性微分方程
  author    : ZhengPu Shi
  date      : 2024.05
 *)

Require Import DEbase.


(* ######################################################################### *)
(** * General solution of 2nd-order homogeneouse linear differential equation *)

(** Equation: y''(x) + ay'(x) + by(x) = 0 *)
Record Eqn := {
    a : R;
    b : R;
  }.
Notation "e .a" := (a e) (at level 20, format "e .a").
Notation "e .b" := (b e) (at level 20, format "e .b").

(** The solution y(x) satisfy the equation *)
Definition isSolution (e : Eqn) (y : R -> R) : Prop :=
  y '' +f (e.a c* y ') +f (e.b c* y) = fzeroR.

(* The characteristic polynomial is: r * r + a * r + b,
     and there are three cases for the solutions, depending on the discriminant
     D = a * a - 4 * b. *)

(** Discriminant *)
Definition D (e : Eqn) : R := e.a * e.a - 4 * e.b.

(* ======================================================================= *)
(** ** The general solution when D > 0 *)

(* If D > 0, the characteristic polynomial has two distinct real roots r1 and r2,
     and the general solution is: c_{1}e^{r_{1}x} + c_{2}e^{r_{2}x}. *)
Module Dgt0.
  Section solution.
    (* Give an equation *)
    Variable e : Eqn.
    
    (* Give two arbitrary constants, used for general solutions *)
    Variable c1 c2 : R.

    (* Assume D > 0 *)
    Hypotheses HDgt0 : D e > 0.

    (** The root of the characteristic polynomial *)
    Definition r1 : R := (- e.a + sqrt (D e)) / 2.
    Definition r2 : R := (- e.a - sqrt (D e)) / 2.
    
    (** The general solutions *)
    Definition y := fun x => c1 * exp (r1 * x) + c2 * exp (r2 * x).
    (** 1st derivative of the solution *)
    Definition dy := fun x => c1 * r1 * exp(r1 * x) + c2 * r2 * exp(r2 * x).
    (** 2st derivative of the solution *)
    Definition d2y :=
      fun x => c1 * r1 * r1 * exp(r1 * x) + c2 * r2 * r2 * exp(r2 * x).
    
    (** verify that: y' = dy *)
    Lemma d_y_eq_dy : y ' = dy.
    Proof.
      extensionality x. unfold dy,y,r1,r2.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: dy' = d2y *)
    Lemma d_dy_eq_d2y : dy ' = d2y.
    Proof.
      extensionality x. unfold dy,d2y.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: y'' = d2y *)
    Lemma d2_y_eq_d2y : y '' = d2y.
    Proof. rewrite d_y_eq_dy. rewrite d_dy_eq_d2y. auto. Qed.
    
    (** The solution satisfy the equation *)
    Theorem y_spec : isSolution e y.
    Proof.
      hnf.
      (* eliminate derivative operations *)
      rewrite d2_y_eq_d2y, d_y_eq_dy.
      (* eliminate function equality *)
      feq.
      (* simplify *)
      unfold d2y,dy,y,r1,r2,D in *. destruct e; simpl in *.
      field_simplify.
      rewrite pow2_sqrt; try lra.
    Qed.
  End solution.
End Dgt0.

(* ======================================================================= *)
(** ** The general solution when D = 0 *)

(* If D = 0, the characteristic polynomial has a double root −a/2, and the
     general solution is: (c_{1}+c_{2}x) e^{-ax/2}. *)
Module Deq0.
  Section solution.
    (* Give an equation *)
    Variable e : Eqn.
    
    (* Give two arbitrary constants, used for general solutions *)
    Variable c1 c2 : R.

    (* Assume D = 0 *)
    Hypotheses HDeq0 : D e = 0.

    (** The root of the characteristic polynomial *)
    Definition r : R := - e.a / 2.
    
    (** The general solutions *)
    Definition y := fun x => (c1 + c2 * x) * exp (r * x).
    (** 1st derivative of the solution *)
    Definition dy := fun x => (c2 + r * c1 + r * c2 * x) * exp (r * x).
    (** 2st derivative of the solution *)
    Definition d2y :=
      fun x => (r * c2 + r * c2 + r * r * c1 + r * r * c2 * x) * exp (r * x).
    
    (** verify that: y' = dy *)
    Lemma d_y_eq_dy : y ' = dy.
    Proof.
      extensionality x. unfold dy,y,r.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: dy' = d2y *)
    Lemma d_dy_eq_d2y : dy ' = d2y.
    Proof.
      extensionality x. unfold dy,d2y.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: y'' = d2y *)
    Lemma d2_y_eq_d2y : y '' = d2y.
    Proof. rewrite d_y_eq_dy. rewrite d_dy_eq_d2y. auto. Qed.
    
    (** The solution satisfy the equation *)
    Theorem y_spec : isSolution e y.
    Proof.
      hnf.
      (* eliminate derivative operations *)
      rewrite d2_y_eq_d2y, d_y_eq_dy.
      (* eliminate function equality *)
      feq.
      (* simplify *)
      unfold d2y,dy,y,r,D in *. destruct e; simpl in *.
      field_simplify.
      replace (a0 ^ 2) with (4 * b0); try lra.
    Qed.
  End solution.
End Deq0.

(* ======================================================================= *)
(** ** The general solution when D < 0 *)

(* If D < 0, the characteristic polynomial has two complex conjugate roots
     r1,r2 = {\alpha} \pm i{\beta}, and the general solution is:
     e^{{\alpha}x}(c_1\cos{\beta x} + c_2\sin{\beta x}). *)
Module Dlt0.
  Section solution.
    (* Give an equation *)
    Variable e : Eqn.
    
    (* Give two arbitrary constants, used for general solutions *)
    Variable c1 c2 : R.

    (* Assume D < 0 *)
    Hypotheses HDlt0 : D e < 0.

    (** The root of the characteristic polynomial *)
    Definition alpha := (- e.a)/2.
    Definition beta := (sqrt (- (D e))) / 2.
    Definition r1 : C := alpha +i beta.
    Definition r2 : C := alpha +i (- beta).
    
    (** The general solutions *)
    Definition y :=
      fun x => exp (alpha * x) *
               (c1 * cos (beta * x)
                + c2 * sin (beta * x)).
    
    (** 1st derivative of the solution *)
    Definition dy :=
      fun x => exp (alpha * x) *
               (c1 * alpha * cos (beta * x)
                + c2 * alpha * sin (beta * x)
                - c1 * beta * sin (beta * x) 
                + c2 * beta * cos (beta * x)).
    (** 2st derivative of the solution *)
    Definition d2y :=
      fun x => exp (alpha * x) *
               (c1 * alpha * alpha * cos (beta * x)
                + c2 * alpha * alpha * sin (beta * x)
                - c1 * alpha * beta * sin (beta * x) 
                + c2 * alpha * beta * cos (beta * x)
                - c1 * alpha * beta * sin (beta * x)
                + c2 * alpha * beta * cos (beta * x)
                - c1 * beta * beta * cos (beta * x)
                - c2 * beta * beta * sin (beta * x)).
    
    (** verify that: y' = dy *)
    Lemma d_y_eq_dy : y ' = dy.
    Proof.
      extensionality x. unfold dy,y,alpha,beta.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: dy' = d2y *)
    Lemma d_dy_eq_d2y : dy ' = d2y.
    Proof.
      extensionality x. unfold dy,d2y.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: y'' = d2y *)
    Lemma d2_y_eq_d2y : y '' = d2y.
    Proof. rewrite d_y_eq_dy. rewrite d_dy_eq_d2y. auto. Qed.
    
    (** The solution satisfy the equation *)
    Theorem y_spec : isSolution e y.
    Proof.
      hnf.
      (* eliminate derivative operations *)
      rewrite d2_y_eq_d2y, d_y_eq_dy.
      (* eliminate function equality *)
      feq.
      (* simplify *)
      unfold d2y,dy,y,alpha,beta,D in *. destruct e; simpl in *.
      field_simplify.
      rewrite pow2_sqrt; try lra.
    Qed.
  End solution.
End Dlt0.


(* Test OCaml extraction *)
(* Extraction HomoLDE2. *)

(* Test *)
Section test.

  (* A simple example shows three cases D > 0, D = 0, and D < 0 *)
  Section three_cases.
    (* when D > 0 *)

    (* Give an equation *)
    Let e1 : Eqn := {| a := 3; b := 1 |}. (* D = 3 * 3 - 4 * 1 = 5 *)
    (* Compute its solution *)
    (* Eval cbv in Dgt0.y e1. *)
    (* Verify the solution *)
    Goal forall c1 c2, isSolution e1 (Dgt0.y e1 c1 c2).
    Proof. intros. apply Dgt0.y_spec. cbv. lra. Qed.

    (* when D = 0 *)
    Let e2 : Eqn := {| a := 2; b := 1 |}. (* D = 2 * 2 - 4 * 1 = 0 *)
    (* Eval cbv in Deq0.y e2. *)
    Goal forall c1 c2, isSolution e2 (Deq0.y e2 c1 c2).
    Proof. intros. apply Deq0.y_spec. cbv. lra. Qed.

    (* when D < 0 *)
    Let e3 : Eqn := {| a := 2; b := 3 |}. (* D = 2 * 2 - 4 * 3 = - 8 *)
    (* Eval cbv in Dlt0.y e3. *)
    Goal forall c1 c2, isSolution e3 (Dlt0.y e3 c1 c2).
    Proof. intros. apply Dlt0.y_spec. cbv. lra. Qed.
  End three_cases.

  (* eg 12.4.2, XuXiaoZhan,page336 *)
  Section eg12_4_2.
    (* verify the solution *)
    Let e : Eqn := {| a := 2; b := 1|}.
    Goal forall c1 c2, Deq0.y e c1 c2 = fun x => c1 * exp (- x) + c2 * x * exp (- x).
    Proof.
      intros. cbv. extensionality x. field_simplify.
      f_equal; f_equal; f_equal; field.
    Qed.
    
  End eg12_4_2.
  
End test.
