(*
  Copyright 2024 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Linear differential equation 线性微分方程
  author    : ZhengPu Shi
  date      : 2024.05
  
  ref       :
  1. Wang Yi Peng's work
  2. https://en.wikipedia.org/wiki/Linear_differential_equation#Second-order_case

  remark    :
  1. Notation for R function, with scope Rfun_scope.
     f + g
     f - g
     f * g
     f / g
     c \.* f
     1
     0
 *)


From Coquelicot Require Import Rbar Continuity Derive RInt AutoDerive.
From Coquelicot Require Import Hierarchy ElemFct.
From FinMatrix Require Import RFunExt Complex MyExtrOCamlR.

Open Scope Rfun_scope.
Open Scope C_scope.
Open Scope R_scope.


(** Our Noations *)
Locate " '".
Notation "f '" := (Derive f) (at level 10, left associativity, format "f '").

(** Convert function equality to value equality *)
Ltac feq :=
  let x := fresh "x" in
  extensionality x;
  rewrite ?faddR_ok;
  rewrite ?faddR_ok;
  rewrite ?fcmulR_ok;
  try unfold fzeroR;
  try unfold fcnstR.


(* ######################################################################### *)
(** * Homogeneous linear differential equation of the second order
    (二阶常系数齐次线性微分方程) *)

(* https://en.wikipedia.org/wiki/Linear_differential_equation#Second-order_case *)
Module HomoLDEord2.
  
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
      Hypotheses H_Deq0 : D e > 0.

      (** The root of the characteristic polynomial *)
      Definition r1 : R := (- e.a + sqrt (D e)) / 2.
      Definition r2 : R := (- e.a - sqrt (D e)) / 2.
      
      (** The general solutions *)
      Definition y := fun x => c1 * exp (r1 * x) + c2 * exp (r2 * x).
      (** 1st derivative of the solution *)
      Definition dy := fun t => c1 * r1 * exp(r1 * t) + c2 * r2 * exp(r2 * t).
      (** 2st derivative of the solution *)
      Definition d2y :=
        fun t => c1 * r1 * r1 * exp(r1 * t) + c2 * r2 * r2 * exp(r2 * t).
      
      (** verify that: y' = dy *)
      Lemma d_y_eq_dy : y ' = dy.
      Proof.
        extensionality t. unfold dy,y,r1,r2.
        apply is_derive_unique. auto_derive; auto. ring.
      Qed.

      (** verify that: dy' = d2y *)
      Lemma d_dy_eq_d2y : dy ' = d2y.
      Proof.
        extensionality t. unfold dy,d2y.
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
      Hypotheses H_Deq0 : D e = 0.

      (** The root of the characteristic polynomial *)
      Definition r : R := - e.a / 2.
      
      (** The general solutions *)
      Definition y := fun x => (c1 + c2 * x) * exp (r * x).
      (** 1st derivative of the solution *)
      Definition dy := fun t => (c2 + r * c1 + r * c2 * t) * exp (r * t).
      (** 2st derivative of the solution *)
      Definition d2y :=
            fun t => (r * c2 + r * c2 + r * r * c1 + r * r * c2 * t) * exp (r * t).
      
      (** verify that: y' = dy *)
      Lemma d_y_eq_dy : y ' = dy.
      Proof.
        extensionality t. unfold dy,y,r.
        apply is_derive_unique. auto_derive; auto. ring.
      Qed.

      (** verify that: dy' = d2y *)
      Lemma d_dy_eq_d2y : dy ' = d2y.
      Proof.
        extensionality t. unfold dy,d2y.
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
      Hypotheses H_Deq0 : D e < 0.

      (** The root of the characteristic polynomial *)
      Definition alpha := (- e.a)/2.
      Definition beta := (sqrt (- (D e))) / 2.
      Definition r1 : C := alpha +i beta.
      Definition r2 : C := alpha +i (- beta).
      
      (** The general solutions *)
      Definition y := fun x => exp (alpha * x) * (c1 * cos (beta * x) + c2 * sin (beta * x)).
      
    (*   (** 1st derivative of the solution *) *)
    (*   Definition dy := fun t => c1 * r1 * exp(r1 * t) + c2 * r2 * exp(r2 * t). *)
    (*   (** 2st derivative of the solution *) *)
    (*   Definition d2y := *)
    (*     fun t => c1 * r1 * r1 * exp(r1 * t) + c2 * r2 * r2 * exp(r2 * t). *)
      
    (*   (** verify that: y' = dy *) *)
    (*   Lemma d_y_eq_dy : y ' = dy. *)
    (*   Proof. *)
    (*     extensionality t. unfold dy,y,r1,r2. *)
    (*     apply is_derive_unique. auto_derive; auto. ring. *)
    (*   Qed. *)

    (*   (** verify that: dy' = d2y *) *)
    (*   Lemma d_dy_eq_d2y : dy ' = d2y. *)
    (*   Proof. *)
    (*     extensionality t. unfold dy,d2y. *)
    (*     apply is_derive_unique. auto_derive; auto. ring. *)
    (*   Qed. *)

    (*   (** verify that: y'' = d2y *) *)
    (*   Lemma d2_y_eq_d2y : y '' = d2y. *)
    (*   Proof. rewrite d_y_eq_dy. rewrite d_dy_eq_d2y. auto. Qed. *)
      
    (*   (** The solution satisfy the equation *) *)
    (*   Theorem y_spec : isSolution e y. *)
    (*   Proof. *)
    (*     hnf. *)
    (*     (* eliminate derivative operations *) *)
    (*     rewrite d2_y_eq_d2y, d_y_eq_dy. *)
    (*     (* eliminate function equality *) *)
    (*     feq. *)
    (*     (* simplify *) *)
    (*     unfold d2y,dy,y,r1,r2,D in *. destruct e; simpl in *. *)
    (*     field_simplify. *)
    (*     rewrite pow2_sqrt; try lra. *)
    (*   Qed. *)
    End solution.
  End Dlt0.
End HomoLDEord2.

Section NonHomoLDEord2.
  
  Definition second_order_non_ode (a b c : R) (y : R -> R) (f : R -> R) :=
    forall t : R,
      let dy := Derive y in
      a * (Derive dy t) + b * (Derive y t) + c * y t = f t.
End NonHomoLDEord2.

(* Test OCaml extraction *)
(* Extraction HomoLDEord2. *)

(* Test *)
Section test.
  Import HomoLDEord2.

  (* when D = 0 *)
  Section case1.
    (* Give an equation *)
    Let e : Eqn := {| a := 2; b := 1 |}.
    (* The solution *)
    Let y c1 c2 := Eval cbv in Deq0.y e c1 c2.

    (* Verify the solution *)
    Goal forall c1 c2, isSolution e (y c1 c2).
    Proof.
      intros. apply Deq0.y_spec.
      cbv. lra.
    Qed.
  End case1.
End test.
