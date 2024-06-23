(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Formalize Coordinate System
  author    : ZhengPu Shi
  date      : Mar, 2021
  
  reference :
  QuanQuan, UAV design and control, page 90-106
  
  remark    :
  
  abbreviations:
    Earth-Fixed Coordinate Frame, short as EFCF, subscript is e.
    Aircraft-Body Coordinate Frame, short as ABCF, subscript is b.
    Intermediate Coordinate Frame k, short AS CFk, subscript is k.
    Intermediate Coordinate Frame n, short AS CFn, subscript is n.
    Euler Angles, short as EA.
    Rotation Matrix, short as RotM.
  
*)

Require Import Lra.

Require Import VectorR.

(* --------------------------------------------------------------- *)
(** Config for Environment *)
Module Cfg4Env.

  (** Rotation type *)
  Inductive RotationType : Set :=
    | RotateCoord
    | RotateVector.

  (** Rotation direction *)
  Inductive RotationDirection : Set :=
    | Clockwise
    | Anticlockwise.

End Cfg4Env.


(* --------------------------------------------------------------- *)
(* Operations for Basic Rotation.

  ref:
  https://mathworld.wolfram.com/Rotationhtml
  https://zhuanlan.zhihu.com/p/166021408
  https://zhuanlan.zhihu.com/p/168772581
  https://blog.csdn.net/csxiaoshui/article/details/65446125
  
    
  That means:
  1. there are four possible conversions when we talk about "rotation":
    (1). rotation of the axes by an clockwise angle.
    (2). rotation of the axes by an counterclockwise angle.
    (3). rotation of the object relative to fixed axes by an clockwise angle.
    (4). rotation of the object relative to fixed axes by an counterclockwise 
      angle.
  2. in R^3, coordinate system rotations of the x-,y-,and z-axes in a 
    counterclockwise direction when looking towards the origin give the 
    matrices Rx,Ry,Rz.
  3. in R^3 rotation of the object ralative x-,y-,and z-axes by an
    counterclockwise direction when looking towards the origin give the 
    matrices Rx^T, Ry^T, Rz^T. i.e., Rx^T is the transpose of Rx, and so on.
  3. How to use the rotation matrix
    (1). Rotate an coordinate system C by an counterclockwise angle α to C', 
      then C' = Rx C. Notice that, C and C' are 3x3 matrix. 
    (2). Rotate an object V relative x-axes to V' by an counterclockwise angle 
      α, then V' = Rx^T V. Notice that, V and V' are 3-dim vector.
  4. the rotation angle has two different meaning:
    ref: https://zhuanlan.zhihu.com/p/172522079
    (1). Rotate by an axis of a coordinate sytem, called "Fixed angles"
    (2). Rotate by a coordinate system (i.e. the rotation could be divided into 
      three basic rotation in (1) if we need. ), called "Euler angles".
*)
Module BasicRotMat.
  
  (* For facilitate the calculation, we pack the 3-dim unit vector into a 
    matrix form *)
  Definition e1 : vec 3 := mk_mat_3_1 1 0 0.
  Definition e2 : vec 3 := mk_mat_3_1 0 1 0.
  Definition e3 : vec 3 := mk_mat_3_1 0 0 1.

  (* Rotation Matrix for: coordinate system rotations of the x-,y-,and z-axes 
    in an counterclockwise direction when looking towards the origin. *)
  Definition Rx (α : R) : mat 3 3 :=
    mk_mat_3_3 
      1 0 0
      0 (cos α) (sin α)
      0 (-sin α)%R (cos α).
  
  Definition Ry (β : R) : mat 3 3 :=
    mk_mat_3_3 
      (cos β) 0 (-sin β)%R
      0 1 0
      (sin β) 0 (cos β).

  Definition Rz (γ : R) : mat 3 3 :=
    mk_mat_3_3 
      (cos γ) (sin γ) 0
      (-sin γ)%R (cos γ) 0
      0 0 1.

  (* Rotation Matrix for: rotations of the object relative x-,y-,and z-axes by 
    an counterclockwise direction when looking towards the origin. *)
  Definition RxT (α : R) : mat 3 3 :=
    mk_mat_3_3 
      1 0 0
      0 (cos α) (-sin α)%R
      0 (sin α) (cos α).

  Definition RyT (β : R) : mat 3 3 :=
    mk_mat_3_3 
      (cos β) 0 (sin β)
      0 1 0
      (-sin β)%R 0 (cos β).

  Definition RzT (γ : R) : mat 3 3 :=
    mk_mat_3_3 
      (cos γ) (-sin γ)%R 0
      (sin γ) (cos γ) 0
      0 0 1.
  
  (* In fact, RxT is the transpose of Rx. and so on *)
  Lemma Rx_RxT_trans (a : R) : (Rx a == (RxT a) \T)%mat.
  Proof. lma. Qed.

  Lemma Ry_RyT_trans (a : R) : (Ry a == (RyT a) \T)%mat.
  Proof. lma. Qed.

  Lemma Rz_RzT_trans (a : R) : (Rz a == (RzT a) \T)%mat.
  Proof. lma. Qed.

  (** a temporary tactic which consists of cbv and ra (R arithmetic solver) *)
  Ltac cbv_ra :=
    cbv; ring_simplify; autorewrite with R; auto.
  
  (* verify that these matrices satisfy SO3 *)
  Lemma Rx_so3 : forall a : R, so3 (Rx a).
  Proof.
    intro. hnf; split. lma; cbv_ra. cbv_ra.
  Qed.

  Lemma Ry_so3 : forall a : R, so3 (Ry a).
  Proof.
    intro. hnf; split. lma; cbv_ra. cbv_ra.
  Qed.

  Lemma Rz_so3 : forall a : R, so3 (Rz a).
  Proof.
    intro. hnf; split. lma; cbv_ra. cbv_ra.
  Qed.

  Lemma RxT_so3 : forall a : R, so3 (RxT a).
  Proof.
    intro. hnf; split. lma; cbv_ra. cbv_ra.
  Qed.

  Lemma RyT_so3 : forall a : R, so3 (RyT a).
  Proof.
    intro. hnf; split. lma; cbv_ra. cbv_ra.
  Qed.

  Lemma RzT_so3 : forall a : R, so3 (RzT a).
  Proof.
    intro. hnf; split. lma; cbv_ra. cbv_ra.
  Qed.

End BasicRotMat.


(* --------------------------------------------------------------- *)
(* Definitions of Euler Angles and it's Rotation 
  5.2.1 ~ 5.2.2

  1. We define the Euler Angles according it's most commonly used definition 
    method.
  2. We also show the singularities of Euler Angles at two moments.
    (1). from formula (5.6), we guess that there exist singularity.
    (2). Given different value to θ in formula (5.9), we get different solution 
      directly. A more strong evidence.
  3. We give the final rotation matrix under this definition of Euler Angles.
*)
Module EA_RotM.

  (* We will use the basic rotaiton matrix here *)
  Import BasicRotMat.

  (** WE DON't USE THE DEFINITIONS WITH TIME, because this is not something 
    that must be done now. And it will increase the complexicity in other 
    related module, like Singularity-Verification below.
    &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& **)
  
  (*
  (* Euler angles over time *)
  Parameter f_ψ : R -> R.   (* yaw angle, rotated by X axis *)
  Parameter f_θ : R -> R.   (* pitch angle, rotated by Y axis *)
  Parameter f_φ : R -> R.   (* roll angle, rotated by Z axis *)

  (* Euler angle rates over time *)
  Parameter f_φ' : R -> R.
  Parameter f_θ' : R -> R.
  Parameter f_ψ' : R -> R.

  (* A given time value, then we got the corresponding Euler angle and Euler 
    angle rate *)
  Parameter t : R.
  
  Definition φ : R := f_φ t.
  Definition θ : R := f_θ t.
  Definition ψ : R := f_ψ t.
  Definition Θ : matrix 3 1 := [[φ], [θ], [ψ]].
  
  Definition θ' : R := f_θ' t.
  Definition φ' : R := f_φ' t.
  Definition ψ' : R := f_ψ' t.
  Definition Θ' : matrix 3 1 := [[φ'], [θ'], [ψ']]. 
  *)
  
  (** WE USE THE DEFINITIONS WITHOUT TIME, because this is simple and enough to 
    use.
    &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&**)

  (* Given Euler angle *)
  Parameter φ : R.
  Parameter θ : R.
  Parameter ψ : R.
  Definition Θ : vec 3 := mk_mat_3_1 φ θ ψ.
  
  (* Given Euler angle rate *)
  Parameter θ' : R.
  Parameter φ' : R.
  Parameter ψ' : R.
  Definition Θ' : vec 3 := mk_mat_3_1 φ' θ' ψ'. 
  
  (* The unit vectors of ABCF looking from the ABCF itself *)
  Definition b1_b : vec 3 := e1.
  Definition b2_b : vec 3 := e2.
  Definition b3_b : vec 3 := e3.
  
  Definition b1_b_direct : vec 3 := mk_mat_3_1 1 0 0.
  
  Lemma f_5_2_b1_b : b1_b = b1_b_direct.
  Proof. auto. Qed.
  
  (* rotation from CFn to ABCF *)
  (* Nitice that, we simplify a small process of Rx and RxT, and so on *)
  Definition R_n2b : mat 3 3 := Rx φ.
  Definition n1_b : vec 3 := mmul R_n2b b1_b.
  Definition n2_b : vec 3 := mmul R_n2b b2_b.
  Definition n3_b : vec 3 := mmul R_n2b b3_b.
  
  Definition n2_b_direct : vec 3 := (mk_mat_3_1 0 (cos φ) (-sin φ))%R.
  
  Lemma f_5_2_n2_b : n2_b == n2_b_direct.
  Proof. lma. Qed.
  
  (* rotation from CFk to ABCF *)
  Definition R_k2b : mat 3 3 := mmul (Rx φ) (Ry θ).
  
  Definition k1_b : vec 3 := mmul R_k2b b1_b.
  Definition k2_b : vec 3 := mmul R_k2b b2_b.
  Definition k3_b : vec 3 := mmul R_k2b b3_b.
  
  Definition k3_b_direct : vec 3 :=
    (mk_mat_3_1 (-sin θ) (sin φ * cos θ) (cos θ * cos φ))%R.
  
  Lemma f_5_2_k3_b : k3_b == k3_b_direct.
  Proof. lma. Qed.

  (** Relationship Between Euler-Angle Rates and Body-Axis Rates **)

  (* angular velocity of the aircraft body *)
  Parameter ωx_b ωy_b ωz_b : R.
  Definition ω_b : vec 3 := mk_mat_3_1 ωx_b ωy_b ωz_b.
  
  (* verify the fomula 5.4, 5.5 *)
  Section f_5_4_to_5_5.
  
    (* Relationship *)
    Hypothesis f_5_1 : ω_b = ((ψ' c* k3_b) + (θ' c* n2_b)) + (φ' c* b1_b).

    Lemma f_5_4 :
      let m : mat 3 3 := (mk_mat_3_3 
        1 0 (-sin θ)
        0 (cos φ) (cos θ * sin φ)
        0 (-sin φ) (cos θ * cos φ))%R in
      ω_b == mmul m Θ'.
    Proof.
      rewrite f_5_1. lma.
    Qed.
  
    (* verify the formula 5.5.
      1. Now, we find that there are cos θ in the denominator. When cos θ equal 
        to zero, then there will be singularities.
    *)
    Definition W : mat 3 3 := (mk_mat_3_3 
      1 (tan θ * sin φ) (tan θ * cos φ)
      0 (cos φ) (-sin φ)
      0 (sin φ / cos θ) (cos φ / cos θ))%R.

    Lemma f_5_5 : cos θ <> 0 -> Θ' == mmul W ω_b.
    Proof.
      intros. rewrite f_5_4. lma. unfold Θ',W. apply meq_iff; simpl.
      repeat apply list_equality; auto;
      unfold ListAux.ldot; simpl; repeat trigo_simp.
      unfold RingTypeR.A, add, mul. ring_simplify.
(*       Search tan.
      Opaque sin.
      autounfold with coordinate; ring_simplify;
      autorewrite with coordinate; try ring_simplify;
      trigo_simp; try assumption.
      Qed. *)
      Admitted.
  
  End f_5_4_to_5_5.
  
  (* Rotation Matrix from ABCF to EFCF *)
  Definition R_b_e : mat 3 3 :=
    ((Rz ψ) ⊤) × (((Ry θ) ⊤) × ((Rx φ) ⊤)).

  Definition R_b_e_direct : mat 3 3 := mk_mat_3_3
    (cos θ * cos ψ) 
    (cos ψ * sin θ * sin φ - sin ψ * cos φ)%R
    (cos ψ * sin θ * cos φ + sin φ * sin ψ)%R
    (cos θ * sin ψ)
    (sin ψ * sin θ * sin φ + cos ψ * cos φ)%R
    (sin ψ * sin θ * cos φ - cos ψ * sin φ)%R
    (-sin θ)%R (sin φ * cos θ) (cos φ * cos θ).

  Lemma f_5_9 : R_b_e = R_b_e_direct.
  Proof.
    unfold R_b_e,R_b_e_direct. apply meq_iff. simpl.
    unfold ListAux.ldot; simpl.
    repeat apply list_equality;
    unfold RingTypeR.A, add, sub, mul; trigo_simp.
  Qed.
  
  (* verify that the matrix satisfies SO3 *)
  Lemma R_b_e_so3 : forall a : R, so3 R_b_e.
  Proof.
    rewrite f_5_9.
    intro. unfold so3; split.
    - apply meq_iff. simpl.
      unfold ListAux.ldot; simpl.
      repeat apply list_equality;
      unfold RingTypeR.A, add, sub, mul; trigo_simp.
   (*    
      unfold Ring simpl_mat_AxB;
      autounfold with coordinate; ring_simplify;
      autorewrite with coordinate; try ring_simplify;
      repeat rewrite -> Rsqr_pow2; ring_simplify; trigo_simp.
    - unfold m_3x3_det; simpl; simpl_etype. 
      ring_simplify. trigo_simp.
    Qed.
   *)
  Admitted.
  
  (* Assume a rotation matrix *)
  Parameter r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
  Definition R_b_e_hyp : mat 3 3 := mk_mat_3_3
    r11 r12 r13
    r21 r22 r23
    r31 r32 r33.
  
  (* (5.10), Trigonometrics of euler angles deriving by hypothesis *)
  Definition φ_trigo_by_hyp := tan φ = r32 / r33.
  Definition θ_trigo_by_hyp := sin θ = (-r31)%R.
  Definition ψ_trigo_by_hyp := tan ψ = r21 / r11.
  
  (* Note that, when we verify the formula, we found the condition that 
    must satisfy. for example, the denomination can't be zero. *)
  Lemma f_5_10_correct : cos φ <> 0 /\ cos θ <> 0 /\ cos ψ <> 0 ->
    R_b_e_hyp = R_b_e -> (φ_trigo_by_hyp /\ θ_trigo_by_hyp /\ ψ_trigo_by_hyp).
  Proof.
    rewrite f_5_9.
    unfold R_b_e_hyp,R_b_e_direct,φ_trigo_by_hyp,θ_trigo_by_hyp,ψ_trigo_by_hyp.
    intros [Ha1 [Ha2 Ha3]].
    intros H; injection H as H11 H12 H13 H21 H22 H23 H31 H32 H33.
    repeat split.
    - rewrite H32,H33. unfold tan; field. split; auto.
    - rewrite H31. trigo_simp.
    - rewrite H21,H11. unfold tan; field. split; auto.
  Qed.

  (* (5.11) calculate the euler angles under the hypothesis *)
  Definition φ_by_hyp := φ = atan (r32 / r33).
  Definition θ_by_hyp := θ = asin (-r31).
  Definition ψ_by_hyp := ψ = atan (r21 / r11).
  
  (* Note that, the boundary conditions are very important in engineering. *)
  
  (* Some constraints are required when using formula (5.11). *)
  Lemma f_5_11_correct : cos φ <> 0 /\ cos θ <> 0 /\ cos ψ <> 0 ->
    - (PI / 2) < φ < PI / 2 ->
    - (PI / 2) <= θ <= PI / 2 ->
    - (PI / 2) < ψ < PI / 2 ->
    R_b_e_hyp = R_b_e -> (φ_by_hyp /\ θ_by_hyp /\ ψ_by_hyp).
  Proof.
    rewrite f_5_9.
    unfold R_b_e_hyp,R_b_e_direct,φ_by_hyp,θ_by_hyp,ψ_by_hyp.
    intros [Ha1 [Ha2 Ha3]].
    intros Hb Hc Hd.
    intros H; injection H as H11 H12 H13 H21 H22 H23 H31 H32 H33.
    repeat split.
    - rewrite H32,H33.
      (* 1. tan_atan/atan_tan are ready in coq new version.
         2. and the definition of asin. This function was considered as an 
          axiom in the previous time.
        So, Coq is a fast developping platform,
        we can see lots of new library and fix after each update, great! *)
      assert (sin φ * cos θ / (cos φ * cos θ) = tan φ).
      { unfold tan. field. split; auto. }
      rewrite H. rewrite atan_tan; auto.
    - rewrite H31. rewrite Ropp_involutive. rewrite asin_sin; auto.
    - rewrite H21,H11.
      assert (cos θ * sin ψ / (cos θ * cos ψ) = tan ψ).
      { unfold tan. field. split; auto. }
      rewrite H. rewrite atan_tan; auto.
    Qed.
  
  (* There are some problems with this method:
    1. There are several preconditions must be satisfied before we can use 
      these formulas, but these constraints are too strong.
      (1). the codomain of function atan or asin is [-pi/2, pi/2], but in 
        actual situation, the values range between -pi and pi.
    2. when θ = (+/-)pi/2, then r11=r21=r32=r33=0, then ψ and φ cannot be 
      uniquely determined. Because we cannot use formulas (5.11) at all caused 
      by denomintor is zero.
    
    So, we need to fix the result using other method. *)
  Definition R_b_e_θ_eq_pi_2 := mk_mat_3_3
    0 (-sin(ψ - φ))%R (cos(ψ - φ))
    0 (cos(ψ - φ)) (sin(ψ - φ))
    (-1) 0 0.
  
  Definition R_b_e_θ_eq_neg_pi_2 := mk_mat_3_3
    0 (-sin(ψ + φ))%R (-cos(ψ + φ))%R
    0 (cos(ψ + φ)) (-sin(ψ + φ))%R
    1 0 0.
  
  (* verify the formula 5.12 *)
  Lemma R_b_e_θ_eq_pi_2_correct : θ = (PI / 2) -> 
    R_b_e = R_b_e_θ_eq_pi_2.
  Proof. 
    intros. unfold R_b_e_θ_eq_pi_2. rewrite f_5_9. unfold R_b_e_direct.
    apply meq_iff; simpl.
    rewrite H; trigo_simp.
    repeat apply list_equality; trigo_simp.
(*   Qed. *)
  Admitted.
  
  Lemma R_b_e_θ_eq_neg_pi_2_correct : θ = (- (PI / 2))%R -> 
    R_b_e = R_b_e_θ_eq_neg_pi_2.
  Proof.
    intros. unfold R_b_e_θ_eq_neg_pi_2. rewrite f_5_9. unfold R_b_e_direct. 
    rewrite H; trigo_simp.
(*   Qed. *)
  Admitted.
  
  (* verify the formula 5.12 *)
  Lemma f_5_12_correct : (θ = (PI / 2) -> R_b_e = R_b_e_θ_eq_pi_2)
    /\ (θ = (- (PI / 2))%R -> R_b_e = R_b_e_θ_eq_neg_pi_2).
  Proof.
    split.
    apply R_b_e_θ_eq_pi_2_correct.
    apply R_b_e_θ_eq_neg_pi_2_correct.
  Qed.
  

End EA_RotM.

(* --------------------------------------------------------------- *)
(* 5.2.2 (Part II) The Calculate Euler Angles from Rotation 
  
  1. We give a set of basic formulas but singular.
  2. We show a complex algorithm to eliminate the singularity.
*)
Module CalcEulerAnglesByRotation

  
End CalcEulerAnglesByRotation
  


Require Import Extraction.
Extraction "coordinate.ml" Get_Attitude_from_RotationMatrix_Complex.f_5_14_findBest.
