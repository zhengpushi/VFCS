(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  Coordinate System
  
  reference:
  QuanQuan, UAV design and control, page 90-106
  
  remark:
  2020.12.28, fix some formulas
*)

From FlyCtrl Require Import Array.
From FlyCtrl Require Import Real_proof.
From FlyCtrl Require Import Quaternion_tttt.

Require Import List.  (* formula 5.14 will use it *)

Import Module_ArrayR.
Import Module_Quaternion_tttt_R.    (* It also imported VectorR *)

Open Scope R. (* we mainly use R *)


(* --------------------------------------------------------------- *)
(* custome tactics *)

(* Tactic for type convertion *)
Ltac simpl_etype :=
  unfold mul,add,sub,neg,Zero,One,T.

(* Tactic for solve one equation, like A = B *)
Ltac simpl_one_equation :=
  (* trigo and real simplification *)
  trigo_simp; real_simp;
  (* type convertion *)
  simpl_etype;
  (* try solve *)
  try ring.


(* Tactic for simplify matrix multiplication with form of AXB*)
Ltac simpl_mat_AxB :=
  (* unfold matrix_mult *)
  unfold m_mul, Array.m_mul; simpl;
  (* unfold vector_mult *)
  unfold Array.a_dot; simpl;
  (* turn to its components *)
  simpl_equal_of_tuples;
  (* solve every equation *)
  simpl_one_equation.

(* Tactic for solve matrix multiplication with forms AxB=C *)
(*Ltac simpl_AB_eq_C :=
  simpl_mat_AxB;
  (* type convertion *)
  simpl_etype;
  (* real, trigo, simplification *)
  real_simp; trigo_simp;
  (* type convertion *)
  simpl_etype; ring_simplify;
  (* rewrite, unfold *)
  autorewrite with coordinate; ring_simplify;
  autounfold with coordinate; ring_simplify; 
  autorewrite with coordinate; 
  (* try again *)
  try ring.
*)

(* --------------------------------------------------------------- *)
(*
  Coordinate,
  e: Earth-Fixed Coordinate Frame, short as EFCF
  b: Aircraft-Body Coordinate Frame, short as ABCF
*)

(* unit vectors of EFCF axis in EFCF. *)
Definition e1 : matrix 3 1 := [[1], [0], [0]].
Definition e2 : matrix 3 1 := [[0], [1], [0]].
Definition e3 : matrix 3 1 := [[0], [0], [1]].

(* unit vectors of ABCF axis in ABCF *)
Definition b1_b : matrix 3 1 := e1.
Definition b2_b : matrix 3 1 := e2.
Definition b3_b : matrix 3 1 := e3.

(* NOTE, THESE MATRIX are same with the book, but I think Ry is WRONG.
I don't fix it. *)
   
(* three basic rotate matrices, roatate an coordinate. [W' = R W] *)
Definition Rx (α : R) : matrix 3 3 := 
  [[1,  0,        0      ],
   [0,  cos α,    sin α ],
   [0,  -sin α,   cos α ]].

Definition Ry (β : R) : matrix 3 3 := 
  [[cos β,  0,  -sin β],
   [0,      1,  0     ],
   [sin β,  0,  cos β ]].

Definition Rz (γ : R) : matrix 3 3 := 
  [[cos γ,    sin γ,  0],
   [-sin γ,   cos γ,  0],
   [0,        0,       1]].

(* three basic rotate matrices, roatate an vector. [V' = R' V] *)
Definition Rx' (α : R) : matrix 3 3 := 
  [[1,  0,        0      ],
   [0,  cos α,    -sin α ],
   [0,  sin α,   cos α ]].

Definition Ry' (β : R) : matrix 3 3 := 
  [[cos β,  0,  sin β],
   [0,      1,  0     ],
   [-sin β,  0,  cos β ]].

Definition Rz' (γ : R) : matrix 3 3 := 
  [[cos γ,    -sin γ,  0],
   [sin γ,   cos γ,  0],
   [0,        0,       1]].

Lemma Rx_Rx'_trans (a : R) : Rx a = m_trans (Rx' a).
Proof. unfold Rx,Rx'. simpl_equal_of_tuples. Qed.

Lemma Ry_Ry'_trans (a : R) : Ry a = m_trans (Ry' a).
Proof. unfold Ry,Ry'. simpl_equal_of_tuples. Qed.

Lemma Rz_Rz'_trans (a : R) : Rz a = m_trans (Rz' a).
Proof. unfold Rz,Rz'. simpl_equal_of_tuples. Qed.

(* check if some matrices are so3 matrix *)
Lemma Rx_so3 : forall a : R, so3 (Rx a).
Proof.
  intro. unfold so3; split.
  simpl_mat_AxB.
  unfold m_3x3_det,Array.m_3x3_det; simpl. simpl_one_equation.
  Qed.

Lemma Ry_so3 : forall a : R, so3 (Ry a).
Proof.
  intro. unfold so3; split.
  simpl_mat_AxB.
  unfold m_3x3_det,Array.m_3x3_det; simpl. simpl_one_equation.
  Qed.

Lemma Rz_so3 : forall a : R, so3 (Rz a).
Proof.
  intro. unfold so3; split.
  simpl_mat_AxB.
  unfold m_3x3_det,Array.m_3x3_det; simpl. simpl_one_equation.
  Qed.

Lemma Rx'_so3 : forall a : R, so3 (Rx' a).
Proof.
  intro. unfold so3; split.
  simpl_mat_AxB.
  unfold m_3x3_det,Array.m_3x3_det; simpl. simpl_one_equation.
  Qed.

Lemma Ry'_so3 : forall a : R, so3 (Ry' a).
Proof.
  intro. unfold so3; split.
  simpl_mat_AxB.
  unfold m_3x3_det,Array.m_3x3_det; simpl. simpl_one_equation.
  Qed.

Lemma Rz'_so3 : forall a : R, so3 (Rz' a).
Proof.
  intro. unfold so3; split.
  simpl_mat_AxB.
  unfold m_3x3_det,Array.m_3x3_det; simpl. simpl_one_equation.
  Qed.

(* function of attitude (Euler's angle) by time *)
Parameter f_φ : R -> R.     (* roll *)
Parameter f_θ : R -> R.     (* pitch *)
Parameter f_ψ : R -> R.     (* yaw *)

(* function of attitude rate by time *)
Parameter f_φ' : R -> R.
Parameter f_θ' : R -> R.
Parameter f_ψ' : R -> R.

(* --------------------------------------------------------------- *)
(* 5.2.1 Euler Angle *)

Module Relation_AttituteRate_AngularVelocityOfAricraftBody.

  (* assumed time *)
  Parameter t : R.

  (* attitude *)
  Definition φ : R := f_φ t.
  Definition θ : R := f_θ t.
  Definition ψ : R := f_ψ t.
  Definition Θ : matrix 3 1 := [[φ], [θ], [ψ]].

  (* attitue rate *)
  Definition θ' : R := f_θ' t.
  Definition φ' : R := f_φ' t.
  Definition ψ' : R := f_ψ' t.
  Definition Θ' : matrix 3 1 := [[φ'], [θ'], [ψ']].

  (* angular velocity of the aircraft body *)
  Parameter ωx_b ωy_b ωz_b : R.
  Definition ω_b : matrix 3 1 := [[ωx_b], [ωy_b], [ωz_b]].

  (* two temp matrices have no meaning *)
  Definition Rn_b : matrix 3 3 := Rx φ.
  Definition Rk_b : matrix 3 3 := m_mul (Rx φ) (Ry θ).

  (* formula 5.2 *)
  
  Definition b1_b : matrix 3 1 := [[1], [0], [0]].
  Definition n2_b : matrix 3 1 := [[0], [cos φ], [-sin φ]].
  Definition k3_b : matrix 3 1 := [[-sin θ], [sin φ * cos θ], [cos θ * cos φ]].

  (* verification of formula 5.2 *)
  Lemma f_5_2_n2b : n2_b = m_mul Rn_b e2.
  Proof. unfold n2_b, e2. simpl_mat_AxB. Qed.

  Lemma f_5_2_k3b : k3_b = m_mul Rk_b e3.
  Proof. unfold k3_b, e3. simpl_mat_AxB. Qed.

  (* known formula 5.1 *)
  Axiom f_5_1 : ω_b = 
    m_add 
      (m_add 
        (m_cmul ψ' k3_b) (m_cmul θ' n2_b))
      (m_cmul φ' b1_b).

  (* verification of fomula 5.4 *)
  Lemma f_5_4 :
    let m : matrix 3 3 := 
      [[1, 0, -sin θ],
       [0, cos φ, cos θ * sin φ],
       [0, -sin φ, cos θ * cos φ]] in
    ω_b = m_mul m Θ'.
  Proof. rewrite f_5_1. simpl. unfold m_add,m_binary. simpl_mat_AxB. Qed.

  (* verification of formula 5.5 *)
  Definition W : matrix 3 3 := 
    [[1, tan θ * sin φ, tan θ * cos φ],
     [0, cos φ, -sin φ],
     [0, sin φ / cos θ, cos φ / cos θ]].

  Lemma f_5_5 : cos θ <> 0 -> Θ' = m_mul W ω_b.
  Proof. intros. rewrite f_5_4. simpl_mat_AxB;
    autounfold with coordinate; ring_simplify;
    autorewrite with coordinate; try ring_simplify;
    trigo_simp; try assumption.
    Qed.

End Relation_AttituteRate_AngularVelocityOfAricraftBody.

(* --------------------------------------------------------------- *)
(* 5.2.2 Rotation Matrix *)


Module RotationMatrix_between_EFCF_and_ABCF.

  (* begin to deriving the rotate matrix *)
  
  (* assumed time *)
  Parameter t : R.

  (* euler angles *)
  Definition φ : R := f_φ t.
  Definition θ : R := f_θ t.
  Definition ψ : R := f_ψ t.
  Definition Θ : matrix 3 1 := [[φ], [θ], [ψ]].
  
(*   (* assumed vector *)
  Parameter x_n y_n z_n : R.
  Definition vn : matrix 3 1 := [[x_n], [y_n], [z_n]].

  (* calculated vector *)
  Definition v1 : matrix 3 1 := m_mul (Rz' ψ) vn.
  Definition v2 : matrix 3 1 := m_mul (Ry' θ) v1.
  Definition vb : matrix 3 1 := m_mul (Rx' φ) v2.
 *)
  (* RotationMatrix from ABCF to EFCF *)
  Definition R_b_e : matrix 3 3 := m_mul (Rz' ψ) (m_mul (Ry' θ) (Rx' φ)).

  Definition R_b_e_direct : matrix 3 3 := [
    [cos θ * cos ψ, 
     cos ψ * sin θ * sin φ - sin ψ * cos φ,
     cos ψ * sin θ * cos φ + sin φ * sin ψ],
    [cos θ * sin ψ, 
     sin ψ * sin θ * sin φ + cos ψ * cos φ,
     sin ψ * sin θ * cos φ - cos ψ * sin φ],
    [-sin θ, sin φ * cos θ, cos φ * cos θ]
    ].

  Lemma f_5_9 : R_b_e = R_b_e_direct.
  Proof. unfold R_b_e,R_b_e_direct. simpl_mat_AxB. Qed.

  Lemma R_b_e_so3 : forall a : R, so3 R_b_e.
  Proof.
    rewrite f_5_9.
    intro. unfold so3; split.
    - simpl_mat_AxB;
      autounfold with coordinate; ring_simplify;
      autorewrite with coordinate; try ring_simplify;
      repeat rewrite -> Rsqr_pow2; ring_simplify; trigo_simp.
    - unfold m_3x3_det,Array.m_3x3_det; simpl; simpl_etype. 
      ring_simplify. trigo_simp.
    Qed.

  (* verification formula 5.12a *)
  Lemma R_b_e_postive : θ = PI / 2 -> R_b_e = 
    [[0, -sin(ψ - φ), cos(ψ - φ)],
     [0, cos(ψ - φ), sin(ψ - φ)],
     [-1, 0, 0]].
  Proof. 
    intros. rewrite f_5_9. unfold R_b_e_direct. rewrite H. trigo_simp.
    simpl_mat_AxB.
  Qed.

  (* verification formula 5.12b, Note that formula in book is error,
   a13,a23 should add a negative sign. *)
  Lemma R_b_e_negative : θ = - (PI / 2) -> R_b_e = 
    [[0, -sin(ψ + φ), -cos(ψ + φ)],
     [0, cos(ψ + φ), -sin(ψ + φ)],
     [1, 0, 0]].
  Proof.
    intros. rewrite f_5_9. unfold R_b_e_direct. rewrite H. trigo_simp.
    simpl_mat_AxB.
  Qed.

End RotationMatrix_between_EFCF_and_ABCF.


(* simple method, but two problem:
1. the codomain of function atan and asin is [-pi/2, pi/2],
 but, in real case, range of pitch angle if [-pi, pi]. so, need extend result
2. singularity problem of method of euler angle. i.e., when θ = (+,-)pi/2,
that is, r11 = r21 = 0, ψ and φ cannot be uniquely determined *)
Module Get_Attitude_from_RotationMatrix_Simple.

  (* given rotation matrix *)
  Parameter r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
  Definition R_b_e : matrix 3 3 := 
    [[r11,r12,r13],
     [r21,r22,r23],
     [r31,r32,r33]].

  Definition φ : R := atan (r32 / r33).
  Definition θ : R := asin (-r31).
  Definition ψ : R := atan (r21 / r11).

End Get_Attitude_from_RotationMatrix_Simple.


(* complex method, fixed the shortage of simple method *)
Module Get_Attitude_from_RotationMatrix_Complex.

  (* given rotation matrix *)
  Parameter r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
  Definition R_b_e : matrix 3 3 :=
    [[r11,r12,r13],
     [r21,r22,r23],
     [r31,r32,r33]].

  (*
  Inductive bool : Set :=  true : bool | false : bool
  Inductive nat : Set :=  O : nat | S : nat -> nat
  Inductive sumbool (A B : Prop) : Set :=  left : A -> {A} + {B} | right : B -> {A} + {B}

  Req_EM_T: forall r1 r2 : R, {r1 = r2} + {r1 <> r2}
  Rge_dec: forall r1 r2 : R, {r1 >= r2} + {~ r1 >= r2}
  Rlt_le_dec: forall r1 r2 : R, {r1 < r2} + {r2 <= r1}
  Rgt_ge_dec: forall r1 r2 : R, {r1 > r2} + {r2 >= r1}
  Rle_lt_dec: forall r1 r2 : R, {r1 <= r2} + {r2 < r1}

  Z.eq_dec: forall x y : Z, {x = y} + {x <> y}
  Z_gt_le_dec: forall x y : Z, {x > y} + {x <= y}
  Z_le_gt_dec: forall x y : Z, {x <= y} + {x > y}
  Z_lt_le_dec: forall x y : Z, {x < y} + {y <= x}
  Z_lt_ge_dec: forall x y : Z, {x < y} + {x >= y}

  Check Rgt_ge_dec 0 0. (* : {0 > 0} + {0 >= 0}, sumbool (0>0) (0>=0) *)

  Check fun (x:nat) => if x then 3 else 4.
  Check fun (x:nat) => match x with
    |O => 3
    |_ => 4
    end.

  Check fun f1 => match (Rgt_ge_dec 0 1) with
    | left _ => 1
    | right _ => 2
    end.
  *)

  Definition atan2 (x y : R) : R :=
    if Rgt_ge_dec x 0           (* {x > 0} + {x <= 0} *)
    then (* x > 0 *)
      atan (y/x)
    else (* x <= 0 *)
      if Rlt_le_dec x 0         (* {x < 0} + {x >= 0} *)
      then (* x < 0 *)
        if Rlt_le_dec y 0       (* {y < 0} + {y >= 0} *)
        then (* x < 0, y < 0 *)
          atan (y/x) - PI
        else (* x < 0, y >= 0 *)
          atan (y/x) + PI
      else (* x = 0 *)
        if Rgt_ge_dec y 0       (* {y > 0} + {y <= 0} *)
        then (* x = 0, y > 0 *)
          PI / 2
        else (* x = 0, y <= 0 *)
          if Rlt_le_dec y 0     (* {y < 0} + {y >= 0} *)
          then (* x = 0, y < 0 *)
            - PI / 2
          else (* x = 0, y = 0 *)
            0. (* IN FACT, this is undefined *)

  Definition φ_0 : R := atan2 r32 r33.
  Definition θ_0 : R := asin (-r31).
  Definition ψ_0 : R := atan2 r21 r11.
  Definition φ_1 : R := atan2 (-r32) (-r33).
  Definition θ_1 : R := (Rsign θ_0) * PI - θ_0.
  Definition ψ_1 : R := atan2 (-r21) (-r11).

  (* a struct for tracking parameter and result of formula 5.14 *)
  Record ParamAndResult : Set := mkParamAndResult {
    p_φ : R;
    p_θ : R;
    p_ψ : R;
    r_det : R
  }.

  (* function of right part for formula 5.14 *)
  Definition f_5_14_det (φ θ ψ : R) : R := 
    let R_x' : matrix 3 3 := m_trans (Rx φ) in 
    let R_y' : matrix 3 3 := m_trans (Ry θ) in 
    let R_z' : matrix 3 3 := m_trans (Rz ψ) in 
    let m1 : matrix 3 3 := m_mul (m_mul R_z' R_y') R_x' in
    let m2 : matrix 3 3 := m_sub R_b_e m1 in
      m_3x3_det m2.

  Definition f_5_14_1 : ParamAndResult := mkParamAndResult
    φ_0 θ_0 ψ_0 (f_5_14_det φ_0 θ_0 ψ_0).

  (* find the position of a list where has minimum element
   parameters:
    fcompare, x < y then true else false
    minPos, record position where the element is minum, init is 0
    len, a temporary nat as a counter, to count the length, init is 0
   return value:
    if given list is empty, return minPos we given
    
  *)
  Fixpoint list_min_pos {T : Set} (fcompare : T -> T -> bool) (s : list T) 
    (len : nat) (minPos : nat) (minT : T) : nat := match s with
    | nil => minPos
    | cons x xs => if fcompare x minT 
      then list_min_pos fcompare xs (S len) len x
      else list_min_pos fcompare xs (S len) minPos minT
    end.
  
  Module list_min_pos_TEST.
    
    Open Scope Z.
    Compute list_min_pos (fun x y => if Z_lt_le_dec x y then true else false)
      (cons 4 (cons 3 (cons 6 nil))) 0 0 999.
    Compute list_min_pos (fun x y => if Z_lt_le_dec x y then true else false)
      nil 9 9 999.
    
  End list_min_pos_TEST.

  (* THIS IS A TEMPORARY scope operation, we will use R after this example *)
  Open Scope Z.
  
  Compute list_min_pos (fun x y => if Z_lt_le_dec x y then true else false)
    (cons 4 (cons 3 (cons 2 nil))) 0 0 999.

  Open Scope R.

  Definition f_5_14_findBest : ParamAndResult :=
    let pr000 := mkParamAndResult φ_0 θ_0 ψ_0 (f_5_14_det φ_0 θ_0 ψ_0) in
    let pr001 := mkParamAndResult φ_0 θ_0 ψ_1 (f_5_14_det φ_0 θ_0 ψ_1) in
    let pr010 := mkParamAndResult φ_0 θ_1 ψ_0 (f_5_14_det φ_0 θ_1 ψ_0) in
    let pr011 := mkParamAndResult φ_0 θ_1 ψ_1 (f_5_14_det φ_0 θ_1 ψ_1) in
    let pr100 := mkParamAndResult φ_1 θ_0 ψ_0 (f_5_14_det φ_1 θ_0 ψ_0) in
    let pr101 := mkParamAndResult φ_1 θ_0 ψ_1 (f_5_14_det φ_1 θ_0 ψ_1) in
    let pr110 := mkParamAndResult φ_1 θ_1 ψ_0 (f_5_14_det φ_1 θ_1 ψ_0) in
    let pr111 := mkParamAndResult φ_1 θ_1 ψ_1 (f_5_14_det φ_1 θ_1 ψ_1) in
    let s : list ParamAndResult := 
      cons pr000 (cons pr001 (cons pr010 (cons pr011 
     (cons pr100 (cons pr101 (cons pr110 (cons pr111 nil))))))) in
    let minPos := list_min_pos 
      (fun x y => if (Rlt_le_dec (r_det x) (r_det y)) then true else false)
      s 0 0 pr000 in
      nth minPos s pr000.

  (* last problem, there is a more special case:
   when rotation matrix is unit 3x3 matrix, there are two solutions below,
   your program need to track the continuity of euler angles, they should 
   close to the value last moment *)

  Definition special_solution_0 : matrix 3 1 := [[0],[0],[0]].
  Definition special_solution_1 : matrix 3 1 := [[PI],[PI],[PI]].

End Get_Attitude_from_RotationMatrix_Complex.


Require Import Extraction.
Extraction "coordinate.ml" Get_Attitude_from_RotationMatrix_Complex.f_5_14_findBest.
