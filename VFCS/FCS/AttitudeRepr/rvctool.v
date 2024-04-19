(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Formalize rvctool
  author    : ZhengPu Shi
  date      : Apr, 2023
  
  reference :
  1. Peter Corke, Robotics Vision and Control
*)

Require Import Lra.

(* Require Import Quaternion. *)
Require Import VectorC.
Require Import VectorR.
Require Import VectorR3.

(* short name for matrix/vector theory on C *)
Module C.
  Include MatrixTheoryC.
  Include VectorTheoryC.
End C.

Open Scope cvec_scope.

(* Another name for R type *)
Notation Real := R.

(** Convert cvecC to cvecR *)
Definition cvecC_to_cvecR {n} (v : C.cvec n) (f : Complex.C -> R) : cvec n :=
  f2cv (fun i => f (C.cv2f v i)).

(** Calculate engenvalues and eigenvectors of a matrix.
    if [x,e] = eig(R), then:
    the eigenvalues are returned on the diagonal of the matrix e,
    and the corresponding eigenvectors are the corresponding columns of x *)
Parameter eig : forall {n : nat} (m : mat n n), C.mat n n * C.mat n n.
  

(** A matrix is orthonormal:
 1. each column is a unit vector
 2. the columns are orthogonal *)
(* Definition orthogonal {r c} (m : mat r c) :=?. *)
(* Definition orthonormal {n} (m : smat n) :=?. *)

(** Two vectors are orthogonal *)
Definition cvorthogonal {n} (v1 v2 : cvec n) := <v1,v2> = 0.

(** * Orientation in 3-Dimensions *)
Module SO3.

  (** A 3D square matrix is orthonormal *)
  Definition orthonormal3 (m : smat 3) :=
    let c0 := mcol m 0 in
    let c1 := mcol m 1 in
    let c2 := mcol m 2 in
    cvunit c0 /\ cvunit c1 /\ cvunit c2 /\
      (cvorthogonal c0 c1) /\
      (cvorthogonal c0 c2) /\
      (cvorthogonal c1 c2).

  (** Special Orthogonal Group of dimension 3: R ∈ SO(3) ⊂ R^(3x3) *)
  Record SO3 := {
      SO3R :> mat 3 3;
      _ : orthonormal3 SO3R
    }.
  

  (* Orthogormal rotation matrices for rotation of θ aobout 
     the x-,y- and z- axes *)
  Definition Rx (θ : R) : mat 3 3 :=
    l2m [[1; 0; 0];
         [0; cos θ; - sin θ];
         [0; sin θ; cos θ]]%R.

  Definition Ry (θ : R) : mat 3 3 :=
    l2m [[cos θ; 0; sin θ];
         [0; 1; 0];
         [- sin θ; 0; cos θ]]%R.

  Definition Rz (θ : R) : mat 3 3 :=
    l2m [[cos θ; - sin θ; 0];
         [sin θ; cos θ; 0];
         [0; 0; 1]]%R.

  Lemma Rx_orthonormal : forall θ, orthonormal3 (Rx θ).
  Proof. intros. cbv. split_intro; autorewrite with R; ra. Qed.

  Lemma Rx_mdet1 : forall θ, mdet (Rx θ) = 1.
  Proof. intros. cbv. autorewrite with R. auto. Qed.

  Lemma Rx_inv_eq_trans : forall θ, minv3 (Rx θ) == (Rx θ)\T.
  Proof. lma; try rewrite mdet3_eq_mdet, Rx_mdet1; autounfold with T; ra.
         autorewrite with R; ra. Qed.

  (** Create a rotation matrix of dimension 3 about the x-axis *)
  Definition rotx (θ : angle) : mat 3 3 := Rx (angle_radian θ).

  (** Create a rotation matrix of dimension 3 about the y-axis *)
  Definition roty (θ : angle) : mat 3 3 := Ry (angle_radian θ).

  (** Create a rotation matrix of dimension 3 about the z-axis *)
  Definition rotz (θ : angle) : mat 3 3 := Rz (angle_radian θ).

  Example ex1 : rotx((PI/2) 'rad) * roty((PI/2) 'rad) ==
                  l2m [[0;0;1];[1;0;0];[0;1;0]].
  Proof. lma; try autorewrite with R; autounfold with T; ra. Qed.

  Example ex2 : roty((PI/2) 'rad) * rotx((PI/2) 'rad) ==
                  l2m [[0;1;0];[0;0;-1];[-1;0;0]].
  Proof. lma; try autorewrite with R; autounfold with T; ra. Qed.

  
  (** ** The angle representations *)

  (** 欧拉定理要求对三个轴的相继旋转，并且相邻两次使用不同的轴。有两种类型的旋转顺序：
      (1) Eulerian: 有重复，但不是相继的重复。包括：XYX,XZX,YXY,YZY,ZXZ,ZYZ
      (2) Cardanian: 没有重复。XYZ,XZY,YXZ,YZX,ZXY,ZYX
      共有12种类型。
      实际的顺序在特定技术领域有不同的惯例。
      (1) ZYZ, 航空和机械力学中，也是toolbox的顺序。欧拉角是3D向量 Γ=(ϕ,θ,ψ).
      (2) Cardan angles: roll, pitch, yaw. 
          教科书上有两个版本，取决于是否有移动机器人:
          (a) ZYX: 描述车辆的姿态，例如轮船，飞机，汽车。
              x轴指向前进方向；z轴向上或向下。
              yaw是行进方向，pitch是头部关于水平方向的抬升，roll是关于前进轴的旋转。
              Roll-pitch-yaw angles also known as Tait-Bryan angles or nautical angles,
              and for aeronautical application they can be called bank, attitude and 
              heading angles respectively.
          (b) XYZ: 描述机械手的姿态。
              z轴指向前进方向；x轴向上或向下。
          这种方式使得所有的角都可以有任意的符号，当θ_pitch = ±π/2 时发生奇异。
      (3) 用于航天器导航的机械陀螺仪，使用 Cardanian YZX 顺序。
          x轴指向向上的推力轴，z轴指向前面，y轴指向右侧。
   *)

  Module ZYZ.

    Definition R (ϕ θ ψ : R) : mat 3 3 := Rz ϕ * Ry θ * Rz ψ.

    (** Convert Euler angles to equivalent rotation matrix. *)
    Definition eul2r (Γ : cvec 3) : mat 3 3 :=
      let ϕ := Γ.1 in
      let θ := Γ.2 in
      let ψ := Γ.3 in
      R ϕ θ ψ.

    (** If θ = 0, then ϕ and ψ can not be uniquely decided *)
    (* The author's convension choice is : let ϕ = 0 *)
    Lemma R_theta0 : forall (ϕ θ ψ : Real), θ = 0 -> R ϕ θ ψ == Rz (ϕ + ψ).
    Proof. lma; rewrite H; autorewrite with R; autounfold with T; ra. Qed.

    (** Convert rotation matrix to equivalent Euler angles. *)
    (* Definition r2eul (m : mat 3 3) : cvec 3 := ? *)

  End ZYZ.

  Module ZYX.

    Definition R (roll pitch yaw : Real) : mat 3 3 := Rz yaw * Ry pitch * Rx roll.

    Definition rpy2r (roll pitch yaw : Real) : mat 3 3 := R yaw pitch roll.

    (* Definition r2rpy (m : mat 3 3) : cvec 3. *)

  End ZYX.

  Module XYZ.

    Definition R (roll pitch yaw : Real) : mat 3 3 := Rx yaw * Ry pitch * Rz roll.

    Definition rpy2r (roll pitch yaw : Real) : mat 3 3 := R yaw pitch roll.
    
    (* Definition r2rpy (m : mat 3 3) : cvec 3. *)
  End XYZ.

  Module YZX.

    Definition R (roll pitch yaw : Real) : mat 3 3 := Ry pitch * Rz roll * Rx yaw.

    (** If θ_roll = ±π/2, then {pitch,yaw} can not be uniquely decided *)
    Lemma R_roll_pi2 : forall (roll pitch yaw : Real),
        (* (roll = PI/2 \/ roll = - PI/2) -> *)
        (roll = PI/2) ->
        R roll pitch yaw == Rz (PI/2) * Rx (pitch + yaw).
    Proof. lma;
             (* destruct H as [H | H]; *)
             rewrite H; autorewrite with R; autounfold with T; ra; try easy.
    Qed.
    (** 丢失了一个自由度，在数学上意味着我们无法反转这个变换，只能建立两个角的线性关系 *)
    (** 本例中，我们只能得到pitch和yaw这两个角的和。*)

  End YZX.

  (** 奇异性问题：在所有三个角的表示中都有y这样的问题。
      问题发生的条件：当两个相继的轴变得对齐时 ？？
      对于 ZYZ Euler angles: 当θ=kπ, k∈Z 时
      对于 roll-pitch-yaw angles：当 pitch = ±(2k+1)π/2 时
      
      作者建议：精心的选择坐标系和角度顺序，使得交通工具的正常操作中不发生奇异
      参考全权老师的书中的算法：应该能够避免奇异性问题i。
   *)
  Section Singularities.

    (** Rotations obey the cyclic rotation rules *)
    Lemma Ry_Rz : forall θ, Rx (PI/2) * Ry θ * (Rx (PI/2))\T == Rz θ.
    Proof. lma; autorewrite with R; autounfold with T; ra. Qed.

    Lemma Rz_Rx : forall θ, Ry (PI/2) * Rz θ * (Ry (PI/2))\T == Rx θ.
    Proof. lma; autorewrite with R; autounfold with T; ra. Qed.

    Lemma Rx_Ry : forall θ, Rz (PI/2) * Rx θ * (Rz (PI/2))\T == Ry θ.
    Proof. lma; autorewrite with R; autounfold with T; ra. Qed.

    (** Rotations obey the anti-cyclic rotation rules *)
    Lemma Rz_Ry : forall θ, (Rx (PI/2))\T * Rz θ * Rx (PI/2) == Ry θ.
    Proof. lma; autorewrite with R; autounfold with T; ra. Qed.

    Lemma Rx_Rz : forall θ, (Ry (PI/2))\T * Rx θ * Ry (PI/2) == Rz θ.
    Proof. lma; autorewrite with R; autounfold with T; ra. Qed.

    Lemma Ry_Rx : forall θ, (Rz (PI/2))\T * Ry θ * Rz (PI/2) == Rx θ.
    Proof. lma; autorewrite with R; autounfold with T; ra. Qed.

  End Singularities.


  (** Rotation about an Arbitrary Vector *)
  Section Rotation_about_arbitrary_vector.

    (** The eigenvalue and eigenvectors of an orthonormal rotation matrix 
        always have one real eigenvalue at λ = 1, and a complex pair 
        λ = cos θ ± i * sin θ, where θ is the rotation angle. *)
    (* Hypotheses eig_of_SO3 : forall (m : mat 3 3), *)
    (*     orthonormal2 m -> *)
    (*     let (x,e) := eig m in *)
    (*     ? *)

    (** determine an angle and some axis (a vector) of a orthogonal rotation matrix *)
    Definition r2angvec (m : mat 3 3) : R * cvec 3 :=
      (* The eigenvalues are returned on the diagonal of the matrix e,
         and the corresponding eigenvectors are the corresponding columns of x *)
      let (x,e) := eig m in
      (* e(idx,idx) = cosθ +i sinθ *)
      let theta_of_idx (idx : nat) :=
        (let ele := C.m2f e idx idx in atan (ele.b / ele.a)) in
      (* the idx-th column of x contain the needed vector, which is the real part *)
      let vec_of_idx (idx : nat) := cvecC_to_cvecR (C.mcol x idx) (fun c => c.a) in
      (* find the angle and the vector *)
      let x11 := (C.m2f x 0 0) in
      let x22 := (C.m2f x 1 1) in
      if x11 ==? Complex.C1
      (* if x.11 ==? 1 *)
      then (theta_of_idx 1%nat, vec_of_idx 0%nat)
      else (if x22 ==? Complex.C1
            then (theta_of_idx 2%nat, vec_of_idx 1%nat)
            else (theta_of_idx 1%nat, vec_of_idx 2%nat)).

    (** Converting from angle and a unit vector to a rotation matrix, 
        i.e. Rodrigues' rotation formula. *)
    Definition angvec2r (θ : R) (axis : cvec 3) : mat 3 3 :=
      let ssm := cv3skew axis in
      (mat1 + (sin θ) c* ssm + (1 - cos θ)%R c* (ssm * ssm))%M.

  End Rotation_about_arbitrary_vector.

  (** Unit Quaternions *)
  Section UnitQuaternion.

    (* (** rotation matrix to unit quaternion *) *)
    (* (* Definition r2q *) *)
    (* Parameter r2q : mat 3 3 -> quat. *)

    (* (** unit quaternion to rotation matrix *) *)
    (* Parameter q2r : quat -> mat 3 3. *)

  End UnitQuaternion.

End SO3.
