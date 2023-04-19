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

Require Import Quaternion.
Require Import VectorC.
Require Import VectorR.

Open Scope cvec_scope.

(** Another name for R type *)
Notation Real := R.
Notation matC := MatrixC.mat.
Notation matR := MatrixR.mat.
Notation cvecC := ColVectorC.cvec.
Notation cvecR := ColVectorR.cvec.


(** Convert cvecC to cvecR *)
Definition cvecC_to_cvecR {n} (v : cvecC n) (f : Complex.C -> R) : cvecR n :=
  mk_cvec (fun i => f (v$i)).

(** Calculate engenvalues and eigenvectors of a matrix.
    if [x,e] = eig(R), then:
    the eigenvalues are returned on the diagonal of the matrix e,
    and the corresponding eigenvectors are the corresponding columns of x *)
Parameter eig : forall {n : nat} (m : matR n n), matC n n * matC n n.
  

(** A matrix is orthonormal:
 1. each column is a unit vector
 2. the columns are orthogonal *)
(* Definition orthogonal {r c} (m : mat r c) :=?. *)
(* Definition orthonormal {n} (m : smat n) :=?. *)

(** Two vectors are orthogonal *)
Definition cvorthogonal {n} (v1 v2 : cvec n) := (v1 ⋅ v2 == A0)%A.

(** * Convert a angle between degree and radian *)
Module Export Angle.

  Inductive AngleKind := Radian | Degree.

  Definition deg2rad (d : R) : R := d * PI / 180.
  Definition rad2deg (r : R) : R := r * 180 / PI.

  Record angle := {
      angle_radian : R;
      angle_degree : R
    }.
  
  Definition mk_angle_deg (d : R) : angle :=
    Build_angle (deg2rad d) d.

  Definition mk_angle_rad (r : R) : angle :=
    Build_angle r (rad2deg r).

  Notation "r 'rad" := (mk_angle_rad r) (at level 30).
  Notation "d 'deg" := (mk_angle_deg d) (at level 30).

  Goal 180 'deg = PI 'rad.
    cbv. f_equal; field. ra. Qed.

End Angle.

(** * Orientation in 2-Dimensions *)
Module SO2.

  (** A 2D square matrix is orthonormal *)
  Definition orthonormal2 (m : smat 2) :=
    let c0 := mat2col m 0 in
    let c1 := mat2col m 1 in
    cvunit c0 /\ cvunit c1 /\ (cvorthogonal c0 c1).


  (** Special Orthogonal Group of dimension 2: R ∈ SO(2) ⊂ R^(2x2) *)
  Record SO2 := {
      SO2R :> mat 2 2;
      _ : orthonormal2 SO2R
    }.

  Definition SO2_mul (a b : SO2) : SO2.
    destruct a as [a [a1 [a2 a3]]].
    destruct b as [b [b1 [b2 b3]]].
    refine (Build_SO2 (a * b) _).
    split_intro.
    - Admitted.
  
  (* Fact Group_SO2 : Group SO2_mul. *)

  (** 2D rotation matrix *)
  Section rot2.
    (*  列向量表示该新坐标系的坐标轴在参考坐标系中的单位向量 *)
    Definition R (θ : R) : mat 2 2 :=
      l2m _ _
        [[cos θ; - sin θ];
         [sin θ; cos θ]]%R.

    (** Note that: pure rotation is commutative in 2D, but noncommutative in 3D *)
    
    (** Create a rotation matrix of dimension 2 *)
    Definition rot2 (θ : angle) : mat 2 2 := R (angle_radian θ).

    Lemma rot2_orthonormal : forall θ, orthonormal2 (rot2 θ).
    Proof. intros. cbv. split_intro; autorewrite with R; ra. Qed.

    Lemma rot2_det1 : forall θ, det (rot2 θ) = 1.
    Proof. intros. cbv. autorewrite with R. auto. Qed.

    Lemma rot2_inv_eq_trans : forall θ, minv2 (rot2 θ) == (rot2 θ)\T.
    Proof. lma; rewrite det2_eq_det, rot2_det1; ra. Qed.
  End rot2.

  (** Skew-symmetric matrix of 2-dimensions *)
  Section skew.
    (** Given matrix is skew-symmetric matrices *)
    Definition is_skew (m : mat 2 2) : Prop := (- m)%M == m\T.

    Lemma is_skew_spec : forall m : mat 2 2,
        is_skew m -> let '((a11,a12),(a21,a22)) := m2t_2_2 m in
                     (a11 = 0) /\ (a22 = 0) /\ (a12 = -a21)%A.
    Proof.
      intros. destruct m as [m]; simpl in *. cbv in H. split_intro.
      - epose proof (H 0 0 _ _)%nat. ra.
      - epose proof (H 1 1 _ _)%nat. ra.
      - epose proof (H 0 1 _ _)%nat. ra.
        Unshelve. all: ra.
    Qed.

    (** Convert a value to its corresponding skew-symmetric matrix *)
    Definition skew (a : A) : mat 2 2 := l2m _ _ [[0; -a];[a; 0]]%R.

    (** Convert a skew-symmetric matrix to its corresponding value *)
    Definition vex (m : mat 2 2) : option A := Some (m $ 1 $ 0).

    Lemma skew_vex_id : forall (m : mat 2 2), is_skew m -> 
                                         match vex m with
                                         | Some a => skew a == m
                                         | _ => False
                                         end.
    Proof. intros [m]. simpl. intros. apply is_skew_spec in H. lma. Qed.

    Lemma vex_skew_id : forall (a : A), vex (skew a) = Some a.
    Proof. intros. cbv. auto. Qed.
  End skew.

End SO2.


(** * Pose in 2-Dimensions *)
Module SE2.

  (* Compute m2l (mappr (@mat1 3) (@mat1 3)).  *)
  (* Compute m2l (mappc (@mat1 3) (@mat1 3)).  *)

  (** Special Euclidean Group of dimension 3: T ∈ SE(2) ⊂ R^(3x3) *)
  (* Record SE2 := { *)
  (*     SE2R :> mat 3 3; *)
  (*     _ : orthonormal2 SO2R *)
  (*   }. *)

  (** 2D homogeneous transformation, to represent relative pose *)
  Definition T (θ : R) (x y : R) : mat 3 3 :=
    l2m _ _
      [[cos θ; - sin θ; x];
       [sin θ; cos θ; y];
       [0; 0; 1]]%R.

  (** create a relative pose with a finite translation but zero rotation *)
  Definition transl2 (P : cvec 2) : mat 3 3 := T 0 (P$0) (P$1).

  (** create a relative pose with a finite rotation but zero translation *)
  Definition trot2 (θ : angle) : mat 3 3 := T (angle_radian θ) 0 0.

  Example ex_T1 := transl2 (mk_cvec2 1 2) * trot2(30 'deg).

  (** Convert Euclidean coordinates to homogeneous coordinates *)
  Definition e2h (v : cvec 2) : cvec 3 :=
    let '(a0,a1) := cv2t_2 v in
    mk_cvec3 a0 a1 1.

  (** Convert homogeneous coordinates to Euclidean coordinates *)
  Definition h2e (v : cvec 3) : cvec 2 :=
    let '(a0,a1,a2) := cv2t_3 v in
    mk_cvec2 (a0/a2) (a1/a2).

  (** A transformation to rotate about point C *)
  Definition trot2center (C : cvec 2) (θ : angle) : mat 3 3 :=
    transl2 C * trot2 θ * transl2 (-C).

End SE2.


(** * Orientation in 3-Dimensions *)
Module SO3.

  (** A 3D square matrix is orthonormal *)
  Definition orthonormal3 (m : smat 3) :=
    let c0 := mat2col m 0 in
    let c1 := mat2col m 1 in
    let c2 := mat2col m 2 in
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
    l2m _ _
      [[1; 0; 0];
       [0; cos θ; - sin θ];
       [0; sin θ; cos θ]]%R.

  Definition Ry (θ : R) : mat 3 3 :=
    l2m _ _
      [[cos θ; 0; sin θ];
       [0; 1; 0];
       [- sin θ; 0; cos θ]]%R.

  Definition Rz (θ : R) : mat 3 3 :=
    l2m _ _
      [[cos θ; - sin θ; 0];
       [sin θ; cos θ; 0];
       [0; 0; 1]]%R.

  Lemma Rx_orthonormal : forall θ, orthonormal3 (Rx θ).
  Proof. intros. cbv. split_intro; autorewrite with R; ra. Qed.

  Lemma Rx_det1 : forall θ, det (Rx θ) = 1.
  Proof. intros. cbv. autorewrite with R. auto. Qed.

  Lemma Rx_inv_eq_trans : forall θ, minv3 (Rx θ) == (Rx θ)\T.
  Proof. lma; try rewrite det3_eq_det, Rx_det1; ra. autorewrite with R; ra. Qed.

  (** Create a rotation matrix of dimension 3 about the x-axis *)
  Definition rotx (θ : angle) : mat 3 3 := Rx (angle_radian θ).

  (** Create a rotation matrix of dimension 3 about the y-axis *)
  Definition roty (θ : angle) : mat 3 3 := Ry (angle_radian θ).

  (** Create a rotation matrix of dimension 3 about the z-axis *)
  Definition rotz (θ : angle) : mat 3 3 := Rz (angle_radian θ).

  Example ex1 : rotx((PI/2) 'rad) * roty((PI/2) 'rad) ==
                  l2m 3 3 [[0;0;1];[1;0;0];[0;1;0]].
  Proof. lma; try autorewrite with R; ra. Qed.

  Example ex2 : roty((PI/2) 'rad) * rotx((PI/2) 'rad) ==
                  l2m 3 3 [[0;1;0];[0;0;-1];[-1;0;0]].
  Proof. lma; try autorewrite with R; ra. Qed.

  
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
      let ϕ := Γ$0 in
      let θ := Γ$1 in
      let ψ := Γ$2 in
      R ϕ θ ψ.

    (** If θ = 0, then ϕ and ψ can not be uniquely decided *)
    (* The author's convension choice is : let ϕ = 0 *)
    Lemma R_theta0 : forall (ϕ θ ψ : Real), θ = 0 -> R ϕ θ ψ == Rz (ϕ + ψ).
    Proof. lma; rewrite H; autorewrite with R; ra. Qed.

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
             rewrite H; autorewrite with R; ra; try easy.
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
    Proof. lma; autorewrite with R; ra. Qed.

    Lemma Rz_Rx : forall θ, Ry (PI/2) * Rz θ * (Ry (PI/2))\T == Rx θ.
    Proof. lma; autorewrite with R; ra. Qed.

    Lemma Rx_Ry : forall θ, Rz (PI/2) * Rx θ * (Rz (PI/2))\T == Ry θ.
    Proof. lma; autorewrite with R; ra. Qed.

    (** Rotations obey the anti-cyclic rotation rules *)
    Lemma Rz_Ry : forall θ, (Rx (PI/2))\T * Rz θ * Rx (PI/2) == Ry θ.
    Proof. lma; autorewrite with R; ra. Qed.

    Lemma Rx_Rz : forall θ, (Ry (PI/2))\T * Rx θ * Ry (PI/2) == Rz θ.
    Proof. lma; autorewrite with R; ra. Qed.

    Lemma Ry_Rx : forall θ, (Rz (PI/2))\T * Ry θ * Rz (PI/2) == Rx θ.
    Proof. lma; autorewrite with R; ra. Qed.

  End Singularities.

  (** Skew-symmetric matrix of 3-dimensions *)
  Section skew.
    
    (** Given matrix is skew-symmetric matrices *)
    Definition is_skew (m : mat 3 3) : Prop := (- m)%M == m\T.

    Lemma is_skew_spec : forall m : mat 3 3,
        is_skew m ->
        let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := m2t_3_3 m in
        (a11 = 0) /\ (a22 = 0) /\ (a33 = 0) /\
          (a12 = -a21)%A /\ (a13 = -a31)%A /\ (a23 = -a32)%A.
    Proof.
      intros. destruct m as [m]; simpl in *. cbv in H. split_intro.
      - epose proof (H 0 0 _ _)%nat. ra.
      - epose proof (H 1 1 _ _)%nat. ra.
      - epose proof (H 2 2 _ _)%nat. ra.
      - epose proof (H 0 1 _ _)%nat. ra.
      - epose proof (H 0 2 _ _)%nat. ra.
      - epose proof (H 1 2 _ _)%nat. ra.
        Unshelve. all: ra.
    Qed.

    (** Convert a vector to its corresponding skew-symmetric matrix *)
    Definition skew (v : cvec 3) : mat 3 3 :=
      let x := v$0 in
      let y := v$1 in
      let z := v$2 in
      l2m _ _ [[0; -z; y]; [z; 0; -x]; [-y; x; 0]]%R.

    (** Convert a skew-symmetric matrix to its corresponding vector *)
    Definition vex (m : mat 3 3) : option (cvec 3) :=
      Some (l2cv 3 [m$2$1; m$0$2; m$1$00]).

    Lemma skew_vex_id : forall (m : mat 3 3), is_skew m -> 
                                         match vex m with
                                         | Some v => skew v == m
                                         | _ => False
                                         end.
    Proof.
      intros [m]. simpl. intros. apply is_skew_spec in H.
      do 5 destruct H as [? H]. lma. ra.
    Qed.

    Lemma vex_skew_id : forall (v : cvec 3),
        match vex (skew v) with
        | Some v' => v == v'
        | _ => False
        end.
    Proof.
      intros. cvec_to_fun. cbv. intros.
      assert (j = 0%nat) by lia. rewrite H1.
      destruct i; try easy.
      destruct i; try easy.
      destruct i; try easy. lia.
    Qed.
    
  End skew.


  (** Rotation about an Arbitrary Vector *)
  Section Rotation_about_arbitrary_vector.

    (** The eigenvalue and eigenvectors of an orthonormal rotation matrix always have 
        one real eigenvalue at λ = 1, and a complex pair λ = cos θ ± i * sin θ where
        θ is the rotation angle. *)
    (* Hypotheses eig_of_SO3 : forall (m : mat 3 3), *)
    (*     orthonormal2 m -> *)
    (*     let (x,e) := eig m in *)
    (*     ? *)

    (** determine an angle and some axis (a vector) of a orthonormal rotation matrix *)
    Definition r2angvec (m : mat 3 3) : R * cvec 3 :=
      (* The eigenvalues are returned on the diagonal of the matrix e,
         and the corresponding eigenvectors are the corresponding columns of x *)
      let (x,e) := eig m in
      (* e(idx,idx) = cosθ +i sinθ *)
      let theta_of_idx (idx : nat) := atan ((e $ idx $ idx).b / (e $ idx $ idx).a) in
      (* the idx-th column of x contain the needed vector, which is the real part *)
      let vec_of_idx (idx : nat) := cvecC_to_cvecR (mat2col x idx) (fun c => c.a) in
      (* find the angle and the vector *)
      if x$0$0 ==? 1
      then (theta_of_idx 1%nat, vec_of_idx 0%nat)
      else (if x$1$1 ==? 1
            then (theta_of_idx 2%nat, vec_of_idx 1%nat)
            else (theta_of_idx 1%nat, vec_of_idx 2%nat)).

    (** Converting from angle and a unit vector to a rotation matrix, 
        i.e. Rodrigues' rotation formula. *)
    Definition angvec2r (θ : R) (axis : cvec 3) : mat 3 3 :=
      let ssm := skew axis in
      (mat1 + (sin θ) c* ssm + (1 - cos θ) c* (ssm * ssm))%M.

  End Rotation_about_arbitrary_vector.

  (** Unit Quaternions *)
  Section UnitQuaternion.

    (** rotation matrix to unit quaternion *)
    (* Definition r2q *)
    Parameter r2q : mat 3 3 -> quat.

    (** unit quaternion to rotation matrix *)
    Parameter q2r : quat -> mat 3 3.

  End UnitQuaternion.

End SO3.
