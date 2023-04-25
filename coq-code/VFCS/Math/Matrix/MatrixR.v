(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on R.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export RExt.
Require Import MatrixModule.


(* ======================================================================= *)
(** ** Matrix theory come from common implementations *)

Module Export FieldMatrixTheoryR := FieldMatrixTheory FieldElementTypeR.

Open Scope R_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** ** Matrix theory applied to this type *)

(** *** Orthogonal matrix *)
Section OrthogonalMatrix.

  (*
  Refernece: https://en.wikipedia.org/wiki/3D_rotation_group

  Every rotation maps an orthonormal basis of R^3 to another orthonormal basis.
  Like any linear transformation of finite-dimensional vector spaces, a rotation 
  can always be represented by a matrix.

  Let R be a given rotation. With respect to the standard basis e1, e2, e3 of R^3 
  the columns of R are given by (Re1, Re2, Re3). Since the standard basis is 
  orthonormal, and since R preserves angles and length, the columns of R form 
  another orthonormal basis. This orthonormality condition can be expressed in the 
  form 
       R^{T} R = R R^{T} = I,
  where RT denotes the transpose of R and I is the 3 × 3 identity matrix. 
  Matrices for which this property holds are called orthogonal matrices.

  The group of all 3 × 3 orthogonal matrices is denoted O(3), and consists of all 
  proper and improper rotations.

  In addition to preserving length, proper rotations must also preserve orientation. 
  A matrix will preserve or reverse orientation according to whether the determinant 
  of the matrix is positive or negative. For an orthogonal matrix R, note that 
  det R^{T} = det R implies (det R)^2 = 1, so that det R = ±1. 
  The subgroup of orthogonal matrices with determinant +1 is called the special 
  orthogonal group, denoted SO(3). 
  Thus every rotation can be represented uniquely by an orthogonal matrix with unit 
  determinant. Moreover, since composition of rotations corresponds to matrix 
  multiplication, the rotation group is isomorphic to the special orthogonal group 
  SO(3).

  Improper rotations correspond to orthogonal matrices with determinant −1, and they 
  do not form a group because the product of two improper rotations is a proper 
  rotation. 

  ----------- 中文笔记 ---------------
  Orthogonal: 正交的，一般用于描述一组基是相互正交的（垂直的）
  Orthonormal Basic: 标准正交基，两两正交，并且单个向量具有单位长度。
  Gram-Schmidt: 施密特正交化。以2维为例，该算法保持r1不变，r3的改变最多。
  有一种无偏差的递增正交化算法，不偏向特定轴，需要多次迭代（比如10次），然后用1次
    标准的Gram-Schmidt算法来保证完全正交。
  O(n): Orthogonal Group 正交群（保距，行列式为±1）
  SO(n): Special Orthogonal Group 特殊正交群（保持手性，行列式为1）
    Proper rotation: 正确的旋转 (行列式为1)
    Improper rotation: 错误的旋转（行列式为-1）, rotation-reflect, 旋转反射，瑕旋转
  ----------------------
  补充一些理论：
  1. 特殊矩阵：对称（自伴）、斜对称（斜伴）、正交（酉）、正规矩阵
      实矩阵                      复矩阵
      条件           名称         条件            名称
  (1) A = A\T        对称阵       A = A\H         自伴阵
  (2) A = -A\T       斜称阵       A = -A\H        斜伴阵
  (3) AA\T = E       正交阵       AA\H = E        酉矩阵
  (4)                            A A\H=A\H A      正规矩阵
  其中，(1),(2),(3)都是正规矩阵

  正规矩阵的一个定理：每个 n*n 正规矩阵A，都有一个由对应于特征值λ1,...,λn的特征向量
  组成的完全正交基 x1,...,xn。
  若设 U = (x1,...,xn)，则 U 是酉矩阵，并且有
  U^{-1} A U = 对角阵 {λ1,...,λn}

  正交矩阵的应用（旋转）：若一个 n*n 实矩阵A是正交的，则其特征值等于
  ±1 或 e^{±iϕ}成对出现（ϕ是实数）。
  
  2. 特征值、特征向量、矩阵的谱
  (1) 方阵A，使方程 A x = λ x 有非零解时，λ(复数)称一个特征值，x称对应的特征向量
  (2) A的所有特征值的集合称为A的谱 σ(A)，A的特征值的绝对值的最大值称为A的谱半径，记做 r(A)
  (3) 特征方程：det(A-λE)=0，其解是A的特征值λ，λ的重数称为代数重数。
  (4) 设矩阵U是正交的（酉的），U的谱由数 e^{±iϕ} 组成，
      变换 x' = U x 对应于笛卡尔坐标系中的正向旋转，旋转角ϕ
      x1' = x1 * cos ϕ + x2 * sin ϕ
      y1' = - x1 * sin ϕ + x2 * cos ϕ
  (5) 谱定理
      (i) 自伴矩阵的谱在实直线上
      (ii) 斜伴矩阵的谱在虚轴上
      (iii) 酉矩阵的谱在单位圆上

  3. 正交性

   *)

  (** A real square matrix m is an orthogonal matrix *)
  Definition morthogonal {n} (m : smat n) : Prop := m\T * m == mat1.

  (** orthogonal m -> invertible m *)
  Lemma morthogonal_invertible : forall {n} (m : smat n),
      morthogonal m -> minvertible m.
  Proof. intros. hnf in *. exists (m\T). auto. Qed.

  (** orthogonal m -> m⁻¹ = m\T *)
  Lemma morthogonal_inv_eq_trans : forall {n} (m : smat n),
      morthogonal m -> m⁻¹ == m\T.
  Proof. intros. red in H. apply mmul_eq1_imply_minv_r in H. auto. Qed.

  (** orthogonal m <-> m\T * m = mat1 *)
  Lemma morthogonal_iff_mul_trans_l : forall {n} (m : smat n),
      morthogonal m <-> m\T * m == mat1.
  Proof. intros. red. auto. Qed.

  (** orthogonal m <-> m * m\T = mat1 *)
  Lemma morthogonal_iff_mul_trans_r : forall {n} (m : smat n),
      morthogonal m <-> m * m\T == mat1.
  Proof.
    intros. split; intros H.
    - apply mmul_eq1_imply_minv_r in H. rewrite <- H. apply mmul_minv_r.
    - red. apply mmul_eq1_imply_minv_l in H. rewrite <- H. apply mmul_minv_l.
  Qed.

  (** orthogonal mat1 *)
  Lemma morthogonal_1 : forall {n}, morthogonal (@mat1 n).
  Proof. intros. red. rewrite mtrans_1, mmul_1_r. easy. Qed.

  (** orthogonal m -> orthogonal p -> orthogonal (m * p) *)
  Lemma morthogonal_mul : forall {n} (m p : smat n),
      morthogonal m -> morthogonal p -> morthogonal (m * p).
  Proof.
    intros. red. red in H, H0. rewrite mtrans_mul.
    rewrite mmul_assoc. rewrite <- (mmul_assoc _ m).
    rewrite H. rewrite mmul_1_l. rewrite H0. easy.
  Qed.

  (** orthogonal m -> orthogonal m\T *)
  Lemma morthogonal_trans : forall {n} (m : smat n), morthogonal m -> morthogonal (m\T).
  Proof.
    intros. red. rewrite mtrans_trans. apply morthogonal_iff_mul_trans_r in H. auto.
  Qed.

  (** orthogonal m -> orthogonal m⁻¹ *)
  Lemma morthogonal_inv : forall {n} (m : smat n), morthogonal m -> morthogonal (m⁻¹).
  Proof.
    intros. red. rewrite morthogonal_inv_eq_trans; auto.
    rewrite mtrans_trans. apply morthogonal_iff_mul_trans_r in H. auto.
  Qed.

  (** orthogonal m -> |m| = ± 1 *)
  Lemma morthogonal_det : forall {n} (m : smat n),
      morthogonal m -> (det m = 1 \/ det m = -1).
  Proof.
    intros. red in H.
    assert (det (m\T * m) = @det n mat1). { rewrite H. auto. }
    rewrite det_mul in H0. rewrite det_trans, det_1 in H0.
    apply Rsqr_eq1 in H0. auto.
  Qed.

End OrthogonalMatrix.

(** *** SO(n): Special Orthogonal Group *)
Section SOn.

  (** The set of SOn *)
  Record SOn (n: nat) := {
      SOn_mat :> smat n;
      SOn_props : morthogonal SOn_mat /\ det SOn_mat = 1
    }.

  Definition SOn_eq {n} (s1 s2 : SOn n) : Prop := SOn_mat _ s1 == SOn_mat _ s2.

  Definition SOn_mul {n} (s1 s2 : SOn n) : SOn n.
    refine (Build_SOn n (s1 * s2) _).
    destruct s1 as [s1 [H1 H1']], s2 as [s2 [H2 H2']]. simpl. split.
    - apply morthogonal_mul; auto.
    - rewrite det_mul. rewrite H1', H2'. ring.
  Defined.

  Definition SOn_1 {n} : SOn n.
    refine (Build_SOn n mat1 _). split.
    apply morthogonal_1. apply det_1.
  Defined.

  Definition SOn_inv {n} (s : SOn n) : SOn n.
    refine (Build_SOn n (s\T) _). destruct s as [s [H1 H2]]. simpl. split.
    apply morthogonal_trans; auto. rewrite det_trans. auto.
  Defined.

  (** SOn_eq is equivalence relation *)
  Lemma SOn_eq_equiv : forall n, Equivalence (@SOn_eq n).
  Proof.
    intros. unfold SOn_eq. constructor; hnf; intros; try easy.
    rewrite H; easy.
  Qed.

  (** SOn_mul is a proper morphism respect to SOn_eq *)
  Lemma SOn_mul_proper : forall n, Proper (SOn_eq ==> SOn_eq ==> SOn_eq) (@SOn_mul n).
  Proof. unfold SOn_eq in *. simp_proper. intros. simpl. rewrite H,H0. easy. Qed.

  (** SOn_inv is a proper morphism respect to SOn_eq *)
  Lemma SOn_inv_proper : forall n, Proper (SOn_eq ==> SOn_eq) (@SOn_inv n).
  Proof. unfold SOn_eq in *. simp_proper. intros. simpl. rewrite H. easy. Qed.

  (** SOn_mul is associative *)
  Lemma SOn_mul_assoc : forall n, Associative SOn_mul (@SOn_eq n).
  Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_assoc. Qed.

  (** SOn_1 is left-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_l : forall n, IdentityLeft SOn_mul SOn_1 (@SOn_eq n).
  Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_1_l. Qed.
    
  (** SOn_1 is right-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_r : forall n, IdentityRight SOn_mul SOn_1 (@SOn_eq n).
  Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply mmul_1_r. Qed.

  (** SOn_inv is left-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_l : forall n, InverseLeft SOn_mul SOn_1 SOn_inv (@SOn_eq n).
  Proof. unfold SOn_eq. intros. constructor. intros; simpl. apply a. Qed.

  (** SOn_inv is right-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_r : forall n, InverseRight SOn_mul SOn_1 SOn_inv (@SOn_eq n).
  Proof.
    unfold SOn_eq. intros. constructor. intros; simpl.
    apply morthogonal_iff_mul_trans_r. apply a.
  Qed.
    
  (** <SOn, +, 1> is a monoid *)
  Lemma Monoid_SOn : forall n, Monoid (@SOn_mul n) SOn_1 SOn_eq.
  Proof.
    intros. constructor.
    - apply SOn_mul_proper.
    - apply SOn_eq_equiv.
    - apply SOn_mul_assoc.
    - apply SOn_mul_id_l.
    - apply SOn_mul_id_r.
  Qed.

  (** <SOn, +, 1, /s> is a group *)
  Theorem Group_SOn : forall n, Group (@SOn_mul n) SOn_1 SOn_inv SOn_eq.
  Proof.
    intros. constructor.
    - apply Monoid_SOn.
    - apply SOn_mul_inv_l.
    - apply SOn_mul_inv_r.
    - apply SOn_mul_proper.
    - apply SOn_inv_proper.
  Qed.

End SOn.

(** *** SO(3): special orthogonal group *)
Section SO3.

  (** If a matrix is SO3? *)
  Definition so3 (m : smat 3) : Prop := 
    let so3_mul_unit : Prop := m\T * m == mat1 in
    let so3_det : Prop := (det3 m) = 1 in
    so3_mul_unit /\ so3_det.

End SO3.



(* ======================================================================= *)
(** ** Usage demo *)

Section test.
  Let l1 := [[1;2];[3;4]].
  Let m1 := l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Ropp m1). *)
  (* Compute m2l (m1 * m1). *)

  Variable a11 a12 a21 a22 : R.
  Variable f : R -> R.
  Let m2 := l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.       (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f m2).       (* = [[f a11; f a12]; [f a21; f a22]] *) *)
  (* Compute m2l (m2 * m2). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

  (** Outer/inner product of two vectors *)
  Variables a1 a2 a3 b1 b2 b3 : A.
  Let m10 := l2m 3 1 [[a1];[a2];[a3]].
  Let m11 := l2m 1 3 [[b1;b2;b3]].
  (* Compute m2l (m10 * m11). *)
  (* Compute m2l (m11 * m10). *)

  (** mmul_sub_distr_r *)
  Goal forall r c s (m1 m2 : mat r c) (m3 : mat c s), (m1 - m2) * m3 == m1 * m3 - m2 * m3.
    intros. rewrite mmul_sub_distr_r. easy. Qed.

  (* test rewriting *)
  Goal forall r c (m1 m2 : mat r c) x, m1 == m2 -> x c* m1 == x c* m2.
  Proof. intros. f_equiv. easy. Qed.

  Goal forall r c (m1 m2 m3 m4 : mat r c), m1 == m2 -> m3 == m4 -> m1 - m3 == m2 - m4.
  Proof. clear. intros. f_equiv. easy. easy. Qed.

End test.

Section test_monoid.
  Goal forall r c (m1 m2 : mat r c), mat0 + m1 == m1.
    monoid_simp. Qed.
End test_monoid.


Section Example4CoordinateSystem.
  Variable ψ θ φ: R.
  Let Rx := mk_mat_3_3 1 0 0 0 (cos φ) (sin φ) 0 (-sin φ) (cos φ).
  Let Ry := mk_mat_3_3 (cos θ) 0 (-sin θ) 0 1 0 (sin θ) 0 (cos θ).
  Let Rz := mk_mat_3_3 (cos ψ) (sin ψ) 0 (-sin ψ) (cos ψ) 0 0 0 1.
  Let Rbe := mk_mat_3_3
    (cos θ * cos ψ) (cos ψ * sin θ * sin φ - sin ψ * cos φ)
    (cos ψ * sin θ * cos φ + sin φ * sin ψ) (cos θ * sin ψ)
    (sin ψ * sin θ * sin φ + cos ψ * cos φ)
    (sin ψ * sin θ * cos φ - cos ψ * sin φ)
    (-sin θ) (sin φ * cos θ) (cos φ * cos θ).
  Lemma Rbe_ok : (Rbe == Rz\T * Ry\T * Rx\T).
  Proof. lma. Qed.
    
End Example4CoordinateSystem.


(** example for symbol matrix *)
Module Exercise_Ch1_Symbol.

  (* for better readibility *)
  Notation "0" := R0.
  Notation "1" := R1.
  Notation "2" := (R1 + R1)%R.
  Notation "3" := (R1 + (R1 + R1))%R.
  Notation "4" := ((R1 + R1) * (R1 + R1))%R.
  
  Example ex6_1 : forall a b : R,
      let m := mk_mat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1 in
      (det m = (a - b)^3)%R.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_2 : forall a b x y z : A,
      let m1 := mk_mat_3_3
                  (a*x+b*y) (a*y+b*z) (a*z+b*x)
                  (a*y+b*z) (a*z+b*x) (a*x+b*y)
                  (a*z+b*x) (a*x+b*y) (a*y+b*z) in
      let m2 := mk_mat_3_3 x y z y z x z x y in
      (det m1 = (a^3 + b^3) * det m2)%R.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_3 : forall a b e d : A,
      let m := mk_mat_4_4
                 (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
                 (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
                 (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
                 (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2) in
      det m = 0.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_4 : forall a b e d : A,
      let m := mk_mat_4_4
                 1 1 1 1
                 a b e d
                 (a^2) (b^2) (e^2) (d^2)
                 (a^4) (b^4) (e^4) (d^4) in
      (det m = (a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%R.
  Proof.
    intros. cbv. ring.
  Qed.
  
  (* (** 6.(5), it is an infinite structure, need more work, later... *) *)

End Exercise_Ch1_Symbol.
