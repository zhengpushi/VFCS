(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Record-List model
  author    : ZhengPu Shi
  date      : 2021.12

  remark    :

  Ref: 
  1. https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group
  2. https://en.wikipedia.org/wiki/Orthogonal_matrix

  -------------------------- O(n) -----------------------------------
  In mathematics, the orthogonal group in dimension n, denoted O(n), is the 
  group of distance-preserving transformations of a Euclidean space of dimension
  n that preserve a fixed point, where the group operation is given by composing
  transformations. 

  The orthogonal group is sometimes called the general orthogonal group, by 
  analogy with the general linear group. Equivalently, it is the group of 
  n × n matrices, where the group operation is given by matrix multiplication 
  (an orthogonal matrix is a real matrix whose inverse equals its transpose). 

  By extension, for any field F, an n × n matrix with entries in F such that its 
  inverse equals its transpose is called an orthogonal matrix over F. 
  The n × n orthogonal matrices form a subgroup, denoted O(n,F), of the general 
  linear group GL(n,F); that is 
         O(n,F) = {Q ∈ GL(n,F) ∣ Q\T * Q = Q * Q\T = I}.
  
  -------------------------- O(3) -----------------------------------
  Every rotation maps an orthonormal basis of R^3 to another orthonormal basis.
  Like any linear transformation of finite-dimensional vector spaces, a rotation 
  can always be represented by a matrix.

  Let R be a given rotation. With respect to the standard basis e1, e2, e3 of R^3 
  the columns of R are given by (Re1, Re2, Re3). Since the standard basis is 
  orthonormal, and since R preserves angles and length, the columns of R form 
  another orthonormal basis. This orthonormality condition can be expressed in 
  the form 
     R\T * R = R * R\T = I,
  where R\T denotes the transpose of R and I is the 3 × 3 identity matrix. 
  Matrices for which this property holds are called orthogonal matrices.

  The group of all 3 × 3 orthogonal matrices is denoted O(3), and consists of all 
  proper and improper rotations.

  In addition to preserving length, proper rotations must also preserve 
  orientation. 
  T matrix will preserve or reverse orientation according to whether the 
  determinant of the matrix is positive or negative. 
  For an orthogonal matrix R, note that "det R\T = det R" implies 
  "(det R)^2 = 1", so that "det R = ±1".

  The subgroup of orthogonal matrices with determinant +1 is called the special 
  orthogonal group, denoted SO(3). 
  Thus every rotation can be represented uniquely by an orthogonal matrix with unit 
  determinant. Moreover, since composition of rotations corresponds to matrix 
  multiplication, the rotation group is isomorphic to the special orthogonal group 
  SO(3).

  Improper rotations correspond to orthogonal matrices with determinant −1, and 
  they do not form a group because the product of two improper rotations is a 
  proper rotation. 

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
  (1) T = A\T        对称阵       T = A\H         自伴阵
  (2) T = -A\T       斜称阵       T = -A\H        斜伴阵
  (3) AA\T = E       正交阵       AA\H = E        酉矩阵
  (4)                            T A\H=A\H T      正规矩阵
  其中，(1),(2),(3)都是正规矩阵

  正规矩阵的一个定理：每个 n*n 正规矩阵A，都有一个由对应于特征值λ1,...,λn的特征向量
  组成的完全正交基 x1,...,xn。
  若设 U = (x1,...,xn)，则 U 是酉矩阵，并且有
  U^{-1} T U = 对角阵 {λ1,...,λn}

  正交矩阵的应用（旋转）：若一个 n*n 实矩阵A是正交的，则其特征值等于
  ±1 或 e^{±iϕ}成对出现（ϕ是实数）。
  
  2. 特征值、特征向量、矩阵的谱
  (1) 方阵A，使方程 T x = λ x 有非零解时，λ(复数)称一个特征值，x称对应的特征向量
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


Require Export Hierarchy.
Require Export Matrix.
Require Export MatrixDet.
Require Export MatrixInv.

Generalizable Variable A Aadd Aopp Amul Ainv.

Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** ** Orthogonal matrix *)
Section morth.
  Context `{HField:Field}.

  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := (@mmul _ Aadd Azero Amul _ _ _) : mat_scope.
  Notation smat n := (smat A n).
  Notation mat1 n := (@mat1 _ Azero Aone n).
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone _).
  Notation minvertible := (@minvertible _ Aadd Azero Amul Aone _).
  Notation "M \-1" := (@minvAM _ Aadd Azero Aopp Amul Aone Ainv _ M) : mat_scope.

  (** An orthogonal matrix *)
  Definition morth {n} (M : smat n) : Prop := M\T * M = mat1 n.

  (** orthogonal M -> invertible M *)
  Lemma morth_invertible : forall {n} (M : smat n),
      morth M -> minvertible M.
  Proof. intros. hnf in *. exists (M\T). auto. Qed.

  (** orthogonal M -> M\-1 = M\T *)
  Lemma morth_imply_inv_eq_trans : forall {n} (M : smat n),
      morth M -> M\-1 = M\T.
  Proof. intros. red in H. apply AM_mmul_eq1_iff_minv_r in H. auto. Qed.

  (** M\-1 = M\T -> orthogonal M *)
  Lemma minv_eq_trans_imply_morth : forall {n} (M : smat n),
      M\-1 = M\T -> morth M.
  Proof. intros. apply AM_mmul_eq1_iff_minv_r in H. auto. Qed.

  (** orthogonal M <-> M\T * M = mat1 *)
  Lemma morth_iff_mul_trans_l : forall {n} (M : smat n),
      morth M <-> M\T * M = mat1 n.
  Proof. intros. red. auto. Qed.

  (** orthogonal M <-> M * M\T = mat1 *)
  Lemma morth_iff_mul_trans_r : forall {n} (M : smat n),
      morth M <-> M * M\T = mat1 n.
  Proof.
    intros. split; intros H.
    - apply AM_mmul_eq1_iff_minv_r in H. rewrite <- H. apply AM_mmul_minv_r.
    - red. apply AM_mmul_eq1_iff_minv_l in H. rewrite <- H. apply AM_mmul_minv_l.
  Qed.

  (** orthogonal mat1 *)
  Lemma morth_mat1 : forall {n}, morth (mat1 n).
  Proof. intros. red. rewrite mtrans_mat1, mmul_1_r. easy. Qed.

  (** orthogonal M -> orthogonal p -> orthogonal (m * p) *)
  Lemma morth_mul : forall {n} (M N : smat n),
      morth M -> morth N -> morth (M * N).
  Proof.
    intros. red. red in H, H0. rewrite mtrans_mmul.
    rewrite mmul_assoc. rewrite <- (mmul_assoc _ M).
    rewrite H. rewrite mmul_1_l. rewrite H0. easy.
  Qed.

  (** orthogonal M -> orthogonal M\T *)
  Lemma morth_mtrans : forall {n} (M : smat n), morth M -> morth (M\T).
  Proof.
    intros. red. rewrite mtrans_mtrans.
    apply morth_iff_mul_trans_r in H. auto.
  Qed.

  (** orthogonal M -> orthogonal M\-1 *)
  Lemma morth_minv : forall {n} (M : smat n), morth M -> morth (M\-1).
  Proof.
    intros. red.
    rewrite morth_imply_inv_eq_trans; auto. rewrite mtrans_mtrans.
    apply morth_iff_mul_trans_r; auto.
  Qed.

  (** orthogonal M -> |M| = ± 1 *)
  Lemma morth_mdet : forall {n} (M : smat n),
      morth M -> (mdet M = Aone \/ mdet M = (- Aone)%A).
  Proof.
    intros. unfold morth in H.
    pose proof (mdet_mmul (M\T) M). rewrite H in H0.
    rewrite mdet_mtrans,mdet_mat1 in H0.
    symmetry in H0. apply ring_sqr_eq1_imply_1_neg1 in H0. auto.
  Qed.

End morth.


(* ======================================================================= *)
(** ** O(n): General Orthogonal Group, General Linear Group *)
(* https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group *)
Section GOn.
  Context `{HField:Field}.
  
  Notation smat n := (smat A n).
  Notation mat1 n := (@mat1 _ Azero Aone n).
  Infix "*" := (@mmul _ Aadd Azero Amul _ _ _) : mat_scope.
  Notation morth := (@morth _ Aadd Azero Amul Aone).
  Notation "M \-1" := (@minvAM _ Aadd Azero Aopp Amul Aone Ainv _ M) : mat_scope.

  
  (** The set of GOn *)
  Record GOn {n: nat} := {
      GOn_mat :> smat n;
      GOn_orth : morth GOn_mat
    }.
  
  Arguments Build_GOn {n}.

  (** Two GOn are equal, only need the matrix are equal *)
  Lemma GOn_eq_iff : forall {n} (x1 x2 : @GOn n), GOn_mat x1 = GOn_mat x2 -> x1 = x2.
  Proof.
    intros. destruct x1,x2; simpl in H.
    subst. f_equal. apply proof_irrelevance.
  Qed.

  (** Multiplication of elements in GOn *)
  Definition GOn_mul {n} (x1 x2 : @GOn n) : @GOn n.
    refine (Build_GOn (x1 * x2) _).
    destruct x1 as [M1 Horth1], x2 as [M2 Horth2]. simpl.
    apply morth_mul; auto.
  Defined.

  (** Identity element in GOn *)
  Definition GOn_1 {n} : @GOn n.
    refine (Build_GOn (mat1 n) _).
    apply morth_mat1.
  Defined.

  (** GOn_mul is associative *)
  Lemma GOn_mul_assoc : forall n, Associative (@GOn_mul n).
  Proof.
    intros. constructor; intros. apply GOn_eq_iff; simpl. apply mmul_assoc.
  Qed.

  (** GOn_1 is left-identity-element of GOn_mul operation *)
  Lemma GOn_mul_id_l : forall n, IdentityLeft (@GOn_mul n) GOn_1.
  Proof.
    intros. constructor; intros. apply GOn_eq_iff; simpl. apply mmul_1_l.
  Qed.
  
  (** GOn_1 is right-identity-element of GOn_mul operation *)
  Lemma GOn_mul_id_r : forall n, IdentityRight (@GOn_mul n) GOn_1.
  Proof.
    intros. constructor; intros. apply GOn_eq_iff; simpl. apply mmul_1_r.
  Qed.

  (** <GOn, +, 1> is a monoid *)
  Instance Monoid_GOn : forall n, Monoid (@GOn_mul n) GOn_1.
  Proof.
    intros. constructor; constructor; intros.
    apply GOn_mul_assoc.
    apply GOn_mul_id_l.
    apply GOn_mul_id_r.
    apply GOn_mul_assoc.
  Qed.

  (** Inverse operation of multiplication in GOn *)
  Definition GOn_inv {n} (x : @GOn n) : @GOn n.
    refine (Build_GOn (x\T) _). destruct x as [M Horth]. simpl.
    apply morth_mtrans; auto.
  Defined.

  (** GOn_inv is left-inversion of <GOn_mul,GOn_1> *)
  Lemma GOn_mul_inv_l : forall n, InverseLeft (@GOn_mul n) GOn_1 GOn_inv.
  Proof.
    intros. constructor; intros. apply GOn_eq_iff; simpl. apply a.
  Qed.

  (** GOn_inv is right-inversion of <GOn_mul,GOn_1> *)
  Lemma GOn_mul_inv_r : forall n, InverseRight (@GOn_mul n) GOn_1 GOn_inv.
  Proof.
    intros. constructor; intros. apply GOn_eq_iff; simpl.
    apply morth_iff_mul_trans_r. apply a.
  Qed.

  (** <GOn, +, 1, /s> is a group *)
  Theorem Group_GOn : forall n, Group (@GOn_mul n) GOn_1 GOn_inv.
  Proof.
    intros. constructor.
    apply Monoid_GOn.
    apply GOn_mul_inv_l.
    apply GOn_mul_inv_r.
  Qed.
  
  (* ======================================================================= *)
  (** ** Extract the properties of GOn to its carrier *)

  (* Tips: this lemma is useful to get the inversion matrix *)
  
  (** M\-1 = M\T *)
  Lemma GOn_imply_inv_eq_trans : forall {n} (M : @GOn n), M\-1 = M\T.
  Proof.
    intros. destruct M as [M H]. simpl in *.
    rewrite morth_imply_inv_eq_trans; auto.
  Qed.

End GOn.


(* ======================================================================= *)
(** ** SO(n): Special Orthogonal Group, Rotation Group *)
(* https://en.wikipedia.org/wiki/Orthogonal_group#Special_orthogonal_group *)
Section SOn.
  Context `{HField:Field}.
  (* Add Field field_inst : (make_field_theory HField). *)
  
  Notation smat n := (smat A n).
  Notation mat1 n := (@mat1 _ Azero Aone n).
  Infix "*" := (@mmul _ Aadd Azero Amul _ _ _) : mat_scope.
  Notation morth := (@morth _ Aadd Azero Amul Aone).
  Notation "M \-1" := (@minvAM _ Aadd Azero Aopp Amul Aone Ainv _ M) : mat_scope.
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone _).
  Notation GOn := (@GOn _ Aadd Azero Amul Aone).
  Notation GOn_mat := (@GOn_mat _ Aadd Azero Amul Aone _).
  
  (** The set of SOn *)
  Record SOn {n: nat} := {
      SOn_GOn :> @GOn n;
      SOn_det1 : mdet SOn_GOn = Aone
    }.

  Arguments Build_SOn {n}.

  (* 这个证明失败了，所以下面分解为两个步骤 *)
  Lemma SOn_eq_iff_try : forall {n} (x1 x2 : @SOn n),
      GOn_mat x1 = GOn_mat x2 -> x1 = x2.
  Proof.
    intros.
    destruct x1 as [[M1 Horth1] Hdet1], x2 as [[M2 Horth2] Hdet2]; simpl in *.
    subst. f_equal.             (* Tips: f_equal 不能正确的处理 Record *)
    - intros. rewrite H1. f_equal.
  Abort.
  
  (** Two SOn are equal, only need the GOn are equal *)
  Lemma SOn_eq_iff_step1 : forall {n} (x1 x2 : @SOn n),
      SOn_GOn x1 = SOn_GOn x2 -> x1 = x2.
  Proof.
    intros. destruct x1,x2. simpl in *. subst. f_equal. apply proof_irrelevance.
  Qed.

  (** Two SOn are equal, only need the matrix are equal *)
  Lemma SOn_eq_iff : forall {n} (x1 x2 : @SOn n), GOn_mat x1 = GOn_mat x2 -> x1 = x2.
  Proof.
    intros. apply SOn_eq_iff_step1. simpl in *.
    destruct x1,x2. simpl in *. apply GOn_eq_iff. auto.
  Qed.

  Definition SOn_mul {n} (s1 s2 : @SOn n) : @SOn n.
    refine (Build_SOn (GOn_mul s1 s2) _).
    destruct s1 as [[M1 Horth1] Hdet1], s2 as [[M2 Horth2] Hdet2]. simpl in *.
    rewrite mdet_mmul. rewrite Hdet1,Hdet2. monoid.
  Defined.

  Definition SOn_1 {n} : @SOn n.
    refine (Build_SOn (GOn_1) _).
    apply mdet_mat1.
  Defined.

  (** SOn_mul is associative *)
  Lemma SOn_mul_assoc : forall n, Associative (@SOn_mul n).
  Proof.
    intros. constructor; intros. apply SOn_eq_iff; simpl. apply mmul_assoc.
  Qed.

  (** SOn_1 is left-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_l : forall n, IdentityLeft SOn_mul (@SOn_1 n).
  Proof.
    intros. constructor; intros. apply SOn_eq_iff; simpl. apply mmul_1_l.
  Qed.
  
  (** SOn_1 is right-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_r : forall n, IdentityRight SOn_mul (@SOn_1 n).
  Proof.
    intros. constructor; intros. apply SOn_eq_iff; simpl. apply mmul_1_r.
  Qed.
  
  (** <SOn, +, 1> is a monoid *)
  Lemma Monoid_SOn : forall n, Monoid (@SOn_mul n) SOn_1.
  Proof.
    intros. constructor; constructor; intros.
    apply SOn_mul_assoc.
    apply SOn_mul_id_l.
    apply SOn_mul_id_r.
    apply SOn_mul_assoc.
  Qed.

  Definition SOn_inv {n} (x : @SOn n) : @SOn n.
    refine (Build_SOn (GOn_inv x) _).
    destruct x as [[M Horth] Hdet]; simpl.
    rewrite mdet_mtrans. auto.
  Defined.

  (** SOn_inv is left-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_l : forall n, InverseLeft SOn_mul SOn_1 (@SOn_inv n).
  Proof.
    intros. constructor; intros. apply SOn_eq_iff; simpl.
    destruct a. apply SOn_GOn0.
  Qed.
  

  (** SOn_inv is right-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_r : forall n, InverseRight SOn_mul SOn_1 (@SOn_inv n).
  Proof.
    intros. constructor; intros. apply SOn_eq_iff; simpl.
    apply morth_iff_mul_trans_r. destruct a. apply SOn_GOn0.
  Qed.

  (** <SOn, +, 1, /s> is a group *)
  Theorem Group_SOn : forall n, Group (@SOn_mul n) SOn_1 SOn_inv.
  Proof.
    intros. constructor.
    apply Monoid_SOn.
    apply SOn_mul_inv_l.
    apply SOn_mul_inv_r.
  Qed.

  (* ======================================================================= *)
  (** ** Extract the properties of SOn to its carrier *)

  (** M\-1 = M\T *)
  Lemma SOn_inv_eq_trans : forall {n} (M : @SOn n), M\-1 = M\T.
  Proof.
    intros. destruct M as [[M Horth] Hdet]; simpl.
    apply morth_imply_inv_eq_trans. auto.
  Qed.

  (** M\T * M = mat1 *)
  Lemma SOn_mul_trans_l_eq1 : forall {n} (M : @SOn n), M\T * M = mat1 n.
  Proof. intros. rewrite <- SOn_inv_eq_trans. apply AM_mmul_minv_l. Qed.

  (** M * M\T = mat1 *)
  Lemma SOn_mul_trans_r_eq1 : forall {n} (M : @SOn n), M * M\T = mat1 n.
  Proof. intros. rewrite <- SOn_inv_eq_trans. apply AM_mmul_minv_r. Qed.

End SOn.

