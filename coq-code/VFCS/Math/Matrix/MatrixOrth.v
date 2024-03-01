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
  在数学中，n维正交群，记作O(n)，是保持欧几里得空间距离的变换群，这些
  变换保持一个固定点不变，群操作是通过组合变换来定义的。

  The orthogonal group is sometimes called the general orthogonal group, by 
  analogy with the general linear group. Equivalently, it is the group of 
  n × n matrices, where the group operation is given by matrix multiplication 
  (an orthogonal matrix is a real matrix whose inverse equals its transpose). 
  正交群有时被称为一般正交群，这是与一般线性群进行类比的结果。等价地，
  它是n×n矩阵的群，其中群操作是通过矩阵乘法来定义的（正交矩阵是一个实
  矩阵，其逆等于其转置）。

  By extension, for any field F, an n × n matrix with entries in F such that its 
  inverse equals its transpose is called an orthogonal matrix over F. 
  The n × n orthogonal matrices form a subgroup, denoted O(n,F), of the general 
  linear group GL(n,F); that is 
  通过扩展，对于任何域F，一个n×n矩阵，其元素在F中，且其逆等于其转置，
  被称为F上的正交矩阵。n×n正交矩阵形成了一般线性群GL(n,F)的一个子群，
  记作O(n,F)；也就是说，

         O(n,F) = {Q ∈ GL(n,F) ∣ Q\T * Q = Q * Q\T = I}.
  
  -------------------------- O(3) -----------------------------------
  Every rotation maps an orthonormal basis of R^3 to another orthonormal basis.
  Like any linear transformation of finite-dimensional vector spaces, a rotation 
  can always be represented by a matrix.
  每个旋转都将R3的一个正交基映射到另一个正交基。与有限维向量空间的任何
  线性变换一样，旋转总是可以通过矩阵来表示。

  Let R be a given rotation. With respect to the standard basis e1, e2, e3 of R^3 
  the columns of R are given by (Re1, Re2, Re3). Since the standard basis is 
  orthonormal, and since R preserves angles and length, the columns of R form 
  another orthonormal basis. This orthonormality condition can be expressed in 
  the form 
  设R是一个给定的旋转。关于R3的标准基e1​,e2​,e3​，R的列由(Re1​,Re2​,Re3​)给
  出。由于标准基是正交的，并且R保持角度和长度不变，因此R的列形成另一个
  正交基。这个正交性条件可以表示为

     R\T * R = R * R\T = I,

  where R\T denotes the transpose of R and I is the 3 × 3 identity matrix. 
  Matrices for which this property holds are called orthogonal matrices.
  其中R\T表示R的转置，I是3×3单位矩阵。满足这个性质的矩阵被称为正交矩阵。

  The group of all 3 × 3 orthogonal matrices is denoted O(3), and consists of all 
  proper and improper rotations.
  所有3×3正交矩阵的群记作O(3)，由所有适当和不适当的旋转组成。

  In addition to preserving length, proper rotations must also preserve 
  orientation. 
  T matrix will preserve or reverse orientation according to whether the 
  determinant of the matrix is positive or negative. 
  For an orthogonal matrix R, note that "det R\T = det R" implies 
  "(det R)^2 = 1", so that "det R = ±1".
  除了保持长度外，适当的旋转还必须保持方向。一个矩阵将根据矩阵的行列式
  是正是负来保持或反转方向。对于正交矩阵R，注意“det R\T = det R”意味
  着“(det R)^2=1”，所以“detR=±1”。

  The subgroup of orthogonal matrices with determinant +1 is called the special 
  orthogonal group, denoted SO(3). 
  Thus every rotation can be represented uniquely by an orthogonal matrix with unit 
  determinant. Moreover, since composition of rotations corresponds to matrix 
  multiplication, the rotation group is isomorphic to the special orthogonal group 
  SO(3).
  行列式为+1的正交矩阵的子群被称为特殊正交群，记作SO(3)。因此，每个旋
  转都可以由具有单位行列式的正交矩阵唯一表示。此外，由于旋转的组合对应
  于矩阵乘法，旋转群与特殊正交群SO(3)是同构的。

  Improper rotations correspond to orthogonal matrices with determinant −1, and 
  they do not form a group because the product of two improper rotations is a 
  proper rotation. 
  不适当的旋转对应于行列式为−1的正交矩阵，并且它们不形成一个群，因为两
  个不适当旋转的乘积是一个适当的旋转。


  ----------- 中文笔记 ---------------
  Orthogonal: 正交的，一般用于描述一组基是相互正交的（垂直的）
  Orthonormal Basic: 标准正交基，不仅相互正交，而且每个向量具有单位长度。
  Gram-Schmidt: 施密特正交化。以2维为例，该算法保持r1不变，r3的改变最多。
    有一种无偏差的递增正交化算法，不偏向特定轴，需要多次迭代（比如10次），然后用1次
    标准的Gram-Schmidt算法来保证完全正交。
  GL(n): 一般线性群，是n阶可逆矩阵的集合。
  O(n): Orthogonal Group 正交群（保距，行列式为±1）
  SO(n): Special Orthogonal Group 特殊正交群（保持手性，行列式为1）
    Proper rotation:  适当的旋转 (行列式为1)
    Improper rotation: 不适当的旋转（行列式为-1）, rotation-reflect, 旋转反射，瑕旋转
  ----------------------
  补充一些理论：
  1. 特殊矩阵：对称（自伴）、斜对称（斜伴）、正交（酉）、正规矩阵
      实矩阵                      复矩阵
      条件           名称         条件            名称
  (1) A = A\T        对称阵       A = A\H         自伴阵
  (2) A = -A\T       斜称阵       A = -A\H        斜伴阵
  (3) A*A\T = E      正交阵       A*A\H = E       酉矩阵
  (4)                             A*A\H = A\H*A   正规矩阵
  其中，(1),(2),(3)都是正规矩阵

  正规矩阵的一个定理：每个 n*n 正规矩阵A，都有一个由对应于特征值λ1,...,λn的特征向量
  组成的完全正交基 x1,...,xn。
  若设 U = (x1,...,xn)，则 U 是酉矩阵，并且有
  U^{-1} A U = 对角阵 {λ1,...,λn}

  正交矩阵的应用（旋转）：若一个 n*n 实矩阵A是正交的，则其特征值等于
  ±1 或 e^{±iϕ}成对出现（ϕ是实数）。
  
  2. 特征值、特征向量、矩阵的谱
  (1) 方阵A，使方程 Ax = λx 有非零解时，λ(复数)称一个特征值，x称对应的特征向量
  (2) A的所有特征值的集合称为A的谱 σ(A)，A的特征值的绝对值的最大值称为A的谱半径，
      记做 r(A)
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

Generalizable Variable A Aadd Aopp Amul Ainv Alt Ale Altb Aleb a2r.

Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** ** Orthonormal vectors 标准正交的向量组 *)
Section mcolsOrthonormal_mrowsOrthonormal.
  Context `{HField:Field}.
  Notation mat r c := (mat A r c).
  Notation vunit := (@vunit _ Aadd Azero Amul Aone).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "_|_" := vorth : vec_scope.

  (** All (different) columns of a matrix are orthogonal each other.
      For example: [v1;v2;v3] => u_|_v2 && u_|_v3 && v_|_v3. *)
  Definition mcolsOrth {r c} (M : mat r c) : Prop :=
    forall j1 j2, j1 <> j2 -> mcol M j1 _|_ mcol M j2.

  (** All (different) rows of a matrix are orthogonal each other. *)
  Definition mrowsOrth {r c} (M : mat r c) : Prop :=
    forall i1 i2, i1 <> i2 -> mrow M i1 _|_ mrow M i2.

  (*
  (** bool version *)
  Definition mcolsorthb {r c} (m : mat r c) : bool :=
    let is_orth (i j : nat) : bool := (<mcol m i, mcol m j> =? Azero)%R in
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    let chk_col (j : nat) : bool := and_blist (map (fun k => is_orth j k) (cids j)) in
    and_blist (map (fun j => chk_col j) (seq 0 c)).

  Lemma mcolsorthb_spec : forall {r c} (m : mat r c),
      mcolsorthb m <-> mcolsorth m.
  Proof.
  Abort.
  
  Section test.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.
    Let m1 : mat 1 3 := l2m [[a11;a12;a13];[a21;a22;a23]].
    Let m2 : mat 3 1 := l2m [[a11;a12];[a21;a22];[a31;a32]].

    (* Compute mcolsorthb m1. *)
    (* Compute mcolsorthb m2. (* because only one column, needn't be check *) *)
  End test.
   *)

  (** All columns of a matrix are unit vector.
      For example: [v1;v2;v3] => unit u && unit v && unit v3 *)
  Definition mcolsUnit {r c} (m : mat r c) : Prop := forall j, vunit (mcol m j).
  (** All rows of a matrix are unit vector. *)
  Definition mrowsUnit {r c} (m : mat r c) : Prop := forall i, vunit (mrow m i).

  (*
  (** bool version *)
  Definition mcolsUnitb {r c} (m : mat r c) : bool :=
    and_blist (map (fun i => vunitb (mcol m i)) (seq 0 c)).

  Lemma mcolsUnitb_spec : forall {r c} (m : mat r c),
      mcolsUnitb m <-> mcolsUnit m.
  Proof.
  Abort.
   *)

  (** The columns of a matrix is orthogomal *)
  Definition mcolsOrthonormal {r c} (m : mat r c) : Prop := mcolsOrth m /\ mcolsUnit m.

  (** The rows of a matrix is orthogomal *)
  Definition mrowsOrthonormal {r c} (m : mat r c) : Prop := mrowsOrth m /\ mrowsUnit m.

End mcolsOrthonormal_mrowsOrthonormal.


(* ======================================================================= *)
(** ** Orthogonal matrix *)
Section morth.
  Context `{HField : Field}.
  
  Notation "- a" := (Aopp a) : A_scope.
  
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation "< u , v >" := (vdot u v) : vec_scope.

  Notation vec n := (@vec A n).
  Notation vzero := (vzero Azero).
  Notation smat n := (smat A n).
  Notation mat1 n := (@mat1 _ Azero Aone n).
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul  : mat_scope.
  Notation mmulv := (@mmulv _ Aadd Azero Amul).
  Infix "*" := mmulv  : vec_scope.
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone _).
  Notation minvertible := (@minvertible _ Aadd Azero Amul Aone _).
  Notation mcolsOrthonormal := (@mcolsOrthonormal _ Aadd Azero Amul Aone).
  Notation mrowsOrthonormal := (@mrowsOrthonormal _ Aadd Azero Amul Aone).
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
    - pose proof (morth_invertible M H).
      apply AM_mmul_eq1_iff_minv_r in H. rewrite <- H. apply AM_mmul_minv_r; auto.
    - apply minv_eq_trans_imply_morth. apply AM_mmul_eq1_iff_minv_l. auto.
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
  
  (** matrix M is orthogonal <-> columns of M are orthogomal *)
  Lemma morth_iff_mcolsOrthonormal : forall {n} (M : smat n),
      morth M <-> mcolsOrthonormal M.
  Proof.
    intros. unfold mcolsOrthonormal, mcolsOrth, mcolsUnit, vorth, vunit.
    split; intros.
    - split; intros.
      + rewrite vdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_diff; auto.
      + rewrite vdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_same; auto.
    - destruct H as [H1 H2]. apply meq_iff_mnth; intros.
      rewrite <- vdot_col_col; auto.
      destruct (i ??= j)%fin.
      + subst. rewrite mnth_mat1_same; auto.
      + rewrite mnth_mat1_diff; auto.
  Qed.
  
  (** matrix M is orthogonal <-> rows of M are orthogomal *)
  Lemma morth_iff_mrowsOrthonormal : forall {n} (M : smat n),
      morth M <-> mrowsOrthonormal M.
  Proof.
    intros. unfold mrowsOrthonormal, mrowsOrth, mrowsUnit, vorth, vunit.
    split; intros.
    - split; intros.
      + rewrite vdot_row_row; auto. rewrite morth_iff_mul_trans_r in H.
        rewrite H, mnth_mat1_diff; auto.
      + rewrite vdot_row_row; auto. rewrite morth_iff_mul_trans_r in H.
        rewrite H, mnth_mat1_same; auto.
    - (* 这一步不能直接证明，因为 morth 定义为 M\T*M=mat1，而不是 M*M\T=mat1。
         可借助已证明的列的性质。*)
      destruct H as [H1 H2].
      apply morth_mtrans. apply morth_iff_mcolsOrthonormal. hnf. split; auto.
  Qed.
  
  (** columns of M are orthonormal <-> rows of M are orthonormal *)
  Lemma mcolsOrthonormalorth_iff_mrowsOrthonormal : forall {n} (M : smat n),
      mcolsOrthonormal M <-> mrowsOrthonormal M.
  Proof.
    intros. rewrite <- morth_iff_mrowsOrthonormal, <- morth_iff_mcolsOrthonormal.
    easy.
  Qed.

  (** Transformation by orthogonal matrix will keep inner-product *)
  Theorem morth_keep_dot : forall {n} (M : smat n) (u v : vec n),
      morth M -> <M * u, M * v>%V = <u, v>.
  Proof.
    intros. rewrite vdot_eq_mmul. rewrite v2rv_mmulv. rewrite v2cv_mmulv.
    rewrite mmul_assoc. rewrite <- (mmul_assoc _ M).
    rewrite morth_iff_mul_trans_l in H. rewrite H. rewrite mmul_1_l. auto.
  Qed.
  
  Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv}.
  Context `{HConvertToR
      : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb a2r}.
  Notation vlen := (@vlen _ Aadd Azero Amul a2r).
  Notation "|| v ||" := (vlen v) : vec_scope.

  (** Transformation by orthogonal matrix will keep length. *)
  Corollary morth_keep_length : forall {n} (M : smat n) (v : vec n),
      morth M -> ||(M * v)%V|| = ||v||.
  Proof.
    intros. rewrite vlen_eq_iff_dot_eq. apply morth_keep_dot. auto.
  Qed.

  (** Transformation by orthogonal matrix will keep zero. *)
  Lemma morth_keep_nonzero : forall {n} (M : smat n) (v : vec n),
      v <> vzero -> morth M -> (M * v)%V <> vzero.
  Proof.
    intros. intro.
    pose proof (morth_keep_length M v H0). rewrite H1 in H2.
    rewrite vlen_vzero in H2. symmetry in H2.
    rewrite vlen_eq0_iff_eq0 in H2. easy.
  Qed.

(** 由于正交矩阵可保持变换向量的长度和角度，它可保持坐标系的整体结构不变。
    因此，正交矩阵仅可用于旋转变换和反射变换或二者的组合变换。
    当正交矩阵的行列式为1，表示一个旋转，行列式为-1，表示一个反射。*)

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

  (** The condition to form a GOn from a matrix *)
  Definition GOnP {n} (m : smat n) : Prop := morth m.

  Lemma GOnP_spec : forall {n} (x : @GOn n), GOnP x.
  Proof. intros. apply x. Qed.

  (** Create a GOn from a matrix satisfing `GOnP` *)
  Definition mkGOn {n} (m : smat n) (H : GOnP m) : @GOn n.
    refine (Build_GOn m _). apply H.
  Defined.

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

  (** The condition to form a SOn from a matrix *)
  Definition SOnP {n} (m : smat n) : Prop := morth m /\ mdet m = Aone.

  Lemma SOnP_spec : forall {n} (x : @SOn n), SOnP x.
  Proof. intros. hnf. destruct x. split; auto. apply SOn_GOn0. Qed.

  (** Create a SOn from a matrix satisfing `SOnP` *)
  Definition mkSOn {n} (m : smat n) (H : SOnP m) : @SOn n.
    refine (Build_SOn (Build_GOn _ m _) _). apply H.
    Unshelve. apply H.
  Defined.

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
  Proof.
    intros. rewrite <- SOn_inv_eq_trans. apply AM_mmul_minv_l.
    destruct M as [[M H] H1]. simpl. apply morth_invertible; auto.
  Qed.

  (** M * M\T = mat1 *)
  Lemma SOn_mul_trans_r_eq1 : forall {n} (M : @SOn n), M * M\T = mat1 n.
  Proof.
    intros. rewrite <- SOn_inv_eq_trans. apply AM_mmul_minv_r.
    destruct M as [[M H] H1]. simpl. apply morth_invertible; auto.
  Qed.

End SOn.

