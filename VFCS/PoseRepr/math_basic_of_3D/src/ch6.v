
From FinMatrix Require Import MatrixR.
Import V3Notations.

(** ch6 矩阵详解：*)

(* 本章讨论一些有趣和有用的矩阵运算来结束矩阵主题 *)

(** * 6.1 矩阵的行列式 *)

(** ** 6.1.1 2x2和3x3矩阵的行列式 *)
Section sec_6_1_1.

  Open Scope fun_scope.
  
  (** 方阵M的行列式表示为 |M|，或 det M。
      可直接给出 2x2 和 3x3 矩阵的行列式公式。
      另外，3x3矩阵的行列式等于混合积，也称 triple product of the three vectors *)
  (* Check mdet2. *)
  (* Check mdet3. *)
  (* Check v3mixed. *)

  Lemma mdet3_eq_cv3mixed : forall m : smat 3,
      mdet3 m = <mcol m #0 \x mcol m #1, mcol m #2>.
  Proof. intros. cbv. ring. Qed.
  
End sec_6_1_1.

(** ** 6.1.2 子矩阵行列式和余子式 *)
Section sec_6_1_2.
  (* minor : M的去掉{ij}元后的子矩阵的行列式，记做 M^{ij} *)
  (* cofactor : 也就是代数余子式 A_ij = (-1)^(i+j) M_ij *)
  
End sec_6_1_2.

(** ** 6.1.3 任意nxn矩阵的行列式 *)
Section sec_6_1_3.
  (* 按行或按列展开 *)

  (* 当进行更高维的行列式时，复杂性迅速增长。
     有一种称为 pivoting 的操作，可以保持单个元素(Pivot元素)不变，其余元素用0填充。。。
     由于这里不需要高于4x4矩阵的行列式，该技术暂不讨论。*)

  (* 单位阵的行列式 *)
  Check mdet1.
  (* 矩阵乘积的行列式 *)
  Check mdet_mmul.
  (* 转置的行列式 *)
  Check mdet_mtrans.

  (* 任何行或列包含全0，则行列式为0 *)

  (* 交换任意行对(pair of rows) 或 列对，行列式变负 *)
  
  (* 行（列）的任意倍数加到另一行（列）不改变行列式*)
End sec_6_1_3.

(** ** 6.1.4 行列式的几何解释 *)
Section sec_6_1_4.
  (* 2D中，等于将基矢量(行？列？)作为两条边的平行四边形或倾斜框(skew box)的有符号面积 *)
  (* 3D中，是平行六面体(parallelepiped)的体积。*)

(* 行列式的绝对值与通过矩阵变换对象而发生的面积(2D)或体积(3D)的变换有关，
     符号则表示在矩阵中是否含有任何反射或投影。*)
  (* 行列式还能用于帮助对由矩阵表示的变换类型进行分类。参见 5.7 *)
End sec_6_1_4.


(** * 6.2 逆矩阵 *)

(* 可逆的 invertible, 非奇异的 Nonsingular, 
   不可逆的 Noninvertible, 奇异的 singular,
   对于可逆阵 M，只有 v=0 能使得 M v = 0。
   
   可逆性测试的常用方法是检查行列式，简单而且快速。但是，该方法也可能失败。
   极端情况，某个极端的错切矩阵，它构成具有单位体积的非常长的薄平行六面体。
   即使它的行列式是1，但这个病态条件的矩阵几乎是奇异的。
   这种情况下的一个合适的工具是 condition number，但这是一个高级主题。

   有若干种计算逆矩阵的方法，这里基于经典伴随矩阵的方法。*)

(** ** 6.2.1 经典伴随矩阵 *)
Section sec_6_2_1.
  (* 伴随矩阵，记为 adj M，被定义为M的余子式的矩阵的转置 *)
End sec_6_2_1.

(** ** 6.2.2 逆矩阵 *)
Section sec_6_2_2.
  (** 通过经典伴随矩阵和行列式计算逆矩阵 *)
  (* M^{-1} = adj M / (|M|) *)

  (* 其他技术，如 gaussian elimination。
     许多线性代数教科书指出这些技术更适合在计算机上实现，它们需要较少的算术运算，
     该说法对于较大矩阵和具有可利用的结构的矩阵是适用的。
     然而，较小阶的矩阵，如在几何中使用的2x2,3x3,4x4矩阵，经典伴随方法更好。
     因为该方法提供了无分支实现，即，没有if语句或静态无法展开的循环。
     在今天的超标量体系结构和专用矢量处理器上，这是一个很大的胜利。*)
  (* 题外话：专用指令来计算2,3,4阶矩阵的逆矩阵。*)

  (* 逆的逆等于原始阵 *)
  Check minv_minv.
  (* 单位阵的逆 *)
  Check minv_mat1.
  (* 还有一些矩阵的逆是自身，正交+对称时，例如 反射矩阵，绕轴旋转180度 *)
  (* 转置的逆等于逆的转置 *)
  Check minv_mtrans.
  (* 乘法的逆 *)
  Check minv_mmul.
  (* 逆的行列式 *)
  Check mdet_minv.
End sec_6_2_2.

(** ** 6.2.3 逆矩阵的几何解释 *)
Section sec_6_2_3.
  (* 几何上，它可以计算一个变换的反向，可撤销另一个变换。
     所以，对于一个向量，若用矩阵M来变换，然后用 M的逆 来变换，则得到原始矩阵 *)

  (* 验证逆矩阵可以撤销一个变换。
     分别用列向量和行向量，以及先变换再逆变换，或先逆变换再变换，共4种情形。 *)
  Example minv_ex1 : forall {n} (v : cvec n) (M : smat n),
      minvtble M -> M\-1 * (M * v) = v.
  Proof.
    intros. rewrite <- mmul_assoc. rewrite mmul_minv_l; auto. rewrite mmul_1_l; auto.
  Qed.

  Example minv_ex2 : forall {n} (v : cvec n) (M : smat n),
      minvtble M -> M * (M\-1 * v) = v.
  Proof.
    intros. rewrite <- mmul_assoc. rewrite mmul_minv_r; auto. rewrite mmul_1_l; auto.
  Qed.

  Example minv_ex3 : forall {n} (v : vec n) (M : smat n),
      minvtble M -> (v v* M) v* M\-1 = v.
  Proof.
    intros. rewrite <- mvmul_assoc. rewrite mmul_minv_r; auto.
    rewrite mvmul_1_r; auto.
  Qed.

  Example minv_ex4 : forall {n} (v : vec n) (M : smat n),
      minvtble M -> (v v* M\-1) v* M = v.
  Proof.
    intros. rewrite <- mvmul_assoc. rewrite mmul_minv_l; auto.
    rewrite mvmul_1_r. auto.
  Qed.

End sec_6_2_3.

(** * 6.3 正交矩阵（Orthogonal Matrices）*)

(* 线性代数中，如果一组基矢量相互垂直，则称它们是正交的（Orthogonal），
   它们不需要有单位长度。
   若具有了单位长度，则称它们是标准正交基（Orthonormal Basis）。
   正交矩阵（Orthogonal Marix）的行和列是标准正交基矢量（Orthonormal Basis Vector）*)

(** ** 6.3.1 正式定义 *)
Section sec_6_3_1.

  (** 正交矩阵：乘以其转置矩阵是单位阵 *)
  Print morth.

  (* 等价定义，转置等于逆。这是一个非常有用的信息，避免了高昂的逆矩阵计算。 *)
  Check morth_imply_minv_eq_trans.
  Check minv_eq_trans_imply_morth.

End sec_6_3_1.

(** ** 6.3.2 正交矩阵的几何解释 *)
Section sec_6_3_2.
  (* 正交矩阵有很好的性质。但是，如何知道矩阵是否正交以利用其结构呢？
     许多情况下，可获得矩阵构造方式的信息，例如只包含旋转和/或反射时。
     但是，如果事先不知道来源，如何判断任意矩阵M是否正交？

     以3x3矩阵为例，
     方法1：根据定义，展开转置和乘法，并验证是否等于单位阵。
     方法2：给出9个数值表达式的等式，作为正交矩阵的判定条件。
        形如 m11 m11 + m12 m12 + m13 m13 = 1, ...
     方法3：取出3个行或3个列，然后验证9个点积表达式的等式。
        形如 <r1,r2> = 1, <r1,r2> = 0, ...
     需要注意的是，有3个方程是重复的，因为点积满足交换律。
        
     通过观察可知，要使矩阵正交，必须有如下条件
     (1) 每一行(或列)是单位向量
     (2) 行(或列)必须相互垂直。
   *)

  (* 如果不知道矩阵是否正交，可能要花时间来检查。
     最好的情况下，检查正交性发现矩阵确实是正交的，但这可能需要几乎与计算逆矩阵相同的时间。
     最坏的情况下，矩阵不是正交的，此时花费在检查上的时间被浪费了。
     另外，即使矩阵在理想情况下是正交的，但由于浮点数表示可能不完全正交。
     因此，我们必须使用容差（tolerance），并根据需要调整该值。*)

End sec_6_3_2.

(** ** 6.3.3 矩阵的正交化 *)
Section sec_6_3_3.
  (* 有的矩阵会略微偏离正交性，可能是从外部获得了不良数据，也可能是累计了浮点误差，
     后者又称矩阵蠕变（Matrix Creep）。
     此时，希望对矩阵进行正交化（Orthogonalize），以得到一个尽可能接近原始阵并正交的矩阵。
     标准算法是 Gram-Schmidt 正交化，基本思想是按顺序遍历基矢量，对每个基矢量，减去与
     基矢量平行的矢量，必然产生垂直矢量。*)

  (* 还有一些技巧或补充说明：
     1. 3d中，可用叉乘来代替第三个基矢量的求解
     2. gram-schmidt算法有偏差，取决于取出基矢量的顺序。
        例如，r1永远不变，而r3改变最多。
        有一种不偏向任何特定轴的变体算法：设定一个因子k，不是减去所有的投影，而是只减去
        它们的k倍。并通过多次迭代，每次比上一次“更正交”。
        例如，可设定k=1/4，迭代10次则相当接近正交，然后再用标准的正交化算法来保证完全正交。
   *)
End sec_6_3_3.

(** * 6.4 关于4x4齐次矩阵 *)
(* 这里的四维矢量和4x4矩阵只不过是为了简化三维运算而设计的方便表示法。*)

(** ** 6.4.1 关于四维齐次空间 *)
Section sec_6_4_1.

  (*  四维矢量有4个分量：x,y,z,w。有时称为齐次坐标（Homogeneous Coordinate）。
      homogeneous: 同性质的，同类的。
      
      为理解物理三维空间是如何扩展到四维的，先理解二维中的齐次坐标，形式为 (x,y,w)。
      在三维中w=1的标准二维平面上，实际的二维点(x,y)用齐次坐标表示为(x,y,1)，
      不在该平面的点可通过除以w，投影到w=1平面，从而得到相应的二维点。
      于是，齐次坐标(x,y,w)映射到实际的二维点(x/w,y/w)。

      而任意的物理二维点(x,y)，在齐次空间中存在无数的对应点，形如(kx,ky,k)，只要k≠0。
      这些点都在穿过原点的同一条直线上（homogeneous的意思）。
      当 w=0，因除零是未定义的，在二维空间中没有对应的物理点，但可以写成(x,y,0)而
      二维齐次坐标表示“无限远的点”，它定义的是方向而不是位置。
      当我们需要对“点”和“向量”进行概念上的区分时，当w≠0表示点；当w=0表示矢量。

      将三维扩展到四维时，同样的思想，虽然可视化更难。
      物理三维点被认为是存在于四维的w=1的超平面（hyperplane）中。
      四维点(x,y,z,w)可以投影到该超平面上以产生相应的物理三维点(x/w,y/w,z/w)。
      当w=0，四维点代表“无限远的点”，它将定义方向而不是位置。
      
      为什么我们想要使用四维空间呢？有两个主要原因：
      1. 为了表示上的方便，比如平移和缩放能同时处理。
      2. 将适当的值放入w，齐次除法将导致透视投影。*)
End sec_6_4_1.

(** ** 6.4.2 关于 4x4 平移矩阵 *)
Section sec_6_4_2.
  (* 由之前分析可知，3x3变换矩阵表示线性变换，不含平移。
     因零向量总被变换为零向量，因此任何可由矩阵乘法表示的变换都不能表示平移。
     但矩阵是非常方便的工具，是否能找到一种方法扩展标准3x3变换矩阵来处理包含平移的
     变换，那将很美好。
     4x4矩阵就提供了这样一个数学上的组装方法。*)

  (* 假设w为1，则三维矢量[x,y,z]在四维中表示为[x,y,z,1] *)
  Definition v324 (v : vec 3) : vec 4 := l2v [v.1; v.2; v.3; 1].
  (* 将四维表示 [x,y,z,1] 转换为三维矢量 [x,y,z] *)
  Definition v423 (v : vec 4) : vec 3 := l2v [v.1; v.2; v.3].

  (* 三维矢量[x,y,z]在四维中表示为[x,y,z,0] *)
  Definition v324_0 (v : vec 3) : vec 4 := l2v [v.1; v.2; v.3; 0].

    
  (* 任意3x3变换矩阵扩展到四维 *)
  Definition m324 (m : smat 3) : smat 4 :=
    l2m [[m.11; m.12; m.13; 0];
         [m.21; m.22; m.23; 0];
         [m.31; m.32; m.33; 0];
         [0; 0; 0; 1]].
  (* 反之 *)
  Definition m423 (m : smat 4) : smat 3 :=
    l2m [[m.11; m.12; m.13];
         [m.21; m.22; m.23];
         [m.31; m.32; m.33]].

  (* 可验证，任意三维向量与3x3矩阵的乘法，等效于四维向量和4x4矩阵的乘法 *)
  Lemma m324_mul_spec : forall (v : vec 3) (m : smat 3),
      m *v v = v423 ((m324 m) *v (v324 v)).
  Proof. intros. veq; ring. Qed.

  (** 最有趣的部分，在四维中，可使用矩阵乘法来表示平移，而三维中这是不可能的。*)
  (** 使用4x4矩阵执行三维中的平移(translation) *)
  Definition mtransl3 (p : vec 3) : smat 4 :=
    l2m [[1; 0; 0; p.1];
         [0; 1; 0; p.2];
         [0; 0; 1; p.3];
         [0; 0; 0; 1]].

  (* 可验证，该矩阵执行了平移 *)
  Lemma mtransl3_spec : forall (p u : vec 3),
      v423 ((mtransl3 p) *v (v324 u)) = (u + p)%V.
  Proof. intros. veq; ring. Qed.

  (* 需要理解，这种矩阵乘法仍然是线性变换，它不能表示四维中的平移，
     因为四维零矢量始终变换到四维零矢量。
     之所以该技巧能够在三维中表示平移，实际上是我们在错切四维空间。（可以证明之）
     由于物理三维空间对应的四维超平面不会通过四维中的原点，因此错切四维空间时，
     能够在三维中进行平移。*)

  (* 现在，考虑先执行一次没有平移的变换，接着执行一次仅有平移的变换 *)
  Section test.
    Variable R : smat 3. (* 一个旋转矩阵，实际上也可以包含其他三维线性变换 *)
    Variable t : vec 3. (* 平移的量，储存在该向量的各分量中 *)

    Let R4 : smat 4 := m324 R. (* 对应的四维形式 *)
    Let T : smat 4 := mtransl3 t. (* 平移矩阵 *)

    Variable v : vec 3. (* 任给一个向量，或说一个点 *)

    (* 先旋转，再平移，得到变换后的向量 *)
    Let v' : vec 3 := v423 (T *v (R4 *v (v324 v))).

    (* 可发现，T * R 合成的单个变换矩阵包含了旋转和平移两部分。*)
    (* 以列向量的方式为例：右侧的列包含了平移，底下的行是 [0;0;0;1]，
       以行向量的方式为例：底下的行包含了平移，右侧的列是 [0;0;0;1] *)

    Goal T * R4 = mconsrT (mconscT R t) v4l.
    Proof. intros; meq; ring. Qed.
  End test.

  (** 旋转再平移的直接矩阵形式，R是旋转，p是平移 *)
  Definition mrottransl (R : smat 3) (p : vec 3) : smat 4 :=
    l2m [[R.11; R.12; R.13; p.1];
         [R.21; R.22; R.23; p.2];
         [R.31; R.32; R.33; p.3];
         [0; 0; 0; 1]].

  (* 验证上述矩阵定义在语法上的正确性，还可以代入向量来做语义上更完整的验证 *)
  Lemma mrottransl_spec1 : forall (R : smat 3) (p : vec 3),
      mrottransl R p = mconsrT (mconscT R p) v4l.
  Proof. intros; meq; ring. Qed.

  (* 反过来，任给 4x4矩阵，可分为线性变换部分和平移部分。   
     用块矩阵表示法（Block Matrix Notation）来表示。*)

  (* 对于“无限远的点”[x,y,z,0]，用标准的3x3线性变换矩阵（不含平移）扩展为
     四维后做乘法，会发生预期的变换，结果是另一个无穷远的点的矢量[x',y',z',0] *)
  Goal forall (R : smat 3) (p : vec 3), (m324 R) *v (v324_0 p) = v324_0 (R *v p).
  Proof. intros; veq; ring. Qed.

  (* 对于“无限远的点”[x,y,z,0]，用包含平移的变换矩阵做乘法，其结果是一样的。
     即，不会发生平移。*)
  Goal forall (R : smat 3) (p : vec 3) (v : vec 3),
      (mrottransl R p) *v (v324_0 v) = v324_0 (R *v v).
  Proof. intros; veq; ring. Qed.
  
  (* 换言之，四维矢量的w分量可以决定是否使用4x4矩阵的平移部分。
     因为有些矢量代表“位置”，它应该被平移，而其他矢量则代表方向，不该平移。
     在几何上，可以将第一类数据(w=1)视为“点”，第二类数据，“无限远的点”(w=0) 视为矢量。

     在编写代码时，一种常用的技术是使用 4x3 或 3x4 的矩阵，假设最右或最下的是[0,0,0,1]。
   *)
End sec_6_4_2.

(** ** 6.4.3 一般仿射变换 *)
Section sec_6_4_3.
  (* 使用4x4变换矩阵，可创建包含平移的更一般的仿射变换，例如：
     绕不穿过原点的轴旋转；
     绕不穿过原点的平面缩放；
     绕不穿过原点的平面反射；
     在不穿过原点的平面上进行正交投影。

     基本思想是，先将变换的“中心”平移到原点，然后用ch5的技术执行线性变换，再将中心
     平移回原始位置。*)

  (** 平移变换矩阵的的逆矩阵，等于反向平移 *)
  Lemma minv_mtransl3 : forall (p : vec 3), (mtransl3 p)\-1 = mtransl3 (-p)%V.
  Proof.
    intros.
    assert ((mtransl3 p) * (mtransl3 (-p)%V) = mat1). intros. meq; ring.
    apply mmul_eq1_imply_minvAM_l in H. auto.
  Qed.

  (* 仿射变换的额外平移仅改变矩阵最后一列，而旋转部分不受影响 *)
  Goal forall (R : smat 3) (p : vec 3),
      let T := mtransl3 p in
      let R4 := m324 R in
      T * R4 * (T\-1) = mrottransl R (p - R *v p)%V.
  Proof.
    intros. unfold T,R4; clear T R4. unfold mrottransl, mtransl3,m324.
    (* 展开矩阵和向量，以加速运算 *)
    v2e R2. v2e p.
    (* 首先用4维上的逆矩阵公式展开，以简化逆矩阵运算 *)
    rewrite <- minvAM4_eq_minvAM.
    (* 2.6 s *)
    Time meq; field.
    (* 计算可逆性比较快 *)
    apply minvtble_iff_mdet_neq0; cbv; lra.
  Qed.
      
End sec_6_4_3.


(** * 6.5 关于4x4矩阵和透视投影 *)

(** 将三维空间投影到二维平面，该平面称为投影平面。
    正交投影也称为正投影或平行投影，因为投影线是平行的。
    投影线（Projector）是从初始点到平面上的最终投影点的线。
    三维中的透视投影（Perspective Projection）也投影到二维平面上，但投影线不平行。
    实际上，它们在一个点上相交，该点称为投影中心（Center of Projection）。

    由于投影中心位于投影迎面的前方，投影线在撞击平面之前交叉，因此图像被反转。
    在投影中心固定时，物体离投影中心越远，其正交投影保持不变，而透视投影a越小，
    这称为透视缩小（Perspective Foreshortening）。 *)

(** ** 6.5.1 针孔相机 *)
Section sec_6_5_1.
  (* 透视投影模拟了人类视觉系统。但人的视觉系统更复杂，有两只眼镜，且眼镜的投影表面
     （视网膜）都不是平的。
     一个更简单的例子是针孔相机（Pinhole Camera）：光线进入针孔后投影到盒子另一端,
     即投影平面。此时，投影出的图像是反转的，因为光线在针孔（投影中心）相遇时交叉。
     
     考虑针孔相机透视投影背后的几何问题。
     一个三维空间，原点位于针孔（投影中心），给定投影平面 z = -d，那么可以计算其投影。*)

  (** 投影到 z = -d 平面上的 *)
  Let proj_point_to_neg_z (d : R) (p : vec 3) : vec 3 :=
        l2v [- d * p.x / p.z; - d * p.y / p.z; (-d)%R].

  (** 实践中，减号会产生额外的复杂性，可将投影平面移动到 z = d。
      虽然真正的针孔相机不可能是这样。然而，计算机内部的数学处理是完全有效的。*)

  (** 投影到 z = d 平面上的 *)
  Let proj_point_to_z (d : R) (p : vec 3) : vec 3 :=
        l2v [d * p.x / p.z; d * p.y / p.z; d].
  
End sec_6_5_1.

(** ** 6.5.2 透视投影矩阵 *)
Section sec_6_5_2.
  (* 在 6.5.1 中推导出的转换公式含有除法，可以在4x4矩阵中编码透视投影。
     将齐次矢量 [x y z 1] 投影到 [x y z z/d] *)

  (** 使用 4x4 矩阵投影到 z = d 平面上 *)
  Definition proj4 (d : R) : smat 4 :=
    l2m [[1; 0; 0; 0];
         [0; 1; 0; 0];
         [0; 0; 1; 0];
         [0; 0; (1/d); 0]].

  Lemma proj4_spec : forall d (p : vec 3),
      let p' := v324 p in
      (proj4 d) *v p' = l2v [p.x; p.y; p.z; p.z / d].
  Proof. intros. veq; ring. Qed.

  (** 这个 4x4 投影矩阵的一些说明：
      1. 矩阵乘法并不真正执行透视变换，它计算w。当将四维转换到3维时，才会真正执行透视除法
      2. 可以有许多变体。例如，投影平面z=0，投影中心在 [0 0 d]，这会得到一个稍不同的公式
      3. 此过程看起来似乎只是将三维坐标的各分量除以z，而不必使用矩阵。那么，为什么
         要使用齐次空间呢？首先，4x4矩阵提供的这个变换可以和其他变换连接。其次，也可能会
         投影到非轴对称平面。
      4. 真实图形几何管道中的投影矩阵（Projection Matrix）——更准确地被称为剪辑矩阵
         （Clip Matrix）——不仅仅是将z复制到w，它还会有些额外的工作。

         在 10.3.2 会有技术细节，以及实际应用。*)

End sec_6_5_2.


