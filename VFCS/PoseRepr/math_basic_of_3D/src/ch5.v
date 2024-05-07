
From FinMatrix Require Import MatrixR.

(* ch5 本章将讨论通过矩阵实现线性变换 *)

(* 注意，这里假定了一个主动变换模式：在坐标空间保持静止时变换对象 *)
(* 而相反的变换是被动变换：对象保持静止，变换坐标空间。*)

(* 注意，原书采用行向量左乘矩阵来表示，而我更习惯用列向量右乘的矩阵（我已经转置了）。
   另外，本书采用左手规则。 *)

(** * 5.1 旋转 *)

(** ** 5.1.1 在2D中的旋转 *)
Section sec_5_1_1.
  
  (** 2D中，基矢量p和q绕原点旋转，产生新的基矢量p'和q'的值为：*)
  Definition mrot2 (θ : R) : smat 2 := l2m [[cos θ; -sin θ];[sin θ; cos θ]]%R.

End sec_5_1_1.

(** ** 5.1.2 绕主轴的3D旋转 *)
Section sec_5_1_2.

  (* 注意，由于定义正旋转方向的惯例，左右手坐标系统都可以工作。*)
  
  (** 3D中，基矢量p,q,r绕x轴旋转，产生新的基矢量p',q',r'的值为：*)
  Definition mrot3x (θ : R) : smat 3 :=
    l2m [[1;0;0];[0;cos θ;-sin θ];[0;sin θ;cos θ]]%R.

  (** 3D中，基矢量p,q,r绕y轴旋转，产生新的基矢量p',q',r'的值为：*)
  Definition mrot3y (θ : R) : smat 3 :=
    l2m [[cos θ;0;sin θ];[0;1;0];[-sin θ;0;cos θ]]%R.
  
  (** 3D中，基矢量p,q,r绕z轴旋转，产生新的基矢量p',q',r'的值为：*)
  Definition mrot3z (θ : R) : smat 3 :=
    l2m [[cos θ;-sin θ;0];[sin θ;cos θ;0];[0;0;1]]%R.
  
End sec_5_1_2.

(** ** 5.1.3 绕任意轴的3D旋转 *)
Section sec_5_1_3.

  (** 3D中，绕任意轴（单位矢量n̂）旋转的矩阵。将标准基矢量p,q,r变换为p',q',r' *)
  Definition mrot3 (θ : R) (n : vec 3) : smat 3 :=
        let c := cos θ in
        let s := sin θ in
        l2m
          [[n.x*n.x*(1-c) + c; n.x*n.y*(1-c) - n.z*s; n.x*n.z*(1-c) + n.y*s];
           [n.x*n.y*(1-c) + n.z*s; n.y*n.y*(1-c) + c; n.y*n.z*(1-c) - n.x*s];
           [n.x*n.z*(1-c) - n.y*s; n.y*n.z*(1-c) + n.x*s; n.z*n.z*(1-c) + c]]%R.

End sec_5_1_3.


(** * 5.2 缩放 *)

(** 整体缩放，基于原点执行均匀缩放(uniform scale)。
    保留角度和比例，即长度变为k倍，面积k^2倍，体积k^3倍 *)

(** 拉伸或挤压对象，则可在不同方向应用不同的比例因子，导致不均匀缩放(Nonuniform scale)。
    此时仍会保留角度，而长度、面积、体积会根据各方向的比例因子而调整。具体的：
    1. |k| < 1，缩短
    2. |k| > 1，拉伸
    3. k = 0，该方向上得到一个正交投影（orthographic projection）
    4. k < 0, 一个反射的结果
    本书其余部分，假设 k > 0
 *)

(** ** 5.2.1 沿主轴缩放 *)
Section sec_5_2_1.

  (* 2D中绕主轴缩放的矩阵 *)
  Definition mscale2_axis (kx ky : R) : smat 2 := l2m [[kx;0];[0;ky]].

  (* 3D中绕主轴缩放的矩阵 *)
  Definition mscale3_axis (kx ky kz : R) : smat 3 := l2m [[kx;0;0];[0;ky;0];[0;0;kz]].

  (* 例如，该矩阵乘以任意矢量，将被缩放 *)
  Lemma scale3_ex1 : forall x y z kx ky kz,
      let v : vec 3 := l2v [x;y;z] in
      let v' : vec 3 := l2v [kx*x;ky*y;kz*z]%R in
      mscale3_axis kx ky kz *v v = v'.
  Proof. intros. veq; ring. Qed.

End sec_5_2_1.

(** ** 5.2.2 任意方向的缩放 *)
Section sec_5_2_2.
  
  (** 可独立于坐标系统在任意方向上缩放。
    按照 5.1.3中类似的思路，分解为平行和垂直两个分量来推导。 *)

  (** 2D中，在任意方向上缩放的矩阵 *)
  Definition mscale2 (n : vec 2) (k : R) : smat 2 :=
    l2m [[1 + (k-1)*n.x*n.x; (k-1)*n.x*n.y];
         [(k-1)*n.x*n.y; 1+(k-1)*n.y*n.y]]%R.

  (** 3D中，在任意方向上缩放的矩阵 *)
  Definition mscale3 (n : vec 3) (k : R) : smat 3 :=
    l2m [[1+(k-1)*n.x*n.x; (k-1)*n.x*n.y; (k-1)*n.x*n.z];
         [(k-1)*n.x*n.y; 1+(k-1)*n.y*n.y; (k-1)*n.y*n.z];
         [(k-1)*n.x*n.z; (k-1)*n.y*n.z; 1+(k-1)*n.z*n.z]]%R.
  
End sec_5_2_2.


(** * 5.3  正交投影 *)

(** 一般而言，正交（projection）表示任意的降维操作。
    如同在 5.2 缩放中讨论的，可以在一个方向使用零比例因子，则该方向的所有点被
    扁平化，在2D中投影到垂直轴，在3D中投影到平面。
    这种类型的投影是正交投影（orthographic projection），也称平行投影（parallel
    projection）。在6.5节还将介绍另一种投影，透视投影（perspective projection）*)

(** ** 5.3.1 投影到主轴或主平面上 *)
Section sec_5_3_1.

  (* 这是最简单的投影，实际上不需要变换，简单地丢弃一个坐标，并将数据指定给较小维度的
     变量。但是，也可以在垂直轴上使用零刻度值。以下表示了这种变换的矩阵 *)

  (** 2D中投影到主轴上 *)
  Definition mproj2x : smat 2 := l2m [[1;0];[0;0]].
  Definition mproj2y : smat 2 := l2m [[0;0];[0;1]].

  (** 2D中投影到x轴，等价于沿着y轴缩放0倍 *)
  Lemma mproj2x_eq_scale : mproj2x = mscale2 (l2v [0;1]) 0.
  Proof. meq; ring. Qed.

  (** 2D中投影到y轴，等价于沿着x轴缩放0倍 *)
  Lemma mproj2y_eq_scale : mproj2y = mscale2 (l2v [1;0]) 0.
  Proof. meq; ring. Qed.

  (** 3D中投影到主平面上 *)
  Definition mproj3xy : smat 3 := l2m [[1;0;0];[0;1;0];[0;0;0]].
  Definition mproj3zx : smat 3 := l2m [[1;0;0];[0;0;0];[0;0;1]].
  Definition mproj3yz : smat 3 := l2m [[0;0;0];[0;1;0];[0;0;1]].

  (** 3D中投影到xy平面，等价于沿着z轴缩放0倍 *)
  Lemma mproj3xy_eq_scale : mproj3xy = mscale3 (l2v [0;0;1]) 0.
  Proof. meq; ring. Qed.

  (** 3D中投影到zx平面，等价于沿着y轴缩放0倍 *)
  Lemma mproj3zx_eq_scale : mproj3zx = mscale3 (l2v [0;1;0]) 0.
  Proof. meq; ring. Qed.
  
  (** 3D中投影到yz平面，等价于沿着x轴缩放0倍 *)
  Lemma mproj3yz_eq_scale : mproj3yz = mscale3 (l2v [1;0;0]) 0.
  Proof. meq; ring. Qed.
  
End sec_5_3_1.

(** 5.3.2 投影到任意线或平面上 *)

Section sec_5_3_2.

  (** 与之前一样，不考虑平移，先或平面比通过原点。
      可使用第5.2.2中开发的公式，沿此方向应用零比例因子。*)

  (** 2D中，任意方向上投影的矩阵 *)
  Definition mproj2 (n : vec 2) : smat 2 :=
    l2m [[1-n.x*n.x; -n.x*n.y]; [-n.x*n.y; 1-n.y*n.y]]%R.

  (** 3D中，任意方向上投影的矩阵 *)
  Definition mproj3 (n : vec 3) : smat 3 :=
    l2m [[1-n.x*n.x; -n.x*n.y; -n.x*n.z];
         [-n.x*n.y; 1-n.y*n.y; -n.y*n.z];
         [-n.x*n.z; -n.y*n.z; 1-n.z*n.z]]%R.

  (** 2D中，任意方向投影，等价于在该方向缩放0倍 *)
  Lemma mproj2_eq_scale : forall (n : vec 2), mproj2 n = mscale2 n 0.
  Proof. intros. meq; ring. Qed.
  
  (** 3D中，任意方向投影，等价于在该方向缩放0倍 *)
  Lemma mproj3_eq_scale : forall (n : vec 3), mproj3 n = mscale3 n 0.
  Proof. intros. meq; ring. Qed.
  
End sec_5_3_2.


(** * 5.4 反射 *)

Section sec_5_4.

  (** 反射（reflection）也称镜像（mirroring）。在2D中绕直线翻转，在3D中绕平面翻转。
      reflected about y-axis : 绕y轴反射
      reflected about x-axis and y-axis: 绕x和y轴反射（与旋转180度相同）*)

  (** 可通过应用比例因子为-1的缩放来完成 *)

  (** 2D中，绕任意轴反射的矩阵 *)
  Definition mreflect2 (n : vec 2) : smat 2 :=
    l2m [[1 + (-2)*n.x*n.x; (-2)*n.x*n.y]; [(-2)*n.x*n.y; 1+(-2)*n.y*n.y]]%R.

  (** 3D中，在任意平面反射的矩阵 *)
  Definition mreflect3 (n : vec 3) : smat 3 :=
    l2m [[1+(-2)*n.x*n.x; (-2)*n.x*n.y; (-2)*n.x*n.z];
         [(-2)*n.x*n.y; 1+(-2)*n.y*n.y; (-2)*n.y*n.z];
         [(-2)*n.x*n.z; (-2)*n.y*n.z; 1+(-2)*n.z*n.z]]%R.

  Lemma mreflect2_eq_scale : forall (n : vec 2), mreflect2 n = mscale2 n (-1).
  Proof. intros; meq; ring. Qed.

  Lemma mreflect3_eq_scale : forall (n : vec 3), mreflect3 n = mscale3 n (-1).
  Proof. intros; meq; ring. Qed.

End sec_5_4.


(** * 5.5 错切 （shearing） *)
Section sec_5_5.

  (** 这是一种“倾斜（skew）”坐标空间的变形，它不均匀地拉伸坐标空间，不保留角度。
      然而，面积和体积却保留了。
      基本思路：将一个坐标的倍数加到另一个坐标。例如，y'=y, x'=x+s*y。
      错切是一种很少使用的变换，也被称为倾斜变换（skew transformation）。
      结合错切和缩放（均匀或不均匀）会产生一种变形效果，让人分不清它是否包含了
      旋转和非均匀缩放。*)

  (** 在2D中，对x轴方向错切的矩阵。参数s控制错切的量和方向 *)
  Definition mskew2x (s : R) : smat 2 := l2m [[1;s];[0;1]]%R.

  (** 在2D中，对y轴方向错切的矩阵。 *)
  Definition mskew2y (s : R) : smat 2 := l2m [[1;0];[s;1]]%R.

  (** 在3D中，对x和y坐标错切的矩阵。 *)
  Definition mskew3xy (s t : R) : smat 3 := l2m [[1;0;s];[0;1;t];[0;0;1]]%R.

  (** 在3D中，对z和x坐标错切的矩阵。 *)
  Definition mskew3zx (s t : R) : smat 3 := l2m [[1;s;0];[0;1;0];[0;t;1]]%R.

  (** 在3D中，对y和z坐标错切的矩阵。 *)
  Definition mskew3yz (s t : R) : smat 3 := l2m [[1;0;0];[s;1;0];[t;0;1]]%R.
  
End sec_5_5.


(** * 5.6 组合变换 *)
Section sec_5_6.

  (** 如何获取一系列变换矩阵并将它们组合（combine）或连接（concatenate）到一个
      单一的变换矩阵。此矩阵表示按顺序应用所有原始变换的累计效果。
      使用矩阵乘法即可。
      行向量时：给定v，变换A1和变换B1，得到v'，则，v' = v * A1 * B1
      列向量时：给定v，变换A2和变换B2，得到v'，则，v' = B2 * A2 * v.

      注意：
      1. 上述变换A或B在两种情况下是互为转置的
      2. 书上给的是行向量，而这里的代码我已改写为转置形式。

      常见的例子是渲染（rendering）。
      世界上任意位置和方向都有一个对象，我们希望在任何给定位置和方向行的相机渲染此对象。
      需要取对象的顶点（假如是某个三角形），并将它从对象空间变换到世界空间。
      这种变换称为模型变换（model transform），表示为 M(obj->wld)。
      然后使用视图变换（view transform）将世界空间顶点变换到相机空间，M(wrd->cam)。
      
        p_wrd = M(obj->wrd) * p_obj
        p_cam = M(wrd->cam) * p_wrd
              = M(wrd->cam) * (M(obj->wrd) * p_obj)
              = (M(wrd->cam) * M(obj->wrd)) * p_obj
      因此，在循环内只有一个矩阵乘法（有很多顶点）。
        记 M(obj->cam) = M(wrd->cam) * M(obj->wrd)
        则 p_cam = M(obj->cam) * p_obj
   *)
End sec_5_6.


(** * 5.7 变换的分类 *)

(** 可根据若干标准对变换进行分类 *)
(** 本节介绍的分类不是相互排斥的，也不一定遵循“顺序”或“层次结构”，
      只是每个类都可能比其他的类具有更多或更少的限制。*)

(** 一般的变换，使用映射（mapping）或函数（Function）。
      例如，映射F将a映射到b，记做F(a) = b。
      当然，我们主要对使用矩阵乘法表达的变换感兴趣。但要明白，其他映射也是可能的。
      本节还是用了矩阵的行列式（determinant），将在6.1节完整解释。*)

(** ** 5.7.1 线性变换（Linear Transformations）*)
Section sec_5_7_1.
  (** 当F为线性映射时满足的条件
      F(a + b) = F(a) + F(b) 且 F(k * a) = k * F(a) *)

  (** 这种线性变换的定义有两个重要的含义。
      1. 映射 F(a) = M * a 是一个线性变换。其中，M是方阵。因为：
         F(a+b) = M(a+b) = Ma + Mb = F(a) + F(b)
         并且 F(k * a) = M(k * a) = k * (Ma) = k * F(a)
         换言之，可使用矩阵乘法实现的任何变换都是线性变换。
      2. 任何线性变换都将零矢量变换为零矢量。
         因为 ∀k, a=F(0)=F(k0)=kF(0)=ka，所以a=0，及F(0)=0。
         因此，线性变换不包含平移。 *)
End sec_5_7_1.

(** ** 5.7.2 仿射(Affine)变换 *)
Section sec_5_7_2.
  (** 仿射变换是线性变换再加平移。因此，仿射变换集是线性变换集的超集。
   任何形如 v' = M * v + b 的变换都是仿射变换。*)
End sec_5_7_2.

(** ** 5.7.3 可逆变换 *)
Section sec_5_7_3.
  (** 一个变换是可逆的，当存在一个相反的变换，称为F的逆，它将撤销原始的操作。
      换言之，一个映射F(a)是可逆的，若存在一个逆映射F⁻¹使得这个等式对任意a成立。
        F⁻¹(F(a)) = F(F⁻¹(a)) = a
      
      仿射变换是线性变换再加平移。
      我们总是可以通过简单地平移相反的数量来“撤销”平移部分。
      所以，问题在于线性变换是否可逆。

      直觉上，除了投影之外的变换都可以撤销。因为投影会丢弃一个或多个维度的信息。
      当然，缩放时如果倍数为0，也就等效于投影，也不可撤销。
      由于任何线性变换都可表示为矩阵乘法，因此线性变换的逆相当于矩阵的逆。
      若矩阵不可逆，称它是奇异矩阵（Singular Matrix）。
      可逆矩阵的行列式非0。

      非奇异矩阵时，输入空间中只有零向量会被映射到输出空间的零向量，其他向量都会
      被映射到非零向量。
      奇异矩阵时，存在输入向量的一个完整的子空间，它被映射到零向量，称为矩阵的零空间
      （null space）。
      例如，若一个矩阵正交投影到一个包含原点的平面，该矩阵的零空间是垂直于该平面的
      所有向量，因为它们都映射到原点。
  *)
End sec_5_7_3.

(** ** 5.7.4 保持角度(angle-preserving)的变换 *)
Section sec_5_7_4.
  (** 若两个矢量之间的角度在变换后的大小或方向上没有改变，则该变换是保角的。
      只有平移、旋转和均匀缩放保角。
      保角也保留比例。
      反射变换可能改变角度的方向。
      所有保角变换都是仿射和可逆的。*)
End sec_5_7_4.

(** ** 5.7.5 正交(orthogonal)变换 *)
Section sec_5_7_5.
  (** 正交是描述矩阵的术语，当一个矩阵的行（或列）向量形成一个标准正交基时。
      orthonormal basis：向量彼此垂直并具有单位长度。
      正交变换容易计算逆。
      平移、旋转和反射是唯一的正交变换。
      所有正交变换都是仿射和可逆的，其长度、角度、面积、体积都将保留。
      由于反射不认为是一个保持角度的变换，更精确的说，正交矩阵将保留角度、面积和体积
      的大小，但其符号可能不同。
      正交矩阵的行列式为±1。*)
End sec_5_7_5.

(** ** 5.7.6 刚体(rigid body)变换 *)
Section sec_5_7_6.
  (** 指改变对象的位置和方向，但不改变其形状的变换。
      保留所有角度、长度、面积和体积。
      平移和旋转都是，但反射不被认为是严格的刚体变换。
      
      刚体变换也称为恰当的变换(proper)。
      素有刚体变换都是正交的、保角的、可逆的和仿射的。*)
End sec_5_7_6.

(** ** 5.7.6 变换类型总结 *)
Section sec_5_7_7.
  
(** 变换类型汇总
         平移 旋转 均匀缩放  非均匀缩放 正交投影 反射 错切
线性变换         Y     Y          Y        Y      Y    Y
仿射变换  Y      Y     Y          Y        Y      Y    Y
可逆变换  Y            Y          Y               Y    Y
保角变换  Y      Y     Y                                
正交变换  Y      Y                                Y     
刚体变换  Y      Y                                      
保长度的  Y      Y                                Y*    
保面体积  Y      Y                                Y    Y
行列式值  1      1    k^n                  0      -1   1
 *)
End sec_5_7_7.








