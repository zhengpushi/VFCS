
Require Import VectorR.

(** ch7 极坐标系 *)

(* 笛卡尔坐标系不是精确绘制空间和定义位置的唯一系统。
   替代方案是极坐标系（Polar Coordinate System）。
   在 AI 和相机控制的领域有许多实际问题，放在极坐标的框架中可以轻松解决。*)
  
(** * 7.1 关于二维极坐标空间 *)

(** ** 7.1.1 使用二维极坐标定位点 *)
Section sec_7_1_1.
  (* 二维极坐标也有一个原点，称为极点（Pole），目的是定义了坐标空间的“中心”。
     极坐标空间只有一个轴，也称极轴（Polar Axis），被描述为来自原点的射线。
     数学文献习惯极轴指向示意图的右侧，对应于笛卡尔系统中的+x轴。

     极坐标系使用距离和角度来描述一个二维点。
     距离通常使用变量r，是半径（Radius）的缩写，角度用θ，极坐标对(r,θ)指定一个点。
     角度的正值通常是逆时针旋转，负值是顺时针旋转。角度一般使用弧度和角度都可以。*)
End sec_7_1_1.

(** ** 7.1.2 别名 *)
Section sec_7_1_2.
  (* 若两个坐标对具有不同的数值，但是空间中指向相同的点，称它们是彼此的别名(Aliasing)。
     注意，在笛卡尔空间中没有别名，点和坐标对的映射是一对一的。

     但是，别名现象不会造成任何问题：无论r和θ的值如何，都可以给出合理的解释。
     当 r < 0，被解释为反向移动（反向的位移），与 r > 0 的移动方向相反。
     当 θ 超出 [-pi, pi] 时，仍可以解释。
     换言之，空间中的点对应许多坐标对，但坐标对能唯一的空间中的一个点。

     例如，(r,θ) 和 (r,θ+k*2π) 是相同的点，只不过是增加了整体的“旋转”。
     还可以将θ加上π，并且让r变成负数来生成别名，这表示在相反反向的负位移，
     还是等于原方向的正位移。
     
     除了原点外的任何点(r,θ)，其别名的所有极坐标都可表示为 ((-1)^{k} r, θ + k π)
     
     总之，由于任何极坐标都是可以接受的。
     那么，反过来呢？空间的任意点p，究竟用哪一个极坐标呢？
     答案是：任何一个都可以，但只有一个是首选的。
     
     对于极坐标，描述任何点的“首选”方式是该点的典范（Canonical）坐标。
        r非负，并且θ在(-π,π]。当 r = 0 时，通常指定 θ = 0。*)

  (** 规范坐标需要满足的条件：
      r >= 0
      -π < θ <= π
      r = 0  =>  θ = 0 *)

  (** 将极坐标对 (r,θ) 转换为规范形式的算法:
      1. 如果 r = 0，则 (r',θ') = (0,0).
      2. 如果 r < 0，则 (r',θ') = (-r, θ + π)，并继续处理
      3. 如果 θ <= -π，则多次 θ' = θ + 2π，直到 θ' > - π
      4. 如果 θ > -π，则多次 θ' = θ - 2π，直到 θ' <= π
      注意，3,4 中的循环和判断，可以用取模和乘法运算来代替。
   *)
End sec_7_1_2.

(** ** 7.1.3 二维中笛卡尔坐标和极坐标之间的变换 *)
Section sec_7_1_3.

  (** 2D中，极坐标变换为笛卡尔坐标 *)
  Definition polar2cartesian2 (p : cvec 2) : cvec 2 :=
    let r := p.0 in
    let θ := p.1 in
    let x := (r * cos θ)%R in
    let y := (r * sin θ)%R in
    l2cv [x; y].

  (** 计算 r 可以用勾股定理。
      计算 θ 用 arctan(y/x)，但是有一些问题：
      1. 如果 x = 0，除法是未定义的
      2. arctan 的范围仅是 [-π/2, π/2]，原因是除法y/x丢失了一些有用信息。
      x和y都可以是正或负，从而有4种可能，对应于4个不同象限。但y/x得到了单个值。
      由于这些问题，使得我们需要一些“if”判断来处理每个象限。
      好消息是，有 atan2 函数，它可以正确计算所有 x 和 y 的角度，除了原点这种情况。*)

  (** atan2.
  Note that the parameters are y,x, not x,y. Because: tanθ=sinθ/cosθ=y/x

  atan2 y x =
    atan (y/x),       x > 0
    atan (y/x) + pi,  x < 0, y >= 0
    atan (y/x) - pi,  x < 0, y < 0
    +pi/2,            x = 0, y > 0
    -pi/2,            x = 0, y < 0
    undefined,        x = 0, y = 0
   *)
  Definition atan2 (y x : R) : R :=
    if x >? 0
    then atan (y/x)               (* x > 0 *)
    else
      if x <? 0
      then
        if y >=? 0
        then atan (y/x) + PI      (* x < 0, y >= 0 *)
        else atan (y/x) - PI      (* x < 0, y < 0 *)
      else
        if y >? 0
        then PI / 2               (* x = 0, y > 0 *)
        else
          if y <? 0
          then - PI / 2           (* x = 0, y < 0 *)
          else 0                  (* x = 0, y = 0 *) (* mostly, it is undefined *)
  .

  (** Automaticaly destruct inequalities on R, such as Rlt_le_dec. *)
  Ltac destruct_rineq :=
    repeat
      match goal with
      | |- context [Rlt_le_dec _ _] => destruct Rlt_le_dec
      | |- context [Rle_lt_dec _ _] => destruct Rle_lt_dec
      end; try lra.

  Lemma atan2_spec1 : forall y x, x > 0 -> atan2 y x = atan (y/x).
  Proof. intros. cbv. destruct_rineq. Qed.
  
  Lemma atan2_spec2 : forall y x, x < 0 -> y < 0 -> atan2 y x = (atan (y/x) - PI)%R.
  Proof. intros. cbv. destruct_rineq. Qed.
         
  Lemma atan2_spec3 : forall y x, x < 0 -> y >= 0 -> atan2 y x = (atan (y/x) + PI)%R.
  Proof. intros. cbv. destruct_rineq. Qed.
         
  Lemma atan2_spec4 : forall y x, x = 0 -> y > 0 -> atan2 y x = PI/2.
  Proof. intros. cbv. destruct_rineq. Qed.
  
  Lemma atan2_spec5 : forall y x, x = 0 -> y < 0 -> atan2 y x = - PI/2.
  Proof. intros. cbv. destruct_rineq. Qed.
  
  Lemma atan2_spec6 : forall y x, x = 0 -> y = 0 -> atan2 y x = 0.
  Proof. intros. cbv. destruct_rineq. Qed.

  (** 2D中，笛卡尔坐标变换为极坐标 *)
  Definition cartesian2polar2 (p : cvec 2) : cvec 2 :=
    let x := p.0 in
    let y := p.1 in
    let r := sqrt (x * x + y * y) in
    let θ := atan2 y x in
    l2cv [r; θ].

End sec_7_1_3.

(** * 7.2 为什么有人会用极坐标？ *)
(** 由于别名、度数和弧度以及三角函数的复杂性，且当笛卡尔坐标工作良好时，为何要用极坐标？
    1. 事实上，我们可能很频繁的在使用极坐标。例如，描述两个地方，A在B的东南方向1公里处。
    2. 在飞行员之间交换信息时，通常会说，“在你的6点钟方向”。还有视频游戏等场景中。
    3. 通常，摄像机、坦克等都不能瞬间移动，而目标会移动。此时，我们要以某种方式来“跟踪”
    目标。无论使用哪种类型的控制系统（无论是简单的速度限制器、滞后系统还是二阶系统），
    通常最好在极坐标中完成。
    4. 还有一个场景适合极坐标，在球体的表面上移动。精确描述地理位置的纬度和经度坐标并不是
    笛卡尔坐标，它们是极坐标，是一种称为球面坐标(Spherical Coordinate)的三维极坐标。 *)

(** * 7.3 三维极坐标空间 *)

(* 极坐标可用于三维，三维极坐标有三个值，有两种类型：
   1. 2个线性距离+1个角度：圆柱坐标（Cylindrical Coordinate）
   2. 1个线性距离+2个角度：球面坐标（Spherical Coordinate）*)

(** ** 7.3.1 圆柱坐标 *)
Section sec_7_3_1.
  (* 添加一个垂直于二维极坐标平面的z轴，可得到圆柱坐标(r,θ,z)。
     此外，表示法和惯例会有很大差异，有的表示为(ρ,ϕ,z)。而且，轴的方向和
     正向旋转的定义也可根据对实际情况最方便的任何设置来定义 *)
End sec_7_3_1.

(** ** 7.3.2 球面坐标 *)
Section sec_7_3_2.
  (* 在三维中，定义方向需要两个角度。三维球坐标中还有两个极轴：水平的+x，垂直的+y。
     数学中的惯例是两个角度 θ,ϕ。*)

  (** 使用极坐标定位三维中的点：
      这是一个右手坐标系，与+y轴夹角是ϕ，投影到+x所在的二维极坐标平面，与+x夹角是θ。
      其中，水平角θ称为方位角（Azimuth），ϕ是天顶（Zenith）。
      还有更熟悉的术语，经度（Longitude）与θ基本相同，维度（Latitude）是 π/2 - ϕ。
      径向距离r是某点到地球中心的距离，通常说的高度是与地球平均半径抵消后的值，
      以使地平面或海平面为零。*)
End sec_7_3_2.

(** ** 7.3.3 三维虚拟世界中有用的一些极坐标约定 *)
Section sec_7_3_3.
  (* 将水平角度θ重命名为h，是航向（Heading）的缩写。航向为令表示“向北”或“向前”。
     垂直角度ϕ重命名为p，是俯仰（Pitch）的缩写。俯仰角为零表示水平方向。
     
     在书上的左手系中，
     航向的正向旋转是从上方观察时顺时针。
     正俯仰值的旋转是向下的（不是很直观）。
   *)
End sec_7_3_3.

(** ** 7.3.3 球面坐标的别名 *)
Section sec_7_3_4.

(* 除了在二维极坐标中的别名问题，在三维中还有因坐标的相互依赖而引起的别名。
     当俯仰角为±π/2时（或这些值的任何别名）时，会出现奇点，称为万向节死锁（Gimbal Lock）。
     其方向是纯垂直（向上或向下），航向角无关紧要了。*)

(* 类似于二维中，也可以定义一组规范的（Canonical）球形坐标，使得三维空间中的任何点都可
   映射到规范集合中的一个坐标三元组。
   1. 俯仰角被限制在 [-π/2, π/2]
   2. 由于万向节锁时，俯仰角达到极值，航向值无关紧要，因此可规定 h = 0. *)

  (** 本书中的m秋安坐标约定，规范球面坐标满足的条件：
      r >= 0
      -π < h <= π
      -π/2 <= p <= π/2,      俯仰角最多是直上直下，不能“向后”俯仰。
      r = 0 ==> h = p = 0    原点，角度为0
      |p| = π/2 ==> h = 0    直上或直下时，航向为0。*)

  (** 将球面坐标三元组(r,h,p) 转换为规范化形式的算法：.. *)
End sec_7_3_4.

(** ** 7.3.5 球面坐标和笛卡尔坐标之间的转换 *)
Section sec_7_3_5.

  (** 数学惯例中，球面坐标转换为三维笛卡尔坐标 *)
  Definition polar2cartesian3 (p : cvec 3) : cvec 3 :=
    let r := p.0 in
    let θ := p.1 in
    let ϕ := p.2 in
    let x := (r * sin ϕ * cos θ)%R in
    let y := (r * sin ϕ * sin θ)%R in
    let z := (r * cos ϕ)%R in
    l2cv [x; y; z].

  (** 本书惯例中，球面坐标转换为三维笛卡尔坐标 *)
  Definition polar2cartesian3_book (p : cvec 3) : cvec 3 :=
    let r := p.0 in
    let h := p.1 in (* heading *)
    let p := p.2 in (* pitch *)
    let x := (r * cos p * sin h)%R in
    let y := (- r * sin p)%R in
    let z := (r * cos p * cos h)%R in
    l2cv [x; y; z].

  (** 由于别名现象，从笛卡尔坐标变换为求坐标更复杂，我们需要的是规范坐标。
      下面的推导选择航空领域的约定，这也是视频游戏中常用的惯例。*)
      
  (** 3D中，笛卡尔坐标变换为极坐标 *)
  Definition cartesian2polar3 (p : cvec 2) : cvec 2 :=
    let x := p.0 in
    let y := p.1 in
    let z := p.2 in
    let r := sqrt (x * x + y * y + z * z) in
    let h := atan2 x z in
    let p := asin (-y / r) in (* Note, the range of asin is [-π/2,π/2] *)
    l2cv [r; h; p].

End sec_7_3_5.


(** * 7.4 使用极坐标指定矢量 *)

(* 矢量与具有相同坐标的点相关。 *)

