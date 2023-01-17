# 第一章 复数与复变函数

## 1.1 复数

### 1.1.1 复数的基本概念

* 背景：形如 $ z = x + i~y $ 的数称为复数。其中，$x$与$y$是任意实数，依次称为$z$的实部与虚部。两个复数相等，iff，对应的实部和虚部都相等。所以，复数与一个有序实数对一一对应。

* 【定义】复数
  $$
  (x,y) : \mathbb{C}
  $$
  也写作$x + i~y$。

* 【定义】实部和虚部
  $$
  \text{Re} (x+i~y) = x,\quad\text{Im}(x+i~y)=y
  $$

* 【定义】共轭复数
  $$
  \text{Conj}(x+i~y)=x - i~y
  $$
  也写作$ \backslash z$。

### 1.1.2 复数的四则运算

假设$z_1 = x_1 + i~y_1$ 和 $z_2 = x_2 + i~y_2$ 是两个复数。

* 复数的加法和减法

  * 定义：
    $$
    z_1 \pm z_2 = (x_1 \pm x_2) + i~(y_1\pm y_2)
    $$

  * 性质

    * 结合律：
      $$
      (z_1\pm z_2)\pm z_3 = z_1\pm(z_2\pm z_3)
      $$

    * 交换律：
      $$
      z_1\pm z_2 = z_2\pm z_1
      $$

    * 共轭对加减法的分配律：
      $$
      \overline{z_1 \pm z_2} = \overline{z_1}\pm\overline{z_2}
      $$

* 复数的乘法

  * 定义：
    $$
    z_1\cdot z_2 = (x_1 x_2 - y_1 y_2) + i~(x_1 y_2 + x_2 y_1)
    $$

  * 性质

    * 结合律：
      $$
      (z_1\cdot z_2)\cdot z_3 = z_1\cdot(z_2\cdot z_3)
      $$

    * 交换律：
      $$
      z_1\cdot z_2 = z_2\cdot z_1
      $$

    * 乘法对加法的左分配律：
      $$
      z_1\cdot(z_2+z_3)=z_1\cdot z_2+z_1\cdot z_3
      $$

    * 乘法对加法的右分配律：
      $$
      (z_1+z_2)\cdot z_3=z_1\cdot z_3+z_2\cdot z_3
      $$

    * 共轭对乘法的分配律：
      $$
      \overline{z_1 \cdot z_2} = \overline{z_1}\cdot\overline{z_2}
      $$

    * 乘以共轭等于模平方：
      $$
      z\overline{z} = x^2 + y^2 = (\text{Re}~z)^2+(\text{Im}~z)^2
      $$

    * 用共轭来表达实部
      $$
      \text{Re}~z = \frac{1}{2}(z+\overline{z})
      $$
      

    * 用共轭来表达虚部
      $$
      \text{Im}~z = \frac{1}{2i}(z-\overline{z})
      $$
      

* 复数的除法

  * 定义：
    $$
    \frac{z_1}{z_2} = \frac{x_1 x_2 + y_1 y_2}{x_2^2 + y_2^2} + i\frac{x_2 y_1- x_1 y_2}{x_2^2 + y_2^2}\quad (z_2\neq0)
    $$

  * 性质

    * 共轭对除法的分配律：
      $$
      z\neq0\rightarrow\overline{(\frac{z_1}{z_2})}=\frac{\overline{z_1}}{\overline{z_2}}
      $$

* 复数的倒数（可理解为是复数除法的特殊情形，也可将复数除法理解为乘以倒数。书上并未列出）

  * 定义
    $$
    \frac{1}{z} = \frac{x - i~y}{x^2 + y^2}\quad (z_2\neq0)
    $$
    

### 1.1.3 复平面

* 背景：一个复数与一个有序实数对意义对应，并与坐标平面上的点一一对应，所以可以将整个坐标平面称为复（数）平面。

  今后，复数、复平面不加区分。在点、数等同的观点下，复数集合就是一个平面点集。于是，某些特殊的平面点集可用复数所满足的某种关系式来表示。

* 示例：用复数有关的命题来表示某个平面点集。$\{z:\mathtt{Im}~z\ge0\}$就表示了上半平面。





## 1.2 复数的三角表示

### 1.2.1 复数的模与辐角

* 模

  * 定义
    $$
    |z|=\sqrt{x^2+y^2}
    $$

  * 性质

    * 共轭的模不变
      $$
      |\overline{z}|=|z|
      $$

    * 模等平方等于该复数乘以共轭
      $$
      |z|^2=x^2+y^2=z\overline{z}
      $$

    * 倒数用模和共轭来表示的一种形式
      $$
      \frac{1}{z} = \frac{\overline{z}}{z\overline{z}}=\frac{\overline{z}}{|z|^2}\quad (z_2\neq0)
      $$
      

    * 模与实部和虚部之间的一些不等式
      $$
      |x|\le|z|,\quad|y|\le|z|,\quad||x|-|y||\le|z|\le|x|+|y|
      $$

* 

* 主辐角，本书定义为$(-\pi,\pi]$之间，有的书定义为$[0,2\pi)$之间

  * 定义
    $$
    \text{arg}(z)=\left\{\begin{align*}
    &\arctan\frac{y}{x},&x>0\\
    &\frac{\pi}{2},&x=0,y>0\\
    &\arctan\frac{y}{x}+\pi,&x<0,y>=0\\
    &\arctan\frac{y}{x}-\pi,&x<0,y<0\\
    &-\frac{\pi}{2},&x=0,y<0\\
    \end{align*}\right.
    $$

  * 性质

    * 非零复数的共轭的辐角满足如下关系
      $$
      z\neq0\rightarrow arg~\overline{z}=\left\{\begin{align*}
      &-~arg~z, &z不是负实数时\\
      &=\pi=arg~z,&z为负实数时
      \end{align*}\right.
      $$
      

    * 

* 辐角。辐角有无穷多个值，任意两个值相差$2\pi$的整数倍。

  * 定义
    $$
    \text{Arg}(z)=\text{arg}(z)+2k\pi, k\in\mathbb{Z}\quad(z\neq0)
    $$

  * 性质

    * 非零复数，实部等于模长乘以辐角的余弦，虚部等于模长乘以辐角的正弦
      $$
      z\neq0\rightarrow x=|z|\cos~\text{Arg}~z,\quad z\neq0\rightarrow y=|z|\sin~\text{Arg}~z
      $$
      

### 1.2.2 复数模的三角不等式

* 背景：由于复数的加法可用向量相加的三角形法则作图，类似的复数减法也可类似作图。三角形两边长之和大于第三边长，两边长之差小于第三边长。

* 性质

  * 复数和的模的三角不等式
    $$
    ||z_1|-|z_2||\le|z_1-z_2|\le|z_1|+|z_2|
    $$

  * 复数差的模的三角不等式
    $$
    ||z_1|-|z_2||\le|z_1+z_2|\le|z_1|+|z_2|
    $$
    注意：上述两组不等式的证明，可参考书上的利用共轭的证明思路。

### 1.2.3 复数的三角表示

* 复数的（坐标表示）与复数的三角表示，二者可以互相转换

  * 定义
    $$
    (\rho, \theta):\mathbb{C}
    $$

  * 转换
    $$
    (\rho,\theta)=\rho(\cos\theta+i\sin\theta),\quad
    z=x+iy=(|z|,\angle z)
    $$
    

  * 

* 





## 1.3 平面点集的一般概念





## 1.4 无穷大与复球面





## 1.5 复变函数



