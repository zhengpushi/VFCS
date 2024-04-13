
* 点评
  * 我们工作的优势（也是他们工作的劣势）
	* 我们的向量和矩阵库是基于抽象元素的，从向量的运算，到正交矩阵(旋转矩阵)理论等。
	  而且是分层的，使得不同数域上的元素都可以复用这些形式化的定义和性质。
	  而且向量是支持无限嵌套的。
	  并且开发了有限集有关的一系列转换过程。
	* 从几何分析的角度直观的推导了罗德里格斯公式，四元数旋转公式。
	* 也证明了SO(n,F)的多个保持性质。
	* 我们的向量和矩阵库具有统一的命名风格，以v或m开头。
	* 给出了四元数表示旋转的完整证明过程。
	* 我们的代码可立即执行，也能抽取出简洁的Coq代码，源于简单的结构（相比MathComp而言）
  * 他们工作的优势
	* 给出了line，frame的定义，使得讨论比较明确。
	* 给出了一些应用。

------------------------------
* 特点
  * 使用Coq 和 Math Comp库
* 优势
  * 数学内容较多
  * 将角度arg定义为长度为1的复数（也就是(x,y)两个分量，难道是从正x轴出发的角度吗？那么3D呢？）
	定义了特定角度，如将 pi 定义为 (-1,0)，0 定义为 (1,0)。
  * 使用Module构造和复用了正交矩阵、旋转矩阵等定义。
* 缺点
  * SCARA 是4个自由度相对简单
  * MathComp库的嵌套层次、语法结构都较复杂，不容易入手。
  * MC库中的向量 `rV[R]_n`是行向量，默认使用了行向量。而我们使用了向量、行向量、列向量三种类型。
  * 点积使用了矩阵乘法后取出第一个元素（这是由于行向量实际上是矩阵）而造成的复杂性。
	相比而言，我们的库是纯粹的向量类型，与矩阵进行了明显的区分。
  * 叉乘运算使用了行列式和数乘、加法等才构造出，表达式也很冗长，数学上不直观。也许是因为缺乏取出元素的操作。
* 值得借鉴的一些写作技巧
  * This requires to formalize a large amount of three-dimensional
  geometry because robotics uses a wide variety of representations for rotations and 
  rigid body transformations related by non-trivial mathematical properites.
  * 层次分的很细，对于每个概念，定义是一节，性质是一节，应用又是一节。
* 阅读些技术
  * Ch3
	* 将 (u \x v) \x w = <u,w> .* v - <u,v> .* w 作为技术特色展示。实际上，我证明的保持c1\x c2=c3更困难。
	* 表格比较好，三列：函数名签名，coq定义，纸笔定义。
	* 直线定义为 (点+向量) 的对偶，两者的类型都是行向量。放在Module中的做法，以及 Line.point 的语法很是精致。
	判断一个点在直线上，是通过 p - pt 和 dir 是否平行来说明的。
	还定义了平行，垂直，共面等。
	* 定义了NoFrame（包含一个正交矩阵），定义了Frame（旋转矩阵），定义了典范基下的Frame，带有原点的positive frame，
	此时可以导出x,y,z轴，它们是向量。
	* 定义了从一个向量来构造frame的方法，依赖两个函数 j i 和 k i，它们只需要给定i参数即可。
    * Frame的旋转。
  * ch4：旋转和旋转矩阵
	* 定义了谓词 isRot，抽象出了旋转的作用 f : vec -> vec，它要满足 f(j)=cos(a)j+sin(a)k, f(k)=-sin(a)j+cos(a)k
	* 证明了满足 isRot 谓词的一个函数 f，都可以导出一个旋转矩阵。
	  反之，任给一个旋转矩阵，都能找到一个轴，以及一个角。说这是欧拉定理 euler，但我没看懂。
  * ch5 旋转的指数坐标（也就是轴和角），其实等价于罗德里格斯公式。
	* 旋转可用反对称矩阵的指数来表示。
	一般的，矩阵的指数是一个幂级数，而对于斜对称矩阵，它是一个封闭的表达式
	e^(a*S(w))=1+sin(a)*S(w)+(1-cos(a))*S(w)^2，其中a是角度，S(w)是向量w的斜对称矩阵。
	* 定义了斜对称矩阵，以及转换为指数的函数 emx3，并定义了rodrigues公式，证明了罗德里格斯公式等于指数形式。
	* 证明指数形式和旋转是等价的。
  * ch6 旋转的其他表示
	* Angle-Axis表示
	* Rotation Using Quaternions
	  四元数构成了环(ringType)，以及 scaling(lmodType) 和 units (unitRingType)
  * ch7 刚体变换的形式化
	* 刚体变换是一个映射：vec3 -> vec 3，它保持长度和朝向。当映射保长度时称为 isometry（等距）
	  提到了 Murray et al. 1994 Ch2,Sect.1 定义了朝向保持=叉乘保持。f(u\x v)=f(u)\x f(v)，只是提到了别人的工作。
	* 定义了谓词：保持朝向。
  * ch8 使用 Homogeneous Representation 进行刚体变换
	* 刚体表示可以用 Special Euclidean group 表示，它是（平移+旋转的对偶）
  * ch9 DH惯例：Denavit-Hartenberg
  * ch10 Screw Motions 螺旋运动
	* 指数形式
  * ch11 相关工作
  * ch12 总结
  
	
