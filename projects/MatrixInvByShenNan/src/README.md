# Rebuild MatrixInv

## 1. Introduction

* MatrixInv 是由沈楠写的逆矩阵形式化的库，当时使用了基于记录的矩阵结构，以及oemga库。目前，这些库已经无法使用，所以代码也无法编译。
* 基于记录的矩阵库已经整合到了 CoqMatrix 项目，并且具有统一的命名，层次结构等优点。准备用该库来代替原本的底层矩阵库。
* MatrixInv库的代码有些凌乱，可以整理并加深理解。
* 适当简化证明，但函数名和引理名称不做修改。
* 增加更多注释，方便理解。
* 使用 Hierarchy 中的 Ring, Field 等抽象结构，已经 ring, field 等策略帮助证明。

## 2. 逆矩阵的实现和证明
* 第一部分，大量参考了 nat_fun 的设计，比如 sum, sum_eq, sum_add, sum_single 等
* rowSwap, rowK, rowAdd 分别是三个单独的矩阵；
  而我的实现中它们是函数作用，并非单独矩阵。
  我是另外做了RowOp2Mat的转换，即 rowSwap(mat1) 的结果。
* 由于“基于记录”和“基于函数”这两个模型的差异，遗留了很多公理。

## 3. 文件列表
* MatrixInv.v
  无法运行的版本，因Matrix库和omega库导致。
* MatrixInv_v1.v
  适配了CoqMatrix的能够运行的版本，少量调整代码顺序。该版本有很多公理，且代码较为冗长。
* MatrixInv_v11.v
  在 v1 基础上大量改动，统一命名，简化证明，改进注释，便于理解。
* MatrixInv_v111.v
  在 v11 基础上改用 SafeNatFun 模型，进一步简化证明（去掉公理部分）。
* MatrixInv_v12.v
  在 v1 基础上切换其他矩阵模型立即能够编译。(目前是SafeNatFun，其余模型需要增加一个 f2m 的接口)
* MatrixInv_v3.v
  在 v111 基础上，进一步精简，与 fin 模型的矩阵保持一致。

