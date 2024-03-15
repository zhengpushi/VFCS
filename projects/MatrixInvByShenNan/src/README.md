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

* 

