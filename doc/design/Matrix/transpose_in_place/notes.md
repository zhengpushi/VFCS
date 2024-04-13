
* 能否原地转置？
  看到一个帖子 [二维数组行列互换原理(https://juejin.cn/s//二维数组行列互换原理)
  给出了原地转置的简单方法，经过分析，无法应用于行列不相等的情形。
  代码：
  ```
void transpose(int[][] matrix) {
    for (int i = 0; i < matrix.length; i++) {
        for (int j = i; j < matrix[0].length; j++) {
            int temp = matrix[i][j];
            matrix[i][j] = matrix[j][i];
            matrix[j][i] = temp;
        }
    }
}
  ```
  示例
  ```
  给定矩阵
  1 2 3
  4 5 6
  记作 1 2 3; 4 5 6
  
  按照外循环是行数，内循环是列数开始转置
  0,1 -- 1,0   1 4 3; 2 5 6
  0,2 -- 2,0   这里 (2,0) 元素已经不存在了。
  ```
  优点：只遍历一半，即可完成转置。
  缺点：无法对行列数不相等的矩阵做转置。
  
