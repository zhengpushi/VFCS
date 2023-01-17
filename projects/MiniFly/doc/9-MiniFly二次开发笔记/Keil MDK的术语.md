# Keil MDK的术语

* Program Size: Code, RO-data, RW-data, ZI-data
  * Code (inc. data)：代码和数据
    * code：程序代码部分
    * inline data. 例如，literal pools(文字常量池), short strings(短字符串)
  * RO-data: 只读数据
    * 除inline data之外的所有只读数据
  * RW-data: 可读写的数据，将会放入RAM
  * ZI-data: 零初始化的可读写变量
    * keil编译器默认把未初始化的变量都赋值为0,。初始化为零活未初始化的变量，都存储于此。
* 存储空间
  * RO size: Code + RO-data
  * RW size: RW-data + ZI-data
  * Total ROM size = Code + RO_data + RW_data，下载程序到FLASH/ROM时，所占用的最小空间。
    * 为什么Rom要存RW？因上电时要给它们一个初始值。
    * 为什么Rom不存ZI？因为上电时会对ZI所在区域清零，包含了反而浪费存储空间。
  * RAM size: RW_data + ZI-data，程序运行时，RAM使用的空间 
* ARM程序包含3部分：RO段、RW段和ZI段
  * RO是程序中的指令和常量
  * RW是程序中的已初始化变量
  * ZI是程序中的零初始化的变量