
最新资料下载地址:
	http://www.openedv.com/thread-105197-1-1.html

硬件资源：
	1,MCU:NRF51822 (FLAH:256K, RAM:16K, 系统运行时钟频率:16MHz) 
	2,无线通信引脚PIN19,PIN20 
	3,蓝色电源灯LED_BLUE_R连接到PIN8
	4,电源按键连接到PIN17
	5,LDO电源控制脚连接到PIN29
	6,电池充电状态检测引脚PIN1
	7,电池电压采集引脚PIN4,PIN5
	8,STM32 BOOT0控制脚PIN9
	9.STM32 NRST控制脚PIN3
	10.串口通信引脚PIN0(RX),PIN2(RTS),PIN30(TX)
	11.USB插入检测引脚PIN7

实验现象:
	短按电源键开机，开机完成后，M2机臂电源指示灯LED_BLUE_R常亮。
	开机状态下，长按电源键等待电源指示灯闪烁，无线通信配置参数恢复默认值。
	关机状态下，长按电源键等待电源指示灯闪烁，STM32进入bootloder模式。


注意事项:
	NRF51822当前的主要功能是用作无线通信和电源管理，如需要使用蓝牙功能，需要用户自己开发。
	代码下载和调试前，请将下载器开关拨到NRF51xx档。



固件更新记录:
	Firmware V1.0 Release(硬件版本:V1.32, DATE:2017-06-30)
	
	




					正点原子@ALIENTEK
					2017-6-30
					广州市星翼电子科技有限公司
					电话：020-38271790
					传真：020-36773971
					购买：http://shop62103354.taobao.com
					http://shop62057469.taobao.com
					公司网站：www.alientek.com
					技术论坛：www.openedv.com