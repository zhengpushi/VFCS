#ifndef __UARTLINK_H
#define __UARTLINK_H
#include <stdbool.h>
#include "atkp.h"

/********************************************************************************	 
 * 本程序只供学习使用，未经作者许可，不得用于其它任何用途
 * ALIENTEK MiniFly
 * 串口连接通信代码
 * 正点原子@ALIENTEK
 * 技术论坛:www.openedv.com
 * 创建日期:2017/5/2
 * 版本：V1.0
 * 版权所有，盗版必究。
 * Copyright(C) 广州市星翼电子科技有限公司 2014-2024
 * All rights reserved
********************************************************************************/

typedef enum
{
	waitForStartByte1,
	waitForStartByte2,
	waitForMsgID,
	waitForDataLength,
	waitForData,
	waitForChksum1,
	state_done
} uartLinkRxSate_e;

bool uartlinkReceiveATKPPacket(atkp_t *packet);
bool uartlinkSendATKPPacket(atkp_t *packet);

#endif

