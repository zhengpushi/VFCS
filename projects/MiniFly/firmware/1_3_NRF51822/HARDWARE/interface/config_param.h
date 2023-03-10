#ifndef __CONFIG_PARAM_H
#define __CONFIG_PARAM_H
#include <stdint.h>
#include "esb.h"

/********************************************************************************	 
 * 本程序只供学习使用，未经作者许可，不得用于其它任何用途
 * ALIENTEK MiniFly
 * 配置参数驱动代码
 * 正点原子@ALIENTEK
 * 技术论坛:www.openedv.com
 * 创建日期:2017/5/2
 * 版本：V1.0
 * 版权所有，盗版必究。
 * Copyright(C) 广州市星翼电子科技有限公司 2014-2024
 * All rights reserved
********************************************************************************/

/* 默认配置参数 */
#define  VERSION	11		/*11表示V1.1*/

#define  RADIO_CHANNEL 		2
#define  RADIO_DATARATE 	esbDatarate250K
#define  RADIO_ADDRESS 		0x123456789AULL

/*无线配置结构*/
typedef struct{
	uint8_t channel;		
	EsbDatarate dataRate;
	uint32_t addressHigh;	/*通信地址高4字节*/
	uint32_t addressLow;	/*通信地址低4字节*/
}radioConfig_t;

/*保存参数结构*/
typedef struct
{
	uint8_t version;		/*软件版本号*/
	radioConfig_t radio;	/*无线配置*/
	uint8_t cksum;			/*校验*/
} configParam_t;

extern configParam_t configParam;


void configParamInit(void);
void writeConfigParamToFlash(void);
void resetConigParam(void);


#endif /*__CONFIG_PARAM_H*/
