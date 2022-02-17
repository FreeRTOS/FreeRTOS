/**
  ******************************************************************************
  * @file    	    config.h
  * @author  	    FMD AE
  * @brief   		config Header File.             	
  * @version 	    V1.0.0           
  * @data		    2021-09-27
  ******************************************************************************
  * @attention
  * COPYRIGHT (C) 2021 Fremont Micro Devices (SZ) Corporation All rights reserved.
  *    This software is provided by the copyright holders and contributors,and the
  *software is believed to be accurate and reliable. However, Fremont Micro Devices
  *(SZ) Corporation assumes no responsibility for the consequences of use of such
  *software or for any infringement of patents of other rights of third parties,
  *which may result from its use. No license is granted by implication or otherwise
  *under any patent rights of Fremont Micro Devices (SZ) Corporation.
  *  ******************************************************************************
  */

#ifndef __CONFIG_H__
#define __CONFIG_H__
#ifdef __cplusplus
extern "C" {
#endif
#ifndef TRUE
    #define TRUE  1
#endif

#ifndef FALSE
    #define FALSE 0
#endif

#ifndef NULL
    #define NULL  0
#endif

typedef enum
{
  reFALSE = 0,
  reTRUE,
}BOOL;

#ifdef __cplusplus
}
#endif

/* Includes ---------------------------------------------------------------------*/
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <appconfig.h>
#include <stdio.h>
//#include "stdio.h"  
#include "ft32f0xx.h"
#include "ft32f0xx_adc.h"
#include "ft32f0xx_comp.h"
#include "ft32f0xx_crc.h"
#include "ft32f0xx_crs.h"
#include "ft32f0xx_dac.h"
#include "ft32f0xx_dma.h"
#include "ft32f0xx_debug.h"
#include "ft32f0xx_exti.h"
#include "ft32f0xx_flash.h"
#include "ft32f0xx_gpio.h"
#include "ft32f0xx_i2c.h"
#include "ft32f0xx_iwdg.h"
#include "ft32f0xx_misc.h" 
#include "ft32f0xx_opa.h"
#include "ft32f0xx_pwr.h"
#include "ft32f0xx_rcc.h"
#include "ft32f0xx_rtc.h"
#include "ft32f0xx_spi.h"
#include "ft32f0xx_syscfg.h"
#include "ft32f0xx_tim.h"
#include "ft32f0xx_usart.h"
#include "ft32f0xx_wwdg.h"

#include "board.h" 
#include "Peripheral.h"

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "TaskManager.h"
#include "InitTask.h"
/* Public Constant prototypes----------------------------------------------------*/
/* Public typedef ---------------------------------------------------------------*/

/* Public define ----------------------------------------------------------------*/
#define DEFINE_OBJECT_IN_ROM(type, object)  __root const type object @ ".text"
#define container_of(ptr, type, member) (type *)( ((unsigned long)ptr)- offsetof(type,member))
#define XMK_STR(x)				#x
#define MK_STR(x) 				XMK_STR(x)

#define CLR_BIT(data, bit)			((data) &= (~(0x01 << (bit))))
#define CPL_BIT(data, bit)			((data) ^= ((0x01 << (bit))))
#define GET_BIT(data, bit)			(((data) & (0x01 << (bit))) == (0x01 << (bit)))

#define SET_BIT_EX(data, bit)		SET_BIT(data[(bit) / (sizeof(data[0]) * 8)], ((bit) % (sizeof(data[0]) * 8)))
#define CLR_BIT_EX(data, bit)		CLR_BIT(data[(bit) / (sizeof(data[0]) * 8)], ((bit) % (sizeof(data[0]) * 8)))
#define CPL_BIT_EX(data, bit)		CPL_BIT(data[(bit) / (sizeof(data[0]) * 8)], ((bit) % (sizeof(data[0]) * 8)))
#define GET_BIT_EX(data, bit)		GET_BIT(data[(bit) / (sizeof(data[0]) * 8)], ((bit) % (sizeof(data[0]) * 8)))
#define ARRAYLEN(array)				(sizeof(array) / sizeof(array[0]))
#define OFFSETOF(s,m)			    ((int)&(((s*)NULL)->m))
#define SIZEOFFIELD(s,m)			sizeof((((s)*)NULL)->m)
#define SIZEBETWEEN(s,m1,m2)       (OFFSETOF(s,m2)-OFFSETOF(s,m1)) 
/* Public variables prototypes --------------------------------------------------*/


/* Public function prototypes----------------------------------------------------*/


#endif
/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/

