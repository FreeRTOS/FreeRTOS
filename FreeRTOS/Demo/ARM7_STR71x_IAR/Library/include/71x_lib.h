/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : 71x_lib.h
* Author             : MCD Application Team
* Date First Issued  : 05/16/2003
* Description        : Global include for all peripherals
********************************************************************************
*  30/11/2004 : V2.0
*  14/07/2004 : V1.3
*  01/01/2004 : V1.2
*******************************************************************************
 THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
 CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
 AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
 OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
 OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
 CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#ifndef __71x_LIB_H
#define __71x_LIB_H

#include "71x_map.h"
#include "71x_conf.h"


#ifdef _ADC12
  #include "adc12.h"
#endif

#ifdef _APB
  #include "apb.h"
#endif

#ifdef _BSPI
  #include "bspi.h"
#endif

#ifdef _CAN
  #include "can.h"
#endif

#ifdef _EIC
  #include "eic.h"
#endif

#ifdef _EMI
  #include "emi.h"
#endif

#ifdef _FLASH
  #include "flash.h"
#endif

#ifdef _GPIO
  #include "gpio.h"
#endif

#ifdef _I2C
  #include "i2c.h"
#endif

#ifdef _PCU
  #include "pcu.h"
#endif

#ifdef _RCCU
  #include "rccu.h"
#endif

#ifdef _RTC
  #include "rtc.h"
#endif

#ifdef _TIM
  #include "tim.h"
#endif

#ifdef _UART
  #include "uart.h"
#endif

#ifdef _USB
#endif

#ifdef _WDG
  #include "wdg.h"
#endif

#ifdef _XTI
  #include "xti.h"
#endif


#ifdef DEBUG
  void debug(void);
#endif

#endif /* __71x_LIB_H */

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
