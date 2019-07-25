/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_lib.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : Used to include the peripherals header file in the
*                      user application.
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
* CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
* A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
* OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
* OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
* CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

#ifndef __91x_LIB_H
#define __91x_LIB_H

#include "91x_map.h"
#include "91x_conf.h"

#ifdef _AHBAPB
  #include "91x_ahbapb.h"
#endif /* _AHBAPB */

#ifdef _EMI
  #include "91x_emi.h"
#endif /* _EMI */

#ifdef _DMA
  #include "91x_dma.h"
#endif /* _DMA */

#ifdef _FMI
  #include "91x_fmi.h"
#endif /* _FMI */

#ifdef _VIC
  #include "91x_vic.h"
#endif /* _VIC */

#ifdef _WIU
  #include "91x_wiu.h"
#endif /* _WIU */

#ifdef _TIM
  #include "91x_tim.h"
#endif /* _TIM */

#ifdef _GPIO
  #include "91x_gpio.h"
#endif /* _GPIO */

#ifdef _RTC
  #include "91x_rtc.h"
#endif /* _RTC */

#ifdef _SCU
  #include "91x_scu.h"
#endif /* _SCU */

#ifdef _UART
  #include "91x_uart.h"
#endif /* _UART */

#ifdef _SSP
  #include "91x_ssp.h"
#endif /* _SSP */

#ifdef _CAN
  #include "91x_can.h"
#endif /* _CAN */

#ifdef _ADC
  #include "91x_adc.h"
#endif /* _ADC */

#ifdef _WDG
  #include "91x_wdg.h"
#endif /* _WDG */

#ifdef _I2C
  #include "91x_i2c.h"
#endif /* _I2C */

#ifdef _WIU
  #include "91x_wiu.h"
#endif

#ifdef _MC
  #include "91x_mc.h"
#endif

#ifdef _ENET
  #include "91x_enet.h"  
#endif 

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* Module private variables --------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

 void debug( void );


#endif /* __91x_LIB_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
