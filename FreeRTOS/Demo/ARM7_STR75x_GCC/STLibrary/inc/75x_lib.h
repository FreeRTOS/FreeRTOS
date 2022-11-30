/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_lib.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file includes the peripherals header files in the
*                      user application.
********************************************************************************
* History:
* 07/17/2006 : V1.0
* 03/10/2006 : V0.1
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __75x_LIB_H
#define __75x_LIB_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

#ifdef _SMI
  #include "75x_smi.h"
#endif /*_SMI */

#ifdef _CFG
  #include "75x_cfg.h"
#endif /*_CFG*/

#ifdef _MRCC
  #include "75x_mrcc.h"
#endif /*_MRCC */

#ifdef _ADC
  #include "75x_adc.h"
#endif /*_ADC */

#ifdef _TB
  #include "75x_tb.h"
#endif /*_TB */

#ifdef _TIM
  #include "75x_tim.h"
#endif /*_TIM */

#ifdef _PWM
  #include "75x_pwm.h"
#endif /*_PWM */

#ifdef _WDG
  #include "75x_wdg.h"
#endif /*_WDG */

#ifdef _SSP
  #include "75x_ssp.h"
#endif /*_SSP */

#ifdef _CAN
  #include "75x_can.h"
#endif /*_CAN */

#ifdef _I2C
  #include "75x_i2c.h"
#endif /*_I2C */

#ifdef _UART
  #include "75x_uart.h"
#endif /*_UART */

#ifdef _GPIO
  #include "75x_gpio.h"
#endif /*_GPIO */

#ifdef _DMA
  #include "75x_dma.h"
#endif /*_DMA */

#ifdef _RTC
  #include "75x_rtc.h"
#endif /*_RTC */

#ifdef _EXTIT
  #include "75x_extit.h"
#endif /*_EXTIT */

#ifdef _EIC
  #include "75x_eic.h"
#endif /*_EIC */

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void debug(void);

#endif /* __75x_LIB_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
