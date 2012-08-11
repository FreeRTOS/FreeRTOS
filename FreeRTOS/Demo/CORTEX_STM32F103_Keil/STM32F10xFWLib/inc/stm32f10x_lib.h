/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_lib.h
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file includes the peripherals header files in the
*                      user application.
********************************************************************************
* History:
* 04/02/2007: V0.2
* 02/05/2007: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F10x_LIB_H
#define __STM32F10x_LIB_H

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_map.h"

#ifdef _ADC
  #include "stm32f10x_adc.h"
#endif /*_ADC */

#ifdef _BKP
  #include "stm32f10x_bkp.h"
#endif /*_BKP */

#ifdef _CAN
  #include "stm32f10x_can.h"
#endif /*_CAN */

#ifdef _DMA
  #include "stm32f10x_dma.h"
#endif /*_DMA */

#ifdef _EXTI
  #include "stm32f10x_exti.h"
#endif /*_EXTI */

#ifdef _FLASH
  #include "stm32f10x_flash.h"
#endif /*_FLASH */

#ifdef _GPIO
  #include "stm32f10x_gpio.h"
#endif /*_GPIO */

#ifdef _I2C
  #include "stm32f10x_i2c.h"
#endif /*_I2C */

#ifdef _IWDG
  #include "stm32f10x_iwdg.h"
#endif /*_IWDG */

#ifdef _NVIC
  #include "stm32f10x_nvic.h"
#endif /*_NVIC */

#ifdef _PWR
  #include "stm32f10x_pwr.h"
#endif /*_PWR */

#ifdef _RCC
  #include "stm32f10x_rcc.h"
#endif /*_RCC */

#ifdef _RTC
  #include "stm32f10x_rtc.h"
#endif /*_RTC */

#ifdef _SPI
  #include "stm32f10x_spi.h"
#endif /*_SPI */

#ifdef _SysTick
  #include "stm32f10x_systick.h"
#endif /*_SysTick */

#ifdef _TIM1
  #include "stm32f10x_tim1.h"
#endif /*_TIM1 */

#ifdef _TIM
  #include "stm32f10x_tim.h"
#endif /*_TIM */

#ifdef _USART
  #include "stm32f10x_usart.h"
#endif /*_USART */

#ifdef _WWDG
  #include "stm32f10x_wwdg.h"
#endif /*_WWDG */

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void debug(void);

#endif /* __STM32F10x_LIB_H */

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
