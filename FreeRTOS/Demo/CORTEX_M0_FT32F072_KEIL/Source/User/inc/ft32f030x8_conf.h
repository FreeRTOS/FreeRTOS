/**
  ******************************************************************************
  * @file    Project/FT32F030X8_StdPeriph_Templates/ft32f030x8_conf.h 
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    2020-06-22
  * @brief   Library configuration file.
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __FT32F030X8_CONF_H
#define __FT32F030X8_CONF_H

/* Includes ------------------------------------------------------------------*/
/* Comment the line below to disable peripheral header file inclusion */
#include "ft32f030x8_adc.h"
#include "ft32f030x8_crc.h"
#include "ft32f030x8_crs.h"
#include "ft32f030x8_comp.h"
#include "ft32f030x8_dac.h"
#include "ft32f030x8_dbgmcu.h"
#include "ft32f030x8_dma.h"
#include "ft32f030x8_exti.h"
#include "ft32f030x8_flash.h"
#include "ft32f030x8_gpio.h"
#include "ft32f030x8_syscfg.h"
#include "ft32f030x8_i2c.h"
#include "ft32f030x8_iwdg.h"
#include "ft32f030x8_pwr.h"
#include "ft32f030x8_rcc.h"
#include "ft32f030x8_rtc.h"
#include "ft32f030x8_spi.h"
#include "ft32f030x8_tim.h"
#include "ft32f030x8_usart.h"
#include "ft32f030x8_wwdg.h"
#include "ft32f030x8_misc.h"  /* High level functions for NVIC and SysTick (add-on to CMSIS functions) */

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* Uncomment the line below to expanse the "assert_param" macro in the 
   Standard Peripheral Library drivers code */
/* #define USE_FULL_ASSERT    1 */

/* Exported macro ------------------------------------------------------------*/
#ifdef  USE_FULL_ASSERT

/**
  * @brief  The assert_param macro is used for function's parameters check.
  * @param  expr: If expr is false, it calls assert_failed function which reports 
  *         the name of the source file and the source line number of the call 
  *         that failed. If expr is true, it returns no value.
  * @retval None
  */
  #define assert_param(expr) ((expr) ? (void)0 : assert_failed((uint8_t *)__FILE__, __LINE__))
/* Exported functions ------------------------------------------------------- */
  void assert_failed(uint8_t* file, uint32_t line);
#else
  #define assert_param(expr) ((void)0)
#endif /* USE_FULL_ASSERT */

#endif /* __FT32F030X8_CONF_H */

/************************ (C) COPYRIGHT FMD *****END OF FILE****/
