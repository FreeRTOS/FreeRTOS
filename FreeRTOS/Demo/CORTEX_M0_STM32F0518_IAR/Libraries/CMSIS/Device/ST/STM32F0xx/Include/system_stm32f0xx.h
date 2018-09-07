/**
  ******************************************************************************
  * @file    system_stm32f0xx.h
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    27-January-2012
  * @brief   CMSIS Cortex-M0 Device Peripheral Access Layer System Header File.
  ******************************************************************************  
  * @attention
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * FOR MORE INFORMATION PLEASE READ CAREFULLY THE LICENSE AGREEMENT FILE
  * LOCATED IN THE ROOT DIRECTORY OF THIS FIRMWARE PACKAGE.
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
  ******************************************************************************
  */

/** @addtogroup CMSIS
  * @{
  */

/** @addtogroup stm32f0xx_system
  * @{
  */  
  
/**
  * @brief Define to prevent recursive inclusion
  */
#ifndef __SYSTEM_STM32F0XX_H
#define __SYSTEM_STM32F0XX_H

#ifdef __cplusplus
 extern "C" {
#endif 

/** @addtogroup STM32F0xx_System_Includes
  * @{
  */

/**
  * @}
  */


/** @addtogroup STM32F0xx_System_Exported_types
  * @{
  */

extern uint32_t SystemCoreClock;          /*!< System Clock Frequency (Core Clock) */

/**
  * @}
  */

/** @addtogroup STM32F0xx_System_Exported_Constants
  * @{
  */

/**
  * @}
  */

/** @addtogroup STM32F0xx_System_Exported_Macros
  * @{
  */

/**
  * @}
  */

/** @addtogroup STM32F0xx_System_Exported_Functions
  * @{
  */
  
extern void SystemInit(void);
extern void SystemCoreClockUpdate(void);
/**
  * @}
  */

#ifdef __cplusplus
}
#endif

#endif /*__SYSTEM_STM32F0XX_H */

/**
  * @}
  */
  
/**
  * @}
  */  
/******************* (C) COPYRIGHT 2012 STMicroelectronics *****END OF FILE****/
