/**
  ******************************************************************************
  * @file    stm32f0xx_dbgmcu.h
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    27-January-2012
  * @brief   This file contains all the functions prototypes for the DBGMCU firmware 
  *          library.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F0XX_DBGMCU_H
#define __STM32F0XX_DBGMCU_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f0xx.h"

/** @addtogroup STM32F0xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup DBGMCU
  * @{
  */ 
/* Exported types ------------------------------------------------------------*/ 
/* Exported constants --------------------------------------------------------*/


/** @defgroup DBGMCU_Exported_Constants
  * @{
  */

#define DBGMCU_STOP                  DBGMCU_CR_DBG_STOP
#define DBGMCU_STANDBY               DBGMCU_CR_DBG_STANDBY
#define IS_DBGMCU_PERIPH(PERIPH) ((((PERIPH) & 0xFFFFFFF9) == 0x00) && ((PERIPH) != 0x00))

#define DBGMCU_TIM2_STOP             DBGMCU_APB1_FZ_DBG_TIM2_STOP
#define DBGMCU_TIM3_STOP             DBGMCU_APB1_FZ_DBG_TIM3_STOP
#define DBGMCU_TIM6_STOP             DBGMCU_APB1_FZ_DBG_TIM6_STOP
#define DBGMCU_TIM14_STOP            DBGMCU_APB1_FZ_DBG_TIM14_STOP
#define DBGMCU_RTC_STOP              DBGMCU_APB1_FZ_DBG_RTC_STOP
#define DBGMCU_WWDG_STOP             DBGMCU_APB1_FZ_DBG_WWDG_STOP
#define DBGMCU_IWDG_STOP             DBGMCU_APB1_FZ_DBG_IWDG_STOP
#define DBGMCU_I2C1_SMBUS_TIMEOUT    DBGMCU_APB1_FZ_DBG_I2C1_SMBUS_TIMEOUT
#define IS_DBGMCU_APB1PERIPH(PERIPH) ((((PERIPH) & 0xFFDFE2EC) == 0x00) && ((PERIPH) != 0x00))

#define DBGMCU_TIM1_STOP             DBGMCU_APB2_FZ_DBG_TIM1_STOP
#define DBGMCU_TIM15_STOP            DBGMCU_APB2_FZ_DBG_TIM15_STOP
#define DBGMCU_TIM16_STOP            DBGMCU_APB2_FZ_DBG_TIM16_STOP
#define DBGMCU_TIM17_STOP            DBGMCU_APB2_FZ_DBG_TIM17_STOP
#define IS_DBGMCU_APB2PERIPH(PERIPH) ((((PERIPH) & 0xFFF8F7FF) == 0x00) && ((PERIPH) != 0x00))

/**
  * @}
  */ 

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */ 

/* Device and Revision ID management functions ********************************/ 
uint32_t DBGMCU_GetREVID(void);
uint32_t DBGMCU_GetDEVID(void);

/* Peripherals Configuration functions ****************************************/ 
void DBGMCU_Config(uint32_t DBGMCU_Periph, FunctionalState NewState);
void DBGMCU_APB1PeriphConfig(uint32_t DBGMCU_Periph, FunctionalState NewState);
void DBGMCU_APB2PeriphConfig(uint32_t DBGMCU_Periph, FunctionalState NewState);

#ifdef __cplusplus
}
#endif

#endif /* __STM32F0XX_DBGMCU_H */

/**
  * @}
  */ 

/**
  * @}
  */ 

/******************* (C) COPYRIGHT 2012 STMicroelectronics *****END OF FILE****/
