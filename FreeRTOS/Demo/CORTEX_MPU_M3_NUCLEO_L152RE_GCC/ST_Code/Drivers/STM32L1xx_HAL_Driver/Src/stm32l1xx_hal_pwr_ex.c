/**
  ******************************************************************************
  * @file    stm32l1xx_hal_pwr_ex.c
  * @author  MCD Application Team
  * @brief   Extended PWR HAL module driver.
  *          This file provides firmware functions to manage the following
  *          functionalities of the Power Controller (PWR) peripheral:
  *           + Extended Initialization and de-initialization functions
  *           + Extended Peripheral Control functions
  *
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; Copyright (c) 2017 STMicroelectronics.
  * All rights reserved.</center></h2>
  *
  * This software component is licensed by ST under BSD 3-Clause license,
  * the "License"; You may not use this file except in compliance with the
  * License. You may obtain a copy of the License at:
  *                        opensource.org/licenses/BSD-3-Clause
  *
  ******************************************************************************
  */

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx_hal.h"

/** @addtogroup STM32L1xx_HAL_Driver
  * @{
  */

/** @defgroup PWREx PWREx
  * @brief    PWR HAL module driver
  * @{
  */

#ifdef HAL_PWR_MODULE_ENABLED

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/** @defgroup PWREx_Exported_Functions PWREx Exported Functions
  * @{
  */

/** @defgroup PWREx_Exported_Functions_Group1 Peripheral Extended Features Functions
  * @brief    Low Power modes configuration functions
  *
@verbatim

 ===============================================================================
                 ##### Peripheral extended features functions #####
 ===============================================================================
@endverbatim
  * @{
  */

/**
  * @brief Return Voltage Scaling Range.
  * @retval VOS bit field (PWR_REGULATOR_VOLTAGE_SCALE1, PWR_REGULATOR_VOLTAGE_SCALE2 or PWR_REGULATOR_VOLTAGE_SCALE3)
  */
uint32_t HAL_PWREx_GetVoltageRange(void)
{
  return  (PWR->CR & PWR_CR_VOS);
}


/**
  * @brief  Enables the Fast WakeUp from Ultra Low Power mode.
  * @note   This bit works in conjunction with ULP bit.
  *         Means, when ULP = 1 and FWU = 1 :VREFINT startup time is ignored when
  *         exiting from low power mode.
  * @retval None
  */
void HAL_PWREx_EnableFastWakeUp(void)
{
  /* Enable the fast wake up */
  *(__IO uint32_t *) CR_FWU_BB = (uint32_t)ENABLE;
}

/**
  * @brief  Disables the Fast WakeUp from Ultra Low Power mode.
  * @retval None
  */
void HAL_PWREx_DisableFastWakeUp(void)
{
  /* Disable the fast wake up */
  *(__IO uint32_t *) CR_FWU_BB = (uint32_t)DISABLE;
}

/**
  * @brief  Enables the Ultra Low Power mode
  * @retval None
  */
void HAL_PWREx_EnableUltraLowPower(void)
{
  /* Enable the Ultra Low Power mode */
  *(__IO uint32_t *) CR_ULP_BB = (uint32_t)ENABLE;
}

/**
  * @brief  Disables the Ultra Low Power mode
  * @retval None
  */
void HAL_PWREx_DisableUltraLowPower(void)
{
  /* Disable the Ultra Low Power mode */
  *(__IO uint32_t *) CR_ULP_BB = (uint32_t)DISABLE;
}

/**
  * @brief  Enters the Low Power Run mode.
  * @note   Low power run mode can only be entered when VCORE is in range 2.
  *         In addition, the dynamic voltage scaling must not be used when Low
  *         power run mode is selected. Only Stop and Sleep modes with regulator
  *         configured in Low power mode is allowed when Low power run mode is
  *         selected.
  * @note   In Low power run mode, all I/O pins keep the same state as in Run mode.
  * @retval None
  */
void HAL_PWREx_EnableLowPowerRunMode(void)
{
  /* Enters the Low Power Run mode */
  *(__IO uint32_t *) CR_LPSDSR_BB = (uint32_t)ENABLE;
  *(__IO uint32_t *) CR_LPRUN_BB  = (uint32_t)ENABLE;
}

/**
  * @brief  Exits the Low Power Run mode.
  * @retval None
  */
HAL_StatusTypeDef HAL_PWREx_DisableLowPowerRunMode(void)
{
  /* Exits the Low Power Run mode */
  *(__IO uint32_t *) CR_LPRUN_BB  = (uint32_t)DISABLE;
  *(__IO uint32_t *) CR_LPSDSR_BB = (uint32_t)DISABLE;
  return HAL_OK;
}

/**
  * @}
  */

/**
  * @}
  */

#endif /* HAL_PWR_MODULE_ENABLED */
/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
