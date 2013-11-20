/**
  ******************************************************************************
  * @file    tsl_time_stm32f3xx.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the timing with STM32F3xx products.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2013 STMicroelectronics</center></h2>
  *
  * Licensed under MCD-ST Liberty SW License Agreement V2, (the "License");
  * You may not use this file except in compliance with the License.
  * You may obtain a copy of the License at:
  *
  *        http://www.st.com/software_license_agreement_liberty_v2
  *
  * Unless required by applicable law or agreed to in writing, software
  * distributed under the License is distributed on an "AS IS" BASIS,
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  *
  ******************************************************************************
  */

/* Includes ------------------------------------------------------------------*/
#include "tsl_time_stm32f3xx.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/
/* Private macros ------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private functions prototype -----------------------------------------------*/

/**
  * @brief  Initialization of the timing module.
  * @param  None
  * @retval Status Return TSL_STATUS_ERROR if the Systick configuration has failed.
  */
TSL_Status_enum_T TSL_tim_Init(void)
{
  // Program one systick interrupt every (1 / TSLPRM_TICK_FREQ) ms
  if (SysTick_Config(SystemCoreClock / TSLPRM_TICK_FREQ))
  {
    return TSL_STATUS_ERROR;
  }
  else
  {
    return TSL_STATUS_OK;
  }
}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
