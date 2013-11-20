/**
  ******************************************************************************
  * @file    tsl_time_stm8tl5x.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the timing with STM8TL5x products.
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
#include "tsl_time_stm8tl5x.h"
#include "tsl_time.h"
#include "stm8tl5x_it.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/
/* Private macros ------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private functions prototype -----------------------------------------------*/

/**
  * @brief  Initialization of the timing module to generate periodic interruptions
  * @warning The CPU frequency must be equal to 16 MHz
  * @param  None
  * @retval Status Return TSL_STATUS_ERROR if the CPU freq in uncorrect.
  */
TSL_Status_enum_T TSL_tim_Init(void)
{
  CLK->PCKENR1 |= CLK_PCKENR1_TIM4; // The peripheral clock are not enable by default

  if (CLK->CKDIVR != 0x00) // The CPU frequency must be equal to 16 MHz
  {
    return TSL_STATUS_ERROR;
  }

  TIM4->SR1 = 0; // Clear overflow flag

#if (TSLPRM_TICK_FREQ == 2000)
  TIM4->PSCR = 6; // 16 MHz / 64 = 4 us clock
  TIM4->ARR = 124; // 125 * 4 us = 0.5 ms
#endif

#if (TSLPRM_TICK_FREQ == 1000)
  TIM4->PSCR = 6; // 16 MHz / 64 = 4 us clock
  TIM4->ARR = 249; // 250 * 4 us = 1 ms
#endif

#if (TSLPRM_TICK_FREQ == 500)
  TIM4->PSCR = 8; // 16 MHz / 256 = 16 us clock
  TIM4->ARR = 124; // 125 *  16 us = 2 ms
#endif

#if (TSLPRM_TICK_FREQ == 250)
  TIM4->PSCR = 8; // 16 MHz / 256 = 16 us clock
  TIM4->ARR = 249; // 250 *  16 us = 4 ms
#endif

#if (TSLPRM_TICK_FREQ == 125)
  TIM4->PSCR = 10; // 16 MHz / 1024 = 64 us clock
  TIM4->ARR = 124; // 125 *  64 us = 8 ms
#endif

  TIM4->IER = 0x01; // Enable interrupt
  TIM4->CR1 = 0x01; // Start timer

  return TSL_STATUS_OK;
}


/**
  * @brief  Interrupt handler for TIM4 dedicated to ECS
  * @param  None
  * @retval None
  */
#if defined(_COSMIC_)
// 'svlreg option' is added to force the saving of the virtual long register
@svlreg INTERRUPT_HANDLER(TSL_Timer_ISR, 25)
#else
INTERRUPT_HANDLER(TSL_Timer_ISR, 25)
#endif
{
  TIM4->SR1 &= (uint8_t)(~TIM4_SR1_UIF);
  TSL_tim_ProcessIT();
}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
