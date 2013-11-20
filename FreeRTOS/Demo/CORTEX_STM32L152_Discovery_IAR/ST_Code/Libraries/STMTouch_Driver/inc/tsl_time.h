/**
  ******************************************************************************
  * @file    tsl_time.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains external declarations of the tsl_time.c file.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __TSL_TIME_H
#define __TSL_TIME_H

/* Includes ------------------------------------------------------------------*/

#if defined(STM8TL5X)
#include "tsl_acq_stm8tl5x.h"
#include "tsl_time_stm8tl5x.h"
#endif

#if defined(STM32F0XX)
#include "tsl_acq_stm32f0xx.h"
#include "tsl_time_stm32f0xx.h"
#endif

#if defined(STM32F30X) || defined(STM32F37X)
#include "tsl_acq_stm32f3xx.h"
#include "tsl_time_stm32f3xx.h"
#endif

#if defined(STM32L1XX_HD)
#if defined(TSLPRM_STM32L1XX_SW_ACQ)
#include "tsl_acq_stm32l1xx_sw.h" // Software acquisition
#else
#include "tsl_acq_stm32l1xx_hw.h" // Hardware acquisition with Timers (default)
#endif
#include "tsl_time_stm32l1xx.h"
#endif

#if defined(STM32L1XX_MD)
#include "tsl_acq_stm32l1xx_sw.h" // Software acquisition only
#include "tsl_time_stm32l1xx.h"
#endif

#if defined(STM32L1XX_MDP)
#if defined(TSLPRM_STM32L1XX_SW_ACQ)
#include "tsl_acq_stm32l1xx_sw.h" // Software acquisition
#else
#include "tsl_acq_stm32l1xx_hw.h" // Hardware acquisition with Timers (default)
#endif
#include "tsl_time_stm32l1xx.h"
#endif

/* Exported functions ------------------------------------------------------- */

void TSL_tim_ProcessIT(void);
TSL_Status_enum_T TSL_tim_CheckDelay_ms(TSL_tTick_ms_T delay_ms, __IO TSL_tTick_ms_T *last_tick);
TSL_Status_enum_T TSL_tim_CheckDelay_sec(TSL_tTick_sec_T delay_sec, __IO TSL_tTick_sec_T *last_tick);
void TSL_CallBack_TimerTick(void);

#endif /* __TSL_TIME_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
