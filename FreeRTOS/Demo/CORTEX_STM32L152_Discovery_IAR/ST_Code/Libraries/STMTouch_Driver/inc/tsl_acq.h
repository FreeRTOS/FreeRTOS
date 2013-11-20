/**
  ******************************************************************************
  * @file    tsl_acq.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains external declarations of the tsl_acq.c file.
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
#ifndef __TSL_ACQ_H
#define __TSL_ACQ_H

/* Includes ------------------------------------------------------------------*/

// Check the device selection.
// It must be defined in the toolchain compiler preprocessor.
// The same name as in the Standard Peripheral Library is used.
#if !defined(STM8TL5X) &&\
    !defined(STM32F0XX) &&\
    !defined(STM32F30X) &&\
    !defined(STM32F37X) &&\
    !defined(STM32L1XX_HD) &&\
    !defined(STM32L1XX_MD) &&\
    !defined(STM32L1XX_MDP)
#error "Device family not declared in the toolchain compiler preprocessor."
#endif

#if defined(STM8TL5X)
#include "tsl_acq_stm8tl5x.h"
#endif

#if defined(STM32F0XX)
#include "tsl_acq_stm32f0xx.h"
#endif

#if defined(STM32F30X) || defined(STM32F37X)
#include "tsl_acq_stm32f3xx.h"
#endif

#if defined(STM32L1XX_HD)
#if defined(TSLPRM_STM32L1XX_SW_ACQ)
#include "tsl_acq_stm32l1xx_sw.h" // Software acquisition
#else
#include "tsl_acq_stm32l1xx_hw.h" // Hardware acquisition with Timers (default)
#endif
#endif

#if defined(STM32L1XX_MD)
#include "tsl_acq_stm32l1xx_sw.h" // Software acquisition only
#endif

#if defined(STM32L1XX_MDP)
#if defined(TSLPRM_STM32L1XX_SW_ACQ)
#include "tsl_acq_stm32l1xx_sw.h" // Software acquisition
#else
#include "tsl_acq_stm32l1xx_hw.h" // Hardware acquisition with Timers (default)
#endif
#endif

/* Defines -------------------------------------------------------------------*/

/* Exported types ------------------------------------------------------------*/

// Filter functions
typedef TSL_tMeas_T(* TSL_pFuncMeasFilter_T)(TSL_tMeas_T, TSL_tMeas_T); /**< Pointer to the Measure filter function */
typedef TSL_tDelta_T(* TSL_pFuncDeltaFilter_T)(TSL_tDelta_T); /**< Pointer to the Delta filter function */

/** Structure containing all data of a Zone.
  * A Zone is a set of Banks.
  * Variables of this structure type can be placed in RAM or ROM.
  */
typedef struct
{
  // Common to all acquisitions
  TSL_tIndex_T           *BankIndex; /**< Pointer to an array of bank indexes */
  TSL_pFuncDeltaFilter_T *dFilter;   /**< Pointer to a Delta filter function */
  TSL_tNb_T              NbBanks;    /**< Number of banks in the zone */
}
TSL_Zone_T;

/* Exported variables --------------------------------------------------------*/

/* Exported macros -----------------------------------------------------------*/

/* Exported functions ------------------------------------------------------- */
TSL_Status_enum_T TSL_acq_ZoneConfig(CONST TSL_Zone_T *zone, TSL_tIndex_T idx_bk);
TSL_Status_enum_T TSL_acq_BankGetResult(TSL_tIndex_T idx_bk, TSL_pFuncMeasFilter_T mfilter, TSL_pFuncDeltaFilter_T dfilter);
TSL_Status_enum_T TSL_acq_BankCalibrate(TSL_tIndex_T bank);
void TSL_acq_BankClearData(TSL_tIndex_T bank);

#endif /* __TSL_ACQ_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
