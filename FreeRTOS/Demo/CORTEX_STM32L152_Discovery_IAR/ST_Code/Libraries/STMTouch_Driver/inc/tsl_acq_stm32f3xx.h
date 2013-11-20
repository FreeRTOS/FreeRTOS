/**
  ******************************************************************************
  * @file    tsl_acq_stm32f3xx.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions prototypes that manage the TSC
  *          acquisition on STM32F3xx products.
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
#ifndef __TSL_ACQ_STM32F3XX_H
#define __TSL_ACQ_STM32F3XX_H

/* Includes ------------------------------------------------------------------*/
#if defined(STM32F30X)
#include "stm32f30x.h"
#endif
#if defined(STM32F37X)
#include "stm32f37x.h"
#endif
#include "tsl_conf_stm32f3xx.h"
#include "tsl_types.h"

/* Defines -------------------------------------------------------------------*/

#ifndef CONST
#define CONST const
#endif

// SysTick enable/disable interrupt macros
#define enableInterrupts()  {SysTick->CTRL |= SysTick_CTRL_TICKINT_Msk;}
#define disableInterrupts() {SysTick->CTRL &= ~SysTick_CTRL_TICKINT_Msk;}

#define TSL_NB_GROUPS (8) //  Number of groups available on STM32F3xx devices

#define TSL_GROUP1 (0x01)
#define TSL_GROUP2 (0x02)
#define TSL_GROUP3 (0x04)
#define TSL_GROUP4 (0x08)
#define TSL_GROUP5 (0x10)
#define TSL_GROUP6 (0x20)
#define TSL_GROUP7 (0x40)
#define TSL_GROUP8 (0x80)

// GxIOy masks
#define TSL_GROUP1_IO1 (0x00000001)
#define TSL_GROUP1_IO2 (0x00000002)
#define TSL_GROUP1_IO3 (0x00000004)
#define TSL_GROUP1_IO4 (0x00000008)
#define TSL_GROUP2_IO1 (0x00000010)
#define TSL_GROUP2_IO2 (0x00000020)
#define TSL_GROUP2_IO3 (0x00000040)
#define TSL_GROUP2_IO4 (0x00000080)
#define TSL_GROUP3_IO1 (0x00000100)
#define TSL_GROUP3_IO2 (0x00000200)
#define TSL_GROUP3_IO3 (0x00000400)
#define TSL_GROUP3_IO4 (0x00000800)
#define TSL_GROUP4_IO1 (0x00001000)
#define TSL_GROUP4_IO2 (0x00002000)
#define TSL_GROUP4_IO3 (0x00004000)
#define TSL_GROUP4_IO4 (0x00008000)
#define TSL_GROUP5_IO1 (0x00010000)
#define TSL_GROUP5_IO2 (0x00020000)
#define TSL_GROUP5_IO3 (0x00040000)
#define TSL_GROUP5_IO4 (0x00080000)
#define TSL_GROUP6_IO1 (0x00100000)
#define TSL_GROUP6_IO2 (0x00200000)
#define TSL_GROUP6_IO3 (0x00400000)
#define TSL_GROUP6_IO4 (0x00800000)
#define TSL_GROUP7_IO1 (0x01000000)
#define TSL_GROUP7_IO2 (0x02000000)
#define TSL_GROUP7_IO3 (0x04000000)
#define TSL_GROUP7_IO4 (0x08000000)
#define TSL_GROUP8_IO1 (0x10000000)
#define TSL_GROUP8_IO2 (0x20000000)
#define TSL_GROUP8_IO3 (0x40000000)
#define TSL_GROUP8_IO4 (0x80000000)

/* Exported types ------------------------------------------------------------*/

// For all devices/acquisitions

typedef uint16_t  TSL_tMeas_T; /**< Measurement */
typedef uint16_t  TSL_tRef_T; /**< Reference */
typedef int16_t   TSL_tDelta_T; /**< Delta */

typedef uint8_t   TSL_tIndexSrc_T; /**< Channel source index */
typedef uint16_t  TSL_tIndexDest_T; /**< Channel destination index */

typedef uint8_t   TSL_tRefRest_T; /**< Reference Rest (ECS) */
typedef uint16_t  TSL_tKCoeff_T; /**< K coefficient (ECS) */

typedef uint8_t   TSL_tIndex_T; /**< Generic index */
typedef uint16_t  TSL_tNb_T; /**< Generic number */
typedef uint8_t   TSL_tCounter_T; /**< Generic counter used for debounce */

typedef uint8_t   TSL_tThreshold_T; /**< Delta threshold */

typedef int16_t   TSL_tsignPosition_T; /**< Linear and Rotary sensors position */
typedef uint8_t   TSL_tPosition_T; /**< Linear and Rotary sensors position */

typedef uint16_t  TSL_tTick_ms_T; /**< Time in ms */
typedef uint8_t   TSL_tTick_sec_T; /**< Time in sec */

//------------------------------------------------------------------------------
// Channel
//------------------------------------------------------------------------------

/** Channel destination index
  */
typedef struct
{
  TSL_tIndexDest_T  IdxDest; /**< Index in the Channel data array */
} TSL_ChannelDest_T;

/** Channel Source and Configuration
  */
typedef struct
{
  TSL_tIndexSrc_T  IdxSrc; /**< Index of TSC->IOGXCR[] registers */
  // For STM32F3xx TSC acquisition only
  uint32_t         msk_IOCCR_channel; /**< Mask of the Channel IO (electrodes ONLY) */
  uint32_t         msk_IOGCSR_group;  /**< Mask of the Group used (electrodes ONLY) */
} TSL_ChannelSrc_T;

/** Channel flags
  */
typedef struct
{
  unsigned int DataReady : 1; /**< To identify a new measurement (TSL_DataReady_enum_T) */
  unsigned int AcqStatus : 2; /**< Acquisition status (TSL_AcqStatus_enum_T) */
  unsigned int ObjStatus : 2; /**< Object status (TSL_ObjStatus_enum_T) */
} TSL_ChannelFlags_T;

/** Channel Data
  */
typedef struct
{
  TSL_ChannelFlags_T   Flags;   /**< Flags */
  TSL_tRef_T           Ref;     /**< Reference */
  TSL_tRefRest_T       RefRest; /**< Reference rest for ECS */
  TSL_tDelta_T         Delta;   /**< Delta */
#if TSLPRM_USE_MEAS > 0
  TSL_tMeas_T          Meas;    /**< Hold the last acquisition measure */
#endif
} TSL_ChannelData_T;

//------------------------------------------------------------------------------
// Bank
//------------------------------------------------------------------------------

/** Bank
  */
typedef struct
{
  // Common to all acquisitions
  CONST TSL_ChannelSrc_T  *p_chSrc;     /**< Pointer to the Channel Source and Configuration */
  CONST TSL_ChannelDest_T *p_chDest;    /**< Pointer to the Channel Destination */
  TSL_ChannelData_T       *p_chData;    /**< Pointer to the Channel Data */
  TSL_tNb_T               NbChannels;   /**< Number of channels in the bank */
  // For STM32F3xx TSC acquisition only
  uint32_t                msk_IOCCR_channels; /**< Mask of all channel IOs (electrodes AND shields) */
  uint32_t                msk_IOGCSR_groups;  /**< Mask of all groups used (electrodes ONLY) */
} TSL_Bank_T;

/* Exported variables --------------------------------------------------------*/
/* Exported macros -----------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

TSL_Status_enum_T TSL_acq_Init(void);
void TSL_acq_InitGPIOs(void);
TSL_Status_enum_T TSL_acq_BankConfig(TSL_tIndex_T idx_bk);
TSL_Bool_enum_T TSL_acq_UseFilter(TSL_ChannelData_T *pCh);
TSL_Bool_enum_T TSL_acq_TestReferenceOutOfRange(TSL_ChannelData_T *pCh);
TSL_Bool_enum_T TSL_acq_TestFirstReferenceIsValid(TSL_ChannelData_T *pCh, TSL_tMeas_T new_meas);
void TSL_acq_BankStartAcq(void);
TSL_Status_enum_T TSL_acq_BankWaitEOC(void);
TSL_AcqStatus_enum_T TSL_acq_CheckNoise(void);
TSL_tMeas_T TSL_acq_GetMeas(TSL_tIndexSrc_T index);
TSL_tDelta_T TSL_acq_ComputeDelta(TSL_tRef_T ref, TSL_tMeas_T meas);
TSL_tMeas_T TSL_acq_ComputeMeas(TSL_tRef_T ref, TSL_tDelta_T delta);

#endif /* __TSL_ACQ_STM32F3XX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
