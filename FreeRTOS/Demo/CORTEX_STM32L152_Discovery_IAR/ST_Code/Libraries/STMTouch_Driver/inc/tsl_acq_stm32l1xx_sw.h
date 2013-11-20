/**
  ******************************************************************************
  * @file    tsl_acq_stm32l1xx_sw.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains external declarations of the tsl_acq_stm32l1xx_sw.c file.
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
#ifndef __TSL_ACQ_STM32L1XX_SW_H
#define __TSL_ACQ_STM32L1XX_SW_H

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"
#include "tsl_conf_stm32l1xx.h"
#include "tsl_types.h"

/* Defines -------------------------------------------------------------------*/

#ifndef CONST
#define CONST const
#endif

// SysTick enable/disable interrupt macros
#define enableInterrupts()  {SysTick->CTRL |= SysTick_CTRL_TICKINT_Msk;}
#define disableInterrupts() {SysTick->CTRL &= ~SysTick_CTRL_TICKINT_Msk;}

enum
{
  GR1,
  GR2,
  GR3,
  GR4,
  GR5,
  GR6,
  GR7,
  GR8,
  GR9,
  GR10,
  GR11
};

enum
{
  TSL_BANK_GPIOA = 0,
  TSL_BANK_GPIOB,
  TSL_BANK_GPIOC,
  TSL_BANK_GPIOE,
  TSL_BANK_GPIOF,
  TSL_BANK_GPIOG
};

/** GPIOs list
    High significant nibble for the IO port (GPIOA:0,...,GPIOG:6)
    Low significant nibble for the IO number (pin0:0,...,pin15:F)
  */
enum
{
  PA0  = 0x00, /**< TSL_GROUP1_IO1 */
  PA1  = 0x01,
  PA2  = 0x02,
  PA3  = 0x03,
  PA6  = 0x06, /**< TSL_GROUP2_IO1 */
  PA7  = 0x07,
  PA8  = 0x08,
  PA9  = 0x09,
  PA10 = 0x0A,
  PA13 = 0x0D, /**< TSL_GROUP5_IO1 */
  PA14 = 0x0E,
  PA15 = 0x0F,
  PB0  = 0x10, /**< TSL_GROUP3_IO1 */
  PB1  = 0x11,
  PB2  = 0x12,
  PB4  = 0x14, /**< TSL_GROUP6_IO1 */
  PB5  = 0x15,
  PB6  = 0x16,
  PB7  = 0x17,
  PB12 = 0x1C, /**< TSL_GROUP7_IO1 */
  PB13 = 0x1D,
  PB14 = 0x1E,
  PB15 = 0x1F,
  PC0  = 0x20, /**< TSL_GROUP8_IO1 */
  PC1  = 0x21,
  PC2  = 0x22,
  PC3  = 0x23,
  PC4  = 0x24,
  PC5  = 0x25,
  PC6  = 0x26,
  PC7  = 0x27,
  PC8  = 0x28,
  PC9  = 0x29,
  PF6  = 0x56, /**< TSL_GROUP11_IO1 */
  PF7  = 0x57,
  PF8  = 0x58,
  PF9  = 0x59,
  PF10 = 0x5A,
  PF11 = 0x5B,
  PF12 = 0x5C,
  PF13 = 0x5D,
  PF14 = 0x5E,
  PF15 = 0x5F,
  PG0  = 0x60, /**< TSL_GROUP2_IO4 */
  PG1  = 0x61,
  PG2  = 0x62,
  PG3  = 0x63,
  PG4  = 0x64
};

/** GPIOs list:
    - High significant nibble for the IO port (GPIOA:0,...,GPIOG:6)
    - Low significant nibble for the IO number (pin0:0,...,pin15:F)
  */
enum
{
  TSL_GROUP1_IO1  = 0x00, /**< PA0 */
  TSL_GROUP1_IO2  = 0x01,
  TSL_GROUP1_IO3  = 0x02,
  TSL_GROUP1_IO4  = 0x03,
  TSL_GROUP2_IO1  = 0x06, /**< PA6 */
  TSL_GROUP2_IO2  = 0x07,
  TSL_GROUP4_IO1  = 0x08,
  TSL_GROUP4_IO2  = 0x09,
  TSL_GROUP4_IO3  = 0x0A,
  TSL_GROUP5_IO1  = 0x0D, /**< PA13 */
  TSL_GROUP5_IO2  = 0x0E,
  TSL_GROUP5_IO3  = 0x0F,
  TSL_GROUP3_IO1  = 0x10, /**< PB0 */
  TSL_GROUP3_IO2  = 0x11,
  TSL_GROUP3_IO3  = 0x12,
  TSL_GROUP6_IO1  = 0x14, /**< PB4 */
  TSL_GROUP6_IO2  = 0x15,
  TSL_GROUP6_IO3  = 0x16,
  TSL_GROUP6_IO4  = 0x17,
  TSL_GROUP7_IO1  = 0x1C, /**< PB12 */
  TSL_GROUP7_IO2  = 0x1D,
  TSL_GROUP7_IO3  = 0x1E,
  TSL_GROUP7_IO4  = 0x1F,
  TSL_GROUP8_IO1  = 0x20, /**< PC0 */
  TSL_GROUP8_IO2  = 0x21,
  TSL_GROUP8_IO3  = 0x22,
  TSL_GROUP8_IO4  = 0x23,
  TSL_GROUP9_IO1  = 0x24,
  TSL_GROUP9_IO2  = 0x25,
  TSL_GROUP10_IO1 = 0x26,
  TSL_GROUP10_IO2 = 0x27,
  TSL_GROUP10_IO3 = 0x28,
  TSL_GROUP10_IO4 = 0x29,
  TSL_GROUP11_IO1 = 0x56, /**< PF6 */
  TSL_GROUP11_IO2 = 0x57,
  TSL_GROUP11_IO3 = 0x58,
  TSL_GROUP11_IO4 = 0x59,
  TSL_GROUP11_IO5 = 0x5A,
  TSL_GROUP3_IO4  = 0x5B,
  TSL_GROUP3_IO5  = 0x5C,
  TSL_GROUP9_IO3  = 0x5D,
  TSL_GROUP9_IO4  = 0x5E,
  TSL_GROUP2_IO3  = 0x5F,
  TSL_GROUP2_IO4  = 0x60, /**< PG0 */
  TSL_GROUP2_IO5  = 0x61,
  TSL_GROUP7_IO5  = 0x62,
  TSL_GROUP7_IO6  = 0x63,
  TSL_GROUP7_IO7  = 0x64
};

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

typedef uint8_t TSL_Conf_t;

/** Channel destination index
  */
typedef struct
{
  TSL_tIndex_T  IdxDest; /**< Index in the Channel data array */
} TSL_ChannelDest_T;

/** Channel Source and Configuration
  */
typedef struct
{
  TSL_tIndex_T IdxSrc; /**< Index of source value */
  // For stm32l1x acquisition only
  TSL_Conf_t   t_sample;  /**< Indicates which GPIO.n is used for the sample */
  TSL_Conf_t   t_channel; /**< Indicates which GPIO.n is used for the channel */
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
  // For stm32l1x acquisition only
  TSL_Conf_t              shield_sample;  /**< Indicates which GPIO.n is used for the shield sample */
  TSL_Conf_t              shield_channel; /**< Indicates which GPIO.n is used for the shield channel */
} TSL_Bank_T;

/* Exported variables --------------------------------------------------------*/

/* Exported macros -----------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
TSL_Status_enum_T TSL_acq_Init(void);
TSL_Status_enum_T TSL_acq_BankConfig(TSL_tIndex_T idx_bk);
void TSL_acq_BankStartAcq(void);
TSL_Status_enum_T TSL_acq_BankWaitEOC(void);
void TSL_acq_ProcessIT(void);
TSL_tMeas_T TSL_acq_GetMeas(TSL_tIndex_T index);
TSL_AcqStatus_enum_T TSL_acq_CheckNoise(void);

TSL_Bool_enum_T TSL_acq_UseFilter(TSL_ChannelData_T *pCh);
TSL_tDelta_T TSL_acq_ComputeDelta(TSL_tRef_T ref, TSL_tMeas_T meas);
TSL_tMeas_T TSL_acq_ComputeMeas(TSL_tRef_T ref, TSL_tDelta_T delta);
TSL_Bool_enum_T TSL_acq_TestReferenceOutOfRange(TSL_ChannelData_T *pCh);
TSL_Bool_enum_T TSL_acq_TestFirstReferenceIsValid(TSL_ChannelData_T *pCh, TSL_tMeas_T new_meas);

#endif /* __TSL_ACQ_STM32L1XX_SW_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
