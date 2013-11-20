/**
  ******************************************************************************
  * @file    tsl_acq_stm8tl5x.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions prototypes that manage the TSC
  *          acquisition on STM8TL5x products.
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
#ifndef __TSL_ACQ_STM8TL5X_H
#define __TSL_ACQ_STM8TL5X_H

/* Includes ------------------------------------------------------------------*/
#include "stm8tl5x.h"
#include "tsl_conf_stm8tl5x.h"
#include "tsl_types.h"

/*==============================================================================

  *** RECEIVERS AND TRANSMITTERS DESCRIPTION ***

   ProxSense receiver and transmitter description for STM8TL5x
   For more details please refer to the Proxsense
   section in the reference manual


                         Txi
 Group Ai  Rx0a  __/____  |
           Rx1a  __/____  |
           Rx2a  __/____  |
           Rx3a  __/____  |
           Rx4a  __/____  |
           Rx5a  __/____  |
           Rx6a  __/____  |
           Rx7a  __/____  |
           Rx8a  __/____  |
           Rx9a  __/____  |

 Group Bi  Rx0b  __/____  |
           Rx1b  __/____  |
           Rx2b  __/____  |
           Rx3b  __/____  |
           Rx4b  __/____  |
           Rx5b  __/____  |
           Rx6b  __/____  |
           Rx7b  __/____  |
           Rx8b  __/____  |
           Rx9b  __/____  |

==============================================================================*/

/* Defines -------------------------------------------------------------------*/

// Receivers
#define RX0 (0+0x8000)
#define RX1 (1+0x8000)
#define RX2 (2+0x8000)
#define RX3 (3+0x8000)
#define RX4 (4+0x8000)
#define RX5 (5+0x8000)
#define RX6 (6+0x8000)
#define RX7 (7+0x8000)
#define RX8 (8+0x8000)
#define RX9 (9+0x8000)

// Transmitters
#define TX0 (0)
#define TX1 (1)
#define TX2 (2)
#define TX3 (3)
#define TX4 (4)
#define TX5 (5)
#define TX6 (6)
#define TX7 (7)
#define TX8 (8)
#define TX9 (9)
#define TX10 (10)
#define TX11 (11)
#define TX12 (12)
#define TX13 (13)
#define TX14 (14)

#define BIT_MASK_RX(N) ((uint16_t)1<<(uint8_t)(N & 0xFF))
#define BIT_MASK_TX(N) ((uint16_t)1<< N)

// Acquisition Bank
#define BANK01 1
#define BANK02 2
#define BANK03 3
#define BANK04 4
#define BANK05 5
#define BANK06 6
#define BANK07 7
#define BANK08 8
#define BANK09 9
#define BANK10 10
#define BANK11 11
#define BANK12 12
#define BANK13 13
#define BANK14 14
#define BANK15 15
#define BANK16 16
#define BANK17 17
#define BANK18 18
#define BANK19 19
#define BANK20 20
#define BANK21 21
#define BANK22 22
#define BANK23 23
#define BANK24 24
#define BANK25 25
#define BANK26 26
#define BANK27 27
#define BANK28 28
#define BANK29 29
#define BANK30 30

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

// For STM8TL5X only

typedef uint16_t TSL_tMaskRX; /**< Receiver mask */
typedef uint16_t TSL_tMaskTX; /**< Transmitter mask */

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
  TSL_tIndexSrc_T  IdxSrc; /**< Index of the receivers (between 0 and 9) */
} TSL_ChannelSrc_T;

#define TSL_EPCC_CHANGE_MASK (0x04) /**< EPCC change mask */

/** EPCC status
  */
typedef enum
{
  TSL_EPCC_STATUS_UNLOCKED = 0, /**< EPCC is unlocked */
  TSL_EPCC_STATUS_LOCKED   = 1, /**< EPCC is locked */
  TSL_EPCC_STATUS_DECREASE = 4, /**< EPCC must decreased */
  TSL_EPCC_STATUS_INCREASE = 6  /**< EPCC must be increased */
} TSL_EPCCStatus_enum_T;

/** Channel flags
  */
typedef struct
{
  unsigned int DataReady  : 1; /**< To identify a new measurement (TSL_DataReady_enum_T) */
  unsigned int AcqStatus  : 2; /**< Acquisition status (TSL_AcqStatus_enum_T) */
  unsigned int EPCCStatus : 3; /**< Acquisition status (TSL_EPCCStatus_enum_T) */
  unsigned int ObjStatus  : 2; /**< Object status (TSL_ObjStatus_enum_T) */
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
  // For stm8tl5x PXS acquisition only
  TSL_tMaskRX             msk_channels; /**< Mask of all receivers */
  TSL_tMaskTX             msk_TX;       /**< Mask of Tx */
  uint8_t                 msk_group;    /**< Mask of group used (RX_GROUPA or RX_GROUPB) */
  TSL_tMaskRX             msk_RXEN;     /**< Mask of all RX (receivers and transmitters) */
} TSL_Bank_T;

/** Bank Configuration
  */
typedef struct
{
  uint8_t  CSSEL[TSLPRM_HIGH_CHANNEL_NB+1];   /**< Array of CS values */
  uint8_t  EPCCSEL[TSLPRM_HIGH_CHANNEL_NB+1]; /**< Array of EPCC values */
} TSL_BankConfig_T;

/* Exported variables --------------------------------------------------------*/

/* Exported macros -----------------------------------------------------------*/
#define TSL_acq_ComputeDelta(Reference,Measure) (TSL_tDelta_T)(Measure - Reference) /**< Calculate the Delta */
#define TSL_acq_ComputeMeas(Reference,Delta)    (TSL_tMeas_T)(Delta + Reference) /**< Calculate the Measure */

/* Exported functions ------------------------------------------------------- */
TSL_Status_enum_T TSL_acq_Init(void);
TSL_Status_enum_T TSL_acq_BankConfig(TSL_tIndex_T idx_bk);
TSL_Bool_enum_T TSL_acq_UseFilter(TSL_ChannelData_T *pCh);
TSL_Bool_enum_T TSL_acq_TestFirstReferenceIsValid(TSL_ChannelData_T *pCh, TSL_tMeas_T new_meas);
TSL_Bool_enum_T TSL_acq_TestReferenceOutOfRange(TSL_ChannelData_T *pCh);
void TSL_acq_BankStartAcq(void);
TSL_Status_enum_T TSL_acq_BankWaitEOC(void);
TSL_AcqStatus_enum_T TSL_acq_CheckNoise(void);
TSL_tMeas_T TSL_acq_GetMeas(TSL_tIndexSrc_T index);
void TSL_acq_UpdateCS(uint8_t *pCSSEL, TSL_EPCCStatus_enum_T change);

#endif /* __TSL_ACQ_STM8TL5X_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
