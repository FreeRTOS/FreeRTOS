/**
  ******************************************************************************
  * @file    tsl_linrot.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains external declarations of the tsl_linrot.c file.
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
#ifndef __TSL_LINROT_H
#define __TSL_LINROT_H

/* Includes ------------------------------------------------------------------*/
#include "tsl_acq.h"
#include "tsl_time.h"

/* Exported types ------------------------------------------------------------*/

/** Contains all data related to Linear and Rotary sensor.
  * Variables of this structure type must be placed in RAM only.
  */
typedef struct
{
  TSL_StateId_enum_T     StateId;     /**< Current state identifier */
  TSL_tPosition_T        RawPosition; /**< Raw position */
  TSL_tPosition_T        Position;    /**< Scaled position */
  unsigned int Counter   : 6; /**< Generic counter for state debounce, calibration & DTO (TSL_tCounter_T) */
  unsigned int Change    : 1; /**< The State is different from the previous one (TSL_StateChange_enum_T) */
  unsigned int PosChange : 1; /**< The RawPosition/Position is different from the previous one (TSL_StateChange_enum_T) */
  unsigned int Counter2  : 6; /**< Generic counter for direction debounce (TSL_tCounter_T) */
  unsigned int DxSLock   : 1; /**< The State is locked by the DxS (TSL_Bool_enum_T) */
  unsigned int Direction : 1; /**< Movement direction (TSL_Bool_enum_T) */
}
TSL_LinRotData_T;

/** Contains all parameters related to Linear and Rotary sensor.
  * Variables of this structure type can be placed in RAM or ROM.
  */
typedef struct
{
  // Thresholds
#if TSLPRM_USE_PROX > 0
  TSL_tThreshold_T  ProxInTh;            /**< Proximity state in threshold */
  TSL_tThreshold_T  ProxOutTh;           /**< Proximity state out threshold */
#endif
  TSL_tThreshold_T  DetectInTh;          /**< Detection state in threshold */
  TSL_tThreshold_T  DetectOutTh;         /**< Detection state out threshold */
  TSL_tThreshold_T  CalibTh;             /**< Calibration state threshold */
  // Debounce counters
  TSL_tCounter_T    CounterDebCalib;     /**< Debounce counter to enter in Calibration state */
#if TSLPRM_USE_PROX > 0
  TSL_tCounter_T    CounterDebProx;      /**< Debounce counter to enter in Proximity state */
#endif
  TSL_tCounter_T    CounterDebDetect;    /**< Debounce counter to enter in Detect state */
  TSL_tCounter_T    CounterDebRelease;   /**< Debounce counter to enter in Release state */
  TSL_tCounter_T    CounterDebError;     /**< Debounce counter to enter in Error state */
  TSL_tCounter_T    CounterDebDirection; /**< Debounce counter for the direction change */
  // Other parameters
  TSL_tCounter_T    Resolution;          /**< Position resolution */
  TSL_tPosition_T   DirChangePos;        /**< Direction change position threshold */
}
TSL_LinRotParam_T;

/** Contains definition of a Linear and Rotary sensor.
  * Variables of this structure type can be placed in RAM or ROM.
  */
typedef struct
{
  TSL_LinRotData_T          *p_Data;    /**< Data (state id, counter, flags, ...) */
  TSL_LinRotParam_T         *p_Param;   /**< Parameters (thresholds, debounce, ...) */
  TSL_ChannelData_T         *p_ChD;     /**< First Channel Data (Meas, Ref, Delta, ...) */
  TSL_tNb_T                 NbChannels; /**< Number of channels */
  CONST uint16_t            *p_DeltaCoeff; /**< Coefficient to apply on Delta */
  CONST TSL_tsignPosition_T *p_PosOff;  /**< Position offset table */
  TSL_tIndex_T              SctComp;    /**< Sector Computation */
  TSL_tIndex_T              PosCorr;    /**< Position Correction */
  CONST TSL_State_T         *p_SM;      /**< State Machine */
  CONST TSL_LinRotMethods_T *p_Methods; /**< Methods */
}
TSL_LinRot_T;

/** Contains definition of a Basic Linear and Rotary sensor.
  * Variables of this structure type can be placed in RAM or ROM.
  * Basic sensor does not contain its own state machine and methods. It used
  * default ones instead to gain memory space.
  */
typedef struct
{
  TSL_LinRotData_T          *p_Data;    /**< Data (state id, counter, flags, ...) */
  TSL_LinRotParam_T         *p_Param;   /**< Parameters (thresholds, debounce, ...) */
  TSL_ChannelData_T         *p_ChD;     /**< First Channel Data (Meas, Ref, Delta, ...) */
  TSL_tNb_T                 NbChannels; /**< Number of channels */
  CONST uint16_t            *p_DeltaCoeff; /**< Coefficient to apply on Delta */
  CONST TSL_tsignPosition_T *p_PosOff;  /**< Position offset table */
  TSL_tIndex_T              SctComp;    /**< Sector Computation */
  TSL_tIndex_T              PosCorr;    /**< Position Correction */
}
TSL_LinRotB_T;

/* Exported variables --------------------------------------------------------*/
/* Exported macros -----------------------------------------------------------*/

/* Exported functions --------------------------------------------------------*/

// "Object methods" functions
void TSL_linrot_Init(void);
void TSL_linrot_Process(void);
TSL_Status_enum_T TSL_linrot_CalcPos(void);

// Utility functions
void TSL_linrot_SetStateCalibration(TSL_tCounter_T delay);
void TSL_linrot_SetStateOff(void);
#if !defined(TSLPRM_STM8TL5X) && !defined(STM8TL5X)
void TSL_linrot_SetStateBurstOnly(void);
#endif
TSL_StateId_enum_T TSL_linrot_GetStateId(void);
TSL_StateMask_enum_T TSL_linrot_GetStateMask(void);
TSL_tNb_T TSL_linrot_IsChanged(void);

// State machine functions
void TSL_linrot_CalibrationStateProcess(void);
void TSL_linrot_DebCalibrationStateProcess(void);
void TSL_linrot_ReleaseStateProcess(void);
void TSL_linrot_DebReleaseProxStateProcess(void);
void TSL_linrot_DebReleaseDetectStateProcess(void);
void TSL_linrot_DebReleaseTouchStateProcess(void);
void TSL_linrot_ProxStateProcess(void);
void TSL_linrot_DebProxStateProcess(void);
void TSL_linrot_DebProxDetectStateProcess(void);
void TSL_linrot_DebProxTouchStateProcess(void);
void TSL_linrot_DetectStateProcess(void);
void TSL_linrot_DebDetectStateProcess(void);
void TSL_linrot_TouchStateProcess(void);
void TSL_linrot_DebTouchStateProcess(void);
void TSL_linrot_ErrorStateProcess(void);
void TSL_linrot_DebErrorStateProcess(void);
void TSL_linrot_OffStateProcess(void);

// Position offset constant tables and corrections

extern CONST TSL_tsignPosition_T TSL_POSOFF_3CH_LIN_M1[3][3];
extern CONST TSL_tsignPosition_T TSL_POSOFF_3CH_LIN_M2[3][3];
extern CONST TSL_tsignPosition_T TSL_POSOFF_3CH_LIN_H[3][3];
extern CONST TSL_tsignPosition_T TSL_POSOFF_3CH_ROT_M[3][3];

extern CONST TSL_tsignPosition_T TSL_POSOFF_4CH_LIN_M1[4][4];
extern CONST TSL_tsignPosition_T TSL_POSOFF_4CH_LIN_M2[4][4];
extern CONST TSL_tsignPosition_T TSL_POSOFF_4CH_LIN_H[4][4];
extern CONST TSL_tsignPosition_T TSL_POSOFF_4CH_ROT_M[4][4];

extern CONST TSL_tsignPosition_T TSL_POSOFF_5CH_LIN_M1[5][5];
extern CONST TSL_tsignPosition_T TSL_POSOFF_5CH_LIN_M2[5][5];
extern CONST TSL_tsignPosition_T TSL_POSOFF_5CH_LIN_H[5][5];
extern CONST TSL_tsignPosition_T TSL_POSOFF_5CH_ROT_M[5][5];
extern CONST TSL_tsignPosition_T TSL_POSOFF_5CH_ROT_D[5][5];

extern CONST TSL_tsignPosition_T TSL_POSOFF_6CH_LIN_M1[6][6];
extern CONST TSL_tsignPosition_T TSL_POSOFF_6CH_LIN_M2[6][6];
extern CONST TSL_tsignPosition_T TSL_POSOFF_6CH_LIN_H[6][6];
extern CONST TSL_tsignPosition_T TSL_POSOFF_6CH_ROT_M[6][6];

#define TSL_SCTCOMP_3CH_LIN_M1 (128)
#define TSL_POSCORR_3CH_LIN_M1 (64)
#define TSL_SCTCOMP_3CH_LIN_M2 (256)
#define TSL_POSCORR_3CH_LIN_M2 (256)

#define TSL_SCTCOMP_3CH_LIN_H (128)
#define TSL_POSCORR_3CH_LIN_H (128)

#define TSL_SCTCOMP_3CH_ROT_M (85)

#define TSL_SCTCOMP_4CH_LIN_M1 (85)
#define TSL_POSCORR_4CH_LIN_M1 (43)
#define TSL_SCTCOMP_4CH_LIN_M2 (128)
#define TSL_POSCORR_4CH_LIN_M2 (128)

#define TSL_SCTCOMP_4CH_LIN_H (85)
#define TSL_POSCORR_4CH_LIN_H (85)

#define TSL_SCTCOMP_4CH_ROT_M (64)

#define TSL_SCTCOMP_5CH_LIN_M1 (64)
#define TSL_POSCORR_5CH_LIN_M1 (32)
#define TSL_SCTCOMP_5CH_LIN_M2 (85)
#define TSL_POSCORR_5CH_LIN_M2 (85)

#define TSL_SCTCOMP_5CH_LIN_H (64)
#define TSL_POSCORR_5CH_LIN_H (64)

#define TSL_SCTCOMP_5CH_ROT_M (51)

#define TSL_SCTCOMP_5CH_ROT_D (26)

#define TSL_SCTCOMP_6CH_LIN_M1 (51)
#define TSL_POSCORR_6CH_LIN_M1 (25)
#define TSL_SCTCOMP_6CH_LIN_M2 (64)
#define TSL_POSCORR_6CH_LIN_M2 (64)

#define TSL_SCTCOMP_6CH_LIN_H (51)
#define TSL_POSCORR_6CH_LIN_H (51)

#define TSL_SCTCOMP_6CH_ROT_M (43)

#endif /* __TSL_LINROT_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
