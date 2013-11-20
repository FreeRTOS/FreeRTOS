/**
  ******************************************************************************
  * @file    tsl_touchkey.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains external declarations of the tsl_touchkey.c file.
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
#ifndef __TSL_TOUCHKEY_H
#define __TSL_TOUCHKEY_H

/* Includes ------------------------------------------------------------------*/
#include "tsl_acq.h"
#include "tsl_time.h"

/* Exported types ------------------------------------------------------------*/

/** Contains all data related to TouchKey sensor.
  * Variables of this structure type must be placed in RAM only.
  */
typedef struct
{
  TSL_StateId_enum_T StateId; /**< Current state identifier */
  unsigned int Counter : 6; /**< Generic counter for debounce, calibration & DTO */
  unsigned int Change  : 1; /**< The State is different from the previous one (TSL_StateChange_enum_T) */
  unsigned int DxSLock : 1; /**< The State is locked by the DxS (TSL_Bool_enum_T) */
}
TSL_TouchKeyData_T;

/** Contains all parameters related to TouchKey sensor.
  * Variables of this structure type can be placed in RAM or ROM.
  */
typedef struct
{
#if TSLPRM_USE_PROX > 0
  TSL_tThreshold_T  ProxInTh;          /**< Proximity in threshold */
  TSL_tThreshold_T  ProxOutTh;         /**< Proximity out threshold */
#endif
  TSL_tThreshold_T  DetectInTh;        /**< Detection in threshold */
  TSL_tThreshold_T  DetectOutTh;       /**< Detection out threshold */
  TSL_tThreshold_T  CalibTh;           /**< Calibration threshold */
  TSL_tCounter_T    CounterDebCalib;   /**< Debounce counter to enter in Calibration state */
#if TSLPRM_USE_PROX > 0
  TSL_tCounter_T    CounterDebProx;    /**< Debounce counter to enter in Proximity state */
#endif
  TSL_tCounter_T    CounterDebDetect;  /**< Debounce counter to enter in Detect state */
  TSL_tCounter_T    CounterDebRelease; /**< Debounce counter to enter in Release state */
  TSL_tCounter_T    CounterDebError;   /**< Debounce counter to enter in Error state */
}
TSL_TouchKeyParam_T;

/** Contains definition of a TouchKey sensor.
  * Variables of this structure type can be placed in RAM or ROM.
  */
typedef struct
{
  TSL_TouchKeyData_T          *p_Data;    /**< Data (state id, counter, flags, ...) */
  TSL_TouchKeyParam_T         *p_Param;   /**< Parameters (thresholds, debounce, ...) */
  TSL_ChannelData_T           *p_ChD;     /**< Channel Data (Meas, Ref, Delta, ...) */
  CONST TSL_State_T           *p_SM;      /**< State Machine */
  CONST TSL_TouchKeyMethods_T *p_Methods; /**< Methods */
}
TSL_TouchKey_T;

/** Contains definition of a Basic TouchKey sensor.
  * Variables of this structure type can be placed in RAM or ROM.
  * Basic sensor does not contain its own state machine and methods. It used
  * default ones instead to gain memory space.
  */
typedef struct
{
  TSL_TouchKeyData_T          *p_Data;    /**< Data (state id, counter, flags, ...) */
  TSL_TouchKeyParam_T         *p_Param;   /**< Parameters (thresholds, debounce, ...) */
  TSL_ChannelData_T           *p_ChD;     /**< Channel Data (Meas, Ref, Delta, ...) */
}
TSL_TouchKeyB_T;

/* Exported variables --------------------------------------------------------*/
/* Exported macros -----------------------------------------------------------*/

/* Exported functions --------------------------------------------------------*/

// "Object methods" functions
void TSL_tkey_Init(void);
void TSL_tkey_Process(void);

// Utility functions
void TSL_tkey_SetStateCalibration(TSL_tCounter_T delay);
void TSL_tkey_SetStateOff(void);
#if !defined(TSLPRM_STM8TL5X) && !defined(STM8TL5X)
void TSL_tkey_SetStateBurstOnly(void);
#endif
TSL_StateId_enum_T TSL_tkey_GetStateId(void);
TSL_StateMask_enum_T TSL_tkey_GetStateMask(void);
TSL_tNb_T TSL_tkey_IsChanged(void);

// State machine functions
void TSL_tkey_CalibrationStateProcess(void);
void TSL_tkey_DebCalibrationStateProcess(void);
void TSL_tkey_ReleaseStateProcess(void);
void TSL_tkey_DebReleaseProxStateProcess(void);
void TSL_tkey_DebReleaseDetectStateProcess(void);
void TSL_tkey_DebReleaseTouchStateProcess(void);
void TSL_tkey_ProxStateProcess(void);
void TSL_tkey_DebProxStateProcess(void);
void TSL_tkey_DebProxDetectStateProcess(void);
void TSL_tkey_DebProxTouchStateProcess(void);
void TSL_tkey_DetectStateProcess(void);
void TSL_tkey_DebDetectStateProcess(void);
void TSL_tkey_TouchStateProcess(void);
void TSL_tkey_DebTouchStateProcess(void);
void TSL_tkey_ErrorStateProcess(void);
void TSL_tkey_DebErrorStateProcess(void);
void TSL_tkey_OffStateProcess(void);

#endif /* __TSL_TOUCHKEY_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
