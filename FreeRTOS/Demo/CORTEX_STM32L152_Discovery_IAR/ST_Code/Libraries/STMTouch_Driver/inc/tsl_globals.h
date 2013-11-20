/**
  ******************************************************************************
  * @file    tsl_globals.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains external declarations of the tsl_globals.c file.
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
#ifndef __TSL_GLOBALS_H
#define __TSL_GLOBALS_H

/* Includes ------------------------------------------------------------------*/
#include "tsl_acq.h"
#include "tsl_object.h"

/* Exported types ------------------------------------------------------------*/

/** Store all global variables shared between the STMTouch Driver and the Application.
  */
typedef struct
{
  TSL_tTick_ms_T       Tick_ms;     /**< Incremented each 0.5ms by timing interrupt routine */
  TSL_tTick_sec_T      Tick_sec;    /**< Incremented each second by timing interrupt routine */
  CONST TSL_Bank_T     *Bank_Array; /**< Pointer to the array containing all Banks */
  TSL_tIndex_T         This_Bank;   /**< Pointer to the current Bank */
  CONST TSL_Object_T   *This_Obj;   /**< Pointer to the current Object */
#if TSLPRM_USE_ZONE > 0
  CONST TSL_Zone_T     *This_Zone;         /**< Pointer to the current Zone */
  TSL_tIndex_T         Index_In_This_Zone; /**< Index in the current Zone */
#endif
#if TSLPRM_TOTAL_TKEYS > 0
  CONST TSL_TouchKey_T *This_TKey; /**< Pointer to the current TKey */
#endif
#if TSLPRM_TOTAL_LNRTS > 0
  CONST TSL_LinRot_T   *This_LinRot; /**< Pointer to the current Linear or Rotary sensor */
#endif
}
TSL_Globals_T;

/** Store all global parametersshared between the STMTouch Driver and the Application .
  @warning Only one variable of this structure type must be created and be placed
  in RAM only.
  */
typedef struct
{
  TSL_tMeas_T       AcqMin;         /**< Acquisition minimum limit */
  TSL_tMeas_T       AcqMax;         /**< Acquisition maximum limit */
  TSL_tNb_T         NbCalibSamples; /**< Number of Calibration samples */
  TSL_tTick_sec_T   DTO;            /**< Detection Time Out */
#if TSLPRM_TOTAL_TKEYS > 0
  CONST TSL_State_T           *p_TKeySM; /**< Default state machine for TouchKey sensors */
  CONST TSL_TouchKeyMethods_T *p_TKeyMT; /**< Default methods for TouchKey sensors */
#endif
#if TSLPRM_TOTAL_LNRTS > 0
  CONST TSL_State_T         *p_LinRotSM; /**< Default state machine for Linear/Rotary sensors */
  CONST TSL_LinRotMethods_T *p_LinRotMT; /**< Default methods for Linear/Rotary sensors */
#endif
}
TSL_Params_T;

/* Exported variables --------------------------------------------------------*/
extern TSL_Globals_T TSL_Globals;
extern TSL_Params_T TSL_Params;

#endif /* __TSL_GLOBALS_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
