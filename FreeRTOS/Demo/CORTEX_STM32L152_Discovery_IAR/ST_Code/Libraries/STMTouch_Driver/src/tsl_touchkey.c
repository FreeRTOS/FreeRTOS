/**
  ******************************************************************************
  * @file    tsl_touchkey.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage TouchKey sensors.
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
#include "tsl_touchkey.h"
#include "tsl_globals.h"

#if TSLPRM_TOTAL_TKEYS > 0

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/

/* Private macros ------------------------------------------------------------*/

#define THIS_MEAS                 TSL_Globals.This_TKey->p_ChD->Meas
#define THIS_DELTA                TSL_Globals.This_TKey->p_ChD->Delta
#define THIS_REF                  TSL_Globals.This_TKey->p_ChD->Ref
#define THIS_REFREST              TSL_Globals.This_TKey->p_ChD->RefRest
#define THIS_CHANNEL_DATA         TSL_Globals.This_TKey->p_ChD
#define THIS_ACQ_STATUS           TSL_Globals.This_TKey->p_ChD->Flags.AcqStatus
#define THIS_OBJ_STATUS           TSL_Globals.This_TKey->p_ChD->Flags.ObjStatus
#define THIS_DATA_READY           TSL_Globals.This_TKey->p_ChD->Flags.DataReady

#define THIS_STATEID              TSL_Globals.This_TKey->p_Data->StateId
#define THIS_CHANGE               TSL_Globals.This_TKey->p_Data->Change
#define THIS_COUNTER              TSL_Globals.This_TKey->p_Data->Counter
#define THIS_DXSLOCK              TSL_Globals.This_TKey->p_Data->DxSLock

#define THIS_PROXIN_TH            TSL_Globals.This_TKey->p_Param->ProxInTh
#define THIS_PROXOUT_TH           TSL_Globals.This_TKey->p_Param->ProxOutTh
#define THIS_DETECTIN_TH          TSL_Globals.This_TKey->p_Param->DetectInTh
#define THIS_DETECTOUT_TH         TSL_Globals.This_TKey->p_Param->DetectOutTh
#define THIS_CALIB_TH             TSL_Globals.This_TKey->p_Param->CalibTh

#define THIS_COUNTER_DEB_CALIB    TSL_Globals.This_TKey->p_Param->CounterDebCalib
#define THIS_COUNTER_DEB_PROX     TSL_Globals.This_TKey->p_Param->CounterDebProx
#define THIS_COUNTER_DEB_DETECT   TSL_Globals.This_TKey->p_Param->CounterDebDetect
#define THIS_COUNTER_DEB_RELEASE  TSL_Globals.This_TKey->p_Param->CounterDebRelease
#define THIS_COUNTER_DEB_ERROR    TSL_Globals.This_TKey->p_Param->CounterDebError

#if TSLPRM_DTO > 0
#define DTO_GET_TIME  {TSL_tkey_DTOGetTime();}
#else
#define DTO_GET_TIME
#endif

#if TSLPRM_COEFF_TH > 0
#define TEST_DELTA(OPER,TH) (THIS_DELTA OPER (uint16_t)((uint16_t)TH << TSLPRM_COEFF_TH))
#define TEST_DELTA_NEGATIVE {if (THIS_DELTA < 0) {return;}}
#else
#define TEST_DELTA(OPER,TH) (THIS_DELTA OPER TH)
#define TEST_DELTA_NEGATIVE
#endif

/* Private variables ---------------------------------------------------------*/

static TSL_tNb_T CalibDiv;

/* Private functions prototype -----------------------------------------------*/

void TSL_tkey_DTOGetTime(void);


//==============================================================================
// "Object methods" functions
//==============================================================================

/**
  * @brief  Init parameters with default values from configuration file
  * @param  None
  * @retval None
  */
void TSL_tkey_Init(void)
{
  // Thresholds
#if TSLPRM_USE_PROX > 0
  THIS_PROXIN_TH    = TSLPRM_TKEY_PROX_IN_TH;
  THIS_PROXOUT_TH   = TSLPRM_TKEY_PROX_OUT_TH;
#endif
  THIS_DETECTIN_TH  = TSLPRM_TKEY_DETECT_IN_TH;
  THIS_DETECTOUT_TH = TSLPRM_TKEY_DETECT_OUT_TH;
  THIS_CALIB_TH     = TSLPRM_TKEY_CALIB_TH;

  // Debounce counters
  THIS_COUNTER_DEB_CALIB   = TSLPRM_DEBOUNCE_CALIB;
#if TSLPRM_USE_PROX > 0
  THIS_COUNTER_DEB_PROX    = TSLPRM_DEBOUNCE_PROX;
#endif
  THIS_COUNTER_DEB_DETECT  = TSLPRM_DEBOUNCE_DETECT;
  THIS_COUNTER_DEB_RELEASE = TSLPRM_DEBOUNCE_RELEASE;
  THIS_COUNTER_DEB_ERROR   = TSLPRM_DEBOUNCE_ERROR;

  // Initial state
  TSL_tkey_SetStateCalibration(TSLPRM_CALIB_DELAY);
}


/**
  * @brief  Process the State Machine
  * @param  None
  * @retval None
  */
void TSL_tkey_Process(void)
{
  TSL_StateId_enum_T prev_state_id;

  if ((THIS_DATA_READY != 0) || (THIS_STATEID == TSL_STATEID_OFF))
  {

    THIS_DATA_READY = TSL_DATA_NOT_READY; // The new data is processed

    prev_state_id = THIS_STATEID;

#if TSLPRM_TOTAL_TOUCHKEYS > 0
    if (TSL_Globals.This_Obj->Type == TSL_OBJ_TOUCHKEY)
    {
      // Launch the TKey state function
      TSL_Globals.This_TKey->p_SM[THIS_STATEID].StateFunc();
    }
#endif

#if TSLPRM_TOTAL_TOUCHKEYS_B > 0
    if (TSL_Globals.This_Obj->Type == TSL_OBJ_TOUCHKEYB)
    {
      // Launch the TSL_Params state function
      TSL_Params.p_TKeySM[THIS_STATEID].StateFunc();
    }
#endif

    // Check if the new state has changed
    if (THIS_STATEID == prev_state_id)
    {
      THIS_CHANGE = TSL_STATE_NOT_CHANGED;
    }
    else
    {
      THIS_CHANGE = TSL_STATE_CHANGED;
    }

#if TSLPRM_USE_DXS > 0
    if (THIS_STATEID != TSL_STATEID_DETECT)
    {
      THIS_DXSLOCK = TSL_FALSE;
    }
    if (THIS_STATEID == TSL_STATEID_TOUCH)
    {
      THIS_STATEID = TSL_STATEID_DETECT;
    }
#endif

  }
}


//==============================================================================
// Utility functions
//==============================================================================

/**
  * @brief  Go in Calibration state
  * @param[in] delay Delay before calibration starts (stabilization of noise filter)
  * @retval None
  */
void TSL_tkey_SetStateCalibration(TSL_tCounter_T delay)
{
  THIS_STATEID = TSL_STATEID_CALIB;
  THIS_CHANGE = TSL_STATE_CHANGED;
  THIS_OBJ_STATUS = TSL_OBJ_STATUS_ON;

  switch (TSL_Params.NbCalibSamples)
  {
    case 4:
      CalibDiv = 2;
      break;
    case 16:
      CalibDiv = 4;
      break;
    default:
      TSL_Params.NbCalibSamples =  8;
      CalibDiv = 3;
      break;
  }

  // If a noise filter is used, the counter must be initialized to a value
  // different from 0 in order to stabilize the filter.
  THIS_COUNTER = (TSL_tCounter_T)(delay + (TSL_tCounter_T)TSL_Params.NbCalibSamples);
  THIS_REF = 0;
}


/**
  * @brief  Go in Off state with sensor "off"
  * @param  None
  * @retval None
  */
void TSL_tkey_SetStateOff(void)
{
  THIS_STATEID = TSL_STATEID_OFF;
  THIS_CHANGE = TSL_STATE_CHANGED;
  THIS_OBJ_STATUS = TSL_OBJ_STATUS_OFF;
}


#if !defined(TSLPRM_STM8TL5X) && !defined(STM8TL5X)
/**
  * @brief  Go in Off state with sensor in "Burst mode only"
  * @param  None
  * @retval None
  */
void TSL_tkey_SetStateBurstOnly(void)
{
  THIS_STATEID = TSL_STATEID_OFF;
  THIS_CHANGE = TSL_STATE_CHANGED;
  THIS_OBJ_STATUS = TSL_OBJ_STATUS_BURST_ONLY;
}
#endif


/**
  * @brief  Return the current state identifier
  * @param  None
  * @retval State id
  */
TSL_StateId_enum_T TSL_tkey_GetStateId(void)
{
  return(THIS_STATEID);
}


/**
  * @brief  Return the current state mask
  * @param  None
  * @retval State mask
  */
TSL_StateMask_enum_T TSL_tkey_GetStateMask(void)
{
  TSL_StateMask_enum_T state_mask = TSL_STATEMASK_UNKNOWN;

#if TSLPRM_TOTAL_TOUCHKEYS > 0
  if (TSL_Globals.This_Obj->Type == TSL_OBJ_TOUCHKEY)
  {
    state_mask = TSL_Globals.This_TKey->p_SM[THIS_STATEID].StateMask;
  }
#endif

#if TSLPRM_TOTAL_TOUCHKEYS_B > 0
  if (TSL_Globals.This_Obj->Type == TSL_OBJ_TOUCHKEYB)
  {
    state_mask = TSL_Params.p_TKeySM[THIS_STATEID].StateMask;
  }
#endif

  return state_mask;
}


/**
  * @brief  Return the Change flag
  * @param  None
  * @retval Change flag status
  */
TSL_tNb_T TSL_tkey_IsChanged(void)
{
  return(THIS_CHANGE);
}


//==============================================================================
// State machine functions
//==============================================================================

#if TSLPRM_USE_PROX > 0
/**
  * @brief  Debounce Release processing (previous state = Proximity)
  * @param  None
  * @retval None
  */
void TSL_tkey_DebReleaseProxStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_PROX; // Go back to the previous state
  }
  else // Acquisition is OK or has NOISE
  {
    if (THIS_DELTA > THIS_PROXOUT_TH)
    {
      THIS_STATEID = TSL_STATEID_PROX; // Go back to the previous state
    }
    else
    {
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_RELEASE;
      }
      // else stay in Debounce Release
    }
  }
}
#endif // if TSLPRM_USE_PROX > 0


/**
  * @brief  Debounce Release processing (previous state = Detect)
  * @param  None
  * @retval None
  */
void TSL_tkey_DebReleaseDetectStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_DETECT; // Go back to the previous state
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>, THIS_DETECTOUT_TH)
    {
      TEST_DELTA_NEGATIVE;
      THIS_STATEID = TSL_STATEID_DETECT;
    }
    else
    {
#if TSLPRM_USE_PROX > 0
      if (THIS_DELTA > THIS_PROXOUT_TH)
      {
        THIS_STATEID = TSL_STATEID_PROX;
        return;
      }
#endif
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_RELEASE;
      }
      // else stay in Debounce Release
    }
  }
}


/**
  * @brief  Debounce Release processing (previous state = Touch)
  * Same as Debounce Release Detect processing
  * @param  None
  * @retval None
  */
void TSL_tkey_DebReleaseTouchStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_TOUCH; // Go back to the previous state
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>, THIS_DETECTOUT_TH)
    {
      TEST_DELTA_NEGATIVE;
      THIS_STATEID = TSL_STATEID_TOUCH;
    }
    else
    {
#if TSLPRM_USE_PROX > 0
      if (THIS_DELTA > THIS_PROXOUT_TH)
      {
        THIS_STATEID = TSL_STATEID_PROX;
        return;
      }
#endif
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_RELEASE;
      }
      // else stay in Debounce Release
    }
  }
}


/**
  * @brief  Release state processing
  * @param  None
  * @retval None
  */
void TSL_tkey_ReleaseStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_COUNTER = THIS_COUNTER_DEB_ERROR;
    if (THIS_COUNTER == 0)
    {
      THIS_STATEID = TSL_STATEID_ERROR;
    }
    else
    {
      THIS_STATEID = TSL_STATEID_DEB_ERROR_RELEASE;
    }
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>=, THIS_DETECTIN_TH)
    {
      TEST_DELTA_NEGATIVE;
      THIS_COUNTER = THIS_COUNTER_DEB_DETECT;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_DETECT;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_DETECT;
      }
      return;
    }

#if TSLPRM_USE_PROX > 0
    if (THIS_DELTA >= THIS_PROXIN_TH)
    {
      THIS_COUNTER = THIS_COUNTER_DEB_PROX;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_PROX;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_PROX;
      }
      return;
    }
#endif

    // Check delta for re-calibration
    // Warning: the threshold value is inverted
    if (THIS_DELTA <= -THIS_CALIB_TH)
    {
      THIS_COUNTER = THIS_COUNTER_DEB_CALIB;
      if (THIS_COUNTER == 0)
      {
        TSL_tkey_SetStateCalibration(0);
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_CALIB;
      }
    }
  }
}


/**
  * @brief  Debounce Calibration processing (previous state = Release)
  * @param  None
  * @retval None
  */
void TSL_tkey_DebCalibrationStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_RELEASE; // Go back to the previous state
  }
  else // Acquisition is OK or has NOISE
  {
    // Still below recalibration threshold
    // Warning: the threshold value is inverted
    if (THIS_DELTA <= -THIS_CALIB_TH)
    {
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        TSL_tkey_SetStateCalibration(0);
      }
      // else stay in Debounce Calibration
    }
    else // Go back to previous state
    {
      THIS_STATEID = TSL_STATEID_RELEASE;
    }
  }
}


/**
  * @brief  Calibration state processing
  * @param  None
  * @retval None
  */
void TSL_tkey_CalibrationStateProcess(void)
{
  TSL_tMeas_T new_meas;

#if TSLPRM_CALIB_DELAY > 0
  // Noise filter stabilization time
  if (THIS_COUNTER > (TSL_tCounter_T)TSL_Params.NbCalibSamples)
  {
    THIS_COUNTER--;
    return; // Skip the sample
  }
#endif

  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_COUNTER = THIS_COUNTER_DEB_ERROR;
    if (THIS_COUNTER == 0)
    {
      THIS_STATEID = TSL_STATEID_ERROR;
    }
    else
    {
      THIS_STATEID = TSL_STATEID_DEB_ERROR_CALIB;
    }
  }
  else // Acquisition is OK or has NOISE
  {

    // Get the new measure or Calculate it
#if TSLPRM_USE_MEAS > 0
    new_meas = THIS_MEAS;
#else // Calculate it
    new_meas = TSL_acq_ComputeMeas(THIS_REF, THIS_DELTA);
#endif

    // Verify the first Reference value
    if (THIS_COUNTER == (TSL_tCounter_T)TSL_Params.NbCalibSamples)
    {
      if (TSL_acq_TestFirstReferenceIsValid(THIS_CHANNEL_DATA, new_meas))
      {
        THIS_REF = new_meas;
      }
      else
      {
        THIS_REF = 0;
        return;
      }
    }
    else
    {
      // Add the measure in temporary Reference
      THIS_REF += new_meas;

      // Check reference overflow
      if (THIS_REF < new_meas)
      {
        THIS_REF = 0; // Suppress the bad reference
        THIS_STATEID = TSL_STATEID_ERROR;
        return;
      }
    }

    // Check that we have all the needed measurements
    if (THIS_COUNTER > 0) {THIS_COUNTER--;}
    if (THIS_COUNTER == 0)
    {
      // Divide temporary Reference by the number of samples
      THIS_REF >>= CalibDiv;
      THIS_REFREST = 0;
      THIS_DELTA = 0;
      THIS_STATEID = TSL_STATEID_RELEASE;
    }
  }
}


#if TSLPRM_USE_PROX > 0
/**
  * @brief  Debounce Proximity processing (previous state = Release)
  * @param  None
  * @retval None
  */
void TSL_tkey_DebProxStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_RELEASE;
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>=, THIS_DETECTIN_TH)
    {
      TEST_DELTA_NEGATIVE;
      THIS_COUNTER = THIS_COUNTER_DEB_DETECT;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_DETECT;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_DETECT;
      }
      return;
    }

    if (THIS_DELTA >= THIS_PROXIN_TH)
    {
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_PROX;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      // else stay in Debounce Proximity
    }
    else
    {
      THIS_STATEID = TSL_STATEID_RELEASE;
    }
  }
}
#endif


#if TSLPRM_USE_PROX > 0
/**
  * @brief  Debounce Proximity processing (previous state = Detect)
  * @param  None
  * @retval None
  */
void TSL_tkey_DebProxDetectStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_DETECT;
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>, THIS_DETECTOUT_TH)
    {
      TEST_DELTA_NEGATIVE;
      THIS_STATEID = TSL_STATEID_DETECT;
      return;
    }

    if (THIS_DELTA > THIS_PROXOUT_TH)
    {
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_PROX;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      // else stay in Debounce Proximity
    }
    else
    {
      THIS_COUNTER = THIS_COUNTER_DEB_RELEASE;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_RELEASE;
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_RELEASE_DETECT;
      }
    }
  }
}
#endif


#if TSLPRM_USE_PROX > 0
/**
  * @brief  Debounce Proximity processing (previous state = Touch)
  * @param  None
  * @retval None
  */
void TSL_tkey_DebProxTouchStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_TOUCH;
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>, THIS_DETECTOUT_TH)
    {
      TEST_DELTA_NEGATIVE;
      THIS_STATEID = TSL_STATEID_TOUCH;
      return;
    }

    if (THIS_DELTA > THIS_PROXOUT_TH)
    {
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_PROX;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      // else stay in Debounce Proximity
    }
    else
    {
      THIS_COUNTER = THIS_COUNTER_DEB_RELEASE;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_RELEASE;
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_RELEASE_TOUCH;
      }
    }
  }
}
#endif


#if TSLPRM_USE_PROX > 0
/**
  * @brief  Proximity state processing
  * @param  None
  * @retval None
  */
void TSL_tkey_ProxStateProcess(void)
{
#if TSLPRM_DTO > 0
  TSL_tTick_sec_T tick_detected;
#endif

  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_COUNTER = THIS_COUNTER_DEB_ERROR;
    if (THIS_COUNTER == 0)
    {
      THIS_STATEID = TSL_STATEID_ERROR;
    }
    else
    {
      THIS_STATEID = TSL_STATEID_DEB_ERROR_PROX;
    }
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>=, THIS_DETECTIN_TH)
    {
      TEST_DELTA_NEGATIVE;
      THIS_COUNTER = THIS_COUNTER_DEB_DETECT;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_DETECT;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_DETECT;
      }
      return;
    }

    if (THIS_DELTA <= THIS_PROXOUT_TH)
    {
      THIS_COUNTER = THIS_COUNTER_DEB_RELEASE;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_RELEASE;
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_RELEASE_PROX;
      }
      return;
    }

    // Stay in Proximity state
#if TSLPRM_DTO > 0
    //------------------------------------
    // Detection Time Out (DTO) processing
    //------------------------------------
    if ((TSL_Params.DTO > 1) && (TSL_Params.DTO < 64))
    {
      tick_detected = THIS_COUNTER; // Get the detected time previously saved
      // Enter in calibration state if the DTO duration has elapsed
      if (TSL_tim_CheckDelay_sec(TSL_Params.DTO, &tick_detected) == TSL_STATUS_OK)
      {
        TSL_tkey_SetStateCalibration(0);
      }
    }
#endif

  }
}
#endif


/**
  * @brief  Debounce Detect processing (previous state = Release or Proximity)
  * @param  None
  * @retval None
  */
void TSL_tkey_DebDetectStateProcess(void)
{
  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_RELEASE;
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>=, THIS_DETECTIN_TH)
    {
      TEST_DELTA_NEGATIVE;
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_DETECT;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      // else stay in Debounce Detect
    }
    else
    {
#if TSLPRM_USE_PROX > 0
      if (THIS_DELTA >= THIS_PROXIN_TH)
      {
        THIS_COUNTER = THIS_COUNTER_DEB_PROX;
        if (THIS_COUNTER == 0)
        {
          THIS_STATEID = TSL_STATEID_PROX;
          DTO_GET_TIME; // Take current time for DTO processing
        }
        else
        {
          THIS_STATEID = TSL_STATEID_DEB_PROX;
        }
      }
      else
      {
        THIS_STATEID = TSL_STATEID_RELEASE;
      }
#else
      THIS_STATEID = TSL_STATEID_RELEASE;
#endif
    }
  }
}


/**
  * @brief  Detect state processing
  * @param  None
  * @retval None
  */
void TSL_tkey_DetectStateProcess(void)
{
#if TSLPRM_DTO > 0
  TSL_tTick_sec_T tick_detected;
#endif

  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_COUNTER = THIS_COUNTER_DEB_ERROR;
    if (THIS_COUNTER == 0)
    {
      THIS_STATEID = TSL_STATEID_ERROR;
    }
    else
    {
      THIS_STATEID = TSL_STATEID_DEB_ERROR_DETECT;
    }
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>, THIS_DETECTOUT_TH)
    {
      TEST_DELTA_NEGATIVE;
#if TSLPRM_DTO > 0
      //------------------------------------
      // Detection Time Out (DTO) processing
      //------------------------------------
      if ((TSL_Params.DTO > 1) && (TSL_Params.DTO < 64))
      {
        tick_detected = THIS_COUNTER; // Get the detected time previously saved
        // Enter in calibration state if the DTO duration has elapsed
        if (TSL_tim_CheckDelay_sec(TSL_Params.DTO, &tick_detected) == TSL_STATUS_OK)
        {
          TSL_tkey_SetStateCalibration(0);
        }
      }
#endif
      return; // Normal operation, stay in Detect state
    }

#if TSLPRM_USE_PROX > 0
    if (THIS_DELTA > THIS_PROXOUT_TH)
    {
      THIS_COUNTER = THIS_COUNTER_DEB_PROX;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_PROX;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_PROX_DETECT;
      }
      return;
    }
#endif

    THIS_COUNTER = THIS_COUNTER_DEB_RELEASE;
    if (THIS_COUNTER == 0)
    {
      THIS_STATEID = TSL_STATEID_RELEASE;
    }
    else
    {
      THIS_STATEID = TSL_STATEID_DEB_RELEASE_DETECT;
    }

  }
}


/**
  * @brief  Touch state processing
  * Same as Detect state
  * @param  None
  * @retval None
  */
void TSL_tkey_TouchStateProcess(void)
{
#if TSLPRM_DTO > 0
  TSL_tTick_sec_T tick_detected;
#endif

  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    THIS_COUNTER = THIS_COUNTER_DEB_ERROR;
    if (THIS_COUNTER == 0)
    {
      THIS_STATEID = TSL_STATEID_ERROR;
    }
    else
    {
      THIS_STATEID = TSL_STATEID_DEB_ERROR_TOUCH;
    }
  }
  else // Acquisition is OK or has NOISE
  {
    if TEST_DELTA(>, THIS_DETECTOUT_TH)
    {
      TEST_DELTA_NEGATIVE;
#if TSLPRM_DTO > 0
      //------------------------------------
      // Detection Time Out (DTO) processing
      //------------------------------------
      if ((TSL_Params.DTO > 1) && (TSL_Params.DTO < 64))
      {
        tick_detected = THIS_COUNTER; // Get the detected time previously saved
        // Enter in calibration state if the DTO duration has elapsed
        if (TSL_tim_CheckDelay_sec(TSL_Params.DTO, &tick_detected) == TSL_STATUS_OK)
        {
          TSL_tkey_SetStateCalibration(0);
        }
      }
#endif
      return; // Normal operation, stay in Touch state
    }

#if TSLPRM_USE_PROX > 0
    if (THIS_DELTA > THIS_PROXOUT_TH)
    {
      THIS_COUNTER = THIS_COUNTER_DEB_PROX;
      if (THIS_COUNTER == 0)
      {
        THIS_STATEID = TSL_STATEID_PROX;
        DTO_GET_TIME; // Take current time for DTO processing
      }
      else
      {
        THIS_STATEID = TSL_STATEID_DEB_PROX_TOUCH;
      }
      return;
    }
#endif

    THIS_COUNTER = THIS_COUNTER_DEB_RELEASE;
    if (THIS_COUNTER == 0)
    {
      THIS_STATEID = TSL_STATEID_RELEASE;
    }
    else
    {
      THIS_STATEID = TSL_STATEID_DEB_RELEASE_TOUCH;
    }

  }
}


/**
  * @brief  Debounce error state processing
  * @param  None
  * @retval None
  */
void TSL_tkey_DebErrorStateProcess(void)
{
  volatile TSL_StateMask_enum_T mask;

  if (THIS_ACQ_STATUS & TSL_ACQ_STATUS_ERROR_MASK) // Acquisition error (min or max)
  {
    if (THIS_COUNTER > 0) {THIS_COUNTER--;}
    if (THIS_COUNTER == 0)
    {
      THIS_STATEID = TSL_STATEID_ERROR;
    }
  }
  else // Acquisition is OK or has NOISE
  {
    // Get state mask
    mask = TSL_tkey_GetStateMask();
    // Mask Error and Debounce bits
#ifdef _RAISONANCE_
    mask &= ~(TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_ERROR_BIT_MASK);
#else
    mask &= (TSL_StateMask_enum_T)(~(TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_ERROR_BIT_MASK));
#endif
    // Go back to the previous state
    switch (mask)
    {
      case TSL_STATEMASK_RELEASE :
        THIS_STATEID = TSL_STATEID_RELEASE;
        break;
      case TSL_STATEMASK_PROX :
        THIS_STATEID = TSL_STATEID_PROX;
        break;
      case TSL_STATEMASK_DETECT :
        THIS_STATEID = TSL_STATEID_DETECT;
        break;
      case TSL_STATEMASK_TOUCH :
        THIS_STATEID = TSL_STATEID_TOUCH;
        break;
      default:
        TSL_tkey_SetStateCalibration(0);
        break;
    }
  }
}


//==============================================================================
// Private functions
//==============================================================================

/**
  * @brief  Get the current time in second and affect it to the DTO counter (Private)
  * @param  None
  * @retval None
  */
void TSL_tkey_DTOGetTime(void)
{
  disableInterrupts();
  THIS_COUNTER = (TSL_tCounter_T)TSL_Globals.Tick_sec;
  enableInterrupts();
}

#endif
// #if TSLPRM_TOTAL_TKEYS > 0

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
