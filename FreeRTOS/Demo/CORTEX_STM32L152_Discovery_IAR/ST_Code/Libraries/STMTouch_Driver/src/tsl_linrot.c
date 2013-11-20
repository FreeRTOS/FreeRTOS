/**
  ******************************************************************************
  * @file    tsl_linrot.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage Linear and Rotary sensors.
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
#include "tsl_linrot.h"
#include "tsl_globals.h"

#if TSLPRM_TOTAL_LNRTS > 0

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/

/* Private macros ------------------------------------------------------------*/

#define THIS_OBJ_TYPE             TSL_Globals.This_Obj->Type

#define THIS_STATEID              TSL_Globals.This_LinRot->p_Data->StateId
#define THIS_RAW_POSITION         TSL_Globals.This_LinRot->p_Data->RawPosition
#define THIS_POSITION             TSL_Globals.This_LinRot->p_Data->Position
#define THIS_CHANGE               TSL_Globals.This_LinRot->p_Data->Change
#define THIS_POSCHANGE            TSL_Globals.This_LinRot->p_Data->PosChange
#define THIS_COUNTER              TSL_Globals.This_LinRot->p_Data->Counter
#define THIS_COUNTER2             TSL_Globals.This_LinRot->p_Data->Counter2
#define THIS_DXSLOCK              TSL_Globals.This_LinRot->p_Data->DxSLock
#define THIS_DIRECTION            TSL_Globals.This_LinRot->p_Data->Direction

#define THIS_PROXIN_TH            TSL_Globals.This_LinRot->p_Param->ProxInTh
#define THIS_PROXOUT_TH           TSL_Globals.This_LinRot->p_Param->ProxOutTh
#define THIS_DETECTIN_TH          TSL_Globals.This_LinRot->p_Param->DetectInTh
#define THIS_DETECTOUT_TH         TSL_Globals.This_LinRot->p_Param->DetectOutTh
#define THIS_CALIB_TH             TSL_Globals.This_LinRot->p_Param->CalibTh

#define THIS_RESOLUTION           TSL_Globals.This_LinRot->p_Param->Resolution
#define THIS_DIR_CHG_POS          TSL_Globals.This_LinRot->p_Param->DirChangePos

#define THIS_COUNTER_DEB_CALIB     TSL_Globals.This_LinRot->p_Param->CounterDebCalib
#define THIS_COUNTER_DEB_PROX      TSL_Globals.This_LinRot->p_Param->CounterDebProx
#define THIS_COUNTER_DEB_DETECT    TSL_Globals.This_LinRot->p_Param->CounterDebDetect
#define THIS_COUNTER_DEB_RELEASE   TSL_Globals.This_LinRot->p_Param->CounterDebRelease
#define THIS_COUNTER_DEB_ERROR     TSL_Globals.This_LinRot->p_Param->CounterDebError
#define THIS_COUNTER_DEB_DIRECTION TSL_Globals.This_LinRot->p_Param->CounterDebDirection

#define THIS_NB_CHANNELS           TSL_Globals.This_LinRot->NbChannels
#define THIS_SCT_COMP              TSL_Globals.This_LinRot->SctComp
#define THIS_POS_CORR              TSL_Globals.This_LinRot->PosCorr

#if TSLPRM_DTO > 0
#define DTO_GET_TIME  {TSL_linrot_DTOGetTime();}
#else
#define DTO_GET_TIME
#endif

/* Private variables ---------------------------------------------------------*/

//================================================================
// See AN2869 for more details on Linear and Rotary sensors design
//================================================================

//==============================================================================
// 3 CHANNELS - LINEAR - MONO - 0/255 at extremities
// i.e. CH1 CH2 CH3
//==============================================================================
#if TSLPRM_USE_3CH_LIN_M1 > 0
CONST TSL_tsignPosition_T TSL_POSOFF_3CH_LIN_M1[3][3] =
{
// sec = 1     2     3
//   j = 0     1     2
    {    0,  -96,    0 }, // maj = 1; i = 0
    {   32,    0, -160 }, // maj = 2; i = 1
    {    0,   96,    0 }  // maj = 3; i = 2
};
#endif

//==============================================================================
// 3 CHANNELS - LINEAR - MONO
// i.e. CH1 CH2 CH3
//==============================================================================
#if TSLPRM_USE_3CH_LIN_M2 > 0
CONST TSL_tsignPosition_T TSL_POSOFF_3CH_LIN_M2[3][3] =
{
// sec = 1     2     3
//   j = 0     1     2
    {    0, -192,    0 }, // maj = 1; i = 0
    {   64,    0, -320 }, // maj = 2; i = 1
    {    0,  192,    0 }  // maj = 3; i = 2
};
#endif

//==============================================================================
// 3 CHANNELS - LINEAR - HALF-ENDED
// i.e. CH1 CH2 CH3 CH1
//==============================================================================
#if TSLPRM_USE_3CH_LIN_H > 0
CONST TSL_tsignPosition_T TSL_POSOFF_3CH_LIN_H[3][3] =
{
// sec = 1     2     3
//   j = 0     1     2
    {    0,  -96,  160 }, // maj = 1; i = 0
    {   32,    0, -160 }, // maj = 2; i = 1
    { -224,   96,    0 }  // maj = 3; i = 2
};
#endif

//==============================================================================
// 3 CHANNELS - ROTARY - MONO
// i.e. CH1 CH2 CH3
//==============================================================================
#if TSLPRM_USE_3CH_ROT_M > 0
CONST TSL_tsignPosition_T TSL_POSOFF_3CH_ROT_M[3][3] =
{
// sec = 1     2     3
//   j = 0     1     2
    {    0,  -64,  107 }, // maj = 1; i = 0
    {   21,    0, -107 }, // maj = 2; i = 1
    { -149,   64,    0 }  // maj = 3; i = 2
};
#endif

//==============================================================================
// 4 CHANNELS - LINEAR - MONO - 0/255 at extremities
// i.e. CH1 CH2 CH3 CH4
//==============================================================================
#if TSLPRM_USE_4CH_LIN_M1 > 0
CONST TSL_tsignPosition_T TSL_POSOFF_4CH_LIN_M1[4][4] =
{
// sec = 1     2     3     4
//   j = 0     1     2     3
    {    0,  -64,    0,    0 }, // maj = 1; i = 0
    {   21,    0, -107,    0 }, // maj = 2; i = 1
    {    0,   64,    0, -149 }, // maj = 3; i = 2
    {    0,    0,  107,    0 }  // maj = 4; i = 3
};
#endif

//==============================================================================
// 4 CHANNELS - LINEAR - MONO
// i.e. CH1 CH2 CH3 CH4
//==============================================================================
#if TSLPRM_USE_4CH_LIN_M2 > 0
CONST TSL_tsignPosition_T TSL_POSOFF_4CH_LIN_M2[4][4] =
{
// sec = 1     2     3     4
//   j = 0     1     2     3
    {    0,  -96,    0,    0 }, // maj = 1; i = 0
    {   32,    0, -160,    0 }, // maj = 2; i = 1
    {    0,   96,    0, -224 }, // maj = 3; i = 2
    {    0,    0,  160,    0 }  // maj = 4; i = 3
};
#endif

//==============================================================================
// 4 CHANNELS - LINEAR - HALF-ENDED
// i.e. CH1 CH2 CH3 CH4 CH1
//==============================================================================
#if TSLPRM_USE_4CH_LIN_H > 0
CONST TSL_tsignPosition_T TSL_POSOFF_4CH_LIN_H[4][4] =
{
// sec = 1     2     3     4
//   j = 0     1     2     3
    {    0,  -64,    0,  149 }, // maj = 1; i = 0
    {   21,    0, -107,    0 }, // maj = 2; i = 1
    {    0,   64,    0, -149 }, // maj = 3; i = 2
    { -192,    0,  107,    0 }  // maj = 4; i = 3
};
#endif

//==============================================================================
// 4 CHANNELS - ROTARY - MONO
// i.e. CH1 CH2 CH3 CH4
//==============================================================================
#if TSLPRM_USE_4CH_ROT_M > 0
CONST TSL_tsignPosition_T TSL_POSOFF_4CH_ROT_M[4][4] =
{
// sec = 1     2     3     4
//   j = 0     1     2     3
    {    0,  -48,    0,  112 }, // maj = 1; i = 0
    {   16,    0,  -80,    0 }, // maj = 2; i = 1
    {    0,   48,    0, -112 }, // maj = 3; i = 2
    { -144,    0,   80,    0 }  // maj = 4; i = 3
};
#endif

//==============================================================================
// 5 CHANNELS - LINEAR - MONO - 0/255 at extremities
// i.e. CH1 CH2 CH3 CH4 CH5
//==============================================================================
#if TSLPRM_USE_5CH_LIN_M1 > 0
CONST TSL_tsignPosition_T TSL_POSOFF_5CH_LIN_M1[5][5] =
{
// sec = 1     2     3     4     5
//   j = 0     1     2     3     4
    {    0,  -48,    0,    0,    0 }, // maj = 1; i = 0
    {   16,    0,  -80,    0,    0 }, // maj = 2; i = 1
    {    0,   48,    0, -112,    0 }, // maj = 3; i = 2
    {    0,    0,   80,    0, -144 }, // maj = 4; i = 3
    {    0,    0,    0,  112,    0 }  // maj = 5; i = 4
};
#endif

//==============================================================================
// 5 CHANNELS - LINEAR - MONO
// i.e. CH1 CH2 CH3 CH4 CH5
//==============================================================================
#if TSLPRM_USE_5CH_LIN_M2 > 0
CONST TSL_tsignPosition_T TSL_POSOFF_5CH_LIN_M2[5][5] =
{
// sec = 1     2     3     4     5
//   j = 0     1     2     3     4
    {    0,  -64,    0,    0,    0 }, // maj = 1; i = 0
    {   21,    0, -107,    0,    0 }, // maj = 2; i = 1
    {    0,   64,    0, -149,    0 }, // maj = 3; i = 2
    {    0,    0,  107,    0, -192 }, // maj = 4; i = 3
    {    0,    0,    0,  149,    0 }  // maj = 5; i = 4
};
#endif

//==============================================================================
// 5 CHANNELS - LINEAR - HALF-ENDED
// i.e. CH1 CH2 CH3 CH4 CH5 CH1
//==============================================================================
#if TSLPRM_USE_5CH_LIN_H > 0
CONST TSL_tsignPosition_T TSL_POSOFF_5CH_LIN_H[5][5] =
{
// sec = 1     2     3     4     5
//   j = 0     1     2     3     4
    {    0,  -48,    0,    0,  144 }, // maj = 1; i = 0
    {   16,    0,  -80,    0,    0 }, // maj = 2; i = 1
    {    0,   48,    0, -112,    0 }, // maj = 3; i = 2
    {    0,    0,   80,    0, -144 }, // maj = 4; i = 3
    { -176,    0,    0,  112,    0 }  // maj = 5; i = 4
};
#endif

//==============================================================================
// 5 CHANNELS - ROTARY - MONO
// i.e. CH1 CH2 CH3 CH4 CH5
//==============================================================================
#if TSLPRM_USE_5CH_ROT_M > 0
CONST TSL_tsignPosition_T TSL_POSOFF_5CH_ROT_M[5][5] =
{
// sec = 1     2     3     4     5
//   j = 0     1     2     3     4
     {   0,  -38,    0,    0,  115 }, // maj = 1; i = 0
     {  13,    0,  -64,    0,    0 }, // maj = 2; i = 1
     {   0,   38,    0,  -90,    0 }, // maj = 3; i = 2
     {   0,    0,   64,    0, -115 }, // maj = 4; i = 3
     {-141,    0,    0,   90,    0 }  // maj = 5; i = 4
};
#endif

//==============================================================================
// 5 CHANNELS - ROTARY - DUAL
// i.e. CH1 CH2 CH3 CH4 CH5 CH1 CH3 CH5 CH2 CH4
//==============================================================================
#if TSLPRM_USE_5CH_ROT_D > 0
CONST TSL_tsignPosition_T TSL_POSOFF_5CH_ROT_D[5][5] =
{
// sec = 1     2     3     4     5
//   j = 0     1     2     3     4
     {   0,  -19,  -83,  122,   58 }, // maj = 1; i = 0
     {   6,    0,  -32, -122,   96 }, // maj = 2; i = 1
     {  70,   19,    0,  -45,  -96 }, // maj = 3; i = 2
     {-134,  109,   32,    0,  -58 }, // maj = 4; i = 3
     { -70, -109,   83,   45,    0 }  // maj = 5; i = 4
};
#endif

//==============================================================================
// 6 CHANNELS - LINEAR - MONO - 0/255 at extremities
// i.e. CH1 CH2 CH3 CH4 CH5 CH6
//==============================================================================
#if TSLPRM_USE_6CH_LIN_M1 > 0
CONST TSL_tsignPosition_T TSL_POSOFF_6CH_LIN_M1[6][6] =
{
// sec = 1     2     3     4     5     6
//   j = 0     1     2     3     4     5
     {   0,  -38,    0,    0,    0,    0 }, // maj = 1; i = 0
     {  13,    0,  -64,    0,    0,    0 }, // maj = 2; i = 1
     {   0,   38,    0,  -90,    0,    0 }, // maj = 3; i = 2
     {   0,    0,   64,    0, -115,    0 }, // maj = 4; i = 3
     {   0,    0,    0,   90,    0, -141 }, // maj = 5; i = 4
     {   0,    0,    0,    0,  115,    0 }  // maj = 6; i = 5
};
#endif

//==============================================================================
// 6 CHANNELS - LINEAR - MONO
// i.e. CH1 CH2 CH3 CH4 CH5 CH6
//==============================================================================
#if TSLPRM_USE_6CH_LIN_M2 > 0
CONST TSL_tsignPosition_T TSL_POSOFF_6CH_LIN_M2[6][6] =
{
// sec = 1     2     3     4     5     6
//   j = 0     1     2     3     4     5
     {   0,  -48,    0,    0,    0,    0 }, // maj = 1; i = 0
     {  16,    0,  -80,    0,    0,    0 }, // maj = 2; i = 1
     {   0,   48,    0, -112,    0,    0 }, // maj = 3; i = 2
     {   0,    0,   80,    0, -144,    0 }, // maj = 4; i = 3
     {   0,    0,    0,  112,    0, -176 }, // maj = 5; i = 4
     {   0,    0,    0,    0,  144,    0 }  // maj = 6; i = 5
};
#endif

//==============================================================================
// 6 CHANNELS - LINEAR - HALF-ENDED
// i.e. CH1 CH2 CH3 CH4 CH5 CH6 CH1
//==============================================================================
#if TSLPRM_USE_6CH_LIN_H > 0
CONST TSL_tsignPosition_T TSL_POSOFF_6CH_LIN_H[6][6] =
{
// sec = 1     2     3     4     5     6
//   j = 0     1     2     3     4     5
     {   0,  -38,    0,    0,    0,  141 }, // maj = 1; i = 0
     {  13,    0,  -64,    0,    0,    0 }, // maj = 2; i = 1
     {   0,   38,    0,  -90,    0,    0 }, // maj = 3; i = 2
     {   0,    0,   64,    0, -115,    0 }, // maj = 4; i = 3
     {   0,    0,    0,   90,    0, -141 }, // maj = 5; i = 4
     {-166,    0,    0,    0,  115,    0 }  // maj = 6; i = 5
};
#endif

//==============================================================================
// 6 CHANNELS - ROTARY - MONO
// i.e. CH1 CH2 CH3 CH4 CH5 CH6
//==============================================================================
#if TSLPRM_USE_6CH_ROT_M > 0
CONST TSL_tsignPosition_T TSL_POSOFF_6CH_ROT_M[6][6] =
{
// sec = 1     2     3     4     5     6
//   j = 0     1     2     3     4     5
     {   0,  -32,    0,    0,    0,  117 }, // maj = 1; i = 0
     {  11,    0,  -53,    0,    0,    0 }, // maj = 2; i = 1
     {   0,   32,    0,  -75,    0,    0 }, // maj = 3; i = 2
     {   0,    0,   53,    0,  -96,    0 }, // maj = 4; i = 3
     {   0,    0,    0,   75,    0, -117 }, // maj = 5; i = 4
     {-139,    0,    0,    0,   96,    0 }  // maj = 6; i = 5
};
#endif

//------------------
// Common parameters
//------------------

#define DIRECTION_CHANGE_MAX_DISPLACEMENT (255)
#define DIRECTION_CHANGE_TOTAL_STEPS      (256)
#define RESOLUTION_CALCULATION            (8)

static TSL_tNb_T CalibDiv;

/* Private functions prototype -----------------------------------------------*/

void TSL_linrot_DTOGetTime(void);
void TSL_linrot_ProcessCh_All_SetStatus(TSL_ObjStatus_enum_T sts);
TSL_Status_enum_T TSL_linrot_ProcessCh_One_DataReady(void);
TSL_Status_enum_T TSL_linrot_ProcessCh_All_AcqStatus(TSL_AcqStatus_enum_T sts);
TSL_Status_enum_T TSL_linrot_ProcessCh_One_AcqStatusError(void);
TSL_Status_enum_T TSL_linrot_ProcessCh_One_DeltaBelowEquMinus(TSL_tThreshold_T th);
TSL_Status_enum_T TSL_linrot_ProcessCh_One_DeltaAboveEqu(TSL_tThreshold_T th, TSL_tIndex_T coeff);
TSL_Status_enum_T TSL_linrot_ProcessCh_One_DeltaAbove(TSL_tThreshold_T th, TSL_tIndex_T coeff);
TSL_Status_enum_T TSL_linrot_ProcessCh_All_DeltaBelowEqu(TSL_tThreshold_T th, TSL_tIndex_T coeff);
void TSL_linrot_ProcessCh_All_ClearRef(void);
TSL_tDelta_T TSL_linrot_NormDelta(TSL_ChannelData_T *ch, TSL_tIndex_T idx);


//==============================================================================
// "Object methods" functions
//==============================================================================

/**
  * @brief  Init parameters with default values from configuration file
  * @param  None
  * @retval None
  */
void TSL_linrot_Init(void)
{
  // Thresholds
#if TSLPRM_USE_PROX > 0
  THIS_PROXIN_TH    = TSLPRM_LINROT_PROX_IN_TH;
  THIS_PROXOUT_TH   = TSLPRM_LINROT_PROX_OUT_TH;
#endif
  THIS_DETECTIN_TH  = TSLPRM_LINROT_DETECT_IN_TH;
  THIS_DETECTOUT_TH = TSLPRM_LINROT_DETECT_OUT_TH;
  THIS_CALIB_TH     = TSLPRM_LINROT_CALIB_TH;

  // Debounce counters
  THIS_COUNTER_DEB_CALIB   = TSLPRM_DEBOUNCE_CALIB;
#if TSLPRM_USE_PROX > 0
  THIS_COUNTER_DEB_PROX    = TSLPRM_DEBOUNCE_PROX;
#endif
  THIS_COUNTER_DEB_DETECT  = TSLPRM_DEBOUNCE_DETECT;
  THIS_COUNTER_DEB_RELEASE = TSLPRM_DEBOUNCE_RELEASE;
  THIS_COUNTER_DEB_ERROR   = TSLPRM_DEBOUNCE_ERROR;

  // Other parameters for linear/rotary only
  THIS_RESOLUTION            = TSLPRM_LINROT_RESOLUTION;
  THIS_DIR_CHG_POS           = TSLPRM_LINROT_DIR_CHG_POS;
  THIS_COUNTER_DEB_DIRECTION = TSLPRM_LINROT_DIR_CHG_DEB;

  // Initial state
  TSL_linrot_SetStateCalibration(TSLPRM_CALIB_DELAY);
}


/**
  * @brief  Process the State Machine
  * @param  None
  * @retval None
  */
void TSL_linrot_Process(void)
{
  TSL_StateId_enum_T prev_state_id;

  // Check if at least one channel has a data ready
  if ((TSL_linrot_ProcessCh_One_DataReady() == TSL_STATUS_OK) || (THIS_STATEID == TSL_STATEID_OFF))
  {

    prev_state_id = THIS_STATEID;

#if TSLPRM_TOTAL_LINROTS > 0
    if ((TSL_Globals.This_Obj->Type == TSL_OBJ_LINEAR) ||
        (TSL_Globals.This_Obj->Type == TSL_OBJ_ROTARY))
    {
      // Launch the object state function
      TSL_Globals.This_LinRot->p_SM[THIS_STATEID].StateFunc();
    }
#endif

#if TSLPRM_TOTAL_LINROTS_B > 0
    if ((TSL_Globals.This_Obj->Type == TSL_OBJ_LINEARB) ||
        (TSL_Globals.This_Obj->Type == TSL_OBJ_ROTARYB))
    {
      // Launch the TSL_Params state function
      TSL_Params.p_LinRotSM[THIS_STATEID].StateFunc();
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


/**
  * @brief  Calculate the position
  * @param  None
  * @retval Status Return OK if position calculation is correct
  * @note   The position is calculated only if the number of channels is greater than 2
  */
TSL_Status_enum_T TSL_linrot_CalcPos(void)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  TSL_tDelta_T norm_delta;
  static TSL_tDelta_T delta1, delta2, delta3;
  static TSL_tIndex_T index1, index2;
  TSL_tNb_T minor, major;
  TSL_tNb_T sector_computation = 0;
  TSL_tsignPosition_T new_position = 0;
  TSL_tPosition_T u_new_position = 0;
  TSL_tPosition_T position_correction = 0;

  delta1 = 0;
  delta2 = 0;
  delta3 = 0;

  index1 = 0;
  index2 = 0;

  // The position change flag will be set only if a new position is detected.
  THIS_POSCHANGE = TSL_STATE_NOT_CHANGED;

  // The position is calculated only if the number of channels is greater than 2
  if (THIS_NB_CHANNELS < 3)
  {
    return TSL_STATUS_ERROR;
  }

  //--------------------------------------------------------------------------
  // Sort the channels' delta
  //   - delta1 and index1 = biggest
  //   - delta2 and index2 = middle
  //   - delta3 and index3 = lowest
  //--------------------------------------------------------------------------
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {

#if TSLPRM_LINROT_USE_NORMDELTA > 0
    norm_delta = TSL_linrot_NormDelta(p_Ch, idx); // Normalize the Delta
#else
    norm_delta = p_Ch->Delta; // Take only the Delta
#endif

    // The Delta must be positive only otherwise it is noise
    if (norm_delta < 0) {norm_delta = 0;}

    if (norm_delta > delta1)
    {
      delta3 = delta2;
      delta2 = delta1;
      delta1 = norm_delta;
      index2 = index1;
      index1 = idx;
    }
    else
    {
      if (norm_delta > delta2)
      {
        delta3 = delta2;
        delta2 = norm_delta;
        index2 = idx;
      }
      else
      {
        if (norm_delta > delta3)
        {
          delta3 = norm_delta;
        }
      }
    }

    p_Ch++; // Next channel

  } // for all channels

  // Noise filter: we need at least two significant Delta measurements
  if (delta2 < ((TSL_tThreshold_T)(THIS_DETECTOUT_TH >> 1) - 1))
  {
    return TSL_STATUS_ERROR;
  }

  //----------------------------------------------------------------------------
  // Position calculation...
  //----------------------------------------------------------------------------

  /*----------------------------------------------------------------------------
    B = Biggest signal measured (Delta1/Index1)
    M = Middle signal measured (Delta2/Index2)
    S = Smallest signal measured (Delta3/Index3)
    
    - The equation to find the position is:
      Position = Offset +/- [ Sector_Size x ( Major / (Major + Minor) ) ]
   
    - The Offset is the position of the middle of the Middle signal segment.
      All the Offset values are stored in the ROM table Table_POSITION_OFFSET.
   
    - Major = Biggest - Smallest signals
      Minor = Middle - Smallest signals
   
    - The Sector_Size depends of the number of channels used
  ----------------------------------------------------------------------------*/

  // Calculates the Major and Minor parameters
  minor = (TSL_tNb_T)(delta2 - delta3); // Middle - Smallest signals
  major = (TSL_tNb_T)(delta1 - delta3); // Biggest - Smallest signals

  // Select the offset position in the position offset constant table
  // Equal to: new_position = TABLE_POSITION_OFFSET_xCH_xxx[index1][index2];
  new_position = *(TSL_Globals.This_LinRot->p_PosOff + (index1 * THIS_NB_CHANNELS) + index2);
  sector_computation = THIS_SCT_COMP;
  position_correction = THIS_POS_CORR;

  // Calculates: [ Sector_Size x ( Major / (Major + Minor) ) ]
  sector_computation = major * sector_computation;
  sector_computation = sector_computation / (major + minor);

  // Use the sign bit from position table to define the interpretation direction.
  // The NewPosition is multiplied by 2 because the Offset stored in the ROM
  // table is divided by 2...
  if (new_position > 0) // Means Offset is > 0 in the position table
  {
    new_position = (TSL_tsignPosition_T)(new_position << 1);
    new_position += sector_computation;
  }
  else // means Offset is <= 0 in the ROM table
  {
    new_position = (TSL_tsignPosition_T)((-new_position) << 1);
    new_position -= sector_computation;
  }

  // Position is calculated differently if LINEAR or ROTARY sensor
  if ((THIS_OBJ_TYPE == TSL_OBJ_LINEAR) || (THIS_OBJ_TYPE == TSL_OBJ_LINEARB))
  {

    // First adjustment used to shift all the values to obtain the "zero"
    if (new_position > 0)
    {
      new_position -= position_correction;
    }
    else
    {
      new_position = new_position + (256 - position_correction);
    }

    // Second adjustment used to clamp the values at both ends of sensor
    if (new_position < 0)
    {
      new_position = 0;
    }

    if (new_position > 255)
    {
      new_position = 255;
    }

  }
  else // ROTARY sensor: keep only the low byte
  {
    new_position = (TSL_tPosition_T)new_position;
  }

  //----------------------------------------------------------------------------
  // Direction Change Process
  //----------------------------------------------------------------------------

  if (THIS_DIRECTION == TSL_TRUE) // Anticlockwise direction ...
  {

    // Check Direction changed and Position overflow from 0x00 to 0xFF not realized !
    if (((TSL_tPosition_T)new_position > THIS_RAW_POSITION) && (((TSL_tPosition_T)new_position - THIS_RAW_POSITION) < DIRECTION_CHANGE_MAX_DISPLACEMENT))
    {
      if (new_position < (uint16_t)(THIS_RAW_POSITION + THIS_DIR_CHG_POS))
      {
        THIS_COUNTER2 = THIS_COUNTER_DEB_DIRECTION;
        return TSL_STATUS_ERROR;
      }
      else
      {
        THIS_COUNTER2--;
        if (!THIS_COUNTER2)
        {
          THIS_COUNTER2 = THIS_COUNTER_DEB_DIRECTION;
          THIS_DIRECTION = TSL_FALSE;  // New direction accepted: clockwise.
        }
        else
        {
          return TSL_STATUS_ERROR;
        }
      }
    }

    // Check position overflow from 0xFF to 0x00 to be filtered !
    if ((new_position + DIRECTION_CHANGE_MAX_DISPLACEMENT) < THIS_RAW_POSITION)
    {
      if ((new_position + DIRECTION_CHANGE_TOTAL_STEPS) < (uint16_t)(THIS_RAW_POSITION + THIS_DIR_CHG_POS))
      {
        THIS_COUNTER2 = THIS_COUNTER_DEB_DIRECTION;
        return TSL_STATUS_ERROR;
      }
      else
      {
        THIS_COUNTER2--;
        if (!THIS_COUNTER2)
        {
          THIS_COUNTER2 = THIS_COUNTER_DEB_DIRECTION;
          THIS_DIRECTION = TSL_FALSE;  // New direction accepted: clockwise.
        }
        else
        {
          return TSL_STATUS_ERROR;
        }
      }
    }

  }
  else // Clockwise direction... DEFAULT SETTING !
  {

    // Check Direction changed and Position overflow from 0xFF to 0x00 not realized !
    if (((TSL_tPosition_T)new_position < THIS_RAW_POSITION) && ((THIS_RAW_POSITION - (TSL_tPosition_T)new_position) < DIRECTION_CHANGE_MAX_DISPLACEMENT))
    {
      if ((new_position + THIS_DIR_CHG_POS) > THIS_RAW_POSITION)
      {
        THIS_COUNTER2 = THIS_COUNTER_DEB_DIRECTION;
        return TSL_STATUS_ERROR;
      }
      else
      {
        THIS_COUNTER2--;
        if (!THIS_COUNTER2)
        {
          THIS_COUNTER2 = THIS_COUNTER_DEB_DIRECTION;
          THIS_DIRECTION = TSL_TRUE;  // New direction accepted: anticlockwise.
        }
        else
        {
          return TSL_STATUS_ERROR;
        }
      }
    }

    // Check position overflow from 0x00 to 0xFF to be filtered !
    if (new_position > (uint16_t)(THIS_RAW_POSITION + DIRECTION_CHANGE_MAX_DISPLACEMENT))
    {
      if ((new_position + THIS_DIR_CHG_POS) > (uint16_t)(THIS_RAW_POSITION + DIRECTION_CHANGE_TOTAL_STEPS))
      {
        THIS_COUNTER2 = THIS_COUNTER_DEB_DIRECTION;
        return TSL_STATUS_ERROR;
      }
      else
      {
        THIS_COUNTER2--;
        if (!THIS_COUNTER2)
        {
          THIS_COUNTER2 = THIS_COUNTER_DEB_DIRECTION;
          THIS_DIRECTION = TSL_TRUE;  // New direction accepted: anticlockwise.
        }
        else
        {
          return TSL_STATUS_ERROR;
        }
      }
    }

  }

  //----------------------------------------------------------------------------
  // Final result...
  //----------------------------------------------------------------------------

  // The Raw Position is always updated
  // The Position is updated only if different from the previous one

  THIS_RAW_POSITION = (TSL_tPosition_T)new_position;

  u_new_position = (TSL_tPosition_T)((TSL_tPosition_T)new_position >> (RESOLUTION_CALCULATION - THIS_RESOLUTION));

  if (THIS_POSITION == u_new_position)
  {
    return TSL_STATUS_ERROR;
  }
  else
  {
    THIS_POSITION = u_new_position;
    THIS_POSCHANGE = TSL_STATE_CHANGED;
    return TSL_STATUS_OK;
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
void TSL_linrot_SetStateCalibration(TSL_tCounter_T delay)
{
  THIS_STATEID = TSL_STATEID_CALIB;
  THIS_CHANGE = TSL_STATE_CHANGED;
  TSL_linrot_ProcessCh_All_SetStatus(TSL_OBJ_STATUS_ON);

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
  TSL_linrot_ProcessCh_All_ClearRef();
}


/**
  * @brief  Go in Off state with sensor "off"
  * @param  None
  * @retval None
  */
void TSL_linrot_SetStateOff(void)
{
  THIS_STATEID = TSL_STATEID_OFF;
  THIS_CHANGE = TSL_STATE_CHANGED;
  TSL_linrot_ProcessCh_All_SetStatus(TSL_OBJ_STATUS_OFF);
}


#if !defined(TSLPRM_STM8TL5X) && !defined(STM8TL5X)
/**
  * @brief  Go in Off state with sensor in "Burst mode only"
  * @param  None
  * @retval None
  */
void TSL_linrot_SetStateBurstOnly(void)
{
  THIS_STATEID = TSL_STATEID_OFF;
  THIS_CHANGE = TSL_STATE_CHANGED;
  TSL_linrot_ProcessCh_All_SetStatus(TSL_OBJ_STATUS_BURST_ONLY);
}
#endif


/**
  * @brief  Return the current state identifier
  * @param  None
  * @retval State id
  */
TSL_StateId_enum_T TSL_linrot_GetStateId(void)
{
  return(THIS_STATEID);
}


/**
  * @brief  Return the current state mask
  * @param  None
  * @retval State mask
  */
TSL_StateMask_enum_T TSL_linrot_GetStateMask(void)
{
  TSL_StateMask_enum_T state_mask = TSL_STATEMASK_UNKNOWN;

#if TSLPRM_TOTAL_LINROTS > 0
  if ((TSL_Globals.This_Obj->Type == TSL_OBJ_LINEAR) ||
      (TSL_Globals.This_Obj->Type == TSL_OBJ_ROTARY))
  {
    state_mask = TSL_Globals.This_LinRot->p_SM[THIS_STATEID].StateMask;
  }
#endif

#if TSLPRM_TOTAL_LINROTS_B > 0
  if ((TSL_Globals.This_Obj->Type == TSL_OBJ_LINEARB) ||
      (TSL_Globals.This_Obj->Type == TSL_OBJ_ROTARYB))
  {
    state_mask = TSL_Params.p_LinRotSM[THIS_STATEID].StateMask;
  }
#endif

  return state_mask;
}


/**
  * @brief  Return the Change flag
  * @param  None
  * @retval Change flag status
  */
TSL_tNb_T TSL_linrot_IsChanged(void)
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
void TSL_linrot_DebReleaseProxStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_PROX; // Go back to the previous state
  }
  else // Acquisition is OK or has NOISE
  {
    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_PROXOUT_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_DebReleaseDetectStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_DETECT; // Go back to the previous state
  }
  else // Acquisition is OK or has NOISE
  {
    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_DETECTOUT_TH, 1) == TSL_STATUS_OK)
    {
      THIS_STATEID = TSL_STATEID_DETECT;
    }
    else
    {
#if TSLPRM_USE_PROX > 0
      if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_PROXOUT_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_DebReleaseTouchStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_TOUCH; // Go back to the previous state
  }
  else // Acquisition is OK or has NOISE
  {
    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_DETECTOUT_TH, 1) == TSL_STATUS_OK)
    {
      THIS_STATEID = TSL_STATEID_TOUCH;
    }
    else
    {
#if TSLPRM_USE_PROX > 0
      if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_PROXOUT_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_ReleaseStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
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
    if (TSL_linrot_ProcessCh_One_DeltaAboveEqu(THIS_DETECTIN_TH, 1) == TSL_STATUS_OK)
    {
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
    if (TSL_linrot_ProcessCh_One_DeltaAboveEqu(THIS_PROXIN_TH, 0) == TSL_STATUS_OK)
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
    if (TSL_linrot_ProcessCh_One_DeltaBelowEquMinus(THIS_CALIB_TH) == TSL_STATUS_OK)
    {
      THIS_COUNTER = THIS_COUNTER_DEB_CALIB;
      if (THIS_COUNTER == 0)
      {
        TSL_linrot_SetStateCalibration(0);
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
void TSL_linrot_DebCalibrationStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_RELEASE; // Go back to the previous state
  }
  else // Acquisition is OK or has NOISE
  {
    if (TSL_linrot_ProcessCh_One_DeltaBelowEquMinus(THIS_CALIB_TH) == TSL_STATUS_OK) // Still below recalibration threshold
    {
      if (THIS_COUNTER > 0) {THIS_COUNTER--;}
      if (THIS_COUNTER == 0)
      {
        TSL_linrot_SetStateCalibration(0);
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
void TSL_linrot_CalibrationStateProcess(void)
{
  TSL_tMeas_T new_meas;
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch;

#if TSLPRM_CALIB_DELAY > 0
  // Noise filter stabilization time
  if (THIS_COUNTER > (TSL_tCounter_T)TSL_Params.NbCalibSamples)
  {
    THIS_COUNTER--;
    return; // Skip the sample
  }
#endif

  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
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
    // Process all channels
    p_Ch = TSL_Globals.This_LinRot->p_ChD;

    for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
    {

      // Get the new measure or Calculate it
#if TSLPRM_USE_MEAS > 0
      new_meas = p_Ch->Meas;
#else // Calculate it
      new_meas = TSL_acq_ComputeMeas(p_Ch->Ref, p_Ch->Delta);
#endif

      // Verify the first Reference value
      if (THIS_COUNTER == (TSL_tCounter_T)TSL_Params.NbCalibSamples)
      {
        if (TSL_acq_TestFirstReferenceIsValid(p_Ch, new_meas))
        {
          p_Ch->Ref = new_meas;
        }
        else
        {
          p_Ch->Ref = 0;
          return;
        }
      }
      else
      {
        // Add the measure in temporary Reference
        p_Ch->Ref += new_meas;

        // Check reference overflow
        if (p_Ch->Ref < new_meas)
        {
          p_Ch->Ref = 0; // Suppress the bad reference
          THIS_STATEID = TSL_STATEID_ERROR;
          return;
        }
      }

      p_Ch++; // Next channel
    }

    // Check that we have all the needed measurements
    if (THIS_COUNTER > 0) {THIS_COUNTER--;}
    if (THIS_COUNTER == 0)
    {
      // Process all channels
      p_Ch = TSL_Globals.This_LinRot->p_ChD;
      for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
      {
        // Divide temporary Reference by the number of samples
        p_Ch->Ref >>= CalibDiv;
        p_Ch->RefRest = 0;
        p_Ch->Delta = 0;
        p_Ch++; // Next channel
      }
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
void TSL_linrot_DebProxStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_RELEASE;
  }
  else // Acquisition is OK or has NOISE
  {
    if (TSL_linrot_ProcessCh_One_DeltaAboveEqu(THIS_DETECTIN_TH, 1) == TSL_STATUS_OK)
    {
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

    if (TSL_linrot_ProcessCh_One_DeltaAboveEqu(THIS_PROXIN_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_DebProxDetectStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_DETECT;
  }
  else // Acquisition is OK or has NOISE
  {
    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_DETECTOUT_TH, 1) == TSL_STATUS_OK)
    {
      THIS_STATEID = TSL_STATEID_DETECT;
      return;
    }

    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_PROXOUT_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_DebProxTouchStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_TOUCH;
  }
  else // Acquisition is OK or has NOISE
  {
    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_DETECTOUT_TH, 1) == TSL_STATUS_OK)
    {
      THIS_STATEID = TSL_STATEID_TOUCH;
      return;
    }

    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_PROXOUT_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_ProxStateProcess(void)
{
#if TSLPRM_DTO > 0
  TSL_tTick_sec_T tick_detected;
#endif

  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
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
    if (TSL_linrot_ProcessCh_One_DeltaAboveEqu(THIS_DETECTIN_TH, 1) == TSL_STATUS_OK)
    {
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

    if (TSL_linrot_ProcessCh_All_DeltaBelowEqu(THIS_PROXOUT_TH, 0) == TSL_STATUS_OK)
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
        TSL_linrot_SetStateCalibration(0);
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
void TSL_linrot_DebDetectStateProcess(void)
{
  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
  {
    THIS_STATEID = TSL_STATEID_RELEASE;
  }
  else // Acquisition is OK or has NOISE
  {
    if (TSL_linrot_ProcessCh_One_DeltaAboveEqu(THIS_DETECTIN_TH, 1) == TSL_STATUS_OK)
    {
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
      if (TSL_linrot_ProcessCh_One_DeltaAboveEqu(THIS_PROXIN_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_DetectStateProcess(void)
{
#if TSLPRM_DTO > 0
  TSL_Status_enum_T pos_sts;
  TSL_tTick_sec_T tick_detected;
#endif

  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
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

    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_DETECTOUT_TH, 1) == TSL_STATUS_OK)
    {
      //-------------------
      // Calculate position
      //-------------------
      if ((THIS_OBJ_TYPE == TSL_OBJ_LINEAR) || (THIS_OBJ_TYPE == TSL_OBJ_ROTARY))
      {
        // Call the specific method
#if TSLPRM_DTO > 0
        pos_sts = TSL_Globals.This_LinRot->p_Methods->CalcPosition();
#else
        TSL_Globals.This_LinRot->p_Methods->CalcPosition();
#endif
      }
      else // TSL_OBJ_LINEARB or TSL_OBJ_ROTARYB
      {
        // Call the default method
#if TSLPRM_DTO > 0
        pos_sts = TSL_Params.p_LinRotMT->CalcPosition();
#else
        TSL_Params.p_LinRotMT->CalcPosition();
#endif
      }
#if TSLPRM_DTO > 0
      //------------------------------------
      // Detection Time Out (DTO) processing
      // Only if the Position has NOT changed
      //-------------------------------------
      if (pos_sts == TSL_STATUS_OK)
      {
        DTO_GET_TIME; // Take current time
      }
      else
      {
        if ((TSL_Params.DTO > 1) && (TSL_Params.DTO < 64))
        {
          tick_detected = THIS_COUNTER; // Get the detected time previously saved
          // Enter in calibration state if the DTO duration has elapsed
          if (TSL_tim_CheckDelay_sec(TSL_Params.DTO, &tick_detected) == TSL_STATUS_OK)
          {
            TSL_linrot_SetStateCalibration(0);
          }
        }
      }
#endif
      return; // Normal operation, stay in Detect state
    }

#if TSLPRM_USE_PROX > 0
    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_PROXOUT_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_TouchStateProcess(void)
{
#if TSLPRM_DTO > 0
  TSL_Status_enum_T pos_sts;
  TSL_tTick_sec_T tick_detected;
#endif

  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
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

    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_DETECTOUT_TH, 1) == TSL_STATUS_OK)
    {
      //-------------------
      // Calculate position
      //-------------------
      if ((THIS_OBJ_TYPE == TSL_OBJ_LINEAR) || (THIS_OBJ_TYPE == TSL_OBJ_ROTARY))
      {
        // Call the specific method
#if TSLPRM_DTO > 0
        pos_sts = TSL_Globals.This_LinRot->p_Methods->CalcPosition();
#else
        TSL_Globals.This_LinRot->p_Methods->CalcPosition();
#endif
      }
      else // TSL_OBJ_LINEARB or TSL_OBJ_ROTARYB
      {
        // Call the default method
#if TSLPRM_DTO > 0
        pos_sts = TSL_Params.p_LinRotMT->CalcPosition();
#else
        TSL_Params.p_LinRotMT->CalcPosition();
#endif
      }
#if TSLPRM_DTO > 0
      //------------------------------------
      // Detection Time Out (DTO) processing
      // Only if the Position has NOT changed
      //-------------------------------------
      if (pos_sts == TSL_STATUS_OK)
      {
        DTO_GET_TIME; // Take current time
      }
      else
      {
        if ((TSL_Params.DTO > 1) && (TSL_Params.DTO < 64))
        {
          tick_detected = THIS_COUNTER; // Get the detected time previously saved
          // Enter in calibration state if the DTO duration has elapsed
          if (TSL_tim_CheckDelay_sec(TSL_Params.DTO, &tick_detected) == TSL_STATUS_OK)
          {
            TSL_linrot_SetStateCalibration(0);
          }
        }
      }
#endif
      return; // Normal operation, stay in Touch state
    }

#if TSLPRM_USE_PROX > 0
    if (TSL_linrot_ProcessCh_One_DeltaAbove(THIS_PROXOUT_TH, 0) == TSL_STATUS_OK)
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
void TSL_linrot_DebErrorStateProcess(void)
{
  volatile TSL_StateMask_enum_T mask;

  if (TSL_linrot_ProcessCh_One_AcqStatusError() == TSL_STATUS_OK) // Acquisition error (min or max)
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
    mask = TSL_linrot_GetStateMask();
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
        TSL_linrot_SetStateCalibration(0);
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
void TSL_linrot_DTOGetTime(void)
{
  disableInterrupts();
  THIS_COUNTER = (TSL_tCounter_T)TSL_Globals.Tick_sec;
  enableInterrupts();
}


/**
  * @brief  Set all channels status to ON, OFF or BURST ONLY
  * @param  sts  Channel status
  * @retval None
  */
void TSL_linrot_ProcessCh_All_SetStatus(TSL_ObjStatus_enum_T sts)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  // Init channels status
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {
    p_Ch->Flags.ObjStatus = sts;
    p_Ch++;
  }
}


/**
  * @brief  Check if at least one channel has a data ready
  * @param  None
  * @retval Status
  */
TSL_Status_enum_T TSL_linrot_ProcessCh_One_DataReady(void)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  TSL_Status_enum_T retval = TSL_STATUS_ERROR;
  // Return OK if at least one channel has a data ready
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {
    if (p_Ch->Flags.DataReady == TSL_DATA_READY)
    {
      p_Ch->Flags.DataReady = TSL_DATA_NOT_READY; // The new data is processed
      retval = TSL_STATUS_OK;
    }
    p_Ch++;
  }
  return retval;
}


/**
  * @brief  Check if all channels are equal to the status passed
  * @param  sts  Status to be checked
  * @retval Status
  */
TSL_Status_enum_T TSL_linrot_ProcessCh_All_AcqStatus(TSL_AcqStatus_enum_T sts)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  // Return OK if ALL channels have the correct acq status
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {
    if (p_Ch->Flags.AcqStatus != sts)
    {
      return TSL_STATUS_ERROR;
    }
    p_Ch++;
  }
  return TSL_STATUS_OK;
}


/**
  * @brief  Check if at least one channel is in error
  * @param  None
  * @retval Status
  */
TSL_Status_enum_T TSL_linrot_ProcessCh_One_AcqStatusError(void)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  // Return OK if at least one channel is in acquisition error min or max
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {
    if (p_Ch->Flags.AcqStatus & TSL_ACQ_STATUS_ERROR_MASK)
    {
      return TSL_STATUS_OK;
    }
    p_Ch++;
  }
  return TSL_STATUS_ERROR;
}


/**
  * @brief  Check if at least one channel is below or equal a threshold (inverted)
  * @param  th Threshold
  * @retval Status
  */
TSL_Status_enum_T TSL_linrot_ProcessCh_One_DeltaBelowEquMinus(TSL_tThreshold_T th)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  TSL_tDelta_T norm_delta;

  // Return OK if at least one channel is below or equal the threshold
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {

#if TSLPRM_LINROT_USE_NORMDELTA > 0
    norm_delta = TSL_linrot_NormDelta(p_Ch, idx); // Normalize the Delta
#else
    norm_delta = p_Ch->Delta; // Take only the Delta
#endif

    if (norm_delta <= -th) // Warning!!! The threshold is inverted
    {
      return TSL_STATUS_OK;
    }
    p_Ch++;
  }
  return TSL_STATUS_ERROR;
}


/**
  * @brief  Check if at least one channel is above or equal a threshold
  * @param  th Threshold
  * @param  coeff Enable or Disable the multiplier coefficient on threshold
  * @retval Status
  */
TSL_Status_enum_T TSL_linrot_ProcessCh_One_DeltaAboveEqu(TSL_tThreshold_T th, TSL_tIndex_T coeff)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  TSL_tDelta_T norm_delta;

#if TSLPRM_COEFF_TH > 0
  uint16_t lth;
  if (coeff)
  {
    lth = (uint16_t)((uint16_t)th << TSLPRM_COEFF_TH);
  }
  else
  {
    lth = th;
  }
#endif

  // Return OK if at least one channel is above or equal the threshold
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {

#if TSLPRM_LINROT_USE_NORMDELTA > 0
    norm_delta = TSL_linrot_NormDelta(p_Ch, idx); // Normalize the Delta
#else
    norm_delta = p_Ch->Delta; // Take only the Delta
#endif

#if TSLPRM_COEFF_TH > 0
    if (norm_delta >= lth)
#else
    if (norm_delta >= th)
#endif
    {
#if TSLPRM_COEFF_TH > 0
      if (norm_delta < 0)
      {
        p_Ch++;
        continue;
      }
#endif
      return TSL_STATUS_OK;
    }
    p_Ch++;
  }
  return TSL_STATUS_ERROR;
}


/**
  * @brief  Check if at least one channel is stricly above a threshold
  * @param  th Threshold
  * @param  coeff Enable or Disable the multiplier coefficient on threshold
  * @retval Status
  */
TSL_Status_enum_T TSL_linrot_ProcessCh_One_DeltaAbove(TSL_tThreshold_T th, TSL_tIndex_T coeff)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  TSL_tDelta_T norm_delta;

#if TSLPRM_COEFF_TH > 0
  uint16_t lth;
  if (coeff)
  {
    lth = (uint16_t)((uint16_t)th << TSLPRM_COEFF_TH);
  }
  else
  {
    lth = th;
  }
#endif

  // Return OK if at least one channel is above the threshold
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {

#if TSLPRM_LINROT_USE_NORMDELTA > 0
    norm_delta = TSL_linrot_NormDelta(p_Ch, idx); // Normalize the Delta
#else
    norm_delta = p_Ch->Delta; // Take only the Delta
#endif

#if TSLPRM_COEFF_TH > 0
    if (norm_delta > lth)
#else
    if (norm_delta > th)
#endif
    {
#if TSLPRM_COEFF_TH > 0
      if (norm_delta < 0)
      {
        p_Ch++;
        continue;
      }
#endif
      return TSL_STATUS_OK;
    }
    p_Ch++;
  }
  return TSL_STATUS_ERROR;
}


/**
  * @brief  Check if all channels are below or equal a threshold
  * @param  th Threshold
  * @param  coeff Enable or Disable the multiplier coefficient on threshold
  * @retval Status
  */
TSL_Status_enum_T TSL_linrot_ProcessCh_All_DeltaBelowEqu(TSL_tThreshold_T th, TSL_tIndex_T coeff)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  TSL_tDelta_T norm_delta;

#if TSLPRM_COEFF_TH > 0
  uint16_t lth;
  if (coeff)
  {
    lth = (uint16_t)((uint16_t)th << TSLPRM_COEFF_TH);
  }
  else
  {
    lth = th;
  }
#endif

  // Return OK if ALL channels are below or equal the threshold
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {

#if TSLPRM_LINROT_USE_NORMDELTA > 0
    norm_delta = TSL_linrot_NormDelta(p_Ch, idx); // Normalize the Delta
#else
    norm_delta = p_Ch->Delta; // Take only the Delta
#endif

#if TSLPRM_COEFF_TH > 0
    if (norm_delta > lth)
#else
    if (norm_delta > th)
#endif
    {
#if TSLPRM_COEFF_TH > 0
      if (norm_delta < 0)
      {
        p_Ch++;
        continue;
      }
#endif
      return TSL_STATUS_ERROR;
    }
    p_Ch++;
  }
  return TSL_STATUS_OK;
}


/**
  * @brief  Clear the Reference and ReferenceRest for all channels
  * @param  None
  * @retval None
  */
void TSL_linrot_ProcessCh_All_ClearRef(void)
{
  TSL_tIndex_T idx;
  TSL_ChannelData_T *p_Ch = TSL_Globals.This_LinRot->p_ChD;
  for (idx = 0; idx < THIS_NB_CHANNELS; idx++)
  {
    p_Ch->Ref = 0;
    p_Ch->RefRest = 0;
    p_Ch++;
  }
}


/**
  * @brief  Normalize a Delta value
  * @param  ch Pointer to the current channel
  * @param  idx Index of the channel
  * @retval Normalized Delta value
  */
TSL_tDelta_T TSL_linrot_NormDelta(TSL_ChannelData_T *ch, TSL_tIndex_T idx)
{
  uint32_t tmpdelta = ch->Delta;

  // Apply coefficient
  if (TSL_Globals.This_LinRot->p_DeltaCoeff[idx] != 0x0100)
  {
    tmpdelta = (uint32_t)(tmpdelta * TSL_Globals.This_LinRot->p_DeltaCoeff[idx]);
    tmpdelta = tmpdelta >> (uint8_t)8;
  }

  return (TSL_tDelta_T)tmpdelta;
}

#endif
// #if TSLPRM_TOTAL_LNRTS > 0

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
