/**
  ******************************************************************************
  * @file    tsl_dxs.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the
  *          Detection Exclusion System (DxS) algorithm.
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
#include "tsl_dxs.h"
#include "tsl_globals.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/

#define THIS_OBJ_TYPE       TSL_Globals.This_Obj->Type

#define THIS_TKEY           TSL_Globals.This_TKey
#define THIS_TKEY_STATEID   TSL_Globals.This_TKey->p_Data->StateId
#define THIS_TKEY_DXSLOCK   TSL_Globals.This_TKey->p_Data->DxSLock
#define THIS_TKEY_CHANGE    TSL_Globals.This_TKey->p_Data->Change

#define THIS_LINROT         TSL_Globals.This_LinRot
#define THIS_LINROT_STATEID TSL_Globals.This_LinRot->p_Data->StateId
#define THIS_LINROT_DXSLOCK TSL_Globals.This_LinRot->p_Data->DxSLock
#define THIS_LINROT_CHANGE  TSL_Globals.This_LinRot->p_Data->Change

/* Private macros ------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private functions prototype -----------------------------------------------*/

/**
  * @brief Detection Exclusion System on the first object in detect state
  * @param[in] objgrp  Pointer to the objects group to process
  * @retval None
  */
void TSL_dxs_FirstObj(CONST TSL_ObjectGroup_T *objgrp)
{
#if TSLPRM_USE_DXS > 0

  TSL_tIndex_T idx_obj;
  CONST TSL_Object_T *pobj;
  CONST TSL_Object_T *pobj_candidate = 0; // Candidate object for being in Detect state + DxSLock flag
  TSL_tIndex_T obj_locked = 0; // Object with Lock flag

  // Exit if no object are in DETECT state.
  if ((objgrp->StateMask & TSL_STATE_DETECT_BIT_MASK) == 0)
  {
    return;
  }

  pobj = objgrp->p_Obj; // First object in the group

  // Process all objects
  for (idx_obj = 0; idx_obj < objgrp->NbObjects; idx_obj++)
  {

    // Assign global object
    TSL_obj_SetGlobalObj(pobj);

    //--------------------------------------------------------------------------
#if TSLPRM_TOTAL_TKEYS > 0
    if ((THIS_OBJ_TYPE == TSL_OBJ_TOUCHKEY) || (THIS_OBJ_TYPE == TSL_OBJ_TOUCHKEYB))
    {
      if (THIS_TKEY_STATEID == TSL_STATEID_DETECT)
      {
        if (THIS_TKEY_DXSLOCK == TSL_TRUE)
        {
          if (!obj_locked)
          {
            obj_locked = 1;
            pobj_candidate = 0;
          }
          else
          {
            THIS_TKEY_STATEID = TSL_STATEID_TOUCH;
            THIS_TKEY_CHANGE = TSL_STATE_CHANGED;
          }
        }
        else
        {
          THIS_TKEY_STATEID = TSL_STATEID_TOUCH;
          THIS_TKEY_CHANGE = TSL_STATE_CHANGED;
          if ((!pobj_candidate) && (!obj_locked))
          {
            pobj_candidate = pobj;
          }
        }
      }
    }
#endif // TSLPRM_TOTAL_TKEYS > 0

    //--------------------------------------------------------------------------
#if TSLPRM_TOTAL_LNRTS > 0
    if ((THIS_OBJ_TYPE == TSL_OBJ_LINEAR) || (THIS_OBJ_TYPE == TSL_OBJ_LINEARB) ||
        (THIS_OBJ_TYPE == TSL_OBJ_ROTARY) || (THIS_OBJ_TYPE == TSL_OBJ_ROTARYB))
    {
      if (THIS_LINROT_STATEID == TSL_STATEID_DETECT)
      {
        if (THIS_LINROT_DXSLOCK == TSL_TRUE)
        {
          if (!obj_locked)
          {
            obj_locked = 1;
            pobj_candidate = 0;
          }
          else
          {
            THIS_LINROT_STATEID = TSL_STATEID_TOUCH;
            THIS_LINROT_CHANGE = TSL_STATE_CHANGED;
          }
        }
        else
        {
          THIS_LINROT_STATEID = TSL_STATEID_TOUCH;
          THIS_LINROT_CHANGE = TSL_STATE_CHANGED;
          if ((!pobj_candidate) && (!obj_locked))
          {
            pobj_candidate = pobj;
          }
        }
      }
    }
#endif // TSLPRM_TOTAL_LNRTS > 0

    pobj++; // Next object

  } // // for all objects

  // Change state from TOUCH to DETECT + DxSLock flag on the candidate object only
  if (pobj_candidate)
  {

    // Assign global object
    TSL_obj_SetGlobalObj(pobj_candidate);

#if TSLPRM_TOTAL_TKEYS > 0
    if ((THIS_OBJ_TYPE == TSL_OBJ_TOUCHKEY) || (THIS_OBJ_TYPE == TSL_OBJ_TOUCHKEYB))
    {
      THIS_TKEY_STATEID = TSL_STATEID_DETECT;
      THIS_TKEY_CHANGE = TSL_STATE_CHANGED;
      THIS_TKEY_DXSLOCK = TSL_TRUE;
    }
#endif // TSLPRM_TOTAL_TKEYS > 0

#if TSLPRM_TOTAL_LNRTS > 0
    if ((THIS_OBJ_TYPE == TSL_OBJ_LINEAR) || (THIS_OBJ_TYPE == TSL_OBJ_LINEARB) ||
        (THIS_OBJ_TYPE == TSL_OBJ_ROTARY) || (THIS_OBJ_TYPE == TSL_OBJ_ROTARYB))
    {
      THIS_LINROT_STATEID = TSL_STATEID_DETECT;
      THIS_LINROT_CHANGE = TSL_STATE_CHANGED;
      THIS_LINROT_DXSLOCK = TSL_TRUE;
    }
#endif // TSLPRM_TOTAL_LNRTS > 0

  }

#endif // TSLPRM_USE_DXS > 0
}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
