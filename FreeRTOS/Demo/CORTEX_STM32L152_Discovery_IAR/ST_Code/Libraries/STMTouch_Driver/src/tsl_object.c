/**
  ******************************************************************************
  * @file    tsl_object.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the sensors in general.
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
#include "tsl_object.h"
#include "tsl_globals.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/
/* Private macros ------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/

/* Private functions prototype -----------------------------------------------*/

/**
  * @brief Initialize a group of Objects
  * @param[in] objgrp  Pointer to the group of objects
  * @retval None
  */
void TSL_obj_GroupInit(TSL_ObjectGroup_T *objgrp)
{
  TSL_tIndex_T idx_obj;
  CONST TSL_Object_T *pobj;
  TSL_tNb_T objgrp_state_mask = 0;

  pobj = objgrp->p_Obj; // First object in the group

  objgrp->Change = TSL_STATE_NOT_CHANGED;

  // Process all objects
  for (idx_obj = 0; idx_obj < objgrp->NbObjects; idx_obj++)
  {

    // Assign global object
    TSL_obj_SetGlobalObj(pobj);

    switch (pobj->Type)
    {
        //------------------------------------------------------------------------
#if TSLPRM_TOTAL_TOUCHKEYS > 0
      case TSL_OBJ_TOUCHKEY:
        // Call the specific method
        TSL_Globals.This_TKey->p_Methods->Init();
        // Check if the object has changed of state
        if (TSL_Globals.This_TKey->p_Data->Change)
        {
          objgrp->Change = TSL_STATE_CHANGED;
        }
        // Update object group state mask
        objgrp_state_mask |= TSL_Globals.This_TKey->p_SM[TSL_Globals.This_TKey->p_Data->StateId].StateMask;
        break;
#endif
        //------------------------------------------------------------------------
#if TSLPRM_TOTAL_TOUCHKEYS_B > 0
      case TSL_OBJ_TOUCHKEYB:
        // Call the default method
        TSL_Params.p_TKeyMT->Init();
        // Check if the object has changed of state
        if (TSL_Globals.This_TKey->p_Data->Change)
        {
          objgrp->Change = TSL_STATE_CHANGED;
        }
        // Get object state mask from state machine in TSL_Params
        objgrp_state_mask |= TSL_Params.p_TKeySM[TSL_Globals.This_TKey->p_Data->StateId].StateMask;
        break;
#endif
        //------------------------------------------------------------------------
#if TSLPRM_TOTAL_LINROTS > 0
      case TSL_OBJ_LINEAR:
      case TSL_OBJ_ROTARY:
        // Call the specific method
        TSL_Globals.This_LinRot->p_Methods->Init();
        // Check if the object has changed of state
        if (TSL_Globals.This_LinRot->p_Data->Change)
        {
          objgrp->Change = TSL_STATE_CHANGED;
        }
        // Update object group state mask
        objgrp_state_mask |= TSL_Globals.This_LinRot->p_SM[TSL_Globals.This_LinRot->p_Data->StateId].StateMask;
        break;
#endif
        //------------------------------------------------------------------------
#if TSLPRM_TOTAL_LINROTS_B > 0
      case TSL_OBJ_LINEARB:
      case TSL_OBJ_ROTARYB:
        // Call the default method
        TSL_Params.p_LinRotMT->Init();
        // Check if the object has changed of state
        if (TSL_Globals.This_LinRot->p_Data->Change)
        {
          objgrp->Change = TSL_STATE_CHANGED;
        }
        // Get object state mask from state machine in TSL_Params
        objgrp_state_mask |= TSL_Params.p_LinRotSM[TSL_Globals.This_LinRot->p_Data->StateId].StateMask;
        break;
#endif
      default:
        break;
    }

    pobj++; // Next object
  }

  // Update the object group state mask
  objgrp->StateMask = objgrp_state_mask;
}


/**
  * @brief Process the state machine on a group of Objects
  * @param[in] objgrp  Pointer to the group of objects to process
  * @retval None
  */
void TSL_obj_GroupProcess(TSL_ObjectGroup_T *objgrp)
{
  TSL_tIndex_T idx_obj;
  CONST TSL_Object_T *pobj;
  TSL_tNb_T objgrp_state_mask = 0;

  pobj = objgrp->p_Obj; // First object in the group

  objgrp->Change = TSL_STATE_NOT_CHANGED;

  // Process all objects
  for (idx_obj = 0; idx_obj < objgrp->NbObjects; idx_obj++)
  {

    // Assign global object
    TSL_obj_SetGlobalObj(pobj);

    switch (pobj->Type)
    {
        //------------------------------------------------------------------------
#if TSLPRM_TOTAL_TOUCHKEYS > 0
      case TSL_OBJ_TOUCHKEY:
        // Call the specific method
        TSL_Globals.This_TKey->p_Methods->Process();
        // Check if the object has changed of state
        if (TSL_Globals.This_TKey->p_Data->Change)
        {
          objgrp->Change = TSL_STATE_CHANGED;
        }
        // Update object group state mask
        objgrp_state_mask |= TSL_Globals.This_TKey->p_SM[TSL_Globals.This_TKey->p_Data->StateId].StateMask;
        break;
#endif
        //------------------------------------------------------------------------
#if TSLPRM_TOTAL_TOUCHKEYS_B > 0
      case TSL_OBJ_TOUCHKEYB:
        // Call the default method
        TSL_Params.p_TKeyMT->Process();
        // Check if the object has changed of state
        if (TSL_Globals.This_TKey->p_Data->Change)
        {
          objgrp->Change = TSL_STATE_CHANGED;
        }
        // Get object state mask from state machine in TSL_Params
        objgrp_state_mask |= TSL_Params.p_TKeySM[TSL_Globals.This_TKey->p_Data->StateId].StateMask;
        break;
#endif
        //------------------------------------------------------------------------
#if TSLPRM_TOTAL_LINROTS > 0
      case TSL_OBJ_LINEAR:
      case TSL_OBJ_ROTARY:
        // Call the specific method
        TSL_Globals.This_LinRot->p_Methods->Process();
        // Check if the object has changed of state
        if (TSL_Globals.This_LinRot->p_Data->Change)
        {
          objgrp->Change = TSL_STATE_CHANGED;
        }
        // Update object group state mask
        objgrp_state_mask |= TSL_Globals.This_LinRot->p_SM[TSL_Globals.This_LinRot->p_Data->StateId].StateMask;
        break;
#endif
        //------------------------------------------------------------------------
#if TSLPRM_TOTAL_LINROTS_B > 0
      case TSL_OBJ_LINEARB:
      case TSL_OBJ_ROTARYB:
        // Call the default method
        TSL_Params.p_LinRotMT->Process();
        // Check if the object has changed of state
        if (TSL_Globals.This_LinRot->p_Data->Change)
        {
          objgrp->Change = TSL_STATE_CHANGED;
        }
        // Get object state mask from state machine in TSL_Params
        objgrp_state_mask |= TSL_Params.p_LinRotSM[TSL_Globals.This_LinRot->p_Data->StateId].StateMask;
        break;
#endif
      default:
        break;
    }

    pobj++; // Next object
  }

  // Update the object group state mask
  objgrp->StateMask = objgrp_state_mask;
}


/**
  * @brief Set the global object variable
  * @param[in] pobj  Pointer to the object to process
  * @retval None
  */
void TSL_obj_SetGlobalObj(CONST TSL_Object_T *pobj)
{

  TSL_Globals.This_Obj = pobj;

  switch (pobj->Type)
  {
#if TSLPRM_TOTAL_TKEYS > 0
    case TSL_OBJ_TOUCHKEY:
    case TSL_OBJ_TOUCHKEYB:
      TSL_Globals.This_TKey = (TSL_TouchKey_T *)pobj->Elmt;
      break;
#endif
#if TSLPRM_TOTAL_LNRTS > 0
    case TSL_OBJ_LINEAR:
    case TSL_OBJ_LINEARB:
    case TSL_OBJ_ROTARY:
    case TSL_OBJ_ROTARYB:
      TSL_Globals.This_LinRot = (TSL_LinRot_T *)pobj->Elmt;
      break;
#endif
    default:
      break;
  }
}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
