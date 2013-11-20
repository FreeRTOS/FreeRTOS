/**
  ******************************************************************************
  * @file    tsl_ecs.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the ECS.
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
#include "tsl_ecs.h"
#include "tsl_globals.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/

#define THIS_OBJ_TYPE      TSL_Globals.This_Obj->Type
#define THIS_TKEY_REF      TSL_Globals.This_TKey->p_ChD->Ref
#define THIS_TKEY_REFREST  TSL_Globals.This_TKey->p_ChD->RefRest
#define THIS_TKEY_DELTA    TSL_Globals.This_TKey->p_ChD->Delta
#define THIS_TKEY_STATEID  TSL_Globals.This_TKey->p_Data->StateId

#define THIS_LINROT_STATEID      TSL_Globals.This_LinRot->p_Data->StateId
#define THIS_LINROT_NB_CHANNELS  TSL_Globals.This_LinRot->NbChannels

/* Private macros ------------------------------------------------------------*/
#define IS_K_COEFF_OK(COEFF)            (((COEFF) == 0) || (((COEFF) > 0) && ((COEFF) < 256)))
#define IS_POINTER_INITIALIZED(POINTER) ((POINTER) != 0)

/* Private variables ---------------------------------------------------------*/
/* Private functions prototype -----------------------------------------------*/

/**
  * @brief Calculate the K coefficient
  * @param[in] objgrp Pointer to the objects group to process
  * @param[in] k_slow  K coefficient when objects have different delta variation
  * @param[in] k_fast  K coefficient when objects have the same delta variation
  * @retval    K coefficient (slow or fast)
  */
TSL_tKCoeff_T TSL_ecs_CalcK(CONST TSL_ObjectGroup_T *objgrp, TSL_tKCoeff_T k_slow, TSL_tKCoeff_T k_fast)
{
  TSL_tIndex_T idx_obj; // Index of current object
  TSL_tIndex_T idx_ch; // Index of current channel
  TSL_tDelta_T ldelta = 0; // Temporary delta
  TSL_tDelta_T ECS_Fast_Enable = 1;
  TSL_tDelta_T ECS_Fast_Direction = 0;
  CONST TSL_Object_T *pobj;
  TSL_tKCoeff_T retval = k_slow;
  TSL_tNb_T nb_channels = 0; // Number of channels inside current object
  TSL_ChannelData_T *p_Ch = 0;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_K_COEFF_OK(k_slow));
  assert_param(IS_K_COEFF_OK(k_fast));

  pobj = objgrp->p_Obj; // First object in the group

  // Process all objects
  for (idx_obj = 0; idx_obj < objgrp->NbObjects; idx_obj++)
  {

    // Assign global object
    TSL_obj_SetGlobalObj(pobj);

#if TSLPRM_TOTAL_TKEYS > 0
    if ((THIS_OBJ_TYPE == TSL_OBJ_TOUCHKEY) || (THIS_OBJ_TYPE == TSL_OBJ_TOUCHKEYB))
    {
      // Ignore object if not in Release state
      if (THIS_TKEY_STATEID != TSL_STATEID_RELEASE)
      {
        continue; // Take next object
      }
      nb_channels = 1;
      p_Ch = TSL_Globals.This_TKey->p_ChD;
    }
#endif

#if TSLPRM_TOTAL_LNRTS > 0
    if ((THIS_OBJ_TYPE == TSL_OBJ_LINEAR) || (THIS_OBJ_TYPE == TSL_OBJ_LINEARB) ||
        (THIS_OBJ_TYPE == TSL_OBJ_ROTARY) || (THIS_OBJ_TYPE == TSL_OBJ_ROTARYB))
    {
      // Ignore object if not in Release state
      if (THIS_LINROT_STATEID != TSL_STATEID_RELEASE)
      {
        continue; // Take next object
      }
      nb_channels = THIS_LINROT_NB_CHANNELS;
      p_Ch = TSL_Globals.This_LinRot->p_ChD;
    }
#endif

    // Check channel pointer variable (if USE_FULL_ASSERT is defined)
    assert_param(IS_POINTER_INITIALIZED(p_Ch));

    // Check all channels of current object
    for (idx_ch = 0; idx_ch < nb_channels; idx_ch++)
    {

      ldelta = p_Ch->Delta;

      // Check delta
      if (ldelta == 0) // No Fast ECS !
      {
        ECS_Fast_Enable = 0;
      }
      else
      {
        if (ldelta < 0)
        {
          if (ECS_Fast_Direction > 0) // No Fast ECS !
          {
            ECS_Fast_Enable = 0;
          }
          else
          {
            ECS_Fast_Direction = -1;
          }
        }
        else
        {
          if (ECS_Fast_Direction < 0) // No Fast ECS !
          {
            ECS_Fast_Enable = 0;
          }
          else
          {
            ECS_Fast_Direction = 1;
          }
        }
      }

      p_Ch++; // Next channel

    } // for all channels of current object

    pobj++; // Next object

  } // for all objects

  // Assign K fast following Delta variations
  if (ECS_Fast_Enable)
  {
    retval = k_fast;
  }

  return retval;
}


/**
  * @brief Calculate the new Reference on a group of objects
  * @param[in] objgrp Pointer to the objects group to process
  * @param[in] Kcoeff K coefficient to apply
  * @retval None
  */
void TSL_ecs_ProcessK(CONST TSL_ObjectGroup_T *objgrp, TSL_tKCoeff_T Kcoeff)
{
  TSL_tIndex_T idx_obj; // Index of current object
  TSL_tIndex_T idx_ch; // Index of current channel
  CONST TSL_Object_T *pobj;
  TSL_tKCoeff_T Kcoeff_comp;
  uint32_t ECS_meas;
  uint32_t ECS_ref;
  TSL_tNb_T nb_channels = 0; // Number of channels inside current object
  TSL_ChannelData_T *p_Ch = 0;
  void(*pFunc_SetStateCalibration)(TSL_tCounter_T delay) = 0;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_K_COEFF_OK(Kcoeff));

  pobj = objgrp->p_Obj; // First object in the group

  // Calculate the K coefficient complement
  Kcoeff_comp = (0xFF ^ Kcoeff) + 1;

  // Process all objects
  for (idx_obj = 0; idx_obj < objgrp->NbObjects; idx_obj++)
  {

    // Assign global object
    TSL_obj_SetGlobalObj(pobj);

#if TSLPRM_TOTAL_TKEYS > 0
    if ((THIS_OBJ_TYPE == TSL_OBJ_TOUCHKEY) || (THIS_OBJ_TYPE == TSL_OBJ_TOUCHKEYB))
    {
      // Ignore object if not in Release state
      if (THIS_TKEY_STATEID != TSL_STATEID_RELEASE)
      {
        continue; // Take next object
      }
      nb_channels = 1;
      p_Ch = TSL_Globals.This_TKey->p_ChD;
      pFunc_SetStateCalibration = &TSL_tkey_SetStateCalibration;
    }
#endif

#if TSLPRM_TOTAL_LNRTS > 0
    if ((THIS_OBJ_TYPE == TSL_OBJ_LINEAR) || (THIS_OBJ_TYPE == TSL_OBJ_LINEARB) ||
        (THIS_OBJ_TYPE == TSL_OBJ_ROTARY) || (THIS_OBJ_TYPE == TSL_OBJ_ROTARYB))
    {
      // Ignore object if not in Release state
      if (THIS_LINROT_STATEID != TSL_STATEID_RELEASE)
      {
        continue; // Take next object
      }
      nb_channels = THIS_LINROT_NB_CHANNELS;
      p_Ch = TSL_Globals.This_LinRot->p_ChD;
      pFunc_SetStateCalibration = &TSL_linrot_SetStateCalibration;
    }
#endif

    // Check channel pointer variable (if USE_FULL_ASSERT is defined)
    assert_param(IS_POINTER_INITIALIZED(p_Ch));

    // Calculate the new reference + rest for all channels
    for (idx_ch = 0; idx_ch < nb_channels; idx_ch++)
    {
      ECS_meas = TSL_acq_ComputeMeas(p_Ch->Ref, p_Ch->Delta);
      ECS_meas <<= 8;

      ECS_ref = (uint32_t)(p_Ch->Ref);
      ECS_ref <<= 8;
      ECS_ref += p_Ch->RefRest;
      ECS_ref *= Kcoeff_comp;
      ECS_ref += (Kcoeff * ECS_meas);

      p_Ch->RefRest = (TSL_tRefRest_T)((ECS_ref >> 8) & 0xFF);
      p_Ch->Ref = (TSL_tRef_T)(ECS_ref >> 16);

      // Go in Calibration state in the Reference is out of Range
      if (TSL_acq_TestReferenceOutOfRange(p_Ch) == TSL_TRUE)
      {
        pFunc_SetStateCalibration(0);
      }

      p_Ch++; // Next channel
    }

    pobj++; // Next object

  } // for all objects

}


/**
  * @brief ECS algorithm on a group of objects
  * The ECS is only performed if at least an object is in Release state and
  * if no objects are in active states (Prox, Detect or Touch)
  * An optional delay is added after the ECS condition (all sensors in Release state) is reached.
  * @param[in] objgrp Pointer to the objects group to process
  * @retval Status
  */
TSL_Status_enum_T TSL_ecs_Process(CONST TSL_ObjectGroup_T *objgrp)
{
  TSL_tKCoeff_T MyKcoeff;
  TSL_Status_enum_T retval;
  static TSL_tIndex_T exec = 0;
#if TSLPRM_ECS_DELAY > 0
  static TSL_tIndex_T wait = 0;
  static TSL_tTick_ms_T start_time;
#endif

  if ((objgrp->StateMask & TSL_STATE_RELEASE_BIT_MASK) && !(objgrp->StateMask & TSL_STATEMASK_ACTIVE))
  {
#if TSLPRM_ECS_DELAY > 0
    if (!wait)
    {
      disableInterrupts();
      start_time = TSL_Globals.Tick_ms; // Save the current time
      enableInterrupts();
      wait = 1;
      exec = 0;
    }
#else
    exec = 1;
#endif
  }
  else
  {
#if TSLPRM_ECS_DELAY > 0
    wait = 0;
#endif
    exec = 0;
  }

#if TSLPRM_ECS_DELAY > 0
  if ((wait) && (!exec))
  {
    // Execute the ECS only when the delay has elapsed
    if (TSL_tim_CheckDelay_ms(TSLPRM_ECS_DELAY, &start_time) == TSL_STATUS_OK)
    {
      exec = 1;
    }
  }
#endif

  if (exec)
  {
    // Calculate the K coefficient
    MyKcoeff = TSL_ecs_CalcK(objgrp, TSLPRM_ECS_K_SLOW, TSLPRM_ECS_K_FAST);
    // Process the objects
    TSL_ecs_ProcessK(objgrp, MyKcoeff);
    retval = TSL_STATUS_OK;
  }
  else
  {
    retval = TSL_STATUS_BUSY;
  }

  return retval;
}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
