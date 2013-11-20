/**
  ******************************************************************************
  * @file    tsl_acq.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the acquisition in general.
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
#include "tsl_acq.h"
#include "tsl_globals.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/

/* Private macros ------------------------------------------------------------*/
#define IS_BANK_INDEX_OK(INDEX)  (((INDEX) == 0) || (((INDEX) > 0) && ((INDEX) < TSLPRM_TOTAL_BANKS)))

/* Private variables ---------------------------------------------------------*/
/* Private functions prototype -----------------------------------------------*/

/**
  * @brief Read all channels measurement of a Bank, calculate Delta
  * @param[in]  idx_bk  Index of the Bank to access
  * @param[in]  mfilter Pointer to the Measure filter function
  * @param[in]  dfilter Pointer to the Delta filter function
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_BankGetResult(TSL_tIndex_T idx_bk, TSL_pFuncMeasFilter_T mfilter, TSL_pFuncDeltaFilter_T dfilter)
{
  TSL_Status_enum_T retval = TSL_STATUS_OK;
  TSL_tIndex_T idx_ch;
  TSL_tIndexDest_T idx_dest;
  TSL_tMeas_T old_meas, new_meas;
  TSL_tDelta_T new_delta;
  CONST TSL_Bank_T *bank = &(TSL_Globals.Bank_Array[idx_bk]);
  CONST TSL_ChannelDest_T *pchDest = bank->p_chDest;
  CONST TSL_ChannelSrc_T *pchSrc = bank->p_chSrc;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));

  // For all channels in the bank copy the measure + calculate delta and store them.
  for (idx_ch = 0; idx_ch < bank->NbChannels; idx_ch++)
  {

    // Get the Destination Index of the current channel
    idx_dest = pchDest->IdxDest;

    if (bank->p_chData[idx_dest].Flags.ObjStatus == TSL_OBJ_STATUS_ON)
    {

      // Initialize flag to inform the Object of that a new data is ready
      bank->p_chData[idx_dest].Flags.DataReady = TSL_DATA_READY;

      // Get the new measure (the access is different between acquisitions)
      new_meas = TSL_acq_GetMeas(pchSrc->IdxSrc);

      // Store last measure for the filter below
#if TSLPRM_USE_MEAS > 0
      old_meas = bank->p_chData[idx_dest].Meas;
#else
      old_meas = new_meas;
#endif

      // Store the new measure
#if TSLPRM_USE_MEAS > 0
      bank->p_chData[idx_dest].Meas = new_meas;
#endif

      // Check acquisition value min/max and set acquisition status flag
      if (new_meas < TSL_Params.AcqMin)
      {
        bank->p_chData[idx_dest].Flags.AcqStatus = TSL_ACQ_STATUS_ERROR_MIN;
        bank->p_chData[idx_dest].Delta = 0;
        retval = TSL_STATUS_ERROR;
      }
      else
      {
        if (new_meas > TSL_Params.AcqMax)
        {
          bank->p_chData[idx_dest].Flags.AcqStatus = TSL_ACQ_STATUS_ERROR_MAX;
          bank->p_chData[idx_dest].Delta = 0;
          retval = TSL_STATUS_ERROR;
        }
        else // The measure is OK
        {
          if (TSL_acq_UseFilter(&bank->p_chData[idx_dest]))
          {
            // Apply Measure filter if it exists
            if (mfilter)
            {
              new_meas = mfilter(old_meas, new_meas);
              // Store the measure (optional - used for debug purpose)
#if TSLPRM_USE_MEAS > 0
              bank->p_chData[idx_dest].Meas = new_meas;
#endif
            }

            // Calculate the new Delta
            new_delta = TSL_acq_ComputeDelta(bank->p_chData[idx_dest].Ref, new_meas);

            // Check Noise (TSL_ACQ_STATUS_OK if no Noise or if Noise detection is not supported)
            bank->p_chData[idx_dest].Flags.AcqStatus = TSL_acq_CheckNoise();

            // Apply Delta filter if it exists
            if (dfilter)
            {
              bank->p_chData[idx_dest].Delta = dfilter(new_delta);
            }
            else
            {
              bank->p_chData[idx_dest].Delta = new_delta;
            }
          }
          else
          {
            // Calculate the new Delta
            bank->p_chData[idx_dest].Delta = TSL_acq_ComputeDelta(bank->p_chData[idx_dest].Ref, new_meas);

            // Check Noise (TSL_ACQ_STATUS_OK if no Noise or if Noise detection is not supported)
            bank->p_chData[idx_dest].Flags.AcqStatus = TSL_acq_CheckNoise();
          }
        }
      }
    }

    // Next channel
    pchDest++;
    pchSrc++;

  }

  return retval;
}


/**
  * @brief Calibrate a Bank
  * @param[in] idx_bk  Index of the Bank to access
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_BankCalibrate(TSL_tIndex_T idx_bk)
{
  TSL_Status_enum_T retval;
  TSL_Status_enum_T acq_status;
  TSL_tIndex_T idx_ch;
  TSL_tIndexDest_T idx_dest;
  TSL_tMeas_T new_meas;
  static TSL_tIndex_T calibration_ongoing = 0;
  static TSL_tNb_T calibration_done = 0;
  static TSL_tNb_T div;
  CONST TSL_Bank_T *bank;
  CONST  TSL_ChannelDest_T *pchDest; // Pointer to the current channel
  CONST TSL_ChannelSrc_T *pchSrc; // Pointer to the current channel

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));

  bank = &(TSL_Globals.Bank_Array[idx_bk]);

  if (calibration_ongoing == 0)
  {
    switch (TSL_Params.NbCalibSamples)
    {
      case 4:
        div = 2;
        break;
      case 16:
        div = 4;
        break;
      default:
        TSL_Params.NbCalibSamples =  8;
        div = 3;
        break;
    }
    // Clear data for all channels of the bank
    TSL_acq_BankClearData(idx_bk);
    // Configure bank
    if (TSL_acq_BankConfig(idx_bk) == TSL_STATUS_OK)
    {
      // Start acquisition
      TSL_acq_BankStartAcq();
      calibration_ongoing = 1; // Calibration started
      calibration_done = TSL_Params.NbCalibSamples;
      retval = TSL_STATUS_BUSY;
    }
    else
    {
      // Stop calibration
      // Clear data for all channels of the bank
      TSL_acq_BankClearData(idx_bk);
      calibration_ongoing = 0;
      retval = TSL_STATUS_ERROR;
    }

  }
  else // Calibration is on-going
  {
    // Check End of Acquisition
    acq_status = TSL_acq_BankWaitEOC();
    if (acq_status == TSL_STATUS_OK)
    {

      // Get the first channel of the bank
      pchDest = bank->p_chDest;
      pchSrc = bank->p_chSrc;

      // Get new measurement for all channels of the bank
      for (idx_ch = 0; idx_ch < bank->NbChannels; idx_ch++)
      {

        // Get index of the current channel
        idx_dest = pchDest->IdxDest;

        // Get the new measure (the access is different between acquisitions)
        new_meas = TSL_acq_GetMeas(pchSrc->IdxSrc);

        // Check min/max and set status flag
        if ((new_meas < TSL_Params.AcqMin) || (new_meas > TSL_Params.AcqMax))
        {
          // Stop calibration
          // Clear data for all channels of the bank
          TSL_acq_BankClearData(idx_bk);
          calibration_ongoing = 0;
          return TSL_STATUS_ERROR;
        }
        else
        {
          // Add the measure
          bank->p_chData[idx_dest].Ref += new_meas;
        }

        // Next channel
        pchDest++;
        pchSrc++;
      }

      // Check that we have all the needed measurements
      calibration_done--;
      if (calibration_done == 0)
      {

        // Get the first channel of the bank
        pchDest = bank->p_chDest;

        // Calculate the Reference for all channels of the bank
        for (idx_ch = 0; idx_ch < bank->NbChannels; idx_ch++)
        {
          // Get index of the current channel
          idx_dest = pchDest->IdxDest;
          // Divide the Reference by the number of samples
          bank->p_chData[idx_dest].Ref >>= div;
          // Next channel
          pchDest++;
        }

        // End
        calibration_ongoing = 0;
        retval = TSL_STATUS_OK;
      }
      else // Restart a new measurement on the bank
      {
        TSL_acq_BankStartAcq();
        retval = TSL_STATUS_BUSY;
      }
    }
    else
      if (acq_status == TSL_STATUS_ERROR)
      {
        // Stop calibration
        // Clear data for all channels of the bank
        TSL_acq_BankClearData(idx_bk);
        calibration_ongoing = 0;
        retval = TSL_STATUS_ERROR;
      }
      else
      {
        retval = TSL_STATUS_BUSY;
      }
  }

  return retval;
}


/**
  * @brief Clear Reference and Delta on all channels of a Bank
  * @param[in] idx_bk  Index of the Bank to access
  * @retval None
  */
void TSL_acq_BankClearData(TSL_tIndex_T idx_bk)
{
  TSL_tIndex_T idx_ch;
  TSL_tIndexDest_T idx_Dest;
  CONST TSL_Bank_T *bank = &(TSL_Globals.Bank_Array[idx_bk]);
  CONST TSL_ChannelDest_T *pchDest = bank->p_chDest;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));

  // For all channels of the bank
  for (idx_ch = 0; idx_ch < bank->NbChannels; idx_ch++)
  {
    idx_Dest = pchDest->IdxDest;
    bank->p_chData[idx_Dest].Ref = 0;
    bank->p_chData[idx_Dest].Delta = 0;
    pchDest++; // Next channel
  }
}


#if TSLPRM_USE_ZONE > 0

/**
  * @brief Configures a Zone.
  * @param[in] zone  Zone to configure
  * @param[in] idx_bk  Bank index in the zone to configure
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_ZoneConfig(CONST TSL_Zone_T *zone, TSL_tIndex_T idx_bk)
{
  TSL_Status_enum_T retval;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));

  TSL_Globals.This_Zone = zone;

  do
  {
    retval = TSL_acq_BankConfig(zone->BankIndex[idx_bk]);
    TSL_Globals.This_Bank = zone->BankIndex[idx_bk];
    idx_bk++;
  }
  while ((idx_bk < zone->NbBanks) && (retval == TSL_STATUS_ERROR));

  TSL_Globals.Index_In_This_Zone = idx_bk;

#if TSLPRM_PXS_LOW_POWER_MODE > 0
  if (idx_bk < zone->NbBanks)
  {
    resetPXSLowPower();
  }
#endif

  return(retval);

}

#endif

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
