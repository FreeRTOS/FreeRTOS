/**
  ******************************************************************************
  * @file    tsl_acq_stm8tl5x.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the PXS acquisition
  *          on STM8TL5x products.
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
#include "tsl_acq_stm8tl5x.h"
#include "tsl_globals.h"
#include "stm8tl5x_it.h"

/* Private typedefs ----------------------------------------------------------*/

/* Private defines -----------------------------------------------------------*/
#define EPCC_INIT_VALUE (0x80)
#define CS_MIDDLE_VALUE (17)
#define CS_MAX_VALUE    (32)
#define MAX_MEASURE     (0xFFFF)

/* Private macros ------------------------------------------------------------*/
#define IS_BANK_INDEX_OK(INDEX)   (((INDEX) == 0) || (((INDEX) > 0) && ((INDEX) < TSLPRM_TOTAL_BANKS)))
#define IS_SOURCE_INDEX_OK(INDEX) (((INDEX) == 0) || (((INDEX) > 0) && ((INDEX) < TSLPRM_TOTAL_CHANNELS)))
#define IS_EPCC_STATUS_OK(STATUS) ((STATUS & TSL_EPCC_CHANGE_MASK) != 0)
#define IS_CSSEL_OK(CSSEL)        (((CSSEL) == 0) || (((CSSEL) > 0) && ((CSSEL) < CS_MAX_VALUE)))

/* Private variables ---------------------------------------------------------*/
TSL_BankConfig_T PXS_BankConfig[TSLPRM_TOTAL_BANKS];
CONST uint8_t PXS_CSsorting[] = {0, 1, 2, 8, 3, 4, 5, 9, 6, 10, 16, 11, 7, 12, 17, 13, 18, 19, 14, 24, 15, 20, 25, 21, 26, 22, 27, 23, 28, 29, 30, 31};

/* Private functions prototype -----------------------------------------------*/
void TSL_PXS_CS_CalibrateBank(TSL_tIndex_T idx_bk);
int8_t TSL_PXS_EPCC_CalibrateBank(TSL_tIndex_T bank);
TSL_Status_enum_T TSL_PXS_EPCC_CalibrateZone(CONST TSL_Zone_T *);
void SoftDelay(uint32_t val);

/**
  * @brief  Initializes the acquisition module.
  * @param  None
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_Init(void)
{

  TSL_Status_enum_T retval = TSL_STATUS_OK;

  TSL_tIndex_T i;
  TSL_tIndex_T j;
  TSL_tIndex_T idx_bk; // Bank index
  uint16_t TxInUseMask = 0;
  uint16_t RxInUseMask = 0;
  CONST TSL_Bank_T *bank;
  uint8_t *CSArray;

  // Enable the PXS IP clock
  CLK->PCKENR1 |= CLK_PCKENR1_PXS;

  // Initialization of PXS IP
  PXS->CKCR1 &= (uint8_t)~PXS_CKCR1_PRESC;

#if (TSLPRM_PXS_HSI == 16000)
  PXS->CKCR1 |= PXS_CKCR1_16MHZ;
#elif (TSLPRM_PXS_HSI == 8000)
  PXS->CKCR1 |= PXS_CKCR1_8MHZ;
#elif (TSLPRM_PXS_HSI == 4000)
  PXS->CKCR1 |= PXS_CKCR1_4MHZ;
#elif (TSLPRM_PXS_HSI == 2000)
  PXS->CKCR1 |= PXS_CKCR1_2MHZ;
#elif (TSLPRM_PXS_HSI == 1000)
  PXS->CKCR1 |= PXS_CKCR1_1MHZ;
#elif (TSLPRM_PXS_HSI == 500)
  PXS->CKCR1 |= PXS_CKCR1_500KHZ;
#elif (TSLPRM_PXS_HSI == 250)
  PXS->CKCR1 |= PXS_CKCR1_250KHZ;
#elif (TSLPRM_PXS_HSI == 125)
  PXS->CKCR1 |= PXS_CKCR1_125KHZ;
#else
  PXS->CKCR1 |= PXS_CKCR1_16MHZ; // Default
#endif

  PXS->CKCR2 = (uint8_t)(((uint8_t)TSLPRM_PXS_UP_LENGTH & 0x07) << 4) | ((uint8_t)TSLPRM_PXS_PASS_LENGTH & 0x07);

#if TSLPRM_PXS_RF_DETECTION > 0
  enablePXSNoiseDetection();
#endif

  setPXSStab(TSLPRM_PXS_STAB);
  setPXSBias(TSLPRM_PXS_BIAS);

  // Initialization of the GPIO shared with the used TX
  for (i = 0; i < TSLPRM_TOTAL_BANKS; i++)
  {
    bank = &(TSL_Globals.Bank_Array[i]);
    CSArray = PXS_BankConfig[i].CSSEL;
    TxInUseMask |= bank->msk_TX;
    // Set the mask with the receivers use as receiver or as transmitter
    RxInUseMask |= bank->msk_RXEN;
    // Set the CS to 0
    for (j = 0; j <= TSLPRM_HIGH_CHANNEL_NB; j++)
    {
      *CSArray = 0;
      CSArray++;
    }
  }

  GPIOD->ODR &= (uint8_t)(~(TxInUseMask & 0x00FF));
  // Set the port as output
  GPIOD->DDR |= (uint8_t)(TxInUseMask & 0x00FF);
  // Configure the port as open-drain
  GPIOD->CR1 &= (uint8_t)(~(TxInUseMask & 0x00FF));
#if TSLPRM_PXS_INACTIVE_TX > 0
  // Configure as floating
  GPIOD->ODR |= (uint8_t)(TxInUseMask & 0x00FF);
#else
  // Drive them to VSS
  GPIOD->ODR &= (uint8_t)(~(TxInUseMask & 0x00FF));
#endif
  GPIOB->ODR &= (uint8_t)(~((TxInUseMask & 0xFF00) >> 8));
  // Set the port as output
  GPIOB->DDR |= (uint8_t)((TxInUseMask & 0xFF00) >> 8);
  // Configure the port as open-drain
  GPIOB->CR1 &= (uint8_t)(~((TxInUseMask & 0xFF00) >> 8));
#if TSLPRM_PXS_INACTIVE_TX > 0
  // Configure as floating
  GPIOB->ODR |= (uint8_t)((TxInUseMask & 0xFF00) >> 8);
#else
  // Drive it to VSS
  GPIOB->ODR &= (uint8_t)(~((TxInUseMask & 0xFF00) >> 8));
#endif

  enablePXS();

#if TSLPRM_PXS_INACTIVE_RX > 0
  PXS->RXINSR = 0x3FF;
#else
  PXS->RXINSR = 0x0000;
#endif

#if TSLPRM_PXS_RX_COUPLING > 0
  enablePXSCoupling();
#else
  disablePXSCoupling()
#endif

#if TSLPRM_PXS_SYNCHRONIZE > 0
  enablePXSSync();
#if TSLPRM_PXS_SYNCHRO_EDGE > 0
  selectPXSSyncRisingEdge();
#else
  selectPXSSyncFallingEdge();
#endif
#else
  disablePXSSync();
#endif

#if TSLPRM_USE_ACQ_INTERRUPT > 0
  enablePXSInterrupts(PXS_CR2_EOCITEN);
#endif
  // Configure the acquisition mode
  PXS->RXCR3 = (uint16_t)RxInUseMask;
  PXS->RXCR2 = (uint16_t)RxInUseMask;

#if TSLPRM_ACQ_MAX > 0
  PXS->MAXR = TSLPRM_ACQ_MAX;
  PXS->MAXENR = 0x03FF;
#else
  PXS->MAXENR = 0;
#endif

  // Calibrate the CS for all banks
  for (idx_bk = 0;idx_bk < TSLPRM_TOTAL_BANKS;idx_bk++)
  {
    TSL_PXS_CS_CalibrateBank(idx_bk);
  }


  // Calibrate the EPCC for all banks
  for (idx_bk = 0;idx_bk < TSLPRM_TOTAL_BANKS;idx_bk++)
  {
    if (TSL_PXS_EPCC_CalibrateBank(idx_bk) > 0)
    {
      retval = TSL_STATUS_ERROR;
    }
  }
#if TSLPRM_PXS_LOW_POWER_MODE > 0
  setPXSLowPower();
#else
  resetPXSLowPower();
#endif

  return retval;

}

/**
  * @brief Calibrate the CS for a selected acquisition bank
  * @param[in] idx_bk Index of the bank
  * @retval Number of Receivers not correctly calibrated
  */
void TSL_PXS_CS_CalibrateBank(TSL_tIndex_T idx_bk)
{
  TSL_tIndex_T idx_ch;
  uint8_t currentCS = 24;
  uint8_t CS_delta = 4; // Value to add/substract to/from the current CS
  CONST TSL_Bank_T *bank;
  CONST uint16_t targetCount = TSLPRM_KEY_TARGET_REFERENCE / TSLPRM_KEY_TARGET_ATTENUATION;
  CONST uint16_t targetCountError = targetCount >> 3;
  bool CalibrationDone = FALSE;
  uint16_t measSup[TSLPRM_HIGH_CHANNEL_NB+1];
  uint16_t measInf[TSLPRM_HIGH_CHANNEL_NB+1];
  uint8_t CSsup[TSLPRM_HIGH_CHANNEL_NB+1];
  uint8_t CSinf[TSLPRM_HIGH_CHANNEL_NB+1];

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));
#if TSLPRM_USE_ACQ_INTERRUPT == 0
  enablePXSInterrupts(PXS_CR2_EOCITEN);
#endif

  bank = &(TSL_Globals.Bank_Array[idx_bk]);
  resetPXSLowPower();
  TSL_acq_BankConfig(idx_bk);

  PXS->MAXR = TSLPRM_KEY_TARGET_REFERENCE;

  WFE->CR1 |= WFE_CR1_PXS_EV;
  for (idx_ch = 0; idx_ch <= TSLPRM_HIGH_CHANNEL_NB; idx_ch++)
  {
    PXS->RXEPCCSELR[idx_ch] = 0;
    PXS->RXCSSELR[idx_ch] = currentCS;
    CSsup[idx_ch] = 0;
    CSinf[idx_ch] = 0;
    measInf[idx_ch] = 0;
    measSup[idx_ch] = 0xFFFF;

  }
  do
  {
    startPXSAcquisition();
    wfe();
    clearPXS_ISR_EOCF;
    for (idx_ch = 0; idx_ch <= TSLPRM_HIGH_CHANNEL_NB; idx_ch++)
    {
      if (bank->msk_channels & (uint16_t)((uint16_t)1 << idx_ch))
      {
        if (!(PXS->RXSR & (uint16_t)((uint16_t)1 << idx_ch)) || (PXS->RXCNTR[idx_ch] > targetCount - targetCountError))
        {
          PXS->RXCSSELR[idx_ch] -= 8;
        }
      }
    }
    currentCS -= 8;
  }
  while (currentCS);


  for (idx_ch = 0; idx_ch <= TSLPRM_HIGH_CHANNEL_NB; idx_ch++)
  {
    PXS->RXCSSELR[idx_ch] += CS_delta;
  }

  do
  {
    CS_delta >>= 1;
    if ((CS_delta == 0) && (CalibrationDone == FALSE))
    {
      CalibrationDone = TRUE;
      CS_delta = 1;
    }

    startPXSAcquisition();
    wfe();
    clearPXS_ISR_EOCF;
    for (idx_ch = 0; idx_ch <= TSLPRM_HIGH_CHANNEL_NB; idx_ch++)
    {
      if (bank->msk_channels & (uint16_t)((uint16_t)1 << idx_ch))
      {
        if (!(PXS->RXSR & (uint16_t)((uint16_t)1 << idx_ch)) || (PXS->RXCNTR[idx_ch] > targetCount))
        {
          measSup[idx_ch] = PXS->RXCNTR[idx_ch];
          CSsup[idx_ch] = PXS->RXCSSELR[idx_ch];
          PXS->RXCSSELR[idx_ch] -= CS_delta;
        }
        else //if (PXS->RXCNTR[idx_ch] < targetCount )
        {
          measInf[idx_ch] = PXS->RXCNTR[idx_ch];
          CSinf[idx_ch] = PXS->RXCSSELR[idx_ch];
          PXS->RXCSSELR[idx_ch] += CS_delta;
        }
//        else
//        {
        // Do nothing (MISRA requirement)
//        }
      }
    }
  }
  while ((CalibrationDone == FALSE) || (CS_delta != 0));


  // Restore configuration
#if TSLPRM_ACQ_MAX > 0
  PXS->MAXR = TSLPRM_ACQ_MAX;
#else
  PXS->MAXENR = 0;
#endif

  WFE->CR1 &= (uint8_t)~WFE_CR1_PXS_EV;
#if TSLPRM_USE_ACQ_INTERRUPT == 0
  disablePXSInterrupts(PXS_CR2_EOCITEN);
#endif

  // Store the CS
  for (idx_ch = 0;idx_ch <= TSLPRM_HIGH_CHANNEL_NB;idx_ch++)
  {
    if ((measSup[idx_ch] == 0) || ((measSup[idx_ch] - targetCount) > (targetCount - measInf[idx_ch])))
    {
      PXS_BankConfig[idx_bk].CSSEL[idx_ch] = CSinf[idx_ch];
    }
    else
    {
      PXS_BankConfig[idx_bk].CSSEL[idx_ch] = CSsup[idx_ch];
    }
  }
}


/**
  * @brief Calibrate the EPCC for a selected acquisition bank
  * @param[in] idx_bk Index of the bank
  * @retval Number Number of Receivers not correctly calibrated
  */
int8_t TSL_PXS_EPCC_CalibrateBank(TSL_tIndex_T idx_bk)
{
  TSL_tIndex_T idx_ch;
  uint8_t currentEPCC, trial, goodEPCC = 0;
  uint8_t EPCCtoCompute = 0; // Used to define if all the EPCC have their final value
  uint8_t EPCC_delta = EPCC_INIT_VALUE; // Value to add/substract to/from the current EPCC
  CONST TSL_Bank_T *bank;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));
#if TSLPRM_USE_ACQ_INTERRUPT == 0
  enablePXSInterrupts(PXS_CR2_EOCITEN);
#endif

  bank = &(TSL_Globals.Bank_Array[idx_bk]);
  resetPXSLowPower();
  TSL_acq_BankConfig(idx_bk);

  PXS->MAXR = 2 * TSLPRM_KEY_TARGET_REFERENCE;

  WFE->CR1 |= WFE_CR1_PXS_EV;
  for (idx_ch = 0; idx_ch <= TSLPRM_HIGH_CHANNEL_NB; idx_ch++)
  {
    PXS->RXEPCCSELR[idx_ch] = EPCC_delta;
    if (bank->msk_channels & (uint16_t)((uint16_t)1 << idx_ch))
    {
      EPCCtoCompute++;
    }
  }
  do
  {
    EPCC_delta >>= 1;
    startPXSAcquisition();
    wfe();
    clearPXS_ISR_EOCF;
    for (idx_ch = 0; idx_ch <= TSLPRM_HIGH_CHANNEL_NB; idx_ch++)
    {
      if (bank->msk_channels & (uint16_t)((uint16_t)1 << idx_ch))
      {
        if (!(PXS->RXSR & (uint16_t)((uint16_t)1 << idx_ch)) || (PXS->RXCNTR[idx_ch] > TSLPRM_KEY_TARGET_REFERENCE))
        {
          PXS->RXEPCCSELR[idx_ch] -= EPCC_delta;
        }
        else if (PXS->RXCNTR[idx_ch] < TSLPRM_KEY_TARGET_REFERENCE)
        {
          PXS->RXEPCCSELR[idx_ch] += EPCC_delta;
        }
        else
        {
          // Do nothing (MISRA requirement)
        }
      }
    }
  }
  while (EPCC_delta >= 1);
  // Second pass to fine-tune
  trial = TSLPRM_PXS_EPCC_FINE_TUNING_ITERATION;
  do
  {
    startPXSAcquisition();
    goodEPCC = 0; // Reset the goodEPCC variable
    wfe();
    clearPXS_ISR_EOCF;
    for (idx_ch = 0; idx_ch <= TSLPRM_HIGH_CHANNEL_NB; idx_ch++)
    {
      if (bank->msk_channels & (uint16_t)((uint16_t)1 << idx_ch))
      {
        currentEPCC = PXS->RXEPCCSELR[idx_ch]; //this affectation allow to avoid computation of the structure address
        if (!(PXS->RXSR & (uint16_t)((uint16_t)1 << idx_ch)) || (PXS->RXCNTR[idx_ch] > (TSLPRM_KEY_TARGET_REFERENCE + TSLPRM_KEY_TARGET_REFERENCE_ERROR)))
        {
          if (currentEPCC > 0)
          {
            if ((currentEPCC & 0x07) != 0)
            {
              currentEPCC--;
            }
            else
            {
              currentEPCC -= 3; // This is due to the non linearity of the EPCC
            }
          }
        }
        else if (PXS->RXCNTR[idx_ch] < (TSLPRM_KEY_TARGET_REFERENCE - TSLPRM_KEY_TARGET_REFERENCE_ERROR))
        {
          if (currentEPCC < 0xFF)
          {
            if ((currentEPCC & 0x07) != 0x07)
            {
              currentEPCC++;
            }
            else
            {
              currentEPCC += 2; // This is due to the non linearity of the EPCC
            }
          }
          else // Invert the change in case the sorting is not reliable
          {
            currentEPCC--;
          }
        }
        else
        {
          goodEPCC++;
        }
        PXS->RXEPCCSELR[idx_ch] = currentEPCC;
      }
    }
    trial--;
  }
  while ((goodEPCC < EPCCtoCompute) && (trial));

  // Restore configuration
#if TSLPRM_ACQ_MAX > 0
  PXS->MAXR = TSLPRM_ACQ_MAX;
#else
  PXS->MAXENR = 0;
#endif

  WFE->CR1 &= (uint8_t)~WFE_CR1_PXS_EV;
#if TSLPRM_USE_ACQ_INTERRUPT == 0
  disablePXSInterrupts(PXS_CR2_EOCITEN);
#endif

  // Store the EPCC
  for (idx_ch = 0;idx_ch <= TSLPRM_HIGH_CHANNEL_NB;idx_ch++)
  {
    PXS_BankConfig[idx_bk].EPCCSEL[idx_ch] = PXS->RXEPCCSELR[idx_ch];
  }

  return((int8_t)(EPCCtoCompute - goodEPCC));
}


#if TSLPRM_USE_ZONE > 0
/**
  * @brief Calibrate the EPCC for a set of acquisition banks.
  * @param[in] zone Set of banks to calibrate the EPCC
  * @retval Status
  */
TSL_Status_enum_T TSL_PXS_EPCC_CalibrateZone(CONST TSL_Zone_T *zone)
{
  uint16_t idx_bk;
  TSL_Status_enum_T retval = TSL_STATUS_OK;
  for (idx_bk = 0; idx_bk < zone->NbBanks; idx_bk++)
  {
    if (TSL_PXS_EPCC_CalibrateBank(zone->BankIndex[idx_bk]) > 0)
    {
      retval = TSL_STATUS_ERROR;
    }
  }
  return(retval);
}
#endif


/**
  * @brief Test the reference and update the EPCC/CS if needed
  * @param[in] pCh pointer on the channel data information
  * @retval Result
  */
TSL_Bool_enum_T TSL_acq_TestReferenceOutOfRange(TSL_ChannelData_T *pCh)
{
  uint16_t reference, target_error = 0;
  TSL_Bool_enum_T result = TSL_FALSE;

  if (pCh->Flags.EPCCStatus != TSL_EPCC_STATUS_LOCKED)
  {
    reference = pCh->Ref;
#if TSLPRM_TOTAL_TKEYS > 0
    if (TSL_Globals.This_Obj->Type & TSL_OBJ_TYPE_TKEY_MASK)
    {
      target_error = TSLPRM_TOUCHKEY_REFERENCE_RANGE;
    }
#endif

#if TSLPRM_TOTAL_LNRTS > 0
    if (TSL_Globals.This_Obj->Type & TSL_OBJ_TYPE_LINROT_MASK)
    {
      target_error = TSLPRM_LINROT_REFERENCE_RANGE;
    }
#endif
    if ((reference != 0) && ((reference > (TSLPRM_KEY_TARGET_REFERENCE + target_error)) || (reference < (TSLPRM_KEY_TARGET_REFERENCE - target_error))))
    {
      if (reference < (TSLPRM_KEY_TARGET_REFERENCE - target_error))
      {
        pCh->Flags.EPCCStatus = TSL_EPCC_STATUS_INCREASE;
      }
      else if (reference > (TSLPRM_KEY_TARGET_REFERENCE + target_error))
      {
        pCh->Flags.EPCCStatus = TSL_EPCC_STATUS_DECREASE;
      }
      else
      {
        // Do nothing (MISRA requirement)
      }
      result = TSL_TRUE;
    }
  }
  return(result);
}

/**
  * @brief Test if the measure has crossed the reference target
  * @param[in] pCh      Pointer to the channel Data under test
  * @param[in] new_meas Measure of the last acquisition on this channel
  * @retval Result Result of the test
  */
TSL_Bool_enum_T TSL_acq_TestFirstReferenceIsValid(TSL_ChannelData_T *pCh, TSL_tMeas_T new_meas)
{
  TSL_Bool_enum_T result = TSL_TRUE;
  TSL_EPCCStatus_enum_T EPCCStatus;

  EPCCStatus = pCh->Flags.EPCCStatus;
  if (EPCCStatus & TSL_EPCC_CHANGE_MASK)
  {
    // If the previous reference and the new one are on each side of the reference target
    // the EPCC is no more tested and the calibration continues.
    if (((EPCCStatus == TSL_EPCC_STATUS_INCREASE) && (new_meas >= TSLPRM_KEY_TARGET_REFERENCE))
        || ((EPCCStatus == TSL_EPCC_STATUS_DECREASE) && (new_meas <= TSLPRM_KEY_TARGET_REFERENCE)))
    {
      pCh->Flags.EPCCStatus = TSL_EPCC_STATUS_UNLOCKED;
    }
    else
    {
      result = TSL_FALSE;
    }
  }

  return(result);
}


/**
  * @brief Increase or decrease the CS value
  * @param[in] pCSSEL Address of the CS to be modified
  * @param[in] change Define if the Cs must be increased or decreased
  * @retval None
  */
void TSL_acq_UpdateCS(uint8_t *pCSSEL, TSL_EPCCStatus_enum_T change)
{
  uint16_t indexCS;

  assert_param(IS_EPCC_STATUS_OK(change));
  assert_param(IS_CSSEL_OK(*pCSSEL));

  if (*pCSSEL > CS_MIDDLE_VALUE)
  {
    indexCS = (CS_MIDDLE_VALUE - 1);
  }
  else
  {
    indexCS = 0;
  }
  while ((PXS_CSsorting[indexCS] != *pCSSEL) && (indexCS < CS_MAX_VALUE))
  {
    indexCS++;
  }
  if (change == TSL_EPCC_STATUS_INCREASE)
  {
    *pCSSEL = PXS_CSsorting[indexCS + 1];
  }
  else
  {
    *pCSSEL = PXS_CSsorting[indexCS - 1];
  }
}


/**
  * @brief Configures a Bank.
  * @param[in] idx_bk Index of the Bank to configure
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_BankConfig(TSL_tIndex_T idx_bk)
{
  TSL_Status_enum_T retval = TSL_STATUS_OK;
  uint16_t idx_ch;
  TSL_ChannelFlags_T flags;
  CONST TSL_Bank_T *bank = &(TSL_Globals.Bank_Array[idx_bk]);
  CONST TSL_ChannelSrc_T *pchSrc = bank->p_chSrc;
  CONST TSL_ChannelDest_T *pchDest = bank->p_chDest;
  TSL_tMaskRX enabledRX = 0;
  uint8_t *pEPCCSEL, *pCSSEL;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));

  TSL_Globals.This_Bank = idx_bk;

  selectPXSRxGroup(bank->msk_group);
  for (idx_ch = 0;idx_ch < bank->NbChannels;idx_ch++)
  {
    flags = bank->p_chData[pchDest->IdxDest].Flags;
    if (flags.ObjStatus == TSL_OBJ_STATUS_ON)
    {
      enabledRX |= (1 << pchSrc->IdxSrc);
      if (flags.EPCCStatus & TSL_EPCC_CHANGE_MASK)
      {
        pEPCCSEL = &PXS_BankConfig[idx_bk].EPCCSEL[pchSrc->IdxSrc];
        if (flags.EPCCStatus == TSL_EPCC_STATUS_INCREASE)
        {
          if ((*pEPCCSEL) < 0xFF)
          {
            if (((*pEPCCSEL) & 0x07) != 0x07)
            {
              (*pEPCCSEL)++;
            }
            else
            {
              if ((*pEPCCSEL) < 0xFE)
              {
                (*pEPCCSEL) += 2; // This is due to the non linearity of the PCC
              }
              else
              {
                (*pEPCCSEL)++;
              }
            }

          }
          else
          {
            pCSSEL = &PXS_BankConfig[idx_bk].CSSEL[pchSrc->IdxSrc];
            if (*pCSSEL < 0x1F)
            {
              TSL_acq_UpdateCS(pCSSEL, TSL_EPCC_STATUS_INCREASE);
            }
            else
            {}
          }
        }
        else
        {
          if ((*pEPCCSEL) > 0)
          {
            if (((*pEPCCSEL) & 0x07) != 0)
            {
              (*pEPCCSEL)--;
            }
            else
            {
              if ((*pEPCCSEL) > 3)
              {
                (*pEPCCSEL) -= 3; // This is due to the non linearity of the PCC
              }
              else
              {
                (*pEPCCSEL)--;
              }
            }
          }
          else
          {
            pCSSEL = &PXS_BankConfig[idx_bk].CSSEL[pchSrc->IdxSrc];
            if (*pCSSEL > 0)
            {
              TSL_acq_UpdateCS(pCSSEL, TSL_EPCC_STATUS_DECREASE);
            }
            else
            {}
          }
        }
      }
    }

    // Next channel
    pchSrc++;
    pchDest++;
  }

  // The two following loops are more efficient than the two instructions in the same loop
  for (idx_ch = 0;idx_ch <= TSLPRM_HIGH_CHANNEL_NB;idx_ch++)
  {
    PXS->RXCSSELR[idx_ch] = PXS_BankConfig[idx_bk].CSSEL[idx_ch];
  }
  for (idx_ch = 0;idx_ch <= TSLPRM_HIGH_CHANNEL_NB;idx_ch++)
  {
    PXS->RXEPCCSELR[idx_ch] = PXS_BankConfig[idx_bk].EPCCSEL[idx_ch];
  }

  PXS->TXENR = bank->msk_TX; // Enable the Tx selected (if any)
  PXS->RXCR1 = bank->msk_channels; // Configure the Rx and the Tx function modes

  // Enable the Rx which are not disabled including the potential Rx configured as Tx
  PXS->RXENR = bank->msk_RXEN & ((uint16_t)(~bank->msk_channels) | enabledRX);

  if (enabledRX == 0)
  {
    retval = TSL_STATUS_ERROR;
  }

  return(retval);

}


/**
  * @brief Test if EPCC are changing
  * @param[in] pCh Channel to be processed
  * @retval bool Test result
  */
TSL_Bool_enum_T TSL_acq_UseFilter(TSL_ChannelData_T *pCh)
{
  if (pCh->Flags.EPCCStatus & TSL_EPCC_CHANGE_MASK)
  {
    return (TSL_FALSE);
  }
  else
  {
    return(TSL_TRUE);
  }
}


/**
  * @brief Start acquisition on a previously configured bank
  * @param None
  * @retval None
  */
void TSL_acq_BankStartAcq(void)
{
  // Start acquisition
  startPXSAcquisition();
}


/**
  * @brief Wait end of acquisition
  * @param None
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_BankWaitEOC(void)
{
  TSL_Status_enum_T retval = TSL_STATUS_BUSY;

  if (checkPXSInterruptStatusFlag(PXS_ISR_EOCF)) // Check EOC flag
  {
    if (PXS->RXSR != TSL_Globals.Bank_Array[TSL_Globals.This_Bank].msk_channels) // Check MCE flag
    {
      retval = TSL_STATUS_ERROR;
    }
    else
    {
      retval = TSL_STATUS_OK;
    }
  }

  return retval;
}


/**
  * @brief Check noise detection
  * @param None
  * @retval Status
  */
TSL_AcqStatus_enum_T TSL_acq_CheckNoise(void)
{
  TSL_AcqStatus_enum_T retval = TSL_ACQ_STATUS_OK;
#if TSLPRM_PXS_RF_DETECTION > 0
  if (checkPXSInterruptStatusFlag(PXS_ISR_NOISEDETF) == PXS_ISR_NOISEDETF)
  {
    retval = TSL_ACQ_STATUS_NOISE;
  }
#endif
  return(retval);
}


/**
  * @brief Return the current measure
  * @param[in] index Index of the measure source
  * @retval Measure
  */
TSL_tMeas_T TSL_acq_GetMeas(TSL_tIndexSrc_T index)
{
  uint16_t CurrentReceiver;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_SOURCE_INDEX_OK(index));

  CurrentReceiver = (uint16_t)(((uint16_t)1) << index);

  if (PXS->RXSR & CurrentReceiver)
  {
    return(PXS->RXCNTR[index]);
  }
  else
  {
    return(MAX_MEASURE);
  }
}


/**
  * @brief  Process the PXS Interrupt routine
  * @param  None
  * @retval None
  */
INTERRUPT_HANDLER(TSL_acq_ProcessIT, 2)
{
  clearPXS_ISR_EOCF;

  TSL_acq_BankGetResult(TSL_Globals.This_Bank, 0, 0); // No noise filter

#if TSLPRM_USE_ZONE > 0
  if ((TSL_Globals.This_Zone == 0) || (TSL_Globals.Index_In_This_Zone >= TSL_Globals.This_Zone->NbBanks))
  {
    CFG->GCR &= (uint8_t)(~CFG_GCR_AL); // Reset Activation level to resume main processing
    PXS->RXENR = 0; // To reduce consumption
    PXS->TXENR = 0; // To reduce consumption
    TSL_Globals.This_Bank = 0;
  }
  else
  {
    if (TSL_acq_ZoneConfig(TSL_Globals.This_Zone, TSL_Globals.Index_In_This_Zone) != TSL_STATUS_ERROR)
    {
      // Start Bank acquisition
      TSL_acq_BankStartAcq();
#if TSLPRM_PXS_LOW_POWER_MODE > 0
      if (TSL_Globals.Index_In_This_Zone >= TSL_Globals.This_Zone->NbBanks)
      {
        setPXSLowPower();
      }
#endif
    }

  }
#else
  CFG->GCR &= (uint8_t)(~CFG_GCR_AL); // Reset Activation level to resume main processing
  PXS->RXENR = 0; // To reduce consumption
  PXS->TXENR = 0; // To reduce consumption
#endif
}


#ifdef __IAR_SYSTEMS_ICC__
#pragma optimize=low
#elif defined (__CC_ARM)
#pragma O1
#pragma Ospace
#endif
/**
  * @brief  Software delay (private routine)
  * @param  val Wait delay
  * @retval None
  */
void SoftDelay(uint32_t val)
{
  uint32_t i;
  for (i = val; i > 0; i--)
  {}
}

/******************* (C) COPYRIGHT 2013 STMicroelectronics *****END OF FILE****/
