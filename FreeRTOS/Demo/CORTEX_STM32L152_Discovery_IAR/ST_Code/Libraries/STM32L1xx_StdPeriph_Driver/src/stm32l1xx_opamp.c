/**
  ******************************************************************************
  * @file    stm32l1xx_opamp.c
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file provides firmware functions to manage the following
  *          functionalities of the operational amplifiers (opamp) peripheral:
  *           + Initialization and configuration
  *           + Calibration management
  *          
  *  @verbatim
  ==============================================================================
                            ##### How to use this driver #####
  ==============================================================================
    [..] The device integrates three independent rail-to-rail operational amplifiers
         OPAMP1, OPAMP2 and OPAMP3:
               (+) Internal connections to the ADC.
               (+) Internal connections to the DAC.
               (+) Internal connection to COMP1 (only OPAMP3).
               (+) Internal connection for unity gain (voltage follower) configuration.
               (+) Calibration capability.
               (+) Selectable gain-bandwidth (2MHz in normal mode, 500KHz in low power mode).
    [..]    
         (#) COMP AHB clock must be enabled to get write access
             to OPAMP registers using
         (#) RCC_APB1PeriphClockCmd(RCC_APB1Periph_COMP, ENABLE)
  
         (#) Configure the corresponding GPIO to OPAMPx INP, OPAMPx_INN (if used)
             and OPAMPx_OUT in analog mode.
   
         (#) Configure (close/open) the OPAMP switches using OPAMP_SwitchCmd()

         (#) Enable the OPAMP peripheral using OPAMP_Cmd()

         -@- In order to use OPAMP outputs as ADC inputs, the opamps must be enabled
             and the ADC must use the OPAMP output channel number:
             (+@) OPAMP1 output is connected to ADC channel 3.
             (+@) OPAMP2 output is connected to ADC channel 8.
             (+@) OPAMP3 output is connected to ADC channel 13 (SW1 switch must be closed).

  *  @endverbatim
  *
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
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
#include "stm32l1xx_opamp.h"


/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup OPAMP 
  * @brief OPAMP driver modules
  * @{
  */ 

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/** @defgroup OPAMP_Private_Functions
  * @{
  */

/** @defgroup OPAMP_Group1 Initialization and configuration
 *  @brief   Initialization and configuration
 *
@verbatim   
 ===============================================================================
                            ##### Initialization and configuration #####
 ===============================================================================

@endverbatim
  * @{
  */  

/**
  * @brief  Deinitialize the OPAMPs register to its default reset value.
  * @note   At startup, OTR and LPOTR registers are set to factory programmed values.
  * @param  None.
  * @retval None.
  */
void OPAMP_DeInit(void)
{
  /*!< Set OPAMP_CSR register to reset value */
  OPAMP->CSR = 0x00010101;
  /*!< Set OPAMP_OTR register to reset value */
  OPAMP->OTR = (uint32_t)(* (uint32_t*)FLASH_R_BASE + 0x00000038);
  /*!< Set OPAMP_LPOTR register to reset value */
  OPAMP->LPOTR = (uint32_t)(* (uint32_t*)FLASH_R_BASE + 0x0000003C);
}

/**
  * @brief  Close or Open the OPAMP switches.
  * @param  OPAMP_OPAMPxSwitchy: selects the OPAMPx switch.
  *   This parameter can be any combinations of the following values:
  *     @arg OPAMP_OPAMP1Switch3: used to connect internally OPAMP1 output to 
  *                               OPAMP1 negative input (internal follower)
  *     @arg OPAMP_OPAMP1Switch4: used to connect PA2 to OPAMP1 negative input
  *     @arg OPAMP_OPAMP1Switch5: used to connect PA1 to OPAMP1 positive input
  *     @arg OPAMP_OPAMP1Switch6: used to connect DAC_OUT1 to OPAMP1 positive input
  *     @arg OPAMP_OPAMP1SwitchANA: used to meet 1 nA input leakage
  *     @arg OPAMP_OPAMP2Switch3: used to connect internally OPAMP2 output to 
  *                               OPAMP2 negative input (internal follower)
  *     @arg OPAMP_OPAMP2Switch4: used to connect PA7 to OPAMP2 negative input
  *     @arg OPAMP_OPAMP2Switch5: used to connect PA6 to OPAMP2 positive input
  *     @arg OPAMP_OPAMP2Switch6: used to connect DAC_OUT1 to OPAMP2 positive input
  *     @arg OPAMP_OPAMP2Switch7: used to connect DAC_OUT2 to OPAMP2 positive input
  *     @arg OPAMP_OPAMP2SwitchANA: used to meet 1 nA input leakage
  *     @arg OPAMP_OPAMP3Switch3: used to connect internally OPAMP3 output to 
  *                               OPAMP3 negative input (internal follower)
  *     @arg OPAMP_OPAMP3Switch4: used to connect PC2 to OPAMP3 negative input
  *     @arg OPAMP_OPAMP3Switch5: used to connect PC1 to OPAMP3 positive input
  *     @arg OPAMP_OPAMP3Switch6: used to connect DAC_OUT1 to OPAMP3 positive input
  *     @arg OPAMP_OPAMP3SwitchANA: used to meet 1 nA input leakage on negative input
  *
  * @param  NewState: New state of the OPAMP switch. 
  *   This parameter can be:
  *     ENABLE to close the OPAMP switch
  *     or DISABLE to open the OPAMP switch
  * @note OPAMP_OPAMP2Switch6 and OPAMP_OPAMP2Switch7 mustn't be closed together.
  * @retval None
  */
void OPAMP_SwitchCmd(uint32_t OPAMP_OPAMPxSwitchy, FunctionalState NewState)
{
  /* Check the parameter */
  assert_param(IS_OPAMP_SWITCH(OPAMP_OPAMPxSwitchy));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Close the selected switches */
    OPAMP->CSR |= (uint32_t) OPAMP_OPAMPxSwitchy;
  }
  else
  {
    /* Open the selected switches */
    OPAMP->CSR &= (~(uint32_t)OPAMP_OPAMPxSwitchy);
  }
}

/**
  * @brief  Enable or disable the OPAMP peripheral.
  * @param  OPAMP_Selection: the selected OPAMP. 
  *   This parameter can be one of the following values:
  *     @arg OPAMP_Selection_OPAMP1: OPAMP1 is selected
  *     @arg OPAMP_Selection_OPAMP2: OPAMP2 is selected
  *     @arg OPAMP_Selection_OPAMP3: OPAMP3 is selected
  * @param  NewState: new state of the selected OPAMP peripheral. 
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void OPAMP_Cmd(uint32_t OPAMP_Selection, FunctionalState NewState)
{
  /* Check the parameter */
  assert_param(IS_OPAMP_ALL_PERIPH(OPAMP_Selection));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected OPAMP */
    OPAMP->CSR &= (~(uint32_t) OPAMP_Selection);
  }
  else
  {
    /* Disable the selected OPAMP */
    OPAMP->CSR |= (uint32_t) OPAMP_Selection;
  }
}

/**
  * @brief  Enable or disable the low power mode for OPAMP peripheral.
  * @param  OPAMP_Selection: the selected OPAMP. 
  *   This parameter can be one of the following values:
  *     @arg OPAMP_Selection_OPAMP1: OPAMP1 selected
  *     @arg OPAMP_Selection_OPAMP2: OPAMP2 selected
  *     @arg OPAMP_Selection_OPAMP3: OPAMP3 selected
  * @param  NewState: new low power state of the selected OPAMP peripheral.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void OPAMP_LowPowerCmd(uint32_t OPAMP_Selection, FunctionalState NewState)
{
  /* Check the parameter */
  assert_param(IS_OPAMP_ALL_PERIPH(OPAMP_Selection));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Set the selected OPAMP in low power mode */
    OPAMP->CSR |= (uint32_t) (OPAMP_Selection << 7);
  }
  else
  {
    /* Disable the low power mode for the selected OPAMP */
    OPAMP->CSR &= (~(uint32_t) (OPAMP_Selection << 7));
  }
}

/**
  * @brief  Select the OPAMP power range.
  * @note   The OPAMP power range selection must be performed while OPAMPs are powered down.
  * @param  OPAMP_Range: the selected OPAMP power range. 
  *   This parameter can be one of the following values:
  *     @arg OPAMP_PowerRange_Low: Low power range is selected (VDDA is lower than 2.4V).
  *     @arg OPAMP_PowerRange_High: High power range is selected (VDDA is higher than 2.4V).
  * @retval None
  */
void OPAMP_PowerRangeSelect(uint32_t OPAMP_PowerRange)
{
  /* Check the parameter */
  assert_param(IS_OPAMP_RANGE(OPAMP_PowerRange));

  /* Reset the OPAMP range bit */
  OPAMP->CSR &= (~(uint32_t) (OPAMP_CSR_AOP_RANGE));

  /* Select the OPAMP power range */
  OPAMP->CSR |= OPAMP_PowerRange;
}

/**
  * @}
  */

/** @defgroup OPAMP_Group2 Calibration functions
 *  @brief   Calibration functions
 *
@verbatim   
 ===============================================================================
                            ##### Calibration functions #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Select the trimming mode.
  * @param  OffsetTrimming: the selected offset trimming mode. 
  *   This parameter  can be one of the following values:
  *     @arg OffsetTrimming_Factory: factory trimming values are used for offset
  *                                  calibration.
  *     @arg OffsetTrimming_User: user trimming values are used for offset
  *                               calibration.
  * @note When OffsetTrimming_User is selected, use OPAMP_OffsetTrimConfig()
  *       function or OPAMP_OffsetTrimLowPowerConfig() function to adjust 
  *       trimming value.
  * @retval None
  */
void OPAMP_OffsetTrimmingModeSelect(uint32_t OPAMP_Trimming)
{
  /* Check the parameter */
  assert_param(IS_OPAMP_TRIMMING(OPAMP_Trimming));

  /* Reset the OPAMP_OTR range bit */
  OPAMP->CSR &= (~(uint32_t) (OPAMP_OTR_OT_USER));

  /* Select the OPAMP offset trimming  */
  OPAMP->CSR |= OPAMP_Trimming;

}

/**
  * @brief  Configure the trimming value of OPAMPs in normal mode.
  * @param  OPAMP_Selection: the selected OPAMP. 
  *   This parameter can be one of the following values:
  *         @arg OPAMP_Selection_OPAMP1: OPAMP1 is selected to configure the trimming value.
  *         @arg OPAMP_Selection_OPAMP2: OPAMP2 is selected to configure the trimming value.
  *         @arg OPAMP_Selection_OPAMP3: OPAMP3 is selected to configure the trimming value.
  * @param  OPAMP_Input: the selected OPAMP input. 
  *   This parameter can be one of the following values:
  *         @arg OPAMP_Input_NMOS: NMOS input is selected to configure the trimming value.
  *         @arg OPAMP_Input_PMOS: PMOS input is selected to configure the trimming value.
  * @param  OPAMP_TrimValue: the trimming value. This parameter can be any value lower
  *         or equal to 0x0000001F. 
  * @retval None
  */
void OPAMP_OffsetTrimConfig(uint32_t OPAMP_Selection, uint32_t OPAMP_Input, uint32_t OPAMP_TrimValue)
{
  uint32_t tmpreg = 0;

  /* Check the parameter */
  assert_param(IS_OPAMP_ALL_PERIPH(OPAMP_Selection));
  assert_param(IS_OPAMP_INPUT(OPAMP_Input));
  assert_param(IS_OPAMP_TRIMMINGVALUE(OPAMP_TrimValue));

  /* Get the OPAMP_OTR value */
  tmpreg = OPAMP->OTR;

  if(OPAMP_Selection == OPAMP_Selection_OPAMP1)
  {
    /* Reset the OPAMP inputs selection */
    tmpreg &= (uint32_t)~(OPAMP_CSR_OPA1CAL_L | OPAMP_CSR_OPA1CAL_H);
    /* Select the OPAMP input */
    tmpreg |= OPAMP_Input;

    if(OPAMP_Input == OPAMP_Input_PMOS)
    {
      /* Reset the trimming value corresponding to OPAMP1 PMOS input */
      tmpreg &= (0xFFFFFFE0);
      /* Set the new trimming value corresponding to OPAMP1 PMOS input */
      tmpreg |= (OPAMP_TrimValue);
    }
    else
    {
      /* Reset the trimming value corresponding to OPAMP1 NMOS input */
      tmpreg &= (0xFFFFFC1F);
      /* Set the new trimming value corresponding to OPAMP1 NMOS input */
      tmpreg |= (OPAMP_TrimValue<<5);
    }
  }
  else if (OPAMP_Selection == OPAMP_Selection_OPAMP2)
  {
    /* Reset the OPAMP inputs selection */
    tmpreg &= (uint32_t)~(OPAMP_CSR_OPA2CAL_L | OPAMP_CSR_OPA2CAL_H);
    /* Select the OPAMP input */
    tmpreg |= (uint32_t)(OPAMP_Input<<8);

    if(OPAMP_Input == OPAMP_Input_PMOS)
    {
      /* Reset the trimming value corresponding to OPAMP2 PMOS input */
      tmpreg &= (0xFFFF83FF);
      /* Set the new trimming value corresponding to OPAMP2 PMOS input */
      tmpreg |= (OPAMP_TrimValue<<10);
    }
    else
    {
      /* Reset the trimming value corresponding to OPAMP2 NMOS input */
      tmpreg &= (0xFFF07FFF);
      /* Set the new trimming value corresponding to OPAMP2 NMOS input */
      tmpreg |= (OPAMP_TrimValue<<15);
    }
  }
  else
  {
    /* Reset the OPAMP inputs selection */
    tmpreg &= (uint32_t)~(OPAMP_CSR_OPA3CAL_L | OPAMP_CSR_OPA3CAL_H);
    /* Select the OPAMP input */
    tmpreg |= (uint32_t)(OPAMP_Input<<16);

    if(OPAMP_Input == OPAMP_Input_PMOS)
    {
      /* Reset the trimming value corresponding to OPAMP3 PMOS input */
      tmpreg &= (0xFE0FFFFF);
      /* Set the new trimming value corresponding to OPAMP3 PMOS input */
      tmpreg |= (OPAMP_TrimValue<<20);
    }
    else
    {
      /* Reset the trimming value corresponding to OPAMP3 NMOS input */
      tmpreg &= (0xC1FFFFFF);
      /* Set the new trimming value corresponding to OPAMP3 NMOS input */
      tmpreg |= (OPAMP_TrimValue<<25);
    }
  }

  /* Set the OPAMP_OTR register */
  OPAMP->OTR = tmpreg;
}

/**
  * @brief  Configure the trimming value of OPAMPs in low power mode.
  * @param  OPAMP_Selection: the selected OPAMP. 
  *   This parameter can be one of the following values:
  *         @arg OPAMP_Selection_OPAMP1: OPAMP1 is selected to configure the trimming value.
  *         @arg OPAMP_Selection_OPAMP2: OPAMP2 is selected to configure the trimming value.
  *         @arg OPAMP_Selection_OPAMP3: OPAMP3 is selected to configure the trimming value.
  * @param  OPAMP_Input: the selected OPAMP input. 
  *   This parameter can be one of the following values:
  *         @arg OPAMP_Input_NMOS: NMOS input is selected to configure the trimming value.
  *         @arg OPAMP_Input_PMOS: PMOS input is selected to configure the trimming value.
  * @param  OPAMP_TrimValue: the trimming value. 
  *    This parameter can be any value lower or equal to 0x0000001F. 
  * @retval None
  */
void OPAMP_OffsetTrimLowPowerConfig(uint32_t OPAMP_Selection, uint32_t OPAMP_Input, uint32_t OPAMP_TrimValue)
{
  uint32_t tmpreg = 0;

  /* Check the parameter */
  assert_param(IS_OPAMP_ALL_PERIPH(OPAMP_Selection));
  assert_param(IS_OPAMP_INPUT(OPAMP_Input));
  assert_param(IS_OPAMP_TRIMMINGVALUE(OPAMP_TrimValue));

  /* Get the OPAMP_LPOTR value */
  tmpreg = OPAMP->LPOTR;

  if(OPAMP_Selection == OPAMP_Selection_OPAMP1)
  {
    /* Reset the OPAMP inputs selection */
    tmpreg &= (uint32_t)~(OPAMP_CSR_OPA1CAL_L | OPAMP_CSR_OPA1CAL_H);
    /* Select the OPAMP input */
    tmpreg |= OPAMP_Input;

    if(OPAMP_Input == OPAMP_Input_PMOS)
    {
      /* Reset the trimming value corresponding to OPAMP1 PMOS input */
      tmpreg &= (0xFFFFFFE0);
      /* Set the new trimming value corresponding to OPAMP1 PMOS input */
      tmpreg |= (OPAMP_TrimValue);
    }
    else
    {
      /* Reset the trimming value corresponding to OPAMP1 NMOS input */
      tmpreg &= (0xFFFFFC1F);
      /* Set the new trimming value corresponding to OPAMP1 NMOS input */
      tmpreg |= (OPAMP_TrimValue<<5);
    }
  }
  else if (OPAMP_Selection == OPAMP_Selection_OPAMP2)
  {
    /* Reset the OPAMP inputs selection */
    tmpreg &= (uint32_t)~(OPAMP_CSR_OPA2CAL_L | OPAMP_CSR_OPA2CAL_H);
    /* Select the OPAMP input */
    tmpreg |= (uint32_t)(OPAMP_Input<<8);

    if(OPAMP_Input == OPAMP_Input_PMOS)
    {
      /* Reset the trimming value corresponding to OPAMP2 PMOS input */
      tmpreg &= (0xFFFF83FF);
      /* Set the new trimming value corresponding to OPAMP2 PMOS input */
      tmpreg |= (OPAMP_TrimValue<<10);
    }
    else
    {
      /* Reset the trimming value corresponding to OPAMP2 NMOS input */
      tmpreg &= (0xFFF07FFF);
      /* Set the new trimming value corresponding to OPAMP2 NMOS input */
      tmpreg |= (OPAMP_TrimValue<<15);
    }
  }
  else
  {
    /* Reset the OPAMP inputs selection */
    tmpreg &= (uint32_t)~(OPAMP_CSR_OPA3CAL_L | OPAMP_CSR_OPA3CAL_H);
    /* Select the OPAMP input */
    tmpreg |= (uint32_t)(OPAMP_Input<<16);

    if(OPAMP_Input == OPAMP_Input_PMOS)
    {
      /* Reset the trimming value corresponding to OPAMP3 PMOS input */
      tmpreg &= (0xFE0FFFFF);
      /* Set the new trimming value corresponding to OPAMP3 PMOS input */
      tmpreg |= (OPAMP_TrimValue<<20);
    }
    else
    {
      /* Reset the trimming value corresponding to OPAMP3 NMOS input */
      tmpreg &= (0xC1FFFFFF);
      /* Set the new trimming value corresponding to OPAMP3 NMOS input */
      tmpreg |= (OPAMP_TrimValue<<25);
    }
  }

  /* Set the OPAMP_LPOTR register */
  OPAMP->LPOTR = tmpreg;
}

/**
  * @brief  Checks whether the specified OPAMP calibration flag is set or not.
  * @note   User should wait until calibration flag change the value when changing
  *         the trimming value.
  * @param  OPAMP_Selection: the selected OPAMP. 
  *   This parameter can be one of the following values:
  *     @arg OPAMP_Selection_OPAMP1: OPAMP1 is selected.
  *     @arg OPAMP_Selection_OPAMP2: OPAMP2 is selected.
  *     @arg OPAMP_Selection_OPAMP3: OPAMP3 is selected.
  * @retval The new state of the OPAMP calibration flag (SET or RESET).
  */
FlagStatus OPAMP_GetFlagStatus(uint32_t OPAMP_Selection)
{
  FlagStatus bitstatus = RESET;
  uint32_t tmpreg = 0;

  /* Check the parameter */
  assert_param(IS_OPAMP_ALL_PERIPH(OPAMP_Selection));
  
  /* Get the CSR register value */
  tmpreg = OPAMP->CSR;

  /* Check if OPAMP1 is selected */
  if(OPAMP_Selection == OPAMP_Selection_OPAMP1)
  {
    /* Check OPAMP1 CAL bit status */
    if ((tmpreg & OPAMP_CSR_OPA1CALOUT) != (uint32_t)RESET)
    {
      bitstatus = SET;
    }
    else
    {
      bitstatus = RESET;
    }
  }
  /* Check if OPAMP2 is selected */
  else if(OPAMP_Selection == OPAMP_Selection_OPAMP2)
  {
    /* Check OPAMP2 CAL bit status */
    if ((tmpreg & OPAMP_CSR_OPA2CALOUT) != (uint32_t)RESET)
    {
      bitstatus = SET;
    } 
    else
    {
      bitstatus = RESET;
    }
  }
  else
  {
    /* Check OPAMP3 CAL bit status */
    if ((tmpreg & OPAMP_CSR_OPA3CALOUT) != (uint32_t)RESET)
    {
      bitstatus = SET;
    }
    else
    {
      bitstatus = RESET;
    }
  }
  return bitstatus;
}

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
