/**
  ******************************************************************************
  * @file    stm32l1xx_comp.c
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file provides firmware functions to manage the following 
  *          functionalities of the comparators (COMP1 and COMP2) peripheral: 
  *           + Comparators configuration
  *           + Window mode control
  *           + Internal Reference Voltage (VREFINT) output
  *
  *  @verbatim
 ===============================================================================
                     ##### How to use this driver #####
 ===============================================================================
    [..] The device integrates two analog comparators COMP1 and COMP2:
         (+) COMP1 is a fixed threshold (VREFINT) that shares the non inverting
             input with the ADC channels.
         (+) COMP2 is a rail-to-rail comparator whose the inverting input can be 
             selected among: DAC_OUT1, DAC_OUT2, 1/4 VREFINT, 1/2 VERFINT, 3/4 
             VREFINT, VREFINT, PB3 and whose the output can be redirected to 
             embedded timers: TIM2, TIM3, TIM4, TIM10.
  
         (+) The two comparators COMP1 and COMP2 can be combined in window mode.

         -@-
            (#@) Comparator APB clock must be enabled to get write access
                 to comparator register using
                 RCC_APB1PeriphClockCmd(RCC_APB1Periph_COMP, ENABLE).
  
            (#@) COMP1 comparator and ADC can't be used at the same time since
                 they share the same ADC switch matrix (analog switches).
  
            (#@) When an I/O is used as comparator input, the corresponding GPIO 
                 registers should be configured in analog mode.
  
            (#@) Comparators outputs (CMP1OUT and CMP2OUT) are not mapped on
                 GPIO pin. They are only internal.
                 To get the comparator output level, use COMP_GetOutputLevel().
  
            (#@) COMP1 and COMP2 outputs are internally connected to EXTI Line 21
                 and EXTI Line 22 respectively.
                 Interrupts can be used by configuring the EXTI Line using the 
                 EXTI peripheral driver.
  
            (#@) After enabling the comparator (COMP1 or COMP2), user should wait
                 for start-up time (tSTART) to get right output levels.
                 Please refer to product datasheet for more information on tSTART.
  
            (#@) Comparators cannot be used to exit the device from Sleep or Stop 
                 mode when the internal reference voltage is switched off using 
                 the PWR_UltraLowPowerCmd() function (ULP bit in the PWR_CR register).
  
    @endverbatim
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
#include "stm32l1xx_comp.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup COMP 
  * @brief COMP driver modules.
  * @{
  */ 

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/** @defgroup COMP_Private_Functions
  * @{
  */

/** @defgroup COMP_Group1 Initialization and Configuration functions
 *  @brief   Initialization and Configuration functions.
 *
@verbatim
 ===============================================================================
              ##### Initialization and Configuration functions #####
 ===============================================================================

@endverbatim
  * @{
  */
   
/**
  * @brief  Deinitializes COMP peripheral registers to their default reset values.
  * @param  None
  * @retval None
  */
void COMP_DeInit(void)
{
  COMP->CSR = ((uint32_t)0x00000000);    /*!< Set COMP->CSR to reset value */
}

/**
  * @brief  Initializes the COMP2 peripheral according to the specified parameters
  *         in the COMP_InitStruct.
  * @note   This function configures only COMP2.
  * @note   COMP2 comparator is enabled as soon as the INSEL[2:0] bits are 
  *         different from "000".
  * @param  COMP_InitStruct: pointer to an COMP_InitTypeDef structure that contains 
  *         the configuration information for the specified COMP peripheral.  
  * @retval None
  */
void COMP_Init(COMP_InitTypeDef* COMP_InitStruct)
{
  uint32_t tmpreg = 0;
  
  /* Check the parameters */
  assert_param(IS_COMP_INVERTING_INPUT(COMP_InitStruct->COMP_InvertingInput));
  assert_param(IS_COMP_OUTPUT(COMP_InitStruct->COMP_OutputSelect));
  assert_param(IS_COMP_SPEED(COMP_InitStruct->COMP_Speed));

  /*!< Get the COMP CSR value */
  tmpreg = COMP->CSR;

  /*!< Clear the  INSEL[2:0], OUTSEL[1:0] and SPEED bits */ 
  tmpreg &= (uint32_t) (~(uint32_t) (COMP_CSR_OUTSEL | COMP_CSR_INSEL | COMP_CSR_SPEED));
  
  /*!< Configure COMP: speed, inversion input selection and output redirection */
  /*!< Set SPEED bit according to COMP_InitStruct->COMP_Speed value */
  /*!< Set INSEL bits according to COMP_InitStruct->COMP_InvertingInput value */ 
  /*!< Set OUTSEL bits according to COMP_InitStruct->COMP_OutputSelect value */  
  tmpreg |= (uint32_t)((COMP_InitStruct->COMP_Speed | COMP_InitStruct->COMP_InvertingInput 
                        | COMP_InitStruct->COMP_OutputSelect));

  /*!< The COMP2 comparator is enabled as soon as the INSEL[2:0] bits value are 
     different from "000" */
  /*!< Write to COMP_CSR register */
  COMP->CSR = tmpreg;  
}

/**
  * @brief  Enable or disable the COMP1 peripheral.
  * @note   After enabling COMP1, the following functions should be called to 
  *         connect the selected GPIO input to COMP1 non inverting input:
  * @note   Enable switch control mode using SYSCFG_RISwitchControlModeCmd()
  * @note   Close VCOMP switch using SYSCFG_RIIOSwitchConfig()
  * @note   Close the I/O switch number n corresponding to the I/O 
  *         using SYSCFG_RIIOSwitchConfig()
  * @param  NewState: new state of the COMP1 peripheral.
  *         This parameter can be: ENABLE or DISABLE.
  * @note   This function enables/disables only the COMP1.
  * @retval None
  */
void COMP_Cmd(FunctionalState NewState)
{
  /* Check the parameter */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the COMP1 */
    COMP->CSR |= (uint32_t) COMP_CSR_CMP1EN;
  }
  else
  {
    /* Disable the COMP1  */
    COMP->CSR &= (uint32_t)(~COMP_CSR_CMP1EN);
  }
}

/**
  * @brief  Return the output level (high or low) of the selected comparator.
  * @note   Comparator output is low when the noninverting input is at a lower
  *         voltage than the inverting input.
  * @note   Comparator output is high when the noninverting input is at a higher
  *         voltage than the inverting input.
  * @note   Comparators outputs aren't available on GPIO (outputs levels are 
  *         only internal). The COMP1 and COMP2 outputs are connected internally 
  *         to the EXTI Line 21 and Line 22 respectively.
  * @param  COMP_Selection: the selected comparator.
  *   This parameter can be one of the following values:
  *     @arg COMP_Selection_COMP1: COMP1 selected
  *     @arg COMP_Selection_COMP2: COMP2 selected
  * @retval Returns the selected comparator output level.
  */
uint8_t COMP_GetOutputLevel(uint32_t COMP_Selection)
{
  uint8_t compout = 0x0;

  /* Check the parameters */
  assert_param(IS_COMP_ALL_PERIPH(COMP_Selection));

  /* Check if Comparator 1 is selected */
  if(COMP_Selection == COMP_Selection_COMP1)
  {
    /* Check if comparator 1 output level is high */
    if((COMP->CSR & COMP_CSR_CMP1OUT) != (uint8_t) RESET)
    {
      /* Get Comparator 1 output level */
      compout = (uint8_t) COMP_OutputLevel_High;
    }
    /* comparator 1 output level is low */
    else
    {
      /* Get Comparator 1 output level */
      compout = (uint8_t) COMP_OutputLevel_Low;
    }
  }
  /* Comparator 2 is selected */
  else
  {
    /* Check if comparator 2 output level is high */
    if((COMP->CSR & COMP_CSR_CMP2OUT) != (uint8_t) RESET)
    {
      /* Get Comparator output level */
      compout = (uint8_t) COMP_OutputLevel_High;
    }
    /* comparator 2 output level is low */
    else
    {
      /* Get Comparator 2 output level */
      compout = (uint8_t) COMP_OutputLevel_Low;
    }
  }
  /* Return the comparator output level */
  return (uint8_t)(compout);
}

/**
  * @brief  Close or Open the SW1 switch.
  * @param  NewState: new state of the SW1 switch.
  *         This parameter can be: ENABLE or DISABLE.
  * @note   ENABLE to close the SW1 switch
  * @note   DISABLE to open the SW1 switch
  * @retval None.
  */
void COMP_SW1SwitchConfig(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Close SW1 switch */
    COMP->CSR |= (uint32_t) COMP_CSR_SW1;
  }
  else
  {
    /* Open SW1 switch */
    COMP->CSR &= (uint32_t)(~COMP_CSR_SW1);
  }
}

/**
  * @}
  */

/** @defgroup COMP_Group2 Window mode control function
 *  @brief   Window mode control function.
 *
@verbatim
 ===============================================================================
                  ##### Window mode control function #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Enables or disables the window mode.
  *         In window mode:
  * @note   COMP1 inverting input is fixed to VREFINT defining the first
  *         threshold.
  * @note   COMP2 inverting input is configurable (DAC_OUT1, DAC_OUT2, VREFINT
  *         sub-multiples, PB3) defining the second threshold.
  * @note   COMP1 and COMP2 non inverting inputs are connected together.
  * @note   In window mode, only the Group 6 (PB4 or PB5) can be used as
  *         noninverting inputs.
  * @param   NewState: new state of the window mode. 
  *   This parameter can be ENABLE or DISABLE.
  * @retval None
  */
void COMP_WindowCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Enable the window mode */
    COMP->CSR |= (uint32_t) COMP_CSR_WNDWE;
  }
  else
  {
    /* Disable the window mode */
    COMP->CSR &= (uint32_t)(~COMP_CSR_WNDWE);
  }
}

/**
  * @}
  */

/** @defgroup COMP_Group3 Internal Reference Voltage output function
 *  @brief   Internal Reference Voltage (VREFINT) output function.
 *
@verbatim
 ===============================================================================
      ##### Internal Reference Voltage (VREFINT) output function #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Enables or disables the output of internal reference voltage (VREFINT).
  *         The VREFINT output can be routed to any I/O in group 3: CH8 (PB0) or
  *         CH9 (PB1).
  *         To correctly use this function, the SYSCFG_RIIOSwitchConfig() function
  *         should be called after.
  * @param  NewState: new state of the Vrefint output.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void COMP_VrefintOutputCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the output of internal reference voltage */
    COMP->CSR |= (uint32_t) COMP_CSR_VREFOUTEN;
  }
  else
  {
    /* Disable the output of internal reference voltage */
    COMP->CSR &= (uint32_t) (~COMP_CSR_VREFOUTEN);
  }
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

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
