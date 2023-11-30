/**
  ******************************************************************************
  * @file    stm32l1xx_pwr.c
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    07/02/2010
  * @brief   This file provides all the PWR firmware functions.
  ******************************************************************************
  * @copy
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2010 STMicroelectronics</center></h2>
  */ 

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx_pwr.h"
#include "stm32l1xx_rcc.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup PWR 
  * @brief PWR driver modules
  * @{
  */ 

/** @defgroup PWR_Private_TypesDefinitions
  * @{
  */

/**
  * @}
  */

/** @defgroup PWR_Private_Defines
  * @{
  */

/* --------- PWR registers bit address in the alias region ---------- */
#define PWR_OFFSET               (PWR_BASE - PERIPH_BASE)

/* --- CR Register ---*/

/* Alias word address of DBP bit */
#define CR_OFFSET                (PWR_OFFSET + 0x00)
#define DBP_BitNumber            0x08
#define CR_DBP_BB                (PERIPH_BB_BASE + (CR_OFFSET * 32) + (DBP_BitNumber * 4))

/* Alias word address of PVDE bit */
#define PVDE_BitNumber           0x04
#define CR_PVDE_BB               (PERIPH_BB_BASE + (CR_OFFSET * 32) + (PVDE_BitNumber * 4))

/* Alias word address of ULP bit */
#define ULP_BitNumber           0x09
#define CR_ULP_BB               (PERIPH_BB_BASE + (CR_OFFSET * 32) + (ULP_BitNumber * 4))

/* Alias word address of FWU bit */
#define FWU_BitNumber           0x0A
#define CR_FWU_BB               (PERIPH_BB_BASE + (CR_OFFSET * 32) + (FWU_BitNumber * 4))

/* --- CSR Register ---*/

/* Alias word address of EWUP bit */
#define CSR_OFFSET               (PWR_OFFSET + 0x04)
#define EWUP_BitNumber           0x08
#define CSR_EWUP_BB              (PERIPH_BB_BASE + (CSR_OFFSET * 32) + (EWUP_BitNumber * 4))

/* ------------------ PWR registers bit mask ------------------------ */

/* CR register bit mask */
#define CR_DS_MASK               ((uint32_t)0xFFFFFFFC)
#define CR_PLS_MASK              ((uint32_t)0xFFFFFF1F)
#define CR_VOS_MASK              ((uint32_t)0xFFFFE7FF)

/**
  * @}
  */

/** @defgroup PWR_Private_Macros
  * @{
  */

/**
  * @}
  */

/** @defgroup PWR_Private_Variables
  * @{
  */

/**
  * @}
  */

/** @defgroup PWR_Private_FunctionPrototypes
  * @{
  */

/**
  * @}
  */

/** @defgroup PWR_Private_Functions
  * @{
  */

/**
  * @brief  Deinitializes the PWR peripheral registers to their default reset values.
  * @param  None
  * @retval None
  */
void PWR_DeInit(void)
{
  RCC_APB1PeriphResetCmd(RCC_APB1Periph_PWR, ENABLE);
  RCC_APB1PeriphResetCmd(RCC_APB1Periph_PWR, DISABLE);
}

/**
  * @brief  Enables or disables access to the RTC and backup registers.
  * @param  NewState: new state of the access to the RTC and backup registers.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void PWR_RTCAccessCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  *(__IO uint32_t *) CR_DBP_BB = (uint32_t)NewState;
}

/**
  * @brief  Enables or disables the Power Voltage Detector(PVD).
  * @param  NewState: new state of the PVD.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void PWR_PVDCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  *(__IO uint32_t *) CR_PVDE_BB = (uint32_t)NewState;
}

/**
  * @brief  Configures the voltage threshold detected by the Power Voltage Detector(PVD).
  * @param  PWR_PVDLevel: specifies the PVD detection level
  *   This parameter can be one of the following values:
  *     @arg PWR_PVDLevel_0: PVD detection level set to 1.9V
  *     @arg PWR_PVDLevel_1: PVD detection level set to 2.1V
  *     @arg PWR_PVDLevel_2: PVD detection level set to 2.3V
  *     @arg PWR_PVDLevel_3: PVD detection level set to 2.5V
  *     @arg PWR_PVDLevel_4: PVD detection level set to 2.7V
  *     @arg PWR_PVDLevel_5: PVD detection level set to 2.9V
  *     @arg PWR_PVDLevel_6: PVD detection level set to 3.1V
  *     @arg PWR_PVDLevel_7: External input analog voltage (Compare internally to VREFINT)
  * @retval None
  */
void PWR_PVDLevelConfig(uint32_t PWR_PVDLevel)
{
  uint32_t tmpreg = 0;
  
  /* Check the parameters */
  assert_param(IS_PWR_PVD_LEVEL(PWR_PVDLevel));
  
  tmpreg = PWR->CR;
  
  /* Clear PLS[7:5] bits */
  tmpreg &= CR_PLS_MASK;
  
  /* Set PLS[7:5] bits according to PWR_PVDLevel value */
  tmpreg |= PWR_PVDLevel;
  
  /* Store the new value */
  PWR->CR = tmpreg;
}

/**
  * @brief  Enables or disables the WakeUp Pin functionality.
  * @param  PWR_WakeUpPin: specifies the WakeUpPin.
  *   This parameter can be: PWR_WakeUpPin_1, PWR_WakeUpPin_2 or PWR_WakeUpPin_3.
  * @param  NewState: new state of the WakeUp Pin functionality.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void PWR_WakeUpPinCmd(uint32_t PWR_WakeUpPin, FunctionalState NewState)
{
  __IO uint32_t tmp = 0;
  
  /* Check the parameters */
  assert_param(IS_PWR_WAKEUP_PIN(PWR_WakeUpPin));
  
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  tmp = CSR_EWUP_BB + PWR_WakeUpPin;
  
  *(__IO uint32_t *) (tmp) = (uint32_t)NewState;
}

/**
  * @brief  Enables or disables the Fast WakeUp from Ultra Low Power mode.
  * @param  NewState: new state of the Fast WakeUp  functionality.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void PWR_FastWakeUpCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CR_FWU_BB = (uint32_t)NewState;
}

/**
  * @brief  Enables or disables the Ultra Low Power mode.
  * @param  NewState: new state of the Ultra Low Power mode.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void PWR_UltraLowPowerCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CR_ULP_BB = (uint32_t)NewState;
}

/**
  * @brief  Configures the voltage scaling range.
  * @param  PWR_VoltageScaling: specifies the voltage scaling range.
  *   This parameter can be:
  *     @arg PWR_VoltageScaling_Range1: Voltage Scaling Range 1
  *     @arg PWR_VoltageScaling_Range2: Voltage Scaling Range 2
  *     @arg PWR_VoltageScaling_Range3: Voltage Scaling Range 3      
  * @retval None
  */
void PWR_VoltageScalingConfig(uint32_t PWR_VoltageScaling)
{
  uint32_t tmp = 0;
  
  /* Check the parameters */
  assert_param(IS_PWR_VOLTAGE_SCALING_RANGE(PWR_VoltageScaling));
  
  tmp = PWR->CR;

  tmp &= CR_VOS_MASK;
  tmp |= PWR_VoltageScaling;
  
  PWR->CR = tmp & 0xFFFFFFF3;

}

/**
  * @brief  Enters/Exits the Low Power Run mode.
  * @param  NewState: new state of the Low Power Run mode.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void PWR_EnterLowPowerRunMode(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    PWR->CR |= PWR_CR_LPSDSR;
    PWR->CR |= PWR_CR_LPRUN;     
  }
  else
  {
    PWR->CR &= (uint32_t)~((uint32_t)PWR_CR_LPRUN); 
    PWR->CR &= (uint32_t)~((uint32_t)PWR_CR_LPSDSR);  
  }  
}

/**
  * @brief  Enters Sleep mode.
  * @param  PWR_Regulator: specifies the regulator state in Sleep mode.
  *   This parameter can be one of the following values:
  *     @arg PWR_Regulator_ON: Sleep mode with regulator ON
  *     @arg PWR_Regulator_LowPower: Sleep mode with regulator in low power mode
  * @param  PWR_SLEEPEntry: specifies if SLEEP mode in entered with WFI or WFE instruction.
  *   This parameter can be one of the following values:
  *     @arg PWR_SLEEPEntry_WFI: enter SLEEP mode with WFI instruction
  *     @arg PWR_SLEEPEntry_WFE: enter SLEEP mode with WFE instruction
  * @retval None
  */
void PWR_EnterSleepMode(uint32_t PWR_Regulator, uint8_t PWR_SLEEPEntry)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_PWR_REGULATOR(PWR_Regulator));

  assert_param(IS_PWR_SLEEP_ENTRY(PWR_SLEEPEntry));
  
  /* Select the regulator state in Sleep mode ---------------------------------*/
  tmpreg = PWR->CR;
  
  /* Clear PDDS and LPDSR bits */
  tmpreg &= CR_DS_MASK;
  
  /* Set LPDSR bit according to PWR_Regulator value */
  tmpreg |= PWR_Regulator;
  
  /* Store the new value */
  PWR->CR = tmpreg;

  /* Clear SLEEPDEEP bit of Cortex System Control Register */
  SCB->SCR &= (uint32_t)~((uint32_t)SCB_SCR_SLEEPDEEP);
  
  /* Select SLEEP mode entry -------------------------------------------------*/
  if(PWR_SLEEPEntry == PWR_SLEEPEntry_WFI)
  {   
    /* Request Wait For Interrupt */
    __WFI();
  }
  else
  {
    /* Request Wait For Event */
    __WFE();
  }
}

/**
  * @brief  Enters STOP mode.
  * @param  PWR_Regulator: specifies the regulator state in STOP mode.
  *   This parameter can be one of the following values:
  *     @arg PWR_Regulator_ON: STOP mode with regulator ON
  *     @arg PWR_Regulator_LowPower: STOP mode with regulator in low power mode
  * @param  PWR_STOPEntry: specifies if STOP mode in entered with WFI or WFE instruction.
  *   This parameter can be one of the following values:
  *     @arg PWR_STOPEntry_WFI: enter STOP mode with WFI instruction
  *     @arg PWR_STOPEntry_WFE: enter STOP mode with WFE instruction
  * @retval None
  */
void PWR_EnterSTOPMode(uint32_t PWR_Regulator, uint8_t PWR_STOPEntry)
{
  uint32_t tmpreg = 0;
  
  /* Check the parameters */
  assert_param(IS_PWR_REGULATOR(PWR_Regulator));
  assert_param(IS_PWR_STOP_ENTRY(PWR_STOPEntry));
  
  /* Select the regulator state in STOP mode ---------------------------------*/
  tmpreg = PWR->CR;
  /* Clear PDDS and LPDSR bits */
  tmpreg &= CR_DS_MASK;
  
  /* Set LPDSR bit according to PWR_Regulator value */
  tmpreg |= PWR_Regulator;
  
  /* Store the new value */
  PWR->CR = tmpreg;
  
  /* Set SLEEPDEEP bit of Cortex System Control Register */
  SCB->SCR |= SCB_SCR_SLEEPDEEP;
  
  /* Select STOP mode entry --------------------------------------------------*/
  if(PWR_STOPEntry == PWR_STOPEntry_WFI)
  {   
    /* Request Wait For Interrupt */
    __WFI();
  }
  else
  {
    /* Request Wait For Event */
    __WFE();
  }
  /* Reset SLEEPDEEP bit of Cortex System Control Register */
  SCB->SCR &= (uint32_t)~((uint32_t)SCB_SCR_SLEEPDEEP);  
}

/**
  * @brief  Enters STANDBY mode.
  * @param  None
  * @retval None
  */
void PWR_EnterSTANDBYMode(void)
{
  /* Clear Wake-up flag */
  PWR->CR |= PWR_CR_CWUF;
  
  /* Select STANDBY mode */
  PWR->CR |= PWR_CR_PDDS;
  
  /* Set SLEEPDEEP bit of Cortex System Control Register */
  SCB->SCR |= SCB_SCR_SLEEPDEEP;
  
/* This option is used to ensure that store operations are completed */
#if defined ( __CC_ARM   )
  __force_stores();
#endif
  /* Request Wait For Interrupt */
  __WFI();
}

/**
  * @brief  Checks whether the specified PWR flag is set or not.
  * @param  PWR_FLAG: specifies the flag to check.
  *   This parameter can be one of the following values:
  *     @arg PWR_FLAG_WU: Wake Up flag
  *     @arg PWR_FLAG_SB: StandBy flag
  *     @arg PWR_FLAG_PVDO: PVD Output
  *     @arg PWR_FLAG_VREFINTRDY: Internal Voltage Reference Ready flag
  *     @arg PWR_FLAG_VOS: Voltage Scaling select flag
  *     @arg PWR_FLAG_REGLP: Regulator LP flag        
  * @retval The new state of PWR_FLAG (SET or RESET).
  */
FlagStatus PWR_GetFlagStatus(uint32_t PWR_FLAG)
{
  FlagStatus bitstatus = RESET;
  /* Check the parameters */
  assert_param(IS_PWR_GET_FLAG(PWR_FLAG));
  
  if ((PWR->CSR & PWR_FLAG) != (uint32_t)RESET)
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  /* Return the flag status */
  return bitstatus;
}

/**
  * @brief  Clears the PWR's pending flags.
  * @param  PWR_FLAG: specifies the flag to clear.
  *   This parameter can be one of the following values:
  *     @arg PWR_FLAG_WU: Wake Up flag
  *     @arg PWR_FLAG_SB: StandBy flag
  * @retval None
  */
void PWR_ClearFlag(uint32_t PWR_FLAG)
{
  /* Check the parameters */
  assert_param(IS_PWR_CLEAR_FLAG(PWR_FLAG));
         
  PWR->CR |=  PWR_FLAG << 2;
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

/******************* (C) COPYRIGHT 2010 STMicroelectronics *****END OF FILE****/
