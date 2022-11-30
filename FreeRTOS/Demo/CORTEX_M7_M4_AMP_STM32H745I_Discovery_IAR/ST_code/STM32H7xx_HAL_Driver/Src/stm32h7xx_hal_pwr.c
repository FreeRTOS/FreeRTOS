/**
  ******************************************************************************
  * @file    stm32h7xx_hal_pwr.c
  * @author  MCD Application Team
  * @brief   PWR HAL module driver.
  *          This file provides firmware functions to manage the following
  *          functionalities of the Power Controller (PWR) peripheral:
  *           + Initialization and de-initialization functions
  *           + Peripheral Control functions
  *
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT(c) 2017 STMicroelectronics.
  * All rights reserved.</center></h2>
  *
  * This software component is licensed by ST under BSD 3-Clause license,
  * the "License"; You may not use this file except in compliance with the
  * License. You may obtain a copy of the License at:
  *                        opensource.org/licenses/BSD-3-Clause
  *
  ******************************************************************************
  */

/* Includes ------------------------------------------------------------------*/
#include "stm32h7xx_hal.h"

/** @addtogroup STM32H7xx_HAL_Driver
  * @{
  */

/** @defgroup PWR PWR
  * @brief PWR HAL module driver
  * @{
  */

#ifdef HAL_PWR_MODULE_ENABLED

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/** @addtogroup PWR_Private_Constants PWR Private Constants
  * @{
  */

/** @defgroup PWR_PVD_Mode_Mask PWR PVD Mode Mask
  * @{
  */
#if !defined (DUAL_CORE)
#define PVD_MODE_IT              ((uint32_t)0x00010000U)
#define PVD_MODE_EVT             ((uint32_t)0x00020000U)
#endif /* DUAL_CORE */
#define PVD_RISING_EDGE          ((uint32_t)0x00000001U)
#define PVD_FALLING_EDGE         ((uint32_t)0x00000002U)
#define PVD_RISING_FALLING_EDGE  ((uint32_t)0x00000003U)
/**
  * @}
  */

/**
  * @}
  */
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/** @defgroup PWR_Exported_Functions PWR Exported Functions
  * @{
  */

/** @defgroup PWR_Exported_Functions_Group1 Initialization and De-Initialization functions
  *  @brief    Initialization and De-Initialization functions
  *
@verbatim
 ===============================================================================
              ##### Initialization and De-Initialization functions #####
 ===============================================================================
    [..]
      After reset, the backup domain (RTC registers, RTC backup data
      registers and backup SRAM) is protected against possible unwanted
      write accesses.
      To enable access to the RTC Domain and RTC registers, proceed as follows:
        (+) Enable the Power Controller (PWR) APB1 interface clock using the
            __HAL_RCC_PWR_CLK_ENABLE() macro.
        (+) Enable access to RTC domain using the HAL_PWR_EnableBkUpAccess() function.

@endverbatim
  * @{
  */

/**
  * @brief  Deinitialize the HAL PWR peripheral registers to their default reset values.
  * @note   This functionality is not available in this product.
  *         The prototype is kept just to maintain compatibility with other products.
  * @retval None
  */
void HAL_PWR_DeInit(void)
{
}

/**
  * @brief  Enable access to the backup domain (RTC registers, RTC
  *         backup data registers and backup SRAM).
  * @note   If the HSE divided by 2, 3, ..31 is used as the RTC clock, the
  *         Backup Domain Access should be kept enabled.
  * @retval None
  */
void HAL_PWR_EnableBkUpAccess(void)
{
  /* Enable access to RTC and backup registers */
  SET_BIT(PWR->CR1, PWR_CR1_DBP);
}

/**
  * @brief  Disable access to the backup domain (RTC registers, RTC
  *         backup data registers and backup SRAM).
  * @note   If the HSE divided by 2, 3, ..31 is used as the RTC clock, the
  *         Backup Domain Access should be kept enabled.
  * @retval None
  */
void HAL_PWR_DisableBkUpAccess(void)
{
  /* Disable access to RTC and backup registers */
  CLEAR_BIT(PWR->CR1, PWR_CR1_DBP);
}

/**
  * @}
  */

/** @defgroup PWR_Exported_Functions_Group2 Peripheral Control functions
  *  @brief   Low Power modes configuration functions
  *
@verbatim

 ===============================================================================
                 ##### Peripheral Control functions #####
 ===============================================================================

    *** PVD configuration ***
    =========================
    [..]
      (+) The PVD is used to monitor the VDD power supply by comparing it to a
          threshold selected by the PVD Level (PLS[7:0] bits in the PWR_CR1 register).
      (+) A PVDO flag is available to indicate if VDD is higher or lower
          than the PVD threshold. This event is internally connected to the EXTI
          line 16 to generate an interrupt if enabled.
          It is configurable through __HAL_PWR_PVD_EXTI_ENABLE_IT() macro.
      (+) The PVD is stopped in Standby mode.

    *** Wake-up pin configuration ***
    ================================
    [..]
      (+) Wake-up pin is used to wake up the system from Standby mode.
          The pin pull is configurable through the WKUPEPR register to be in No pull-up, Pull-up and Pull-down.
          The pin polarity is configurable through the WKUPEPR register to be active on rising or falling edges.
      (+) There are up to six Wake-up pin in the STM32H7 devices family.

    *** Low Power modes configuration ***
    =====================================
    [..]
     The device present 3 principles low-power modes features:
      (+) SLEEP mode: Cortex-M7 core stopped and D1, D2 and D3 peripherals kept running.
      (+) STOP mode: all clocks are stopped and the regulator is running in main or low power mode.
      (+) STANDBY mode: D1, D2 and D3 domains enter DSTANDBY mode and the VCORE supply
                        regulator is powered off.

   *** SLEEP mode ***
   ==================
    [..]
      (+) Entry:
        The Sleep mode is entered by using the HAL_PWR_EnterSLEEPMode(Regulator, SLEEPEntry)
        function.

          (++) PWR_SLEEPENTRY_WFI: enter SLEEP mode with WFI instruction
          (++) PWR_SLEEPENTRY_WFE: enter SLEEP mode with WFE instruction

      -@@- The Regulator parameter is not used for the STM32H7 family
              and is kept as parameter just to maintain compatibility with the
              lower power families (STM32L).
      (+) Exit:
        Any peripheral interrupt acknowledged by the nested vectored interrupt
        controller (NVIC) can wake up the device from Sleep mode.

   *** STOP mode ***
   =================
    [..]
      In system Stop mode, all clocks in the 1.2V domain are stopped, the PLL, the HSI,
      and the HSE RC oscillators are disabled. Internal SRAM and register contents
      are preserved.
      The voltage regulator can be configured either in normal or low-power mode.
      To minimize the consumption In Stop mode, FLASH can be powered off before
      entering the Stop mode using the HAL_PWREx_EnableFlashPowerDown() function.
      It can be switched on again by software after exiting the Stop mode using
      the HAL_PWREx_DisableFlashPowerDown() function.

      (+) Entry:
         The Stop mode is entered using the HAL_PWR_EnterSTOPMode(Regulator, STOPEntry)
         function with:
         (++) Regulator:
          (+++) PWR_MAINREGULATOR_ON: Main regulator ON.
          (+++) PWR_LOWPOWERREGULATOR_ON: Low Power regulator ON.
         (++) STOPEntry:
          (+++) PWR_STOPENTRY_WFI: enter STOP mode with WFI instruction
          (+++) PWR_STOPENTRY_WFE: enter STOP mode with WFE instruction
      (+) Exit:
        Any EXTI Line (Internal or External) configured in Interrupt/Event mode.

   *** STANDBY mode ***
   ====================
    [..]
    (+)
      The system Standby mode allows to achieve the lowest power consumption. It is based
      on the Cortex-M7 deep sleep mode, with the voltage regulator disabled.
      The system is consequently powered off. The PLL, the HSI oscillator and
      the HSE oscillator are also switched off. SRAM and register contents are lost
      except for the RTC registers, RTC backup registers, backup SRAM and Standby
      circuitry.
    [..]
      The voltage regulator is OFF.
      (++) Entry:
        (+++) The Standby mode is entered using the HAL_PWR_EnterSTANDBYMode() function.
      (++) Exit:
        (+++) WKUP pin rising or falling edge, RTC alarm (Alarm A and Alarm B), RTC
              wakeup, tamper event, time stamp event, external reset in NRST pin, IWDG reset.

   *** Auto-wakeup (AWU) from low-power mode ***
   =============================================
    [..]
     (+) The MCU can be woken up from low-power mode by an RTC Alarm event, an RTC
      Wakeup event, a tamper event or a time-stamp event, without depending on
      an external interrupt (Auto-wakeup mode).
     (+) RTC auto-wakeup (AWU) from the STOP and STANDBY modes
       (++) To wake up from the Stop mode with an RTC alarm event, it is necessary to
            configure the RTC to generate the RTC alarm using the HAL_RTC_SetAlarm_IT() function.
       (++) To wake up from the Stop mode with an RTC Tamper or time stamp event, it
            is necessary to configure the RTC to detect the tamper or time stamp event using the
            HAL_RTCEx_SetTimeStamp_IT() or HAL_RTCEx_SetTamper_IT() functions.
       (++) To wake up from the Stop mode with an RTC WakeUp event, it is necessary to
            configure the RTC to generate the RTC WakeUp event using the HAL_RTCEx_SetWakeUpTimer_IT() function.

@endverbatim
  * @{
  */

/**
  * @brief  Configure the voltage threshold detected by the Power Voltage Detector(PVD).
  * @param  sConfigPVD: pointer to an PWR_PVDTypeDef structure that contains the configuration
  *         information for the PVD.
  * @note   Refer to the electrical characteristics of your device datasheet for
  *         more details about the voltage threshold corresponding to each
  *         detection level.
  * @retval None
  */
void HAL_PWR_ConfigPVD(PWR_PVDTypeDef *sConfigPVD)
{
  /* Check the parameters */
  assert_param(IS_PWR_PVD_LEVEL(sConfigPVD->PVDLevel));
  assert_param(IS_PWR_PVD_MODE(sConfigPVD->Mode));

  /* Set PLS[7:5] bits according to PVDLevel value */
  MODIFY_REG(PWR->CR1, PWR_CR1_PLS, sConfigPVD->PVDLevel);

  /* Clear any previous config */
#if !defined (DUAL_CORE)
  __HAL_PWR_PVD_EXTI_DISABLE_EVENT();
  __HAL_PWR_PVD_EXTI_DISABLE_IT();
#endif /* DUAL_CORE */
  __HAL_PWR_PVD_EXTI_DISABLE_RISING_EDGE();
  __HAL_PWR_PVD_EXTI_DISABLE_FALLING_EDGE();

#if !defined (DUAL_CORE)
  /* Configure interrupt mode */
  if((sConfigPVD->Mode & PVD_MODE_IT) == PVD_MODE_IT)
  {
    __HAL_PWR_PVD_EXTI_ENABLE_IT();
  }

  /* Configure event mode */
  if((sConfigPVD->Mode & PVD_MODE_EVT) == PVD_MODE_EVT)
  {
    __HAL_PWR_PVD_EXTI_ENABLE_EVENT();
  }
#endif /* DUAL_CORE */

  /* Configure the edge */
  if((sConfigPVD->Mode & PVD_RISING_EDGE) == PVD_RISING_EDGE)
  {
    __HAL_PWR_PVD_EXTI_ENABLE_RISING_EDGE();
  }

  if((sConfigPVD->Mode & PVD_FALLING_EDGE) == PVD_FALLING_EDGE)
  {
    __HAL_PWR_PVD_EXTI_ENABLE_FALLING_EDGE();
  }
}

/**
  * @brief  Enable the Power Voltage Detector(PVD).
  * @retval None
  */
void HAL_PWR_EnablePVD(void)
{
  /* Enable the power voltage detector */
  SET_BIT(PWR->CR1, PWR_CR1_PVDEN);
}

/**
  * @brief  Disable the Power Voltage Detector(PVD).
  * @retval None
  */
void HAL_PWR_DisablePVD(void)
{
  /* Disable the power voltage detector */
  CLEAR_BIT(PWR->CR1, PWR_CR1_PVDEN);
}

/**
  * @brief  Enable the WakeUp PINx functionality.
  * @param  WakeUpPinPolarity: Specifies which Wake-Up pin to enable.
  *          This parameter can be one of the following legacy values, which sets the default:
  *          polarity detection on high level (rising edge):
  *            @arg PWR_WAKEUP_PIN1, PWR_WAKEUP_PIN2, PWR_WAKEUP_PIN3, PWR_WAKEUP_PIN4,
  *                 PWR_WAKEUP_PIN5, PWR_WAKEUP_PIN6 or one of the following values where
  *                 the user can explicitly states the enabled pin and the chosen polarity.
  *            @arg PWR_WAKEUP_PIN1_HIGH or PWR_WAKEUP_PIN1_LOW
  *            @arg PWR_WAKEUP_PIN2_HIGH or PWR_WAKEUP_PIN2_LOW
  *            @arg PWR_WAKEUP_PIN3_HIGH or PWR_WAKEUP_PIN3_LOW
  *            @arg PWR_WAKEUP_PIN4_HIGH or PWR_WAKEUP_PIN4_LOW
  *            @arg PWR_WAKEUP_PIN5_HIGH or PWR_WAKEUP_PIN5_LOW
  *            @arg PWR_WAKEUP_PIN6_HIGH or PWR_WAKEUP_PIN6_LOW
  * @note   PWR_WAKEUP_PINx and PWR_WAKEUP_PINx_HIGH are equivalent.
  * @retval None
  */
void HAL_PWR_EnableWakeUpPin(uint32_t WakeUpPinPolarity)
{
  assert_param(IS_PWR_WAKEUP_PIN(WakeUpPinPolarity));

  /* Enable and Specify the Wake-Up pin polarity and the pull configuration
     for the event detection (rising or falling edge) */
  MODIFY_REG(PWR->WKUPEPR, PWR_EWUP_MASK, WakeUpPinPolarity);
}

/**
  * @brief  Disable the WakeUp PINx functionality.
  * @param  WakeUpPinx: Specifies the Power Wake-Up pin to disable.
  *          This parameter can be one of the following values:
  *            @arg PWR_WAKEUP_PIN1
  *            @arg PWR_WAKEUP_PIN2
  *            @arg PWR_WAKEUP_PIN3
  *            @arg PWR_WAKEUP_PIN4
  *            @arg PWR_WAKEUP_PIN5
  *            @arg PWR_WAKEUP_PIN6
  * @retval None
  */
void HAL_PWR_DisableWakeUpPin(uint32_t WakeUpPinx)
{
  assert_param(IS_PWR_WAKEUP_PIN(WakeUpPinx));

  CLEAR_BIT(PWR->WKUPEPR, (PWR_WKUPEPR_WKUPEN & WakeUpPinx));
}

/**
  * @brief  Enter the current core to Sleep mode.
  * @param  Regulator: Specifies the regulator state in SLEEP mode.
  *          This parameter can be one of the following values:
  *            @arg PWR_MAINREGULATOR_ON: SLEEP mode with regulator ON
  *            @arg PWR_LOWPOWERREGULATOR_ON: SLEEP mode with low power regulator ON
  * @note   This parameter is not used for the STM32H7 family and is kept as parameter
  *         just to maintain compatibility with the lower power families.
  * @param  SLEEPEntry: Specifies if SLEEP mode in entered with WFI or WFE instruction.
  *          This parameter can be one of the following values:
  *            @arg PWR_SLEEPENTRY_WFI: enter SLEEP mode with WFI instruction
  *            @arg PWR_SLEEPENTRY_WFE: enter SLEEP mode with WFE instruction
  * @retval None
  */
void HAL_PWR_EnterSLEEPMode(uint32_t Regulator, uint8_t SLEEPEntry)
{
  /* Check the parameters */
  assert_param(IS_PWR_REGULATOR(Regulator));
  assert_param(IS_PWR_SLEEP_ENTRY(SLEEPEntry));

  /* Clear SLEEPDEEP bit of Cortex System Control Register */
  CLEAR_BIT(SCB->SCR, ((uint32_t)SCB_SCR_SLEEPDEEP_Msk));

  /* Select SLEEP mode entry */
  if(SLEEPEntry == PWR_SLEEPENTRY_WFI)
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
  * @brief  Enter the system to STOP mode.
  * @note   This API must be used only for single core devices.
  * @note   In System Stop mode, all I/O pins keep the same state as in Run mode.
  * @note   When exiting System Stop mode by issuing an interrupt or a wakeup event,
  *         the HSI RC oscillator is selected as default system wakeup clock.
  * @note   In System STOP mode, when the voltage regulator operates in low power mode,
  *         an additional startup delay is incurred when the system is waking up.
  *         By keeping the internal regulator ON during Stop mode, the consumption
  *         is higher although the startup time is reduced.
  * @param  Regulator: Specifies the regulator state in Stop mode.
  *          This parameter can be one of the following values:
  *            @arg PWR_MAINREGULATOR_ON: Stop mode with regulator ON
  *            @arg PWR_LOWPOWERREGULATOR_ON: Stop mode with low power regulator ON
  * @param  STOPEntry: Specifies if Stop mode in entered with WFI or WFE instruction.
  *          This parameter can be one of the following values:
  *            @arg PWR_STOPENTRY_WFI: Enter Stop mode with WFI instruction
  *            @arg PWR_STOPENTRY_WFE: Enter Stop mode with WFE instruction
  * @retval None
  */
void HAL_PWR_EnterSTOPMode(uint32_t Regulator, uint8_t STOPEntry)
{
  uint32_t tmpreg;

  /* Check the parameters */
  assert_param(IS_PWR_REGULATOR(Regulator));
  assert_param(IS_PWR_STOP_ENTRY(STOPEntry));

  /* Select the regulator state in Stop mode */
  tmpreg = PWR->CR1;
  /* Clear PDDS and LPDS bits */
  tmpreg &= (uint32_t)~(PWR_CR1_LPDS);

  /* Set LPDS bit according to Regulator value */
  tmpreg |= Regulator;

  /* Store the new value */
  PWR->CR1 = tmpreg;

#if defined(DUAL_CORE)
  /* Keep DSTOP mode when D1 domain enters Deepsleep */
  CLEAR_BIT(PWR->CPUCR, PWR_CPUCR_PDDS_D1);
  CLEAR_BIT(PWR->CPU2CR, PWR_CPU2CR_PDDS_D1);
#else
  /* Keep DSTOP mode when D1 domain enters Deepsleep */
  CLEAR_BIT(PWR->CPUCR, PWR_CPUCR_PDDS_D1);

  /* Keep DSTOP mode when D2 domain enters Deepsleep */
  CLEAR_BIT(PWR->CPUCR, PWR_CPUCR_PDDS_D2);

  /* Keep DSTOP mode when D3 domain enters Deepsleep */
  CLEAR_BIT(PWR->CPUCR, PWR_CPUCR_PDDS_D3);
#endif /*DUAL_CORE*/

  /* Set SLEEPDEEP bit of Cortex System Control Register */
  SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;

  /* Ensure that all instructions done before entering STOP mode */
  __DSB();
  __ISB();

  /* Select Stop mode entry */
  if(STOPEntry == PWR_STOPENTRY_WFI)
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
  SCB->SCR &= (uint32_t)~((uint32_t)SCB_SCR_SLEEPDEEP_Msk);
}

/**
  * @brief  Enter the system to STANDBY mode.
  * @note   The system enters Standby mode only when the D1, D2 and D3 domains are in DStandby.
  * @note   When the System exit STANDBY mode by issuing an interrupt or a wakeup event,
  *         the HSI RC oscillator is selected as system clock.
  * @retval None.
  */
void HAL_PWR_EnterSTANDBYMode(void)
{
#if defined(DUAL_CORE)
  /* Keep DSTANDBY mode when D1 domain enters Deepsleep */
  SET_BIT(PWR->CPUCR, PWR_CPUCR_PDDS_D1);
  SET_BIT(PWR->CPU2CR, PWR_CPU2CR_PDDS_D1);
#else
  /* Keep DSTANDBY mode when D1 domain enters Deepsleep */
  SET_BIT(PWR->CPUCR, PWR_CPUCR_PDDS_D1);

  /* Keep DSTANDBY mode when D2 domain enters Deepsleep */
  SET_BIT(PWR->CPUCR, PWR_CPUCR_PDDS_D2);

  /* Keep DSTANDBY mode when D3 domain enters Deepsleep */
  SET_BIT(PWR->CPUCR, PWR_CPUCR_PDDS_D3);
#endif /*DUAL_CORE*/

  /* Set SLEEPDEEP bit of Cortex System Control Register */
  SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;

  /* This option is used to ensure that store operations are completed */
#if defined ( __CC_ARM)
  __force_stores();
#endif
  /* Request Wait For Interrupt */
  __WFI();
}

/**
  * @brief  Indicate Sleep-On-Exit when returning from Handler mode to Thread mode.
  * @note   Set SLEEPONEXIT bit of SCR register. When this bit is set, the processor
  *         re-enters SLEEP mode when an interruption handling is over.
  *         Setting this bit is useful when the processor is expected to run only on
  *         interruptions handling.
  * @retval None
  */
void HAL_PWR_EnableSleepOnExit(void)
{
  /* Set SLEEPONEXIT bit of Cortex System Control Register */
  SET_BIT(SCB->SCR, ((uint32_t)SCB_SCR_SLEEPONEXIT_Msk));
}


/**
  * @brief  Disable Sleep-On-Exit feature when returning from Handler mode to Thread mode.
  * @note   Clears SLEEPONEXIT bit of SCR register. When this bit is set, the processor
  *         re-enters SLEEP mode when an interruption handling is over.
  * @retval None
  */
void HAL_PWR_DisableSleepOnExit(void)
{
  /* Clear SLEEPONEXIT bit of Cortex System Control Register */
  CLEAR_BIT(SCB->SCR, ((uint32_t)SCB_SCR_SLEEPONEXIT_Msk));
}

/**
  * @brief  Enable CORTEX SEVONPEND bit.
  * @note   Sets SEVONPEND bit of SCR register. When this bit is set, this causes
  *         WFE to wake up when an interrupt moves from inactive to pended.
  * @retval None
  */
void HAL_PWR_EnableSEVOnPend(void)
{
  /* Set SEVONPEND bit of Cortex System Control Register */
  SET_BIT(SCB->SCR, ((uint32_t)SCB_SCR_SEVONPEND_Msk));
}

/**
  * @brief  Disable CORTEX SEVONPEND bit.
  * @note   Clears SEVONPEND bit of SCR register. When this bit is set, this causes
  *         WFE to wake up when an interrupt moves from inactive to pended.
  * @retval None
  */
void HAL_PWR_DisableSEVOnPend(void)
{
  /* Clear SEVONPEND bit of Cortex System Control Register */
  CLEAR_BIT(SCB->SCR, ((uint32_t)SCB_SCR_SEVONPEND_Msk));
}

/**
  * @brief  This function handles the PWR PVD interrupt request.
  * @note   This API should be called under the PVD_IRQHandler().
  * @retval None
  */
void HAL_PWR_PVD_IRQHandler(void)
{
#if defined(DUAL_CORE)
  /* PVD EXTI line interrupt detected */
  if (HAL_GetCurrentCPUID() == CM7_CPUID)
  {
    /* Check PWR EXTI flag */
    if(__HAL_PWR_PVD_EXTI_GET_FLAG() != RESET)
    {
      /* PWR PVD interrupt user callback */
      HAL_PWR_PVDCallback();

      /* Clear PWR EXTI pending bit */
      __HAL_PWR_PVD_EXTI_CLEAR_FLAG();
    }
  }
  else
  {
    /* Check PWR EXTI D2 flag */
    if(__HAL_PWR_PVD_EXTID2_GET_FLAG() != RESET)
    {
      /* PWR PVD interrupt user callback */
      HAL_PWR_PVDCallback();

      /* Clear PWR EXTI D2 pending bit */
      __HAL_PWR_PVD_EXTID2_CLEAR_FLAG();
    }
  }
#else
  /* PVD EXTI line interrupt detected */
  if(__HAL_PWR_PVD_EXTI_GET_FLAG() != RESET)
  {
    /* PWR PVD interrupt user callback */
    HAL_PWR_PVDCallback();

    /* Clear PWR EXTI pending bit */
    __HAL_PWR_PVD_EXTI_CLEAR_FLAG();
  }
#endif /*DUAL_CORE*/
}

/**
  * @brief  PWR PVD interrupt callback
  * @retval None
  */
__weak void HAL_PWR_PVDCallback(void)
{
  /* NOTE : This function Should not be modified, when the callback is needed,
            the HAL_PWR_PVDCallback could be implemented in the user file
  */
}

/**
  * @}
  */

/**
  * @}
  */

#endif /* HAL_PWR_MODULE_ENABLED */
/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
