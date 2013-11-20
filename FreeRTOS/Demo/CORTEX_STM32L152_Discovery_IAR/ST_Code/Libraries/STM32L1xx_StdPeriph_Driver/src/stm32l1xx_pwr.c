/**
  ******************************************************************************
  * @file    stm32l1xx_pwr.c
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file provides firmware functions to manage the following 
  *          functionalities of the Power Controller (PWR) peripheral:           
  *           + RTC Domain Access
  *           + PVD configuration
  *           + WakeUp pins configuration
  *           + Ultra Low Power mode configuration
  *           + Voltage Scaling configuration
  *           + Low Power modes configuration
  *           + Flags management
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
#include "stm32l1xx_pwr.h"
#include "stm32l1xx_rcc.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup PWR 
  * @brief PWR driver modules
  * @{
  */ 

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
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

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/** @defgroup PWR_Private_Functions
  * @{
  */

/** @defgroup PWR_Group1 RTC Domain Access function 
 *  @brief   RTC Domain Access function  
 *
@verbatim   
  ============================================================================== 
                     ##### RTC Domain Access function #####
  ============================================================================== 

    [..] After reset, the RTC Registers (RCC CSR Register, RTC registers and RTC backup 
         registers) are protected against possible stray write accesses.
    [..] To enable access to RTC domain use the PWR_RTCAccessCmd(ENABLE) function.

@endverbatim
  * @{
  */

/**
  * @brief  Deinitializes the PWR peripheral registers to their default reset values.
  * @note   Before calling this function, the VOS[1:0] bits should be configured 
  *         to "10" and the system frequency has to be configured accordingly. 
  *         To configure the VOS[1:0] bits, use the PWR_VoltageScalingConfig()
  *         function.
  * @note   ULP and FWU bits are not reset by this function.    
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
  * @note   If the HSE divided by 2, 4, 8 or 16 is used as the RTC clock, the 
  *         RTC Domain Access should be kept enabled.
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
  * @}
  */

/** @defgroup PWR_Group2 PVD configuration functions
 *  @brief   PVD configuration functions 
 *
@verbatim   
  ============================================================================== 
                    ##### PVD configuration functions #####
  ==============================================================================    
  [..]
  (+) The PVD is used to monitor the VDD power supply by comparing it to a threshold
      selected by the PVD Level (PLS[2:0] bits in the PWR_CR).
  (+) The PVD can use an external input analog voltage (PVD_IN) which is compared 
      internally to VREFINT. The PVD_IN (PB7) has to be configured in Analog mode 
      when PWR_PVDLevel_7 is selected (PLS[2:0] = 111).
  (+) A PVDO flag is available to indicate if VDD/VDDA is higher or lower than the 
      PVD threshold. This event is internally connected to the EXTI line16
      and can generate an interrupt if enabled through the EXTI registers.
  (+) The PVD is stopped in Standby mode.

@endverbatim
  * @{
  */

/**
  * @brief  Configures the voltage threshold detected by the Power Voltage Detector(PVD).
  * @param  PWR_PVDLevel: specifies the PVD detection level.
  *   This parameter can be one of the following values:
  *     @arg PWR_PVDLevel_0: PVD detection level set to 1.9V.
  *     @arg PWR_PVDLevel_1: PVD detection level set to 2.1V.
  *     @arg PWR_PVDLevel_2: PVD detection level set to 2.3V.
  *     @arg PWR_PVDLevel_3: PVD detection level set to 2.5V.
  *     @arg PWR_PVDLevel_4: PVD detection level set to 2.7V.
  *     @arg PWR_PVDLevel_5: PVD detection level set to 2.9V.
  *     @arg PWR_PVDLevel_6: PVD detection level set to 3.1V.
  *     @arg PWR_PVDLevel_7: External input analog voltage (Compare internally to VREFINT).
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
  * @}
  */

/** @defgroup PWR_Group3 WakeUp pins configuration functions
 *  @brief   WakeUp pins configuration functions 
 *
@verbatim   
  ============================================================================== 
               ##### WakeUp pin configuration functions #####
  ==============================================================================   

  (+) WakeUp pins are used to wakeup the system from Standby mode. These pins are 
      forced in input pull down configuration and are active on rising edges.
  (+) There are three WakeUp pins: WakeUp Pin 1 on PA.00, WakeUp Pin 2 on PC.13 and
      WakeUp Pin 3 on PE.06.

@endverbatim
  * @{
  */

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
  * @}
  */

/** @defgroup PWR_Group4 Ultra Low Power mode configuration functions
 *  @brief   Ultra Low Power mode configuration functions 
 *
@verbatim   
  ============================================================================== 
             ##### Ultra Low Power mode configuration functions #####
  ==============================================================================   
  [..]
  (+) The internal voltage reference consumption is not negligible, in particular 
      in Stop and Standby mode. To reduce power consumption, use the PWR_UltraLowPowerCmd()
      function (ULP bit (Ultra low power) in the PWR_CR register) to disable the 
      internal voltage reference. However, in this case, when exiting from the 
      Stop/Standby mode, the functions managed through the internal voltage reference 
      are not reliable during the internal voltage reference startup time (up to 3 ms).
      To reduce the wakeup time, the device can exit from Stop/Standby mode without 
      waiting for the internal voltage reference startup time. This is performed 
      by using the PWR_FastWakeUpCmd() function (setting the FWU bit (Fast
      wakeup) in the PWR_CR register) before entering Stop/Standby mode.

@endverbatim
  * @{
  */

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
  * @}
  */

/** @defgroup PWR_Group5 Voltage Scaling configuration functions
 *  @brief   Voltage Scaling configuration functions 
 *
@verbatim   
  ============================================================================== 
              ##### Voltage Scaling configuration functions #####
  ==============================================================================  

    (+) The dynamic voltage scaling is a power management technique which consists in 
        increasing or decreasing the voltage used for the digital peripherals (VCORE), 
        according to the circumstances.
   
   [..] Depending on the device voltage range, the maximum frequency and FLASH wait
        state should be adapted accordingly:
   [..] 
        +------------------------------------------------------------------+     
        |   Wait states   |                HCLK clock frequency (MHz)      |
        |                 |------------------------------------------------|     
        |    (Latency)    |            voltage range       | voltage range | 
        |                 |            1.65 V - 3.6 V      | 2.0 V - 3.6 V |
        |                 |----------------|---------------|---------------|
        |                 |     Range 3    |    Range 2    |    Range 1    |
        |                 |  VCORE = 1.2 V | VCORE = 1.5 V | VCORE = 1.8 V |
        |---------------- |----------------|---------------|---------------|             
        | 0WS(1CPU cycle) |0 < HCLK <= 2   |0 < HCLK <= 8  |0 < HCLK <= 16 |
        |-----------------|----------------|---------------|---------------|  
        | 1WS(2CPU cycle) |2 < HCLK <= 4   |8 < HCLK <= 16 |16 < HCLK <= 32|
        |-----------------|----------------|---------------|---------------|  
        | CPU Performance |      Low       |     Medium    |     High      |
        |-----__----------|----------------|---------------|---------------|  
        |Power Performance|      High      |     Medium    |      Low      |                 
        +------------------------------------------------------------------+    

    (+) To modify the Product voltage range, user application has to:
        (++) Check VDD to identify which ranges are allowed (see table above).
        (++) Check the PWR_FLAG_VOSF (Voltage Scaling update ongoing) using the PWR_GetFlagStatus() 
             function and wait until it is  reset.
        (++) Configure the Voltage range using the PWR_VoltageScalingConfig() function.

    (+) When VCORE range 1 is selected and VDD drops below 2.0 V, the application must
        reconfigure the system:
        (++) Detect that VDD drops below 2.0 V using the PVD Level 1.
        (++) Adapt the clock frequency to the voltage range that will be selected at next step.
        (++) Select the required voltage range.
        (++) When VCORE range 2 or range 3 is selected and VDD drops below 2.0 V, no system
             reconfiguration is required.
 
    (+) When VDD is above 2.0 V, any of the 3 voltage ranges can be selected.
        (++) When the voltage range is above the targeted voltage range (e.g. from range 
             1 to 2).
        (++) Adapt the clock frequency to the lower voltage range that will be selected 
             at next step.
        (++) Select the required voltage range.
        (++) When the voltage range is below the targeted voltage range (e.g. from range 
             3 to 1).
        (++) Select the required voltage range.
        (++) Tune the clock frequency if needed.
 
    (+) When VDD is below 2.0 V, only range 2 and 3 can be selected:
        (++) From range 2 to range 3.
             (+++) Adapt the clock frequency to voltage range 3.
             (+++) Select voltage range 3.
        (++) From range 3 to range 2.
             (+++) Select the voltage range 2.
             (+++) Tune the clock frequency if needed.

@endverbatim
  * @{
  */

/**
  * @brief  Configures the voltage scaling range.
  * @note   During voltage scaling configuration, the system clock is stopped 
  *         until the regulator is stabilized (VOSF = 0). This must be taken 
  *         into account during application developement, in case a critical 
  *         reaction time to interrupt is needed, and depending on peripheral 
  *         used (timer, communication,...).
  *             
  * @param  PWR_VoltageScaling: specifies the voltage scaling range.
  *   This parameter can be:
  *     @arg PWR_VoltageScaling_Range1: Voltage Scaling Range 1 (VCORE = 1.8V).
  *     @arg PWR_VoltageScaling_Range2: Voltage Scaling Range 2 (VCORE = 1.5V).
  *     @arg PWR_VoltageScaling_Range3: Voltage Scaling Range 3 (VCORE = 1.2V) 
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
  * @}
  */

/** @defgroup PWR_Group6 Low Power modes configuration functions
 *  @brief   Low Power modes configuration functions 
 *
@verbatim   
  ============================================================================== 
              ##### Low Power modes configuration functions #####
  ==============================================================================    

    [..] The devices feature five low-power modes:
    (+) Low power run mode: regulator in low power mode, limited clock frequency, 
        limited number of peripherals running.
    (+) Sleep mode: Cortex-M3 core stopped, peripherals kept running.
    (+) Low power sleep mode: Cortex-M3 core stopped, limited clock frequency, 
        limited number of peripherals running, regulator in low power mode.
    (+) Stop mode: all clocks are stopped, regulator running, regulator in low power mode.
    (+) Standby mode: VCORE domain powered off.
   
  *** Low power run mode (LP run) *** 
  ===================================
      [..]
    (+) Entry:
        (++) Decrease the system frequency.
        (++) The regulator is forced in low power mode using the PWR_EnterLowPowerRunMode()
             function.
    (+) Exit:
        (++) The regulator is forced in Main regulator mode sing the PWR_EnterLowPowerRunMode()
             function.
        (++) Increase the system frequency if needed.

  *** Sleep mode *** 
  ==================
  [..] 
    (+) Entry:
        (++) The Sleep mode is entered by using the PWR_EnterSleepMode(PWR_Regulator_ON,) 
             function with regulator ON.
    (+) Exit:
        (++) Any peripheral interrupt acknowledged by the nested vectored interrupt 
             controller (NVIC) can wake up the device from Sleep mode.

  *** Low power sleep mode (LP sleep) *** 
  =======================================
  [..] 
    (+) Entry:
        (++) The Flash memory must be switched off by using the FLASH_SLEEPPowerDownCmd()
             function.
        (++) Decrease the system frequency.
        (++) The regulator is forced in low power mode and the WFI or WFE instructions
             are executed using the PWR_EnterSleepMode(PWR_Regulator_LowPower,) function 
             with regulator in LowPower.
    (+) Exit:
        (++) Any peripheral interrupt acknowledged by the nested vectored interrupt 
             controller (NVIC) can wake up the device from Sleep LP mode.

  *** Stop mode *** 
  =================
  [..] In Stop mode, all clocks in the VCORE domain are stopped, the PLL, the MSI,
       the HSI and the HSE RC oscillators are disabled. Internal SRAM and register 
       contents are preserved.
       The voltage regulator can be configured either in normal or low-power mode.
       To minimize the consumption In Stop mode, VREFINT, the BOR, PVD, and temperature
       sensor can be switched off before entering the Stop mode. They can be switched 
       on again by software after exiting the Stop mode using the PWR_UltraLowPowerCmd()
       function. 
   
    (+) Entry:
        (++) The Stop mode is entered using the PWR_EnterSTOPMode(PWR_Regulator_LowPower,) 
             function with regulator in LowPower or with Regulator ON.
    (+) Exit:
        (++) Any EXTI Line (Internal or External) configured in Interrupt/Event mode.
      
  *** Standby mode *** 
  ====================
  [..] The Standby mode allows to achieve the lowest power consumption. It is based 
       on the Cortex-M3 deepsleep mode, with the voltage regulator disabled. 
       The VCORE domain is consequently powered off. The PLL, the MSI, the HSI 
       oscillator and the HSE oscillator are also switched off. SRAM and register 
       contents are lost except for the RTC registers, RTC backup registers and 
       Standby circuitry.
   
  [..] The voltage regulator is OFF.
   
  [..] To minimize the consumption In Standby mode, VREFINT, the BOR, PVD, and temperature
       sensor can be switched off before entering the Standby mode. They can be switched 
       on again by software after exiting the Standby mode using the PWR_UltraLowPowerCmd()
       function. 
   
    (+) Entry:
        (++) The Standby mode is entered using the PWR_EnterSTANDBYMode() function.
    (+) Exit:
        (++) WKUP pin rising edge, RTC alarm (Alarm A and Alarm B), RTC wakeup,
            tamper event, time-stamp event, external reset in NRST pin, IWDG reset.

  *** Auto-wakeup (AWU) from low-power mode *** 
  =============================================
  [..]The MCU can be woken up from low-power mode by an RTC Alarm event, an RTC 
      Wakeup event, a tamper event, a time-stamp event, or a comparator event, 
      without depending on an external interrupt (Auto-wakeup mode).

    (+) RTC auto-wakeup (AWU) from the Stop mode
        (++) To wake up from the Stop mode with an RTC alarm event, it is necessary to:
             (+++) Configure the EXTI Line 17 to be sensitive to rising edges (Interrupt 
                   or Event modes) using the EXTI_Init() function.
             (+++) Enable the RTC Alarm Interrupt using the RTC_ITConfig() function
             (+++) Configure the RTC to generate the RTC alarm using the RTC_SetAlarm() 
                   and RTC_AlarmCmd() functions.
        (++) To wake up from the Stop mode with an RTC Tamper or time stamp event, it 
             is necessary to:
             (+++) Configure the EXTI Line 19 to be sensitive to rising edges (Interrupt 
                   or Event modes) using the EXTI_Init() function.
             (+++) Enable the RTC Tamper or time stamp Interrupt using the RTC_ITConfig() 
                   function.
             (+++) Configure the RTC to detect the tamper or time stamp event using the
                   RTC_TimeStampConfig(), RTC_TamperTriggerConfig() and RTC_TamperCmd()
                   functions.
        (++) To wake up from the Stop mode with an RTC WakeUp event, it is necessary to:
             (+++) Configure the EXTI Line 20 to be sensitive to rising edges (Interrupt 
                   or Event modes) using the EXTI_Init() function.
             (+++) Enable the RTC WakeUp Interrupt using the RTC_ITConfig() function.
             (+++) Configure the RTC to generate the RTC WakeUp event using the RTC_WakeUpClockConfig(), 
                   RTC_SetWakeUpCounter() and RTC_WakeUpCmd() functions.

    (+) RTC auto-wakeup (AWU) from the Standby mode
        (++) To wake up from the Standby mode with an RTC alarm event, it is necessary to:
             (+++) Enable the RTC Alarm Interrupt using the RTC_ITConfig() function.
             (+++) Configure the RTC to generate the RTC alarm using the RTC_SetAlarm() 
                   and RTC_AlarmCmd() functions.
        (++) To wake up from the Standby mode with an RTC Tamper or time stamp event, it 
             is necessary to:
             (+++) Enable the RTC Tamper or time stamp Interrupt using the RTC_ITConfig() 
                   function.
             (+++) Configure the RTC to detect the tamper or time stamp event using the
                   RTC_TimeStampConfig(), RTC_TamperTriggerConfig() and RTC_TamperCmd()
                   functions.
        (++) To wake up from the Standby mode with an RTC WakeUp event, it is necessary to:
             (+++) Enable the RTC WakeUp Interrupt using the RTC_ITConfig() function
             (+++) Configure the RTC to generate the RTC WakeUp event using the RTC_WakeUpClockConfig(), 
                   RTC_SetWakeUpCounter() and RTC_WakeUpCmd() functions.

    (+) Comparator auto-wakeup (AWU) from the Stop mode
        (++) To wake up from the Stop mode with an comparator 1 or comparator 2 wakeup
             event, it is necessary to:
             (+++) Configure the EXTI Line 21 for comparator 1 or EXTI Line 22 for comparator 2 
                   to be sensitive to to the selected edges (falling, rising or falling 
                   and rising) (Interrupt or Event modes) using the EXTI_Init() function.
             (+++) Configure the comparator to generate the event.

@endverbatim
  * @{
  */

/**
  * @brief  Enters/Exits the Low Power Run mode.
  * @note   Low power run mode can only be entered when VCORE is in range 2.
  *         In addition, the dynamic voltage scaling must not be used when Low 
  *         power run mode is selected. Only Stop and Sleep modes with regulator 
  *         configured in Low power mode is allowed when Low power run mode is 
  *         selected.  
  * @note   In Low power run mode, all I/O pins keep the same state as in Run mode.
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
  * @note   In Sleep mode, all I/O pins keep the same state as in Run mode.  
  * @param  PWR_Regulator: specifies the regulator state in Sleep mode.
  *   This parameter can be one of the following values:
  *     @arg PWR_Regulator_ON: Sleep mode with regulator ON
  *     @arg PWR_Regulator_LowPower: Sleep mode with regulator in low power mode
  * @note   Low power sleep mode can only be entered when VCORE is in range 2.
  * @note   When the voltage regulator operates in low power mode, an additional 
  *         startup delay is incurred when waking up from Low power sleep mode.
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
  * @note   In Stop mode, all I/O pins keep the same state as in Run mode.
  * @note   When exiting Stop mode by issuing an interrupt or a wakeup event, 
  *         the MSI RC oscillator is selected as system clock.
  * @note   When the voltage regulator operates in low power mode, an additional 
  *         startup delay is incurred when waking up from Stop mode. 
  *         By keeping the internal regulator ON during Stop mode, the consumption 
  *         is higher although the startup time is reduced.
  * @param  PWR_Regulator: specifies the regulator state in STOP mode.
  *   This parameter can be one of the following values:
  *     @arg PWR_Regulator_ON: STOP mode with regulator ON.
  *     @arg PWR_Regulator_LowPower: STOP mode with regulator in low power mode.
  * @param  PWR_STOPEntry: specifies if STOP mode in entered with WFI or WFE instruction.
  *   This parameter can be one of the following values:
  *     @arg PWR_STOPEntry_WFI: enter STOP mode with WFI instruction.
  *     @arg PWR_STOPEntry_WFE: enter STOP mode with WFE instruction.
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
  * @note   In Standby mode, all I/O pins are high impedance except for:
  *         Reset pad (still available) 
  *         RTC_AF1 pin (PC13) if configured for Wakeup pin 2 (WKUP2), tamper, 
  *         time-stamp, RTC Alarm out, or RTC clock calibration out.
  *         WKUP pin 1 (PA0) and WKUP pin 3 (PE6), if enabled.       
  * @param  None
  * @retval None
  */
void PWR_EnterSTANDBYMode(void)
{
  /* Clear Wakeup flag */
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
  * @}
  */

/** @defgroup PWR_Group7 Flags management functions
 *  @brief   Flags management functions 
 *
@verbatim   
  ==============================================================================
                       ##### Flags management functions #####
  ==============================================================================   

@endverbatim
  * @{
  */

/**
  * @brief  Checks whether the specified PWR flag is set or not.
  * @param  PWR_FLAG: specifies the flag to check.
  *   This parameter can be one of the following values:
  *     @arg PWR_FLAG_WU: Wake Up flag. This flag indicates that a wakeup event 
  *       was received from the WKUP pin or from the RTC alarm (Alarm A or Alarm B), 
  *       RTC Tamper event, RTC TimeStamp event or RTC Wakeup.
  *     @arg PWR_FLAG_SB: StandBy flag. This flag indicates that the system was
  *                       resumed from StandBy mode.    
  *     @arg PWR_FLAG_PVDO: PVD Output. This flag is valid only if PVD is enabled 
  *       by the PWR_PVDCmd() function.
  *     @arg PWR_FLAG_VREFINTRDY: Internal Voltage Reference Ready flag. This 
  *       flag indicates the state of the internal voltage reference, VREFINT.
  *     @arg PWR_FLAG_VOS: Voltage Scaling select flag. A delay is required for 
  *       the internal regulator to be ready after the voltage range is changed.
  *       The VOSF flag indicates that the regulator has reached the voltage level 
  *       defined with bits VOS[1:0] of PWR_CR register.
  *     @arg PWR_FLAG_REGLP: Regulator LP flag. This flag is set by hardware 
  *       when the MCU is in Low power run mode.
  *       When the MCU exits from Low power run mode, this flag stays SET until 
  *       the regulator is ready in main mode. A polling on this flag is 
  *       recommended to wait for the regulator main mode. 
  *       This flag is RESET by hardware when the regulator is ready.       
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

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
