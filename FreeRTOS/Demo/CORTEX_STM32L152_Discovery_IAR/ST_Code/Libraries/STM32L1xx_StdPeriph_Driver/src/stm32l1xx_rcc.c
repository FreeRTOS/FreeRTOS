/**
  ******************************************************************************
  * @file    stm32l1xx_rcc.c
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file provides firmware functions to manage the following
  *          functionalities of the Reset and clock control (RCC) peripheral:
  *           + Internal/external clocks, PLL, CSS and MCO configuration
  *           + System, AHB and APB busses clocks configuration
  *           + Peripheral clocks configuration
  *           + Interrupts and flags management
  *
 @verbatim

 ===============================================================================
                        ##### RCC specific features #####
 ===============================================================================
    [..] After reset the device is running from MSI (2 MHz) with Flash 0 WS,
         all peripherals are off except internal SRAM, Flash and JTAG.
         (#) There is no prescaler on High speed (AHB) and Low speed (APB) busses;
             all peripherals mapped on these busses are running at MSI speed.
         (#) The clock for all peripherals is switched off, except the SRAM and
             FLASH.
         (#) All GPIOs are in input floating state, except the JTAG pins which
             are assigned to be used for debug purpose.
    [..] Once the device started from reset, the user application has to:
         (#) Configure the clock source to be used to drive the System clock
             (if the application needs higher frequency/performance)
         (#) Configure the System clock frequency and Flash settings
         (#) Configure the AHB and APB busses prescalers
         (#) Enable the clock for the peripheral(s) to be used
         (#) Configure the clock source(s) for peripherals whose clocks are not
             derived from the System clock (ADC, RTC/LCD and IWDG)

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
#include "stm32l1xx_rcc.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup RCC
  * @brief RCC driver modules
  * @{
  */

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/

/* ------------ RCC registers bit address in the alias region ----------- */
#define RCC_OFFSET                (RCC_BASE - PERIPH_BASE)

/* --- CR Register ---*/

/* Alias word address of HSION bit */
#define CR_OFFSET                 (RCC_OFFSET + 0x00)
#define HSION_BitNumber           0x00
#define CR_HSION_BB               (PERIPH_BB_BASE + (CR_OFFSET * 32) + (HSION_BitNumber * 4))

/* Alias word address of MSION bit */
#define MSION_BitNumber           0x08
#define CR_MSION_BB               (PERIPH_BB_BASE + (CR_OFFSET * 32) + (MSION_BitNumber * 4))

/* Alias word address of PLLON bit */
#define PLLON_BitNumber           0x18
#define CR_PLLON_BB               (PERIPH_BB_BASE + (CR_OFFSET * 32) + (PLLON_BitNumber * 4))

/* Alias word address of CSSON bit */
#define CSSON_BitNumber           0x1C
#define CR_CSSON_BB               (PERIPH_BB_BASE + (CR_OFFSET * 32) + (CSSON_BitNumber * 4))

/* --- CSR Register ---*/

/* Alias word address of LSION bit */
#define CSR_OFFSET                (RCC_OFFSET + 0x34)
#define LSION_BitNumber           0x00
#define CSR_LSION_BB              (PERIPH_BB_BASE + (CSR_OFFSET * 32) + (LSION_BitNumber * 4))

/* Alias word address of LSECSSON bit */
#define LSECSSON_BitNumber        0x0B
#define CSR_LSECSSON_BB          (PERIPH_BB_BASE + (CSR_OFFSET * 32) + (LSECSSON_BitNumber * 4))

/* Alias word address of RTCEN bit */
#define RTCEN_BitNumber           0x16
#define CSR_RTCEN_BB              (PERIPH_BB_BASE + (CSR_OFFSET * 32) + (RTCEN_BitNumber * 4))

/* Alias word address of RTCRST bit */
#define RTCRST_BitNumber          0x17
#define CSR_RTCRST_BB             (PERIPH_BB_BASE + (CSR_OFFSET * 32) + (RTCRST_BitNumber * 4))


/* ---------------------- RCC registers mask -------------------------------- */
/* RCC Flag Mask */
#define FLAG_MASK                 ((uint8_t)0x1F)

/* CR register byte 3 (Bits[23:16]) base address */
#define CR_BYTE3_ADDRESS          ((uint32_t)0x40023802)

/* ICSCR register byte 4 (Bits[31:24]) base address */
#define ICSCR_BYTE4_ADDRESS       ((uint32_t)0x40023807)

/* CFGR register byte 3 (Bits[23:16]) base address */
#define CFGR_BYTE3_ADDRESS        ((uint32_t)0x4002380A)

/* CFGR register byte 4 (Bits[31:24]) base address */
#define CFGR_BYTE4_ADDRESS        ((uint32_t)0x4002380B)

/* CIR register byte 2 (Bits[15:8]) base address */
#define CIR_BYTE2_ADDRESS         ((uint32_t)0x4002380D)

/* CIR register byte 3 (Bits[23:16]) base address */
#define CIR_BYTE3_ADDRESS         ((uint32_t)0x4002380E)

/* CSR register byte 2 (Bits[15:8]) base address */
#define CSR_BYTE2_ADDRESS         ((uint32_t)0x40023835)

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/

static __I uint8_t PLLMulTable[9] = {3, 4, 6, 8, 12, 16, 24, 32, 48};
static __I uint8_t APBAHBPrescTable[16] = {0, 0, 0, 0, 1, 2, 3, 4, 1, 2, 3, 4, 6, 7, 8, 9};

/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/** @defgroup RCC_Private_Functions
  * @{
  */

/** @defgroup RCC_Group1 Internal and external clocks, PLL, CSS and MCO configuration functions
 *  @brief   Internal and external clocks, PLL, CSS and MCO configuration functions
 *
@verbatim
 ===============================================================================
 ##### Internal-external clocks, PLL, CSS and MCO configuration functions #####
 ===============================================================================
    [..] This section provide functions allowing to configure the internal/external
         clocks, PLL, CSS and MCO.
         (#) HSI (high-speed internal), 16 MHz factory-trimmed RC used directly
             or through the PLL as System clock source.
         (#) MSI (multi-speed internal), multispeed low power RC
             (65.536 KHz to 4.194 MHz) MHz used as System clock source.
         (#) LSI (low-speed internal), 37 KHz low consumption RC used as IWDG
             and/or RTC clock source.
         (#) HSE (high-speed external), 1 to 24 MHz crystal oscillator used
             directly or through the PLL as System clock source. Can be used
             also as RTC clock source.
         (#) LSE (low-speed external), 32 KHz oscillator used as RTC clock source.
         (#) PLL (clocked by HSI or HSE), for System clock and USB (48 MHz).
         (#) CSS (Clock security system), once enable and if a HSE clock failure
             occurs (HSE used directly or through PLL as System clock source),
             the System clock is automatically switched to MSI and an interrupt
             is generated if enabled.
             The interrupt is linked to the Cortex-M3 NMI (Non-Maskable Interrupt)
             exception vector.
         (#) MCO (microcontroller clock output), used to output SYSCLK, HSI, MSI,
             HSE, PLL, LSI or LSE clock (through a configurable prescaler) on
             PA8 pin.

@endverbatim
  * @{
  */

/**
  * @brief  Resets the RCC clock configuration to the default reset state.
  * @note   The default reset state of the clock configuration is given below:
  * @note      MSI ON and used as system clock source (MSI range is not modified
  *            by this function, it keep the value configured by user application)
  * @note      HSI, HSE and PLL OFF
  * @note      AHB, APB1 and APB2 prescaler set to 1.
  * @note      CSS and MCO OFF
  * @note      All interrupts disabled
  * @note    However, this function doesn't modify the configuration of the
  * @note      Peripheral clocks
  * @note      LSI, LSE and RTC clocks
  * @param  None
  * @retval None
  */
void RCC_DeInit(void)
{

  /* Set MSION bit */
  RCC->CR |= (uint32_t)0x00000100;

  /* Reset SW[1:0], HPRE[3:0], PPRE1[2:0], PPRE2[2:0], MCOSEL[2:0] and MCOPRE[2:0] bits */
  RCC->CFGR &= (uint32_t)0x88FFC00C;

  /* Reset HSION, HSEON, CSSON and PLLON bits */
  RCC->CR &= (uint32_t)0xEEFEFFFE;

  /* Reset HSEBYP bit */
  RCC->CR &= (uint32_t)0xFFFBFFFF;

  /* Reset PLLSRC, PLLMUL[3:0] and PLLDIV[1:0] bits */
  RCC->CFGR &= (uint32_t)0xFF02FFFF;

  /* Disable all interrupts */
  RCC->CIR = 0x00000000;
}

/**
  * @brief  Configures the External High Speed oscillator (HSE).
  * @note    After enabling the HSE (RCC_HSE_ON or RCC_HSE_Bypass), the application
  *           software should wait on HSERDY flag to be set indicating that HSE clock
  *           is stable and can be used to clock the PLL and/or system clock.
  *  @note    HSE state can not be changed if it is used directly or through the
  *           PLL as system clock. In this case, you have to select another source
  *           of the system clock then change the HSE state (ex. disable it).
  *  @note    The HSE is stopped by hardware when entering STOP and STANDBY modes.
  * @note   This function reset the CSSON bit, so if the Clock security system(CSS)
  *         was previously enabled you have to enable it again after calling this
  *         function.
  * @param RCC_HSE: specifies the new state of the HSE.
  *   This parameter can be one of the following values:
  *     @arg RCC_HSE_OFF: turn OFF the HSE oscillator, HSERDY flag goes low after
  *                       6 HSE oscillator clock cycles.
  *     @arg RCC_HSE_ON: turn ON the HSE oscillator
  *     @arg RCC_HSE_Bypass: HSE oscillator bypassed with external clock
  * @retval None
  */
void RCC_HSEConfig(uint8_t RCC_HSE)
{
  /* Check the parameters */
  assert_param(IS_RCC_HSE(RCC_HSE));

  /* Reset HSEON and HSEBYP bits before configuring the HSE ------------------*/
  *(__IO uint8_t *) CR_BYTE3_ADDRESS = RCC_HSE_OFF;

  /* Set the new HSE configuration -------------------------------------------*/
  *(__IO uint8_t *) CR_BYTE3_ADDRESS = RCC_HSE;

}

/**
  * @brief  Waits for HSE start-up.
  * @note   This functions waits on HSERDY flag to be set and return SUCCESS if
  *         this flag is set, otherwise returns ERROR if the timeout is reached
  *         and this flag is not set. The timeout value is defined by the constant
  *         HSE_STARTUP_TIMEOUT in stm32l1xx.h file. You can tailor it depending
  *         on the HSE crystal used in your application.
  * @param  None
  * @retval An ErrorStatus enumeration value:
  *          - SUCCESS: HSE oscillator is stable and ready to use
  *          - ERROR: HSE oscillator not yet ready
  */
ErrorStatus RCC_WaitForHSEStartUp(void)
{
  __IO uint32_t StartUpCounter = 0;
  ErrorStatus status = ERROR;
  FlagStatus HSEStatus = RESET;

  /* Wait till HSE is ready and if timeout is reached exit */
  do
  {
    HSEStatus = RCC_GetFlagStatus(RCC_FLAG_HSERDY);
    StartUpCounter++;
  } while((StartUpCounter != HSE_STARTUP_TIMEOUT) && (HSEStatus == RESET));

  if (RCC_GetFlagStatus(RCC_FLAG_HSERDY) != RESET)
  {
    status = SUCCESS;
  }
  else
  {
    status = ERROR;
  }
  return (status);
}

/**
  * @brief  Adjusts the Internal Multi Speed oscillator (MSI) calibration value.
  * @note   The calibration is used to compensate for the variations in voltage
  *         and temperature that influence the frequency of the internal MSI RC.
  *         Refer to the Application Note AN3300 for more details on how to
  *         calibrate the MSI.
  * @param  MSICalibrationValue: specifies the MSI calibration trimming value.
  *   This parameter must be a number between 0 and 0xFF.
  * @retval None
  */
void RCC_AdjustMSICalibrationValue(uint8_t MSICalibrationValue)
{

  /* Check the parameters */
  assert_param(IS_RCC_MSI_CALIBRATION_VALUE(MSICalibrationValue));

  *(__IO uint8_t *) ICSCR_BYTE4_ADDRESS = MSICalibrationValue;
}

/**
  * @brief  Configures the Internal Multi Speed oscillator (MSI) clock range.
  * @note     After restart from Reset or wakeup from STANDBY, the MSI clock is
  *           around 2.097 MHz. The MSI clock does not change after wake-up from
  *           STOP mode.
  *  @note    The MSI clock range can be modified on the fly.
  * @param  RCC_MSIRange: specifies the MSI Clock range.
  *   This parameter must be one of the following values:
  *     @arg RCC_MSIRange_0: MSI clock is around 65.536 KHz
  *     @arg RCC_MSIRange_1: MSI clock is around 131.072 KHz
  *     @arg RCC_MSIRange_2: MSI clock is around 262.144 KHz
  *     @arg RCC_MSIRange_3: MSI clock is around 524.288 KHz
  *     @arg RCC_MSIRange_4: MSI clock is around 1.048 MHz
  *     @arg RCC_MSIRange_5: MSI clock is around 2.097 MHz (default after Reset or wake-up from STANDBY)
  *     @arg RCC_MSIRange_6: MSI clock is around 4.194 MHz
  *
  * @retval None
  */
void RCC_MSIRangeConfig(uint32_t RCC_MSIRange)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RCC_MSI_CLOCK_RANGE(RCC_MSIRange));

  tmpreg = RCC->ICSCR;

  /* Clear MSIRANGE[2:0] bits */
  tmpreg &= ~RCC_ICSCR_MSIRANGE;

  /* Set the MSIRANGE[2:0] bits according to RCC_MSIRange value */
  tmpreg |= (uint32_t)RCC_MSIRange;

  /* Store the new value */
  RCC->ICSCR = tmpreg;
}

/**
  * @brief  Enables or disables the Internal Multi Speed oscillator (MSI).
  * @note     The MSI is stopped by hardware when entering STOP and STANDBY modes.
  *           It is used (enabled by hardware) as system clock source after
  *           startup from Reset, wakeup from STOP and STANDBY mode, or in case
  *           of failure of the HSE used directly or indirectly as system clock
  *           (if the Clock Security System CSS is enabled).
  * @note     MSI can not be stopped if it is used as system clock source.
  *           In this case, you have to select another source of the system
  *           clock then stop the MSI.
  * @note     After enabling the MSI, the application software should wait on
  *           MSIRDY flag to be set indicating that MSI clock is stable and can
  *           be used as system clock source.
  * @param  NewState: new state of the MSI.
  *   This parameter can be: ENABLE or DISABLE.
  * @note   When the MSI is stopped, MSIRDY flag goes low after 6 MSI oscillator
  *         clock cycles.
  * @retval None
  */
void RCC_MSICmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CR_MSION_BB = (uint32_t)NewState;
}

/**
  * @brief  Adjusts the Internal High Speed oscillator (HSI) calibration value.
  * @note   The calibration is used to compensate for the variations in voltage
  *         and temperature that influence the frequency of the internal HSI RC.
  *         Refer to the Application Note AN3300 for more details on how to
  *         calibrate the HSI.
  * @param  HSICalibrationValue: specifies the HSI calibration trimming value.
  *   This parameter must be a number between 0 and 0x1F.
  * @retval None
  */
void RCC_AdjustHSICalibrationValue(uint8_t HSICalibrationValue)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RCC_HSI_CALIBRATION_VALUE(HSICalibrationValue));

  tmpreg = RCC->ICSCR;

  /* Clear HSITRIM[4:0] bits */
  tmpreg &= ~RCC_ICSCR_HSITRIM;

  /* Set the HSITRIM[4:0] bits according to HSICalibrationValue value */
  tmpreg |= (uint32_t)HSICalibrationValue << 8;

  /* Store the new value */
  RCC->ICSCR = tmpreg;
}

/**
  * @brief  Enables or disables the Internal High Speed oscillator (HSI).
  * @note     After enabling the HSI, the application software should wait on
  *           HSIRDY flag to be set indicating that HSI clock is stable and can
  *           be used to clock the PLL and/or system clock.
  * @note     HSI can not be stopped if it is used directly or through the PLL
  *           as system clock. In this case, you have to select another source
  *           of the system clock then stop the HSI.
  * @note     The HSI is stopped by hardware when entering STOP and STANDBY modes.
  * @param  NewState: new state of the HSI.
  *   This parameter can be: ENABLE or DISABLE.
  * @note   When the HSI is stopped, HSIRDY flag goes low after 6 HSI oscillator
  *         clock cycles.
  * @retval None
  */
void RCC_HSICmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CR_HSION_BB = (uint32_t)NewState;
}

/**
  * @brief  Configures the External Low Speed oscillator (LSE).
  * @note     As the LSE is in the RTC domain and write access is denied to this
  *           domain after reset, you have to enable write access using
  *           PWR_RTCAccessCmd(ENABLE) function before to configure the LSE
  *           (to be done once after reset).
  * @note     After enabling the LSE (RCC_LSE_ON or RCC_LSE_Bypass), the application
  *           software should wait on LSERDY flag to be set indicating that LSE clock
  *           is stable and can be used to clock the RTC.
  * @param  RCC_LSE: specifies the new state of the LSE.
  *   This parameter can be one of the following values:
  *     @arg RCC_LSE_OFF: turn OFF the LSE oscillator, LSERDY flag goes low after
  *                       6 LSE oscillator clock cycles.
  *     @arg RCC_LSE_ON: turn ON the LSE oscillator
  *     @arg RCC_LSE_Bypass: LSE oscillator bypassed with external clock
  * @retval None
  */
void RCC_LSEConfig(uint8_t RCC_LSE)
{
  /* Check the parameters */
  assert_param(IS_RCC_LSE(RCC_LSE));

  /* Reset LSEON and LSEBYP bits before configuring the LSE ------------------*/
  *(__IO uint8_t *) CSR_BYTE2_ADDRESS = RCC_LSE_OFF;

  /* Set the new LSE configuration -------------------------------------------*/
  *(__IO uint8_t *) CSR_BYTE2_ADDRESS = RCC_LSE;
}

/**
  * @brief  Enables or disables the Internal Low Speed oscillator (LSI).
  * @note     After enabling the LSI, the application software should wait on
  *           LSIRDY flag to be set indicating that LSI clock is stable and can
  *           be used to clock the IWDG and/or the RTC.
  * @note     LSI can not be disabled if the IWDG is running.
  * @param  NewState: new state of the LSI.
  *   This parameter can be: ENABLE or DISABLE.
  * @note   When the LSI is stopped, LSIRDY flag goes low after 6 LSI oscillator
  *         clock cycles.
  * @retval None
  */
void RCC_LSICmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CSR_LSION_BB = (uint32_t)NewState;
}

/**
  * @brief  Configures the PLL clock source and multiplication factor.
  * @note   This function must be used only when the PLL is disabled.
  *
  * @param  RCC_PLLSource: specifies the PLL entry clock source.
  *   This parameter can be one of the following values:
  *     @arg RCC_PLLSource_HSI: HSI oscillator clock selected as PLL clock source
  *     @arg RCC_PLLSource_HSE: HSE oscillator clock selected as PLL clock source
  * @note   The minimum input clock frequency for PLL is 2 MHz (when using HSE as
  *         PLL source).
  *
  * @param  RCC_PLLMul: specifies the PLL multiplication factor, which drive the PLLVCO clock
  *   This parameter can be:
  *     @arg RCC_PLLMul_3: PLL clock source multiplied by 3
  *     @arg RCC_PLLMul_4: PLL clock source multiplied by 4
  *     @arg RCC_PLLMul_6: PLL clock source multiplied by 6
  *     @arg RCC_PLLMul_8: PLL clock source multiplied by 8
  *     @arg RCC_PLLMul_12: PLL clock source multiplied by 12
  *     @arg RCC_PLLMul_16: PLL clock source multiplied by 16
  *     @arg RCC_PLLMul_24: PLL clock source multiplied by 24
  *     @arg RCC_PLLMul_32: PLL clock source multiplied by 32
  *     @arg RCC_PLLMul_48: PLL clock source multiplied by 48
  * @note   The application software must set correctly the PLL multiplication
  *         factor to avoid exceeding:
  *             - 96 MHz as PLLVCO when the product is in range 1
  *             - 48 MHz as PLLVCO when the product is in range 2
  *             - 24 MHz when the product is in range 3
  * @note   When using the USB the PLLVCO should be 96MHz
  *
  * @param  RCC_PLLDiv: specifies the PLL division factor.
  *   This parameter can be:
  *     @arg RCC_PLLDiv_2: PLL Clock output divided by 2
  *     @arg RCC_PLLDiv_3: PLL Clock output divided by 3
  *     @arg RCC_PLLDiv_4: PLL Clock output divided by 4
  * @note   The application software must set correctly the output division to avoid
  *         exceeding 32 MHz as SYSCLK.
  *
  * @retval None
  */
void RCC_PLLConfig(uint8_t RCC_PLLSource, uint8_t RCC_PLLMul, uint8_t RCC_PLLDiv)
{
  /* Check the parameters */
  assert_param(IS_RCC_PLL_SOURCE(RCC_PLLSource));
  assert_param(IS_RCC_PLL_MUL(RCC_PLLMul));
  assert_param(IS_RCC_PLL_DIV(RCC_PLLDiv));

  *(__IO uint8_t *) CFGR_BYTE3_ADDRESS = (uint8_t)(RCC_PLLSource | ((uint8_t)(RCC_PLLMul | (uint8_t)(RCC_PLLDiv))));
}

/**
  * @brief  Enables or disables the PLL.
  * @note     After enabling the PLL, the application software should wait on
  *           PLLRDY flag to be set indicating that PLL clock is stable and can
  *           be used as system clock source.
  * @note     The PLL can not be disabled if it is used as system clock source
  * @note     The PLL is disabled by hardware when entering STOP and STANDBY modes.
  * @param  NewState: new state of the PLL.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_PLLCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CR_PLLON_BB = (uint32_t)NewState;
}

/**
  * @brief  Enables or disables the Clock Security System.
  * @note   If a failure is detected on the HSE oscillator clock, this oscillator
  *         is automatically disabled and an interrupt is generated to inform the
  *         software about the failure (Clock Security System Interrupt, CSSI),
  *         allowing the MCU to perform rescue operations. The CSSI is linked to
  *         the Cortex-M3 NMI (Non-Maskable Interrupt) exception vector.
  * @param  NewState: new state of the Clock Security System.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_ClockSecuritySystemCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CR_CSSON_BB = (uint32_t)NewState;
}

/**
  * @brief  Enables or disables the LSE Clock Security System.
  * @param  NewState: new state of the Clock Security System.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_LSEClockSecuritySystemCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CSR_LSECSSON_BB = (uint32_t)NewState;
}

/**
  * @brief  Selects the clock source to output on MCO pin (PA8).
  * @note   PA8 should be configured in alternate function mode.
  * @param  RCC_MCOSource: specifies the clock source to output.
  *   This parameter can be one of the following values:
  *     @arg RCC_MCOSource_NoClock: No clock selected
  *     @arg RCC_MCOSource_SYSCLK: System clock selected
  *     @arg RCC_MCOSource_HSI: HSI oscillator clock selected
  *     @arg RCC_MCOSource_MSI: MSI oscillator clock selected
  *     @arg RCC_MCOSource_HSE: HSE oscillator clock selected
  *     @arg RCC_MCOSource_PLLCLK: PLL clock selected
  *     @arg RCC_MCOSource_LSI: LSI clock selected
  *     @arg RCC_MCOSource_LSE: LSE clock selected
  * @param  RCC_MCODiv: specifies the MCO prescaler.
  *   This parameter can be one of the following values:
  *     @arg RCC_MCODiv_1: no division applied to MCO clock
  *     @arg RCC_MCODiv_2: division by 2 applied to MCO clock
  *     @arg RCC_MCODiv_4: division by 4 applied to MCO clock
  *     @arg RCC_MCODiv_8: division by 8 applied to MCO clock
  *     @arg RCC_MCODiv_16: division by 16 applied to MCO clock
  * @retval None
  */
void RCC_MCOConfig(uint8_t RCC_MCOSource, uint8_t RCC_MCODiv)
{
  /* Check the parameters */
  assert_param(IS_RCC_MCO_SOURCE(RCC_MCOSource));
  assert_param(IS_RCC_MCO_DIV(RCC_MCODiv));

  /* Select MCO clock source and prescaler */
  *(__IO uint8_t *) CFGR_BYTE4_ADDRESS =  RCC_MCOSource | RCC_MCODiv;
}

/**
  * @}
  */

/** @defgroup RCC_Group2 System AHB and APB busses clocks configuration functions
 *  @brief   System, AHB and APB busses clocks configuration functions
 *
@verbatim
 ===============================================================================
     ##### System, AHB and APB busses clocks configuration functions #####
 ===============================================================================
    [..] This section provide functions allowing to configure the System, AHB,
         APB1 and APB2 busses clocks.
         (#) Several clock sources can be used to drive the System clock (SYSCLK):
             MSI, HSI, HSE and PLL.
             The AHB clock (HCLK) is derived from System clock through configurable
             prescaler and used to clock the CPU, memory and peripherals mapped
             on AHB bus (DMA and GPIO).APB1 (PCLK1) and APB2 (PCLK2) clocks are
             derived from AHB clock through configurable prescalers and used to
             clock the peripherals mapped on these busses. You can use
             "RCC_GetClocksFreq()" function to retrieve the frequencies of these
             clocks.

         -@- All the peripheral clocks are derived from the System clock (SYSCLK)
             except:
             (+@) The USB 48 MHz clock which is derived from the PLL VCO clock.
             (+@) The ADC clock which is always the HSI clock. A divider by 1, 2
                  or 4 allows to adapt the clock frequency to the device operating
                  conditions.
             (+@) The RTC/LCD clock which is derived from the LSE, LSI or 1 MHz
                  HSE_RTC (HSE divided by a programmable prescaler).
                  The System clock (SYSCLK) frequency must be higher or equal to
                  the RTC/LCD clock frequency.
             (+@) IWDG clock which is always the LSI clock.

         (#) The maximum frequency of the SYSCLK, HCLK, PCLK1 and PCLK2 is 32 MHz.
             Depending on the device voltage range, the maximum frequency should
             be adapted accordingly:

        +----------------------------------------------------------------+
        |  Wait states  |                HCLK clock frequency (MHz)      |
        |               |------------------------------------------------|
        |   (Latency)   |            voltage range       | voltage range |
        |               |            1.65 V - 3.6 V      | 2.0 V - 3.6 V |
        |               |----------------|---------------|---------------|
        |               |  VCORE = 1.2 V | VCORE = 1.5 V | VCORE = 1.8 V |
        |-------------- |----------------|---------------|---------------|
        |0WS(1CPU cycle)|0 < HCLK <= 2   |0 < HCLK <= 8  |0 < HCLK <= 16 |
        |---------------|----------------|---------------|---------------|
        |1WS(2CPU cycle)|2 < HCLK <= 4   |8 < HCLK <= 16 |16 < HCLK <= 32|
        +----------------------------------------------------------------+

         (#) After reset, the System clock source is the MSI (2 MHz) with 0 WS,
             Flash 32-bit access is enabled and prefetch is disabled.
    [..] It is recommended to use the following software sequences to tune the
         number of wait states needed to access the Flash memory with the CPU
         frequency (HCLK).
         (+) Increasing the CPU frequency (in the same voltage range)
         (+) Program the Flash 64-bit access, using "FLASH_ReadAccess64Cmd(ENABLE)"
             function
         (+) Check that 64-bit access is taken into account by reading FLASH_ACR
         (+) Program Flash WS to 1, using "FLASH_SetLatency(FLASH_Latency_1)"
             function
         (+) Check that the new number of WS is taken into account by reading
             FLASH_ACR
         (+) Modify the CPU clock source, using "RCC_SYSCLKConfig()" function
         (+) If needed, modify the CPU clock prescaler by using "RCC_HCLKConfig()"
             function
         (+) Check that the new CPU clock source is taken into account by reading
           the clock source status, using "RCC_GetSYSCLKSource()" function
         (+) Decreasing the CPU frequency (in the same voltage range)
         (+) Modify the CPU clock source, using "RCC_SYSCLKConfig()" function
         (+) If needed, modify the CPU clock prescaler by using "RCC_HCLKConfig()"
             function
         (+) Check that the new CPU clock source is taken into account by reading
           the clock source status, using "RCC_GetSYSCLKSource()" function
         (+) Program the new number of WS, using "FLASH_SetLatency()" function
         (+) Check that the new number of WS is taken into account by reading
             FLASH_ACR
         (+) Enable the Flash 32-bit access, using "FLASH_ReadAccess64Cmd(DISABLE)"
             function
         (+) Check that 32-bit access is taken into account by reading FLASH_ACR

@endverbatim
  * @{
  */

/**
  * @brief  Configures the system clock (SYSCLK).
  * @note     The MSI is used (enabled by hardware) as system clock source after
  *           startup from Reset, wake-up from STOP and STANDBY mode, or in case
  *           of failure of the HSE used directly or indirectly as system clock
  *           (if the Clock Security System CSS is enabled).
  * @note     A switch from one clock source to another occurs only if the target
  *           clock source is ready (clock stable after startup delay or PLL locked).
  *           If a clock source which is not yet ready is selected, the switch will
  *           occur when the clock source will be ready.
  *           You can use RCC_GetSYSCLKSource() function to know which clock is
  *           currently used as system clock source.
  * @param  RCC_SYSCLKSource: specifies the clock source used as system clock source
  *   This parameter can be one of the following values:
  *     @arg RCC_SYSCLKSource_MSI:    MSI selected as system clock source
  *     @arg RCC_SYSCLKSource_HSI:    HSI selected as system clock source
  *     @arg RCC_SYSCLKSource_HSE:    HSE selected as system clock source
  *     @arg RCC_SYSCLKSource_PLLCLK: PLL selected as system clock source
  * @retval None
  */
void RCC_SYSCLKConfig(uint32_t RCC_SYSCLKSource)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RCC_SYSCLK_SOURCE(RCC_SYSCLKSource));

  tmpreg = RCC->CFGR;

  /* Clear SW[1:0] bits */
  tmpreg &= ~RCC_CFGR_SW;

  /* Set SW[1:0] bits according to RCC_SYSCLKSource value */
  tmpreg |= RCC_SYSCLKSource;

  /* Store the new value */
  RCC->CFGR = tmpreg;
}

/**
  * @brief  Returns the clock source used as system clock.
  * @param  None
  * @retval The clock source used as system clock. The returned value can be one
  *         of the following values:
  *              - 0x00: MSI used as system clock
  *              - 0x04: HSI used as system clock
  *              - 0x08: HSE used as system clock
  *              - 0x0C: PLL used as system clock
  */
uint8_t RCC_GetSYSCLKSource(void)
{
  return ((uint8_t)(RCC->CFGR & RCC_CFGR_SWS));
}

/**
  * @brief  Configures the AHB clock (HCLK).
  * @note   Depending on the device voltage range, the software has to set correctly
  *         these bits to ensure that the system frequency does not exceed the
  *         maximum allowed frequency (for more details refer to section above
  *         "CPU, AHB and APB busses clocks configuration functions")
  * @param  RCC_SYSCLK: defines the AHB clock divider. This clock is derived from
  *                     the system clock (SYSCLK).
  *   This parameter can be one of the following values:
  *     @arg RCC_SYSCLK_Div1:   AHB clock = SYSCLK
  *     @arg RCC_SYSCLK_Div2:   AHB clock = SYSCLK/2
  *     @arg RCC_SYSCLK_Div4:   AHB clock = SYSCLK/4
  *     @arg RCC_SYSCLK_Div8:   AHB clock = SYSCLK/8
  *     @arg RCC_SYSCLK_Div16:  AHB clock = SYSCLK/16
  *     @arg RCC_SYSCLK_Div64:  AHB clock = SYSCLK/64
  *     @arg RCC_SYSCLK_Div128: AHB clock = SYSCLK/128
  *     @arg RCC_SYSCLK_Div256: AHB clock = SYSCLK/256
  *     @arg RCC_SYSCLK_Div512: AHB clock = SYSCLK/512
  * @retval None
  */
void RCC_HCLKConfig(uint32_t RCC_SYSCLK)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RCC_HCLK(RCC_SYSCLK));

  tmpreg = RCC->CFGR;

  /* Clear HPRE[3:0] bits */
  tmpreg &= ~RCC_CFGR_HPRE;

  /* Set HPRE[3:0] bits according to RCC_SYSCLK value */
  tmpreg |= RCC_SYSCLK;

  /* Store the new value */
  RCC->CFGR = tmpreg;
}

/**
  * @brief  Configures the Low Speed APB clock (PCLK1).
  * @param  RCC_HCLK: defines the APB1 clock divider. This clock is derived from
  *                   the AHB clock (HCLK).
  *   This parameter can be one of the following values:
  *     @arg RCC_HCLK_Div1:  APB1 clock = HCLK
  *     @arg RCC_HCLK_Div2:  APB1 clock = HCLK/2
  *     @arg RCC_HCLK_Div4:  APB1 clock = HCLK/4
  *     @arg RCC_HCLK_Div8:  APB1 clock = HCLK/8
  *     @arg RCC_HCLK_Div16: APB1 clock = HCLK/16
  * @retval None
  */
void RCC_PCLK1Config(uint32_t RCC_HCLK)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RCC_PCLK(RCC_HCLK));

  tmpreg = RCC->CFGR;

  /* Clear PPRE1[2:0] bits */
  tmpreg &= ~RCC_CFGR_PPRE1;

  /* Set PPRE1[2:0] bits according to RCC_HCLK value */
  tmpreg |= RCC_HCLK;

  /* Store the new value */
  RCC->CFGR = tmpreg;
}

/**
  * @brief  Configures the High Speed APB clock (PCLK2).
  * @param  RCC_HCLK: defines the APB2 clock divider. This clock is derived from
  *                   the AHB clock (HCLK).
  *   This parameter can be one of the following values:
  *     @arg RCC_HCLK_Div1:  APB2 clock = HCLK
  *     @arg RCC_HCLK_Div2:  APB2 clock = HCLK/2
  *     @arg RCC_HCLK_Div4:  APB2 clock = HCLK/4
  *     @arg RCC_HCLK_Div8:  APB2 clock = HCLK/8
  *     @arg RCC_HCLK_Div16: APB2 clock = HCLK/16
  * @retval None
  */
void RCC_PCLK2Config(uint32_t RCC_HCLK)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RCC_PCLK(RCC_HCLK));

  tmpreg = RCC->CFGR;

  /* Clear PPRE2[2:0] bits */
  tmpreg &= ~RCC_CFGR_PPRE2;

  /* Set PPRE2[2:0] bits according to RCC_HCLK value */
  tmpreg |= RCC_HCLK << 3;

  /* Store the new value */
  RCC->CFGR = tmpreg;
}

/**
  * @brief  Returns the frequencies of the System, AHB and APB busses clocks.
  * @note     The frequency returned by this function is not the real frequency
  *           in the chip. It is calculated based on the predefined constant and
  *           the source selected by RCC_SYSCLKConfig():
  *
  * @note     If SYSCLK source is MSI, function returns values based on  MSI
  *             Value as defined by the MSI range, refer to RCC_MSIRangeConfig()
  *
  * @note     If SYSCLK source is HSI, function returns values based on HSI_VALUE(*)
  *
  * @note     If SYSCLK source is HSE, function returns values based on HSE_VALUE(**)
  *
  * @note     If SYSCLK source is PLL, function returns values based on HSE_VALUE(**)
  *             or HSI_VALUE(*) multiplied/divided by the PLL factors.
  *
  *         (*) HSI_VALUE is a constant defined in stm32l1xx.h file (default value
  *             16 MHz) but the real value may vary depending on the variations
  *             in voltage and temperature, refer to RCC_AdjustHSICalibrationValue().
  *
  *         (**) HSE_VALUE is a constant defined in stm32l1xx.h file (default value
  *              8 MHz), user has to ensure that HSE_VALUE is same as the real
  *              frequency of the crystal used. Otherwise, this function may
  *              return wrong result.
  *
  *         - The result of this function could be not correct when using fractional
  *           value for HSE crystal.
  *
  * @param  RCC_Clocks: pointer to a RCC_ClocksTypeDef structure which will hold
  *         the clocks frequencies.
  *
  * @note     This function can be used by the user application to compute the
  *           baudrate for the communication peripherals or configure other parameters.
  * @note     Each time SYSCLK, HCLK, PCLK1 and/or PCLK2 clock changes, this function
  *           must be called to update the structure's field. Otherwise, any
  *           configuration based on this function will be incorrect.
  *
  * @retval None
  */
void RCC_GetClocksFreq(RCC_ClocksTypeDef* RCC_Clocks)
{
  uint32_t tmp = 0, pllmul = 0, plldiv = 0, pllsource = 0, presc = 0, msirange = 0;

  /* Get SYSCLK source -------------------------------------------------------*/
  tmp = RCC->CFGR & RCC_CFGR_SWS;

  switch (tmp)
  {
    case 0x00:  /* MSI used as system clock */
      msirange = (RCC->ICSCR & RCC_ICSCR_MSIRANGE ) >> 13;
      RCC_Clocks->SYSCLK_Frequency = (32768 * (1 << (msirange + 1)));
      break;
    case 0x04:  /* HSI used as system clock */
      RCC_Clocks->SYSCLK_Frequency = HSI_VALUE;
      break;
    case 0x08:  /* HSE used as system clock */
      RCC_Clocks->SYSCLK_Frequency = HSE_VALUE;
      break;
    case 0x0C:  /* PLL used as system clock */
      /* Get PLL clock source and multiplication factor ----------------------*/
      pllmul = RCC->CFGR & RCC_CFGR_PLLMUL;
      plldiv = RCC->CFGR & RCC_CFGR_PLLDIV;
      pllmul = PLLMulTable[(pllmul >> 18)];
      plldiv = (plldiv >> 22) + 1;

      pllsource = RCC->CFGR & RCC_CFGR_PLLSRC;

      if (pllsource == 0x00)
      {
        /* HSI oscillator clock selected as PLL clock source */
        RCC_Clocks->SYSCLK_Frequency = (((HSI_VALUE) * pllmul) / plldiv);
      }
      else
      {
        /* HSE selected as PLL clock source */
        RCC_Clocks->SYSCLK_Frequency = (((HSE_VALUE) * pllmul) / plldiv);
      }
      break;
    default: /* MSI used as system clock */
      msirange = (RCC->ICSCR & RCC_ICSCR_MSIRANGE ) >> 13;
      RCC_Clocks->SYSCLK_Frequency = (32768 * (1 << (msirange + 1)));
      break;
  }
  /* Compute HCLK, PCLK1, PCLK2 and ADCCLK clocks frequencies ----------------*/
  /* Get HCLK prescaler */
  tmp = RCC->CFGR & RCC_CFGR_HPRE;
  tmp = tmp >> 4;
  presc = APBAHBPrescTable[tmp];
  /* HCLK clock frequency */
  RCC_Clocks->HCLK_Frequency = RCC_Clocks->SYSCLK_Frequency >> presc;

  /* Get PCLK1 prescaler */
  tmp = RCC->CFGR & RCC_CFGR_PPRE1;
  tmp = tmp >> 8;
  presc = APBAHBPrescTable[tmp];
  /* PCLK1 clock frequency */
  RCC_Clocks->PCLK1_Frequency = RCC_Clocks->HCLK_Frequency >> presc;

  /* Get PCLK2 prescaler */
  tmp = RCC->CFGR & RCC_CFGR_PPRE2;
  tmp = tmp >> 11;
  presc = APBAHBPrescTable[tmp];
  /* PCLK2 clock frequency */
  RCC_Clocks->PCLK2_Frequency = RCC_Clocks->HCLK_Frequency >> presc;
}

/**
  * @}
  */

/** @defgroup RCC_Group3 Peripheral clocks configuration functions
 *  @brief   Peripheral clocks configuration functions
 *
@verbatim
 ===============================================================================
             ##### Peripheral clocks configuration functions #####
 ===============================================================================
    [..] This section provide functions allowing to configure the Peripheral clocks.
         (#) The RTC/LCD clock which is derived from the LSE, LSI or 1 MHz HSE_RTC
         (HSE divided by a programmable prescaler).
         (#) After restart from Reset or wakeup from STANDBY, all peripherals are
             off except internal SRAM, Flash and JTAG. Before to start using a
             peripheral you have to enable its interface clock. You can do this
             using RCC_AHBPeriphClockCmd(), RCC_APB2PeriphClockCmd() and
             RCC_APB1PeriphClockCmd() functions.

         (#) To reset the peripherals configuration (to the default state after
             device reset) you can use RCC_AHBPeriphResetCmd(),
             RCC_APB2PeriphResetCmd() and RCC_APB1PeriphResetCmd() functions.
         (#) To further reduce power consumption in SLEEP mode the peripheral
             clocks can be disabled prior to executing the WFI or WFE instructions.
             You can do this using RCC_AHBPeriphClockLPModeCmd(),
             RCC_APB2PeriphClockLPModeCmd() and RCC_APB1PeriphClockLPModeCmd()
             functions.

@endverbatim
  * @{
  */

/**
  * @brief  Configures the RTC and LCD clock (RTCCLK / LCDCLK).
  * @note     As the RTC clock configuration bits are in the RTC domain and write
  *           access is denied to this domain after reset, you have to enable write
  *           access using PWR_RTCAccessCmd(ENABLE) function before to configure
  *           the RTC clock source (to be done once after reset).
  * @note     Once the RTC clock is configured it can't be changed unless the RTC
  *           is reset using RCC_RTCResetCmd function, or by a Power On Reset (POR)
  * @note     The RTC clock (RTCCLK) is used also to clock the LCD (LCDCLK).
  *
  * @param  RCC_RTCCLKSource: specifies the RTC clock source.
  *   This parameter can be one of the following values:
  *     @arg RCC_RTCCLKSource_LSE: LSE selected as RTC clock
  *     @arg RCC_RTCCLKSource_LSI: LSI selected as RTC clock
  *     @arg RCC_RTCCLKSource_HSE_Div2: HSE divided by 2 selected as RTC clock
  *     @arg RCC_RTCCLKSource_HSE_Div4: HSE divided by 4 selected as RTC clock
  *     @arg RCC_RTCCLKSource_HSE_Div8: HSE divided by 8 selected as RTC clock
  *     @arg RCC_RTCCLKSource_HSE_Div16: HSE divided by 16 selected as RTC clock
  *
  * @note     If the LSE or LSI is used as RTC clock source, the RTC continues to
  *           work in STOP and STANDBY modes, and can be used as wakeup source.
  *           However, when the HSE clock is used as RTC clock source, the RTC
  *           cannot be used in STOP and STANDBY modes.
  *
  * @note     The maximum input clock frequency for RTC is 1MHz (when using HSE as
  *           RTC clock source).
  *
  * @retval None
  */
void RCC_RTCCLKConfig(uint32_t RCC_RTCCLKSource)
{
  uint32_t 	tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RCC_RTCCLK_SOURCE(RCC_RTCCLKSource));

  if ((RCC_RTCCLKSource & RCC_CSR_RTCSEL_HSE) == RCC_CSR_RTCSEL_HSE)
  {
    /* If HSE is selected as RTC clock source, configure HSE division factor for RTC clock */
    tmpreg = RCC->CR;

    /* Clear RTCPRE[1:0] bits */
    tmpreg &= ~RCC_CR_RTCPRE;

    /* Configure HSE division factor for RTC clock */
    tmpreg |= (RCC_RTCCLKSource & RCC_CR_RTCPRE);

    /* Store the new value */
    RCC->CR = tmpreg;
  }

  RCC->CSR &= ~RCC_CSR_RTCSEL;

  /* Select the RTC clock source */
  RCC->CSR |= (RCC_RTCCLKSource & RCC_CSR_RTCSEL);
}

/**
  * @brief  Enables or disables the RTC clock.
  * @note   This function must be used only after the RTC clock source was selected
  *         using the RCC_RTCCLKConfig function.
  * @param  NewState: new state of the RTC clock.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_RTCCLKCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CSR_RTCEN_BB = (uint32_t)NewState;
}

/**
  * @brief  Forces or releases the RTC peripheral and associated resources reset.
  * @note   This function resets the RTC peripheral, RTC clock source selection
  *         (in RCC_CSR) and the backup registers.
  * @param  NewState: new state of the RTC reset.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_RTCResetCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  *(__IO uint32_t *) CSR_RTCRST_BB = (uint32_t)NewState;
}

/**
  * @brief  Enables or disables the AHB peripheral clock.
  * @note   After reset, the peripheral clock (used for registers read/write access)
  *         is disabled and the application software has to enable this clock before
  *         using it.
  * @param  RCC_AHBPeriph: specifies the AHB peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_AHBPeriph_GPIOA:         GPIOA clock
  *     @arg RCC_AHBPeriph_GPIOB:         GPIOB clock
  *     @arg RCC_AHBPeriph_GPIOC:         GPIOC clock
  *     @arg RCC_AHBPeriph_GPIOD:         GPIOD clock
  *     @arg RCC_AHBPeriph_GPIOE:         GPIOE clock
  *     @arg RCC_AHBPeriph_GPIOH:         GPIOH clock
  *     @arg RCC_AHBPeriph_GPIOF:         GPIOF clock
  *     @arg RCC_AHBPeriph_GPIOG:         GPIOG clock
  *     @arg RCC_AHBPeriph_CRC:           CRC clock
  *     @arg RCC_AHBPeriph_FLITF: (has effect only when the Flash memory is in power down mode)
  *     @arg RCC_AHBPeriph_DMA1:          DMA1 clock
  *     @arg RCC_AHBPeriph_DMA2:          DMA2 clock
  *     @arg RCC_AHBPeriph_AES:           AES clock
  *     @arg RCC_AHBPeriph_FSMC:          FSMC clock
  * @param  NewState: new state of the specified peripheral clock.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_AHBPeriphClockCmd(uint32_t RCC_AHBPeriph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_AHB_PERIPH(RCC_AHBPeriph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->AHBENR |= RCC_AHBPeriph;
  }
  else
  {
    RCC->AHBENR &= ~RCC_AHBPeriph;
  }
}

/**
  * @brief  Enables or disables the High Speed APB (APB2) peripheral clock.
  * @note   After reset, the peripheral clock (used for registers read/write access)
  *         is disabled and the application software has to enable this clock before
  *         using it.
  * @param  RCC_APB2Periph: specifies the APB2 peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB2Periph_SYSCFG: SYSCFG APB2 Clock.
  *     @arg RCC_APB2Periph_TIM9: TIM9 APB2 Clock.
  *     @arg RCC_APB2Periph_TIM10: TIM10 APB2 Clock.
  *     @arg RCC_APB2Periph_TIM11: TIM11 APB2 Clock.
  *     @arg RCC_APB2Periph_ADC1: ADC1 APB2 Clock.
  *     @arg RCC_APB2Periph_SDIO: SDIO APB2 Clock.
  *     @arg RCC_APB2Periph_SPI1: SPI1 APB2 Clock.
  *     @arg RCC_APB2Periph_USART1: USART1 APB2 Clock.
  * @param  NewState: new state of the specified peripheral clock.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_APB2PeriphClockCmd(uint32_t RCC_APB2Periph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_APB2_PERIPH(RCC_APB2Periph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->APB2ENR |= RCC_APB2Periph;
  }
  else
  {
    RCC->APB2ENR &= ~RCC_APB2Periph;
  }
}

/**
  * @brief  Enables or disables the Low Speed APB (APB1) peripheral clock.
  * @note   After reset, the peripheral clock (used for registers read/write access)
  *         is disabled and the application software has to enable this clock before
  *         using it.
  * @param  RCC_APB1Periph: specifies the APB1 peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB1Periph_TIM2:      TIM2 clock
  *     @arg RCC_APB1Periph_TIM3:      TIM3 clock
  *     @arg RCC_APB1Periph_TIM4:      TIM4 clock
  *     @arg RCC_APB1Periph_TIM5:      TIM5 clock
  *     @arg RCC_APB1Periph_TIM6:      TIM6 clock
  *     @arg RCC_APB1Periph_TIM7:      TIM7 clock
  *     @arg RCC_APB1Periph_LCD:       LCD clock
  *     @arg RCC_APB1Periph_WWDG:      WWDG clock
  *     @arg RCC_APB1Periph_SPI2:      SPI2 clock
  *     @arg RCC_APB1Periph_SPI3:      SPI3 clock
  *     @arg RCC_APB1Periph_USART2:    USART2 clock
  *     @arg RCC_APB1Periph_USART3:    USART3 clock
  *     @arg RCC_APB1Periph_UART4:     UART4 clock
  *     @arg RCC_APB1Periph_UART5:     UART5 clock
  *     @arg RCC_APB1Periph_I2C1:      I2C1 clock
  *     @arg RCC_APB1Periph_I2C2:      I2C2 clock
  *     @arg RCC_APB1Periph_USB:       USB clock
  *     @arg RCC_APB1Periph_PWR:       PWR clock
  *     @arg RCC_APB1Periph_DAC:       DAC clock
  *     @arg RCC_APB1Periph_COMP       COMP  clock
  * @param  NewState: new state of the specified peripheral clock.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_APB1PeriphClockCmd(uint32_t RCC_APB1Periph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_APB1_PERIPH(RCC_APB1Periph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->APB1ENR |= RCC_APB1Periph;
  }
  else
  {
    RCC->APB1ENR &= ~RCC_APB1Periph;
  }
}

/**
  * @brief  Forces or releases AHB peripheral reset.
  * @param  RCC_AHBPeriph: specifies the AHB peripheral to reset.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_AHBPeriph_GPIOA:         GPIOA clock
  *     @arg RCC_AHBPeriph_GPIOB:         GPIOB clock
  *     @arg RCC_AHBPeriph_GPIOC:         GPIOC clock
  *     @arg RCC_AHBPeriph_GPIOD:         GPIOD clock
  *     @arg RCC_AHBPeriph_GPIOE:         GPIOE clock
  *     @arg RCC_AHBPeriph_GPIOH:         GPIOH clock
  *     @arg RCC_AHBPeriph_GPIOF:         GPIOF clock
  *     @arg RCC_AHBPeriph_GPIOG:         GPIOG clock
  *     @arg RCC_AHBPeriph_CRC:           CRC clock
  *     @arg RCC_AHBPeriph_FLITF: (has effect only when the Flash memory is in power down mode)
  *     @arg RCC_AHBPeriph_DMA1:          DMA1 clock
  *     @arg RCC_AHBPeriph_DMA2:          DMA2 clock
  *     @arg RCC_AHBPeriph_AES:           AES clock
  *     @arg RCC_AHBPeriph_FSMC:          FSMC clock
  * @param  NewState: new state of the specified peripheral reset.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_AHBPeriphResetCmd(uint32_t RCC_AHBPeriph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_AHB_PERIPH(RCC_AHBPeriph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->AHBRSTR |= RCC_AHBPeriph;
  }
  else
  {
    RCC->AHBRSTR &= ~RCC_AHBPeriph;
  }
}

/**
  * @brief  Forces or releases High Speed APB (APB2) peripheral reset.
  * @param  RCC_APB2Periph: specifies the APB2 peripheral to reset.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB2Periph_SYSCFG:       SYSCFG clock
  *     @arg RCC_APB2Periph_TIM9:         TIM9 clock
  *     @arg RCC_APB2Periph_TIM10:        TIM10 clock
  *     @arg RCC_APB2Periph_TIM11:        TIM11 clock
  *     @arg RCC_APB2Periph_ADC1:         ADC1 clock
  *     @arg RCC_APB2Periph_SDIO:         SDIO clock
  *     @arg RCC_APB2Periph_SPI1:         SPI1 clock
  *     @arg RCC_APB2Periph_USART1:       USART1 clock
  * @param  NewState: new state of the specified peripheral reset.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_APB2PeriphResetCmd(uint32_t RCC_APB2Periph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_APB2_PERIPH(RCC_APB2Periph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->APB2RSTR |= RCC_APB2Periph;
  }
  else
  {
    RCC->APB2RSTR &= ~RCC_APB2Periph;
  }
}

/**
  * @brief  Forces or releases Low Speed APB (APB1) peripheral reset.
  * @param  RCC_APB1Periph: specifies the APB1 peripheral to reset.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB1Periph_TIM2:           TIM2 clock
  *     @arg RCC_APB1Periph_TIM3:           TIM3 clock
  *     @arg RCC_APB1Periph_TIM4:           TIM4 clock
  *     @arg RCC_APB1Periph_TIM5:           TIM5 clock
  *     @arg RCC_APB1Periph_TIM6:           TIM6 clock
  *     @arg RCC_APB1Periph_TIM7:           TIM7 clock
  *     @arg RCC_APB1Periph_LCD:            LCD clock
  *     @arg RCC_APB1Periph_WWDG:           WWDG clock
  *     @arg RCC_APB1Periph_SPI2:           SPI2 clock
  *     @arg RCC_APB1Periph_SPI3:           SPI3 clock
  *     @arg RCC_APB1Periph_USART2:         USART2 clock
  *     @arg RCC_APB1Periph_USART3:         USART3 clock
  *     @arg RCC_APB1Periph_UART4:          UART4 clock
  *     @arg RCC_APB1Periph_UART5:          UART5 clock
  *     @arg RCC_APB1Periph_I2C1:           I2C1 clock
  *     @arg RCC_APB1Periph_I2C2:           I2C2 clock
  *     @arg RCC_APB1Periph_USB:            USB clock
  *     @arg RCC_APB1Periph_PWR:            PWR clock
  *     @arg RCC_APB1Periph_DAC:            DAC clock
  *     @arg RCC_APB1Periph_COMP
  * @param  NewState: new state of the specified peripheral clock.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_APB1PeriphResetCmd(uint32_t RCC_APB1Periph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_APB1_PERIPH(RCC_APB1Periph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->APB1RSTR |= RCC_APB1Periph;
  }
  else
  {
    RCC->APB1RSTR &= ~RCC_APB1Periph;
  }
}

/**
  * @brief  Enables or disables the AHB peripheral clock during SLEEP mode.
  * @note     Peripheral clock gating in SLEEP mode can be used to further reduce
  *           power consumption.
  *         - After wakeup from SLEEP mode, the peripheral clock is enabled again.
  *         - By default, all peripheral clocks are enabled during SLEEP mode.
  * @param  RCC_AHBPeriph: specifies the AHB peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_AHBPeriph_GPIOA:           GPIOA clock
  *     @arg RCC_AHBPeriph_GPIOB:           GPIOB clock
  *     @arg RCC_AHBPeriph_GPIOC:           GPIOC clock
  *     @arg RCC_AHBPeriph_GPIOD:           GPIOD clock
  *     @arg RCC_AHBPeriph_GPIOE:           GPIOE clock
  *     @arg RCC_AHBPeriph_GPIOH:           GPIOH clock
  *     @arg RCC_AHBPeriph_GPIOF:           GPIOF clock
  *     @arg RCC_AHBPeriph_GPIOG:           GPIOG clock
  *     @arg RCC_AHBPeriph_CRC:             CRC clock
  *     @arg RCC_AHBPeriph_FLITF: (has effect only when the Flash memory is in power down mode)
  *     @arg RCC_AHBPeriph_SRAM:            SRAM clock
  *     @arg RCC_AHBPeriph_DMA1:            DMA1 clock
  *     @arg RCC_AHBPeriph_DMA2:            DMA2 clock
  *     @arg RCC_AHBPeriph_AES:             AES clock
  *     @arg RCC_AHBPeriph_FSMC:            FSMC clock
  * @param  NewState: new state of the specified peripheral clock.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_AHBPeriphClockLPModeCmd(uint32_t RCC_AHBPeriph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_AHB_LPMODE_PERIPH(RCC_AHBPeriph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->AHBLPENR |= RCC_AHBPeriph;
  }
  else
  {
    RCC->AHBLPENR &= ~RCC_AHBPeriph;
  }
}

/**
  * @brief  Enables or disables the APB2 peripheral clock during SLEEP mode.
  * @note     Peripheral clock gating in SLEEP mode can be used to further reduce
  *           power consumption.
  * @note     After wakeup from SLEEP mode, the peripheral clock is enabled again.
  * @note     By default, all peripheral clocks are enabled during SLEEP mode.
  * @param  RCC_APB2Periph: specifies the APB2 peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB2Periph_SYSCFG:          SYSCFG clock
  *     @arg RCC_APB2Periph_TIM9:            TIM9 clock
  *     @arg RCC_APB2Periph_TIM10:           TIM10 clock
  *     @arg RCC_APB2Periph_TIM11:           TIM11 clock
  *     @arg RCC_APB2Periph_ADC1:            ADC1 clock
  *     @arg RCC_APB2Periph_SDIO:            SDIO clock
  *     @arg RCC_APB2Periph_SPI1:            SPI1 clock
  *     @arg RCC_APB2Periph_USART1:          USART1 clock
  * @param  NewState: new state of the specified peripheral clock.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_APB2PeriphClockLPModeCmd(uint32_t RCC_APB2Periph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_APB2_PERIPH(RCC_APB2Periph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->APB2LPENR |= RCC_APB2Periph;
  }
  else
  {
    RCC->APB2LPENR &= ~RCC_APB2Periph;
  }
}

/**
  * @brief  Enables or disables the APB1 peripheral clock during SLEEP mode.
  * @note     Peripheral clock gating in SLEEP mode can be used to further reduce
  *           power consumption.
  * @note     After wakeup from SLEEP mode, the peripheral clock is enabled again.
  * @note     By default, all peripheral clocks are enabled during SLEEP mode.
  * @param  RCC_APB1Periph: specifies the APB1 peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB1Periph_TIM2:                 TIM2 clock
  *     @arg RCC_APB1Periph_TIM3:                 TIM3 clock
  *     @arg RCC_APB1Periph_TIM4:                 TIM4 clock
  *     @arg RCC_APB1Periph_TIM5:                 TIM5 clock
  *     @arg RCC_APB1Periph_TIM6:                 TIM6 clock
  *     @arg RCC_APB1Periph_TIM7:                 TIM7 clock
  *     @arg RCC_APB1Periph_LCD:                  LCD clock
  *     @arg RCC_APB1Periph_WWDG:                 WWDG clock
  *     @arg RCC_APB1Periph_SPI2:                 SPI2 clock
  *     @arg RCC_APB1Periph_SPI3:                 SPI3 clock
  *     @arg RCC_APB1Periph_USART2:               USART2 clock
  *     @arg RCC_APB1Periph_USART3:               USART3 clock
  *     @arg RCC_APB1Periph_UART4:                UART4 clock
  *     @arg RCC_APB1Periph_UART5:                UART5 clock
  *     @arg RCC_APB1Periph_I2C1:                 I2C1 clock
  *     @arg RCC_APB1Periph_I2C2:                 I2C2 clock
  *     @arg RCC_APB1Periph_USB:                  USB clock
  *     @arg RCC_APB1Periph_PWR:                  PWR clock
  *     @arg RCC_APB1Periph_DAC:                  DAC clock
  *     @arg RCC_APB1Periph_COMP:                 COMP clock
  * @param  NewState: new state
  * @param  NewState: new state of the specified peripheral clock.
  *         This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_APB1PeriphClockLPModeCmd(uint32_t RCC_APB1Periph, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_APB1_PERIPH(RCC_APB1Periph));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    RCC->APB1LPENR |= RCC_APB1Periph;
  }
  else
  {
    RCC->APB1LPENR &= ~RCC_APB1Periph;
  }
}

/**
  * @}
  */

/** @defgroup RCC_Group4 Interrupts and flags management functions
 *  @brief   Interrupts and flags management functions
 *
@verbatim
 ===============================================================================
             ##### Interrupts and flags management functions #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Enables or disables the specified RCC interrupts.
  * @note   The CSS interrupt doesn't have an enable bit; once the CSS is enabled
  *         and if the HSE clock fails, the CSS interrupt occurs and an NMI is
  *         automatically generated. The NMI will be executed indefinitely, and
  *         since NMI has higher priority than any other IRQ (and main program)
  *         the application will be stacked in the NMI ISR unless the CSS interrupt
  *         pending bit is cleared.
  * @param  RCC_IT: specifies the RCC interrupt sources to be enabled or disabled.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_IT_LSIRDY: LSI ready interrupt
  *     @arg RCC_IT_LSERDY: LSE ready interrupt
  *     @arg RCC_IT_HSIRDY: HSI ready interrupt
  *     @arg RCC_IT_HSERDY: HSE ready interrupt
  *     @arg RCC_IT_PLLRDY: PLL ready interrupt
  *     @arg RCC_IT_MSIRDY: MSI ready interrupt
  *     @arg RCC_IT_LSECSS: LSE CSS interrupt
  * @param  NewState: new state of the specified RCC interrupts.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_ITConfig(uint8_t RCC_IT, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RCC_IT(RCC_IT));
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Perform Byte access to RCC_CIR[12:8] bits to enable the selected interrupts */
    *(__IO uint8_t *) CIR_BYTE2_ADDRESS |= RCC_IT;
  }
  else
  {
    /* Perform Byte access to RCC_CIR[12:8] bits to disable the selected interrupts */
    *(__IO uint8_t *) CIR_BYTE2_ADDRESS &= (uint8_t)~RCC_IT;
  }
}

/**
  * @brief  Checks whether the specified RCC flag is set or not.
  * @param  RCC_FLAG: specifies the flag to check.
  *   This parameter can be one of the following values:
  *     @arg RCC_FLAG_HSIRDY: HSI oscillator clock ready
  *     @arg RCC_FLAG_MSIRDY: MSI oscillator clock ready
  *     @arg RCC_FLAG_HSERDY: HSE oscillator clock ready
  *     @arg RCC_FLAG_PLLRDY: PLL clock ready
  *     @arg RCC_FLAG_LSECSS: LSE oscillator clock CSS detected
  *     @arg RCC_FLAG_LSERDY: LSE oscillator clock ready
  *     @arg RCC_FLAG_LSIRDY: LSI oscillator clock ready
  *     @arg RCC_FLAG_OBLRST: Option Byte Loader (OBL) reset
  *     @arg RCC_FLAG_PINRST: Pin reset
  *     @arg RCC_FLAG_PORRST: POR/PDR reset
  *     @arg RCC_FLAG_SFTRST: Software reset
  *     @arg RCC_FLAG_IWDGRST: Independent Watchdog reset
  *     @arg RCC_FLAG_WWDGRST: Window Watchdog reset
  *     @arg RCC_FLAG_LPWRRST: Low Power reset
  * @retval The new state of RCC_FLAG (SET or RESET).
  */
FlagStatus RCC_GetFlagStatus(uint8_t RCC_FLAG)
{
  uint32_t tmp = 0;
  uint32_t statusreg = 0;
  FlagStatus bitstatus = RESET;

  /* Check the parameters */
  assert_param(IS_RCC_FLAG(RCC_FLAG));

  /* Get the RCC register index */
  tmp = RCC_FLAG >> 5;

  if (tmp == 1)               /* The flag to check is in CR register */
  {
    statusreg = RCC->CR;
  }
  else          /* The flag to check is in CSR register (tmp == 2) */
  {
    statusreg = RCC->CSR;
  }

  /* Get the flag position */
  tmp = RCC_FLAG & FLAG_MASK;

  if ((statusreg & ((uint32_t)1 << tmp)) != (uint32_t)RESET)
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
  * @brief  Clears the RCC reset flags.
  *         The reset flags are: RCC_FLAG_OBLRST, RCC_FLAG_PINRST, RCC_FLAG_PORRST,
  *         RCC_FLAG_SFTRST, RCC_FLAG_IWDGRST, RCC_FLAG_WWDGRST, RCC_FLAG_LPWRRST.
  * @param  None
  * @retval None
  */
void RCC_ClearFlag(void)
{
  /* Set RMVF bit to clear the reset flags */
  RCC->CSR |= RCC_CSR_RMVF;
}

/**
  * @brief  Checks whether the specified RCC interrupt has occurred or not.
  * @param  RCC_IT: specifies the RCC interrupt source to check.
  *   This parameter can be one of the following values:
  *     @arg RCC_IT_LSIRDY: LSI ready interrupt
  *     @arg RCC_IT_LSERDY: LSE ready interrupt
  *     @arg RCC_IT_HSIRDY: HSI ready interrupt
  *     @arg RCC_IT_HSERDY: HSE ready interrupt
  *     @arg RCC_IT_PLLRDY: PLL ready interrupt
  *     @arg RCC_IT_MSIRDY: MSI ready interrupt
  *     @arg RCC_IT_LSECSS: LSE CSS interrupt
  *     @arg RCC_IT_CSS: Clock Security System interrupt
  * @retval The new state of RCC_IT (SET or RESET).
  */
ITStatus RCC_GetITStatus(uint8_t RCC_IT)
{
  ITStatus bitstatus = RESET;
  /* Check the parameters */
  assert_param(IS_RCC_GET_IT(RCC_IT));

  /* Check the status of the specified RCC interrupt */
  if ((RCC->CIR & RCC_IT) != (uint32_t)RESET)
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  /* Return the RCC_IT status */
  return  bitstatus;
}

/**
  * @brief  Clears the RCC's interrupt pending bits.
  * @param  RCC_IT: specifies the interrupt pending bit to clear.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_IT_LSIRDY: LSI ready interrupt
  *     @arg RCC_IT_LSERDY: LSE ready interrupt
  *     @arg RCC_IT_HSIRDY: HSI ready interrupt
  *     @arg RCC_IT_HSERDY: HSE ready interrupt
  *     @arg RCC_IT_PLLRDY: PLL ready interrupt
  *     @arg RCC_IT_MSIRDY: MSI ready interrupt
  *     @arg RCC_IT_LSECSS: LSE CSS interrupt
  *     @arg RCC_IT_CSS: Clock Security System interrupt
  * @retval None
  */
void RCC_ClearITPendingBit(uint8_t RCC_IT)
{
  /* Check the parameters */
  assert_param(IS_RCC_CLEAR_IT(RCC_IT));

  /* Perform Byte access to RCC_CIR[23:16] bits to clear the selected interrupt
     pending bits */
  *(__IO uint8_t *) CIR_BYTE3_ADDRESS = RCC_IT;
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
