/**
  ******************************************************************************
  * @file    stm32l1xx_rcc.c
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    07/02/2010
  * @brief   This file provides all the RCC firmware functions.
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
#include "stm32l1xx_rcc.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup RCC 
  * @brief RCC driver modules
  * @{
  */ 

/** @defgroup RCC_Private_TypesDefinitions
  * @{
  */

/**
  * @}
  */

/** @defgroup RCC_Private_Defines
  * @{
  */

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

/**
  * @}
  */ 

/** @defgroup RCC_Private_Macros
  * @{
  */ 

/**
  * @}
  */ 

/** @defgroup RCC_Private_Variables
  * @{
  */ 

static __I uint8_t PLLMulTable[9] = {3, 4, 6, 8, 12, 16, 24, 32, 48};
static __I uint8_t APBAHBPrescTable[16] = {0, 0, 0, 0, 1, 2, 3, 4, 1, 2, 3, 4, 6, 7, 8, 9};
static __I uint8_t MSITable[7] = {0, 0, 0, 0, 1, 2, 4};

/**
  * @}
  */

/** @defgroup RCC_Private_FunctionPrototypes
  * @{
  */

/**
  * @}
  */

/** @defgroup RCC_Private_Functions
  * @{
  */

/**
  * @brief  Resets the RCC clock configuration to the default reset state.
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
  * @note   HSE can not be stopped if it is used directly or through the PLL as system clock.
  * @param RCC_HSE: specifies the new state of the HSE.
  *   This parameter can be one of the following values:
  *     @arg RCC_HSE_OFF: HSE oscillator OFF
  *     @arg RCC_HSE_ON: HSE oscillator ON
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
  * @param  None
  * @retval An ErrorStatus enumuration value:
  *          - SUCCESS: HSE oscillator is stable and ready to use
  *          - ERROR: HSE oscillator not yet ready
  */
ErrorStatus RCC_WaitForHSEStartUp(void)
{
  __IO uint32_t StartUpCounter = 0;
  ErrorStatus status = ERROR;
  FlagStatus HSEStatus = RESET;
  
  /* Wait till HSE is ready and if Time out is reached exit */
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
  * @brief  Adjusts the Internal High Speed oscillator (HSI) calibration value.
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
  * @brief  Adjusts the Internal Multi Speed oscillator (MSI) calibration value.
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
  * @param  RCC_MSIRange: specifies the MSI Clcok range.
  *   This parameter must be one of the following values:
  *     @arg RCC_MSIRange_64KHz:  MSI clock is around 64 KHz
  *     @arg RCC_MSIRange_128KHz: MSI clock is around 128 KHz
  *     @arg RCC_MSIRange_256KHz: MSI clock is around 256 KHz
  *     @arg RCC_MSIRange_512KHz: MSI clock is around 512 KHz
  *     @arg RCC_MSIRange_1MHz:   MSI clock is around 1 MHz
  *     @arg RCC_MSIRange_2MHz:   MSI clock is around 2 MHz
  *     @arg RCC_MSIRange_4MHz:   MSI clock is around 4 MHz             
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
  * @note   MSI can not be stopped if it is used directly as system clock.
  * @param  NewState: new state of the MSI.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_MSICmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  *(__IO uint32_t *) CR_MSION_BB = (uint32_t)NewState;
}

/**
  * @brief  Enables or disables the Internal High Speed oscillator (HSI).
  * @note   HSI can not be stopped if it is used directly or through the PLL as system clock.
  * @param  NewState: new state of the HSI.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_HSICmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  *(__IO uint32_t *) CR_HSION_BB = (uint32_t)NewState;
}

/**
  * @brief  Configures the PLL clock source and multiplication factor.
  * @note   This function must be used only when the PLL is disabled.
  * @param  RCC_PLLSource: specifies the PLL entry clock source.
  *   This parameter can be one of the following values:
  *     @arg RCC_PLLSource_HSI: HSI oscillator clock selected as PLL clock entry
  *     @arg RCC_PLLSource_HSE: HSE oscillator clock selected as PLL clock entry
  * @param  RCC_PLLMul: specifies the PLL multiplication factor.
  *   This parameter can be:
  *     @arg RCC_PLLMul_3: PLL Clock entry multiplied by 3
  *     @arg RCC_PLLMul_4: PLL Clock entry multiplied by 4
  *     @arg RCC_PLLMul_6: PLL Clock entry multiplied by 6
  *     @arg RCC_PLLMul_8: PLL Clock entry multiplied by 8
  *     @arg RCC_PLLMul_12: PLL Clock entry multiplied by 12
  *     @arg RCC_PLLMul_16: PLL Clock entry multiplied by 16  
  *     @arg RCC_PLLMul_24: PLL Clock entry multiplied by 24
  *     @arg RCC_PLLMul_32: PLL Clock entry multiplied by 32
  *     @arg RCC_PLLMul_48: PLL Clock entry multiplied by 48             
  * @param  RCC_PLLDiv: specifies the PLL division factor.
  *   This parameter can be:
  *     @arg RCC_PLLDiv_2: PLL Clock output divided by 2  
  *     @arg RCC_PLLDiv_3: PLL Clock output divided by 3         
  *     @arg RCC_PLLDiv_4: PLL Clock output divided by 4   
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
  * @note   The PLL can not be disabled if it is used as system clock.
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
  * @brief  Configures the system clock (SYSCLK).
  * @param  RCC_SYSCLKSource: specifies the clock source used as system clock. 
  *   This parameter can be one of the following values:
  *     @arg RCC_SYSCLKSource_MSI:    MSI selected as system clock
  *     @arg RCC_SYSCLKSource_HSI:    HSI selected as system clock
  *     @arg RCC_SYSCLKSource_HSE:    HSE selected as system clock
  *     @arg RCC_SYSCLKSource_PLLCLK: PLL selected as system clock
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
  * @brief  Enables or disables the specified RCC interrupts.
  * @param  RCC_IT: specifies the RCC interrupt sources to be enabled or disabled.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_IT_LSIRDY: LSI ready interrupt
  *     @arg RCC_IT_LSERDY: LSE ready interrupt
  *     @arg RCC_IT_HSIRDY: HSI ready interrupt
  *     @arg RCC_IT_HSERDY: HSE ready interrupt
  *     @arg RCC_IT_PLLRDY: PLL ready interrupt
  *     @arg RCC_IT_MSIRDY: MSI ready interrupt
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
  * @brief  Configures the External Low Speed oscillator (LSE).
  * @param  RCC_LSE: specifies the new state of the LSE.
  *   This parameter can be one of the following values:
  *     @arg RCC_LSE_OFF: LSE oscillator OFF
  *     @arg RCC_LSE_ON: LSE oscillator ON
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
  * @note   LSI can not be disabled if the IWDG is running.
  * @param  NewState: new state of the LSI.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_LSICmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  *(__IO uint32_t *) CSR_LSION_BB = (uint32_t)NewState;
}

/**
  * @brief  Configures the RTC and LCD clock (RTCCLK / LCDCLK).
  * @note   
  *   - Once the RTC clock is selected it can't be changed unless the RTC is
  *     reset using RCC_RTCResetCmd function.
  *   - This RTC clock (RTCCLK) is used to clock the LCD (LCDCLK).  
  * @param  RCC_RTCCLKSource: specifies the RTC clock source.
  *   This parameter can be one of the following values:
  *     @arg RCC_RTCCLKSource_LSE: LSE selected as RTC clock
  *     @arg RCC_RTCCLKSource_LSI: LSI selected as RTC clock
  *     @arg RCC_RTCCLKSource_HSE_Div2: HSE divided by 2 selected as RTC clock
  *     @arg RCC_RTCCLKSource_HSE_Div4: HSE divided by 4 selected as RTC clock
  *     @arg RCC_RTCCLKSource_HSE_Div8: HSE divided by 8 selected as RTC clock
  *     @arg RCC_RTCCLKSource_HSE_Div16: HSE divided by 16 selected as RTC clock      
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
  * @note   This function must be used only after the RTC clock was selected using the 
  *   RCC_RTCCLKConfig function.
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
  * @brief  Forces or releases the RTC peripheral reset.
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
  * @brief  Returns the frequencies of different on chip clocks.
  * @param  RCC_Clocks: pointer to a RCC_ClocksTypeDef structure which will hold 
  *   the clocks frequencies.
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
      RCC_Clocks->SYSCLK_Frequency = (((1 << msirange) * 64000) - (MSITable[msirange] * 24000));
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
        /* HSI oscillator clock selected as PLL clock entry */
        RCC_Clocks->SYSCLK_Frequency = (((HSI_VALUE) * pllmul) / plldiv);
      }
      else
      {
        /* HSE selected as PLL clock entry */
        RCC_Clocks->SYSCLK_Frequency = (((HSE_VALUE) * pllmul) / plldiv);
      }
      break;
    default:
      RCC_Clocks->SYSCLK_Frequency = HSI_VALUE;
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
  * @brief  Enables or disables the AHB peripheral clock.
  * @param  RCC_AHBPeriph: specifies the AHB peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_AHBPeriph_GPIOA
  *     @arg RCC_AHBPeriph_GPIOB
  *     @arg RCC_AHBPeriph_GPIOC  
  *     @arg RCC_AHBPeriph_GPIOD
  *     @arg RCC_AHBPeriph_GPIOE
  *     @arg RCC_AHBPeriph_GPIOH
  *     @arg RCC_AHBPeriph_CRC
  *     @arg RCC_AHBPeriph_FLITF (has effect only when the Flash memory is in power down mode)  
  *     @arg RCC_AHBPeriph_DMA1
  * @param  NewState: new state of the specified peripheral clock.
  *   This parameter can be: ENABLE or DISABLE.
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
  * @param  RCC_APB2Periph: specifies the APB2 peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB2Periph_SYSCFG
  *     @arg RCC_APB2Periph_TIM9
  *     @arg RCC_APB2Periph_TIM10
  *     @arg RCC_APB2Periph_TIM11
  *     @arg RCC_APB2Periph_ADC1
  *     @arg RCC_APB2Periph_SPI1
  *     @arg RCC_APB2Periph_USART1            
  * @param  NewState: new state of the specified peripheral clock.
  *   This parameter can be: ENABLE or DISABLE.
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
  * @param  RCC_APB1Periph: specifies the APB1 peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB1Periph_TIM2
  *     @arg RCC_APB1Periph_TIM3
  *     @arg RCC_APB1Periph_TIM4
  *     @arg RCC_APB1Periph_TIM6
  *     @arg RCC_APB1Periph_TIM7
  *     @arg RCC_APB1Periph_LCD
  *     @arg RCC_APB1Periph_WWDG
  *     @arg RCC_APB1Periph_SPI2
  *     @arg RCC_APB1Periph_USART2
  *     @arg RCC_APB1Periph_USART3
  *     @arg RCC_APB1Periph_I2C1
  *     @arg RCC_APB1Periph_I2C2
  *     @arg RCC_APB1Periph_USB
  *     @arg RCC_APB1Periph_PWR
  *     @arg RCC_APB1Periph_DAC
  *     @arg RCC_APB1Periph_COMP                                
  * @param  NewState: new state of the specified peripheral clock.
  *   This parameter can be: ENABLE or DISABLE.
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
  *     @arg RCC_AHBPeriph_GPIOA
  *     @arg RCC_AHBPeriph_GPIOB
  *     @arg RCC_AHBPeriph_GPIOC  
  *     @arg RCC_AHBPeriph_GPIOD
  *     @arg RCC_AHBPeriph_GPIOE
  *     @arg RCC_AHBPeriph_GPIOH
  *     @arg RCC_AHBPeriph_CRC
  *     @arg RCC_AHBPeriph_FLITF (has effect only when the Flash memory is in power down mode)  
  *     @arg RCC_AHBPeriph_DMA1   
  * @param  NewState: new state of the specified peripheral reset.
  *   This parameter can be: ENABLE or DISABLE.
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
  *     @arg RCC_APB2Periph_SYSCFG
  *     @arg RCC_APB2Periph_TIM9
  *     @arg RCC_APB2Periph_TIM10
  *     @arg RCC_APB2Periph_TIM11
  *     @arg RCC_APB2Periph_ADC1
  *     @arg RCC_APB2Periph_SPI1
  *     @arg RCC_APB2Periph_USART1  
  * @param  NewState: new state of the specified peripheral reset.
  *   This parameter can be: ENABLE or DISABLE.
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
  *     @arg RCC_APB1Periph_TIM2
  *     @arg RCC_APB1Periph_TIM3
  *     @arg RCC_APB1Periph_TIM4
  *     @arg RCC_APB1Periph_TIM6
  *     @arg RCC_APB1Periph_TIM7
  *     @arg RCC_APB1Periph_LCD
  *     @arg RCC_APB1Periph_WWDG
  *     @arg RCC_APB1Periph_SPI2
  *     @arg RCC_APB1Periph_USART2
  *     @arg RCC_APB1Periph_USART3
  *     @arg RCC_APB1Periph_I2C1
  *     @arg RCC_APB1Periph_I2C2
  *     @arg RCC_APB1Periph_USB
  *     @arg RCC_APB1Periph_PWR
  *     @arg RCC_APB1Periph_DAC
  *     @arg RCC_APB1Periph_COMP    
  * @param  NewState: new state of the specified peripheral clock.
  *   This parameter can be: ENABLE or DISABLE.
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
  * @brief  Enables or disables the AHB peripheral clock during Low Power (SLEEP) mode.
  * @param  RCC_AHBPeriph: specifies the AHB peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_AHBPeriph_GPIOA
  *     @arg RCC_AHBPeriph_GPIOB
  *     @arg RCC_AHBPeriph_GPIOC  
  *     @arg RCC_AHBPeriph_GPIOD
  *     @arg RCC_AHBPeriph_GPIOE
  *     @arg RCC_AHBPeriph_GPIOH
  *     @arg RCC_AHBPeriph_CRC
  *     @arg RCC_AHBPeriph_FLITF (has effect only when the Flash memory is in power down mode)  
  *     @arg RCC_AHBPeriph_SRAM     
  *     @arg RCC_AHBPeriph_DMA1
  * @param  NewState: new state of the specified peripheral clock.
  *   This parameter can be: ENABLE or DISABLE.
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
  * @brief  Enables or disables the APB2 peripheral clock during Low Power (SLEEP) mode.
  * @param  RCC_APB2Periph: specifies the APB2 peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB2Periph_SYSCFG
  *     @arg RCC_APB2Periph_TIM9
  *     @arg RCC_APB2Periph_TIM10
  *     @arg RCC_APB2Periph_TIM11
  *     @arg RCC_APB2Periph_ADC1
  *     @arg RCC_APB2Periph_SPI1
  *     @arg RCC_APB2Periph_USART1            
  * @param  NewState: new state of the specified peripheral clock.
  *   This parameter can be: ENABLE or DISABLE.
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
  * @brief  Enables or disables the APB1 peripheral clock during Low Power (SLEEP) mode.
  * @param  RCC_APB1Periph: specifies the APB1 peripheral to gates its clock.
  *   This parameter can be any combination of the following values:
  *     @arg RCC_APB1Periph_TIM2
  *     @arg RCC_APB1Periph_TIM3
  *     @arg RCC_APB1Periph_TIM4
  *     @arg RCC_APB1Periph_TIM6
  *     @arg RCC_APB1Periph_TIM7
  *     @arg RCC_APB1Periph_LCD
  *     @arg RCC_APB1Periph_WWDG
  *     @arg RCC_APB1Periph_SPI2
  *     @arg RCC_APB1Periph_USART2
  *     @arg RCC_APB1Periph_USART3
  *     @arg RCC_APB1Periph_I2C1
  *     @arg RCC_APB1Periph_I2C2
  *     @arg RCC_APB1Periph_USB
  *     @arg RCC_APB1Periph_PWR
  *     @arg RCC_APB1Periph_DAC
  *     @arg RCC_APB1Periph_COMP                                
  * @param  NewState: new state of the specified peripheral clock.
  *   This parameter can be: ENABLE or DISABLE.
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
  * @brief  Enables or disables the Clock Security System.
  * @param  NewState: new state of the Clock Security System..
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void RCC_ClockSecuritySystemCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  *(__IO uint32_t *) CR_CSSON_BB = (uint32_t)NewState;
}

/**
  * @brief  Selects the clock source to output on MCO pin.
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
  * @brief  Checks whether the specified RCC flag is set or not.
  * @param  RCC_FLAG: specifies the flag to check.
  *   This parameter can be one of the following values:
  *     @arg RCC_FLAG_HSIRDY: HSI oscillator clock ready
  *     @arg RCC_FLAG_MSIRDY: MSI oscillator clock ready  
  *     @arg RCC_FLAG_HSERDY: HSE oscillator clock ready
  *     @arg RCC_FLAG_PLLRDY: PLL clock ready
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
  *   The reset flags are: RCC_FLAG_OBLRST, RCC_FLAG_PINRST, RCC_FLAG_PORRST, 
  *   RCC_FLAG_SFTRST, RCC_FLAG_IWDGRST, RCC_FLAG_WWDGRST, RCC_FLAG_LPWRRST.
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

/******************* (C) COPYRIGHT 2010 STMicroelectronics *****END OF FILE****/
