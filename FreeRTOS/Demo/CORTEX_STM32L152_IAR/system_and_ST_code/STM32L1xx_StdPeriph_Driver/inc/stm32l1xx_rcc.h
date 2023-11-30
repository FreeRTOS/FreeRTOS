/**
  ******************************************************************************
  * @file    stm32l1xx_rcc.h
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    07/02/2010
  * @brief   This file contains all the functions prototypes for the RCC 
  *          firmware library.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32L1xx_RCC_H
#define __STM32L1xx_RCC_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup RCC
  * @{
  */

/** @defgroup RCC_Exported_Types
  * @{
  */

typedef struct
{
  uint32_t SYSCLK_Frequency;
  uint32_t HCLK_Frequency;
  uint32_t PCLK1_Frequency;
  uint32_t PCLK2_Frequency;
}RCC_ClocksTypeDef;

/**
  * @}
  */

/** @defgroup RCC_Exported_Constants
  * @{
  */

/** @defgroup HSE_configuration 
  * @{
  */

#define RCC_HSE_OFF                      ((uint8_t)0x00)
#define RCC_HSE_ON                       ((uint8_t)0x01)
#define RCC_HSE_Bypass                   ((uint8_t)0x05)
#define IS_RCC_HSE(HSE) (((HSE) == RCC_HSE_OFF) || ((HSE) == RCC_HSE_ON) || \
                         ((HSE) == RCC_HSE_Bypass))

/**
  * @}
  */ 

/** @defgroup MSI_Clock_Range 
  * @{
  */

#define RCC_MSIRange_64KHz               RCC_ICSCR_MSIRANGE_64KHz
#define RCC_MSIRange_128KHz              RCC_ICSCR_MSIRANGE_128KHz
#define RCC_MSIRange_256KHz              RCC_ICSCR_MSIRANGE_256KHz
#define RCC_MSIRange_512KHz              RCC_ICSCR_MSIRANGE_512KHz
#define RCC_MSIRange_1MHz                RCC_ICSCR_MSIRANGE_1MHz
#define RCC_MSIRange_2MHz                RCC_ICSCR_MSIRANGE_2MHz
#define RCC_MSIRange_4MHz                RCC_ICSCR_MSIRANGE_4MHz

#define IS_RCC_MSI_CLOCK_RANGE(RANGE) (((RANGE) == RCC_MSIRange_64KHz) || \
                                       ((RANGE) == RCC_MSIRange_128KHz) || \
                                       ((RANGE) == RCC_MSIRange_256KHz) || \
                                       ((RANGE) == RCC_MSIRange_512KHz) || \
                                       ((RANGE) == RCC_MSIRange_1MHz) || \
                                       ((RANGE) == RCC_MSIRange_2MHz) || \
                                       ((RANGE) == RCC_MSIRange_4MHz))

/**
  * @}
  */ 
  
/** @defgroup PLL_Clock_Source 
  * @{
  */

#define RCC_PLLSource_HSI                ((uint8_t)0x00)
#define RCC_PLLSource_HSE                ((uint8_t)0x01)

#define IS_RCC_PLL_SOURCE(SOURCE) (((SOURCE) == RCC_PLLSource_HSI) || \
                                   ((SOURCE) == RCC_PLLSource_HSE))
/**
  * @}
  */ 

/** @defgroup PLL_Multiplication_Factor 
  * @{
  */

#define RCC_PLLMul_3                     ((uint8_t)0x00)
#define RCC_PLLMul_4                     ((uint8_t)0x04)
#define RCC_PLLMul_6                     ((uint8_t)0x08)
#define RCC_PLLMul_8                     ((uint8_t)0x0C)
#define RCC_PLLMul_12                    ((uint8_t)0x10)
#define RCC_PLLMul_16                    ((uint8_t)0x14)
#define RCC_PLLMul_24                    ((uint8_t)0x18)
#define RCC_PLLMul_32                    ((uint8_t)0x1C)
#define RCC_PLLMul_48                    ((uint8_t)0x20)


#define IS_RCC_PLL_MUL(MUL) (((MUL) == RCC_PLLMul_3) || ((MUL) == RCC_PLLMul_4) || \
                             ((MUL) == RCC_PLLMul_6) || ((MUL) == RCC_PLLMul_8) || \
                             ((MUL) == RCC_PLLMul_12) || ((MUL) == RCC_PLLMul_16) || \
                             ((MUL) == RCC_PLLMul_24) || ((MUL) == RCC_PLLMul_32) || \
                             ((MUL) == RCC_PLLMul_48))
/**
  * @}
  */

/** @defgroup PLL_Divider_Factor 
  * @{
  */

#define RCC_PLLDiv_2                     ((uint8_t)0x40)
#define RCC_PLLDiv_3                     ((uint8_t)0x80)
#define RCC_PLLDiv_4                     ((uint8_t)0xC0)


#define IS_RCC_PLL_DIV(DIV) (((DIV) == RCC_PLLDiv_2) || ((DIV) == RCC_PLLDiv_3) || \
                             ((DIV) == RCC_PLLDiv_4))
/**
  * @}
  */
  
/** @defgroup System_Clock_Source 
  * @{
  */

#define RCC_SYSCLKSource_MSI             RCC_CFGR_SW_MSI
#define RCC_SYSCLKSource_HSI             RCC_CFGR_SW_HSI
#define RCC_SYSCLKSource_HSE             RCC_CFGR_SW_HSE
#define RCC_SYSCLKSource_PLLCLK          RCC_CFGR_SW_PLL
#define IS_RCC_SYSCLK_SOURCE(SOURCE) (((SOURCE) == RCC_SYSCLKSource_MSI) || \
                                      ((SOURCE) == RCC_SYSCLKSource_HSI) || \
                                      ((SOURCE) == RCC_SYSCLKSource_HSE) || \
                                      ((SOURCE) == RCC_SYSCLKSource_PLLCLK))
/**
  * @}
  */

/** @defgroup AHB_Clock_Source
  * @{
  */

#define RCC_SYSCLK_Div1                  RCC_CFGR_HPRE_DIV1
#define RCC_SYSCLK_Div2                  RCC_CFGR_HPRE_DIV2
#define RCC_SYSCLK_Div4                  RCC_CFGR_HPRE_DIV4
#define RCC_SYSCLK_Div8                  RCC_CFGR_HPRE_DIV8
#define RCC_SYSCLK_Div16                 RCC_CFGR_HPRE_DIV16
#define RCC_SYSCLK_Div64                 RCC_CFGR_HPRE_DIV64
#define RCC_SYSCLK_Div128                RCC_CFGR_HPRE_DIV128
#define RCC_SYSCLK_Div256                RCC_CFGR_HPRE_DIV256
#define RCC_SYSCLK_Div512                RCC_CFGR_HPRE_DIV512
#define IS_RCC_HCLK(HCLK) (((HCLK) == RCC_SYSCLK_Div1) || ((HCLK) == RCC_SYSCLK_Div2) || \
                           ((HCLK) == RCC_SYSCLK_Div4) || ((HCLK) == RCC_SYSCLK_Div8) || \
                           ((HCLK) == RCC_SYSCLK_Div16) || ((HCLK) == RCC_SYSCLK_Div64) || \
                           ((HCLK) == RCC_SYSCLK_Div128) || ((HCLK) == RCC_SYSCLK_Div256) || \
                           ((HCLK) == RCC_SYSCLK_Div512))
/**
  * @}
  */ 

/** @defgroup APB1_APB2_Clock_Source
  * @{
  */

#define RCC_HCLK_Div1                    RCC_CFGR_PPRE1_DIV1
#define RCC_HCLK_Div2                    RCC_CFGR_PPRE1_DIV2
#define RCC_HCLK_Div4                    RCC_CFGR_PPRE1_DIV4
#define RCC_HCLK_Div8                    RCC_CFGR_PPRE1_DIV8
#define RCC_HCLK_Div16                   RCC_CFGR_PPRE1_DIV16
#define IS_RCC_PCLK(PCLK) (((PCLK) == RCC_HCLK_Div1) || ((PCLK) == RCC_HCLK_Div2) || \
                           ((PCLK) == RCC_HCLK_Div4) || ((PCLK) == RCC_HCLK_Div8) || \
                           ((PCLK) == RCC_HCLK_Div16))
/**
  * @}
  */
  

/** @defgroup RCC_Interrupt_Source 
  * @{
  */

#define RCC_IT_LSIRDY                    ((uint8_t)0x01)
#define RCC_IT_LSERDY                    ((uint8_t)0x02)
#define RCC_IT_HSIRDY                    ((uint8_t)0x04)
#define RCC_IT_HSERDY                    ((uint8_t)0x08)
#define RCC_IT_PLLRDY                    ((uint8_t)0x10)
#define RCC_IT_MSIRDY                    ((uint8_t)0x20)
#define RCC_IT_CSS                       ((uint8_t)0x80)

#define IS_RCC_IT(IT) ((((IT) & (uint8_t)0xC0) == 0x00) && ((IT) != 0x00))

#define IS_RCC_GET_IT(IT) (((IT) == RCC_IT_LSIRDY) || ((IT) == RCC_IT_LSERDY) || \
                           ((IT) == RCC_IT_HSIRDY) || ((IT) == RCC_IT_HSERDY) || \
                           ((IT) == RCC_IT_PLLRDY) || ((IT) == RCC_IT_MSIRDY) || \
                           ((IT) == RCC_IT_CSS))

#define IS_RCC_CLEAR_IT(IT) ((((IT) & (uint8_t)0x40) == 0x00) && ((IT) != 0x00))

/**
  * @}
  */
  
/** @defgroup LSE_Configuration 
  * @{
  */

#define RCC_LSE_OFF                      ((uint8_t)0x00)
#define RCC_LSE_ON                       ((uint8_t)0x01)
#define RCC_LSE_Bypass                   ((uint8_t)0x05)
#define IS_RCC_LSE(LSE) (((LSE) == RCC_LSE_OFF) || ((LSE) == RCC_LSE_ON) || \
                         ((LSE) == RCC_LSE_Bypass))
/**
  * @}
  */

/** @defgroup RTC_Clock_Source
  * @{
  */

#define RCC_RTCCLKSource_LSE             RCC_CSR_RTCSEL_LSE
#define RCC_RTCCLKSource_LSI             RCC_CSR_RTCSEL_LSI
#define RCC_RTCCLKSource_HSE_Div2        RCC_CSR_RTCSEL_HSE
#define RCC_RTCCLKSource_HSE_Div4        ((uint32_t)RCC_CSR_RTCSEL_HSE | RCC_CR_RTCPRE_0)
#define RCC_RTCCLKSource_HSE_Div8        ((uint32_t)RCC_CSR_RTCSEL_HSE | RCC_CR_RTCPRE_1)
#define RCC_RTCCLKSource_HSE_Div16       ((uint32_t)RCC_CSR_RTCSEL_HSE | RCC_CR_RTCPRE)
#define IS_RCC_RTCCLK_SOURCE(SOURCE) (((SOURCE) == RCC_RTCCLKSource_LSE) || \
                                      ((SOURCE) == RCC_RTCCLKSource_LSI) || \
                                      ((SOURCE) == RCC_RTCCLKSource_HSE_Div2) || \
                                      ((SOURCE) == RCC_RTCCLKSource_HSE_Div4) || \
                                      ((SOURCE) == RCC_RTCCLKSource_HSE_Div8) || \
                                      ((SOURCE) == RCC_RTCCLKSource_HSE_Div16))
/**
  * @}
  */

/** @defgroup AHB_Peripherals 
  * @{
  */

#define RCC_AHBPeriph_GPIOA               RCC_AHBENR_GPIOAEN
#define RCC_AHBPeriph_GPIOB               RCC_AHBENR_GPIOBEN
#define RCC_AHBPeriph_GPIOC               RCC_AHBENR_GPIOCEN
#define RCC_AHBPeriph_GPIOD               RCC_AHBENR_GPIODEN
#define RCC_AHBPeriph_GPIOE               RCC_AHBENR_GPIOEEN
#define RCC_AHBPeriph_GPIOH               RCC_AHBENR_GPIOHEN
#define RCC_AHBPeriph_CRC                 RCC_AHBENR_CRCEN
#define RCC_AHBPeriph_FLITF               RCC_AHBENR_FLITFEN
#define RCC_AHBPeriph_SRAM                RCC_AHBLPENR_SRAMLPEN
#define RCC_AHBPeriph_DMA1                RCC_AHBENR_DMA1EN

#define IS_RCC_AHB_PERIPH(PERIPH) ((((PERIPH) & 0xFEFF6FC0) == 0x00) && ((PERIPH) != 0x00))
#define IS_RCC_AHB_LPMODE_PERIPH(PERIPH) ((((PERIPH) & 0xFEFE6FC0) == 0x00) && ((PERIPH) != 0x00))

/**
  * @}
  */

/** @defgroup APB2_Peripherals 
  * @{
  */

#define RCC_APB2Periph_SYSCFG            RCC_APB2ENR_SYSCFGEN
#define RCC_APB2Periph_TIM9              RCC_APB2ENR_TIM9EN
#define RCC_APB2Periph_TIM10             RCC_APB2ENR_TIM10EN
#define RCC_APB2Periph_TIM11             RCC_APB2ENR_TIM11EN
#define RCC_APB2Periph_ADC1              RCC_APB2ENR_ADC1EN
#define RCC_APB2Periph_SPI1              RCC_APB2ENR_SPI1EN
#define RCC_APB2Periph_USART1            RCC_APB2ENR_USART1EN

#define IS_RCC_APB2_PERIPH(PERIPH) ((((PERIPH) & 0xFFFFADE2) == 0x00) && ((PERIPH) != 0x00))
/**
  * @}
  */ 

/** @defgroup APB1_Peripherals 
  * @{
  */

#define RCC_APB1Periph_TIM2              RCC_APB1ENR_TIM2EN
#define RCC_APB1Periph_TIM3              RCC_APB1ENR_TIM3EN
#define RCC_APB1Periph_TIM4              RCC_APB1ENR_TIM4EN
#define RCC_APB1Periph_TIM6              RCC_APB1ENR_TIM6EN
#define RCC_APB1Periph_TIM7              RCC_APB1ENR_TIM7EN
#define RCC_APB1Periph_LCD               RCC_APB1ENR_LCDEN
#define RCC_APB1Periph_WWDG              RCC_APB1ENR_WWDGEN
#define RCC_APB1Periph_SPI2              RCC_APB1ENR_SPI2EN
#define RCC_APB1Periph_USART2            RCC_APB1ENR_USART2EN
#define RCC_APB1Periph_USART3            RCC_APB1ENR_USART3EN
#define RCC_APB1Periph_I2C1              RCC_APB1ENR_I2C1EN
#define RCC_APB1Periph_I2C2              RCC_APB1ENR_I2C2EN
#define RCC_APB1Periph_USB               RCC_APB1ENR_USBEN
#define RCC_APB1Periph_PWR               RCC_APB1ENR_PWREN
#define RCC_APB1Periph_DAC               RCC_APB1ENR_DACEN
#define RCC_APB1Periph_COMP              RCC_APB1ENR_COMPEN

#define IS_RCC_APB1_PERIPH(PERIPH) ((((PERIPH) & 0x4F19B5C8) == 0x00) && ((PERIPH) != 0x00))
/**
  * @}
  */

/** @defgroup MCO_Clock_Source
  * @{
  */

#define RCC_MCOSource_NoClock            ((uint8_t)0x00)
#define RCC_MCOSource_SYSCLK             ((uint8_t)0x01)
#define RCC_MCOSource_HSI                ((uint8_t)0x02)
#define RCC_MCOSource_MSI                ((uint8_t)0x03)
#define RCC_MCOSource_HSE                ((uint8_t)0x04)
#define RCC_MCOSource_PLLCLK             ((uint8_t)0x05)
#define RCC_MCOSource_LSI                ((uint8_t)0x06)
#define RCC_MCOSource_LSE                ((uint8_t)0x07)

#define IS_RCC_MCO_SOURCE(SOURCE) (((SOURCE) == RCC_MCOSource_NoClock) || ((SOURCE) == RCC_MCOSource_SYSCLK) || \
                                   ((SOURCE) == RCC_MCOSource_HSI)  || ((SOURCE) == RCC_MCOSource_MSI) || \
                                   ((SOURCE) == RCC_MCOSource_HSE)  || ((SOURCE) == RCC_MCOSource_PLLCLK) || \
                                   ((SOURCE) == RCC_MCOSource_LSI) || ((SOURCE) == RCC_MCOSource_LSE))
/**
  * @}
  */

/** @defgroup MCO_Output_Divider 
  * @{
  */

#define RCC_MCODiv_1                     ((uint8_t)0x00)
#define RCC_MCODiv_2                     ((uint8_t)0x10)
#define RCC_MCODiv_4                     ((uint8_t)0x20)
#define RCC_MCODiv_8                     ((uint8_t)0x30)
#define RCC_MCODiv_16                    ((uint8_t)0x40)

#define IS_RCC_MCO_DIV(DIV) (((DIV) == RCC_MCODiv_1) || ((DIV) == RCC_MCODiv_2) || \
                             ((DIV) == RCC_MCODiv_4)  || ((DIV) == RCC_MCODiv_8) || \
                             ((DIV) == RCC_MCODiv_16))
/**
  * @}
  */  

/** @defgroup RCC_Flag 
  * @{
  */

#define RCC_FLAG_HSIRDY                  ((uint8_t)0x21)
#define RCC_FLAG_MSIRDY                  ((uint8_t)0x29)
#define RCC_FLAG_HSERDY                  ((uint8_t)0x31)
#define RCC_FLAG_PLLRDY                  ((uint8_t)0x39)
#define RCC_FLAG_LSERDY                  ((uint8_t)0x49)
#define RCC_FLAG_LSIRDY                  ((uint8_t)0x41)
#define RCC_FLAG_OBLRST                  ((uint8_t)0x59)
#define RCC_FLAG_PINRST                  ((uint8_t)0x5A)
#define RCC_FLAG_PORRST                  ((uint8_t)0x5B)
#define RCC_FLAG_SFTRST                  ((uint8_t)0x5C)
#define RCC_FLAG_IWDGRST                 ((uint8_t)0x5D)
#define RCC_FLAG_WWDGRST                 ((uint8_t)0x5E)
#define RCC_FLAG_LPWRRST                 ((uint8_t)0x5F)

#define IS_RCC_FLAG(FLAG) (((FLAG) == RCC_FLAG_HSIRDY) || ((FLAG) == RCC_FLAG_HSERDY) || \
                           ((FLAG) == RCC_FLAG_MSIRDY) || ((FLAG) == RCC_FLAG_PLLRDY) || \
                           ((FLAG) == RCC_FLAG_LSERDY) || ((FLAG) == RCC_FLAG_LSIRDY) || \
                           ((FLAG) == RCC_FLAG_PINRST) || ((FLAG) == RCC_FLAG_PORRST) || \
                           ((FLAG) == RCC_FLAG_SFTRST) || ((FLAG) == RCC_FLAG_IWDGRST)|| \
                           ((FLAG) == RCC_FLAG_WWDGRST)|| ((FLAG) == RCC_FLAG_LPWRRST)|| \
                           ((FLAG) == RCC_FLAG_WWDGRST))

#define IS_RCC_HSI_CALIBRATION_VALUE(VALUE) ((VALUE) <= 0x1F)
#define IS_RCC_MSI_CALIBRATION_VALUE(VALUE) ((VALUE) <= 0x3F)

/**
  * @}
  */

/**
  * @}
  */

/** @defgroup RCC_Exported_Macros
  * @{
  */

/**
  * @}
  */

/** @defgroup RCC_Exported_Functions
  * @{
  */

void RCC_DeInit(void);
void RCC_HSEConfig(uint8_t RCC_HSE);
ErrorStatus RCC_WaitForHSEStartUp(void);
void RCC_AdjustHSICalibrationValue(uint8_t HSICalibrationValue);
void RCC_AdjustMSICalibrationValue(uint8_t MSICalibrationValue);
void RCC_MSIRangeConfig(uint32_t RCC_MSIRange);
void RCC_MSICmd(FunctionalState NewState);
void RCC_HSICmd(FunctionalState NewState);
void RCC_PLLConfig(uint8_t RCC_PLLSource, uint8_t RCC_PLLMul, uint8_t RCC_PLLDiv);
void RCC_PLLCmd(FunctionalState NewState);
void RCC_SYSCLKConfig(uint32_t RCC_SYSCLKSource);
uint8_t RCC_GetSYSCLKSource(void);
void RCC_HCLKConfig(uint32_t RCC_SYSCLK);
void RCC_PCLK1Config(uint32_t RCC_HCLK);
void RCC_PCLK2Config(uint32_t RCC_HCLK);
void RCC_ITConfig(uint8_t RCC_IT, FunctionalState NewState);
void RCC_LSEConfig(uint8_t RCC_LSE);
void RCC_LSICmd(FunctionalState NewState);
void RCC_RTCCLKConfig(uint32_t RCC_RTCCLKSource);
void RCC_RTCCLKCmd(FunctionalState NewState);
void RCC_RTCResetCmd(FunctionalState NewState);
void RCC_GetClocksFreq(RCC_ClocksTypeDef* RCC_Clocks);
void RCC_AHBPeriphClockCmd(uint32_t RCC_AHBPeriph, FunctionalState NewState);
void RCC_APB2PeriphClockCmd(uint32_t RCC_APB2Periph, FunctionalState NewState);
void RCC_APB1PeriphClockCmd(uint32_t RCC_APB1Periph, FunctionalState NewState);
void RCC_AHBPeriphResetCmd(uint32_t RCC_AHBPeriph, FunctionalState NewState);
void RCC_APB2PeriphResetCmd(uint32_t RCC_APB2Periph, FunctionalState NewState);
void RCC_APB1PeriphResetCmd(uint32_t RCC_APB1Periph, FunctionalState NewState);
void RCC_AHBPeriphClockLPModeCmd(uint32_t RCC_AHBPeriph, FunctionalState NewState);
void RCC_APB2PeriphClockLPModeCmd(uint32_t RCC_APB2Periph, FunctionalState NewState);
void RCC_APB1PeriphClockLPModeCmd(uint32_t RCC_APB1Periph, FunctionalState NewState);
void RCC_ClockSecuritySystemCmd(FunctionalState NewState);
void RCC_MCOConfig(uint8_t RCC_MCOSource, uint8_t RCC_MCODiv);
FlagStatus RCC_GetFlagStatus(uint8_t RCC_FLAG);
void RCC_ClearFlag(void);
ITStatus RCC_GetITStatus(uint8_t RCC_IT);
void RCC_ClearITPendingBit(uint8_t RCC_IT);

#ifdef __cplusplus
}
#endif

#endif /* __STM32L1xx_RCC_H */
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
