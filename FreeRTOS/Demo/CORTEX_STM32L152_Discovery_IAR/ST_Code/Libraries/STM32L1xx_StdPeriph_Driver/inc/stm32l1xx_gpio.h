/**
  ******************************************************************************
  * @file    stm32l1xx_gpio.h
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file contains all the functions prototypes for the GPIO 
  *          firmware library.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32L1xx_GPIO_H
#define __STM32L1xx_GPIO_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup GPIO
  * @{
  */

/* Exported types ------------------------------------------------------------*/

#define IS_GPIO_ALL_PERIPH(PERIPH) (((PERIPH) == GPIOA) || \
                                    ((PERIPH) == GPIOB) || \
                                    ((PERIPH) == GPIOC) || \
                                    ((PERIPH) == GPIOD) || \
                                    ((PERIPH) == GPIOE) || \
                                    ((PERIPH) == GPIOH) || \
                                    ((PERIPH) == GPIOF) || \
                                    ((PERIPH) == GPIOG))

/** @defgroup Configuration_Mode_enumeration 
  * @{
  */ 
typedef enum
{ 
  GPIO_Mode_IN   = 0x00, /*!< GPIO Input Mode */
  GPIO_Mode_OUT  = 0x01, /*!< GPIO Output Mode */
  GPIO_Mode_AF   = 0x02, /*!< GPIO Alternate function Mode */
  GPIO_Mode_AN   = 0x03  /*!< GPIO Analog Mode */
}GPIOMode_TypeDef;
#define IS_GPIO_MODE(MODE) (((MODE) == GPIO_Mode_IN)  || ((MODE) == GPIO_Mode_OUT) || \
                            ((MODE) == GPIO_Mode_AF)|| ((MODE) == GPIO_Mode_AN))
/**
  * @}
  */

/** @defgroup Output_type_enumeration
  * @{
  */ 
typedef enum
{ GPIO_OType_PP = 0x00,
  GPIO_OType_OD = 0x01
}GPIOOType_TypeDef;
#define IS_GPIO_OTYPE(OTYPE) (((OTYPE) == GPIO_OType_PP) || ((OTYPE) == GPIO_OType_OD))

/**
  * @}
  */

/** @defgroup Output_Maximum_frequency_enumeration 
  * @{
  */ 
typedef enum
{ 
  GPIO_Speed_400KHz = 0x00, /*!< Very Low Speed */
  GPIO_Speed_2MHz   = 0x01, /*!< Low Speed */
  GPIO_Speed_10MHz  = 0x02, /*!< Medium Speed */
  GPIO_Speed_40MHz  = 0x03  /*!< High Speed */
}GPIOSpeed_TypeDef;
#define IS_GPIO_SPEED(SPEED) (((SPEED) == GPIO_Speed_400KHz) || ((SPEED) == GPIO_Speed_2MHz) || \
                              ((SPEED) == GPIO_Speed_10MHz)||  ((SPEED) == GPIO_Speed_40MHz))
/**
  * @}
  */

/** @defgroup Configuration_Pull-Up_Pull-Down_enumeration 
  * @{
  */ 
typedef enum
{ GPIO_PuPd_NOPULL = 0x00,
  GPIO_PuPd_UP     = 0x01,
  GPIO_PuPd_DOWN   = 0x02
}GPIOPuPd_TypeDef;
#define IS_GPIO_PUPD(PUPD) (((PUPD) == GPIO_PuPd_NOPULL) || ((PUPD) == GPIO_PuPd_UP) || \
                            ((PUPD) == GPIO_PuPd_DOWN))
/**
  * @}
  */

/** @defgroup Bit_SET_and_Bit_RESET_enumeration
  * @{
  */
typedef enum
{ Bit_RESET = 0,
  Bit_SET
}BitAction;
#define IS_GPIO_BIT_ACTION(ACTION) (((ACTION) == Bit_RESET) || ((ACTION) == Bit_SET))

/**
  * @}
  */

/** 
  * @brief  GPIO Init structure definition
  */ 
typedef struct
{
  uint32_t GPIO_Pin;              /*!< Specifies the GPIO pins to be configured.
                                       This parameter can be any value of @ref GPIO_pins_define */

  GPIOMode_TypeDef GPIO_Mode;     /*!< Specifies the operating mode for the selected pins.
                                       This parameter can be a value of @ref GPIOMode_TypeDef */

  GPIOSpeed_TypeDef GPIO_Speed;   /*!< Specifies the speed for the selected pins.
                                       This parameter can be a value of @ref GPIOSpeed_TypeDef */

  GPIOOType_TypeDef GPIO_OType;   /*!< Specifies the operating output type for the selected pins.
                                       This parameter can be a value of @ref GPIOOType_TypeDef */

  GPIOPuPd_TypeDef GPIO_PuPd;     /*!< Specifies the operating Pull-up/Pull down for the selected pins.
                                       This parameter can be a value of @ref GPIOPuPd_TypeDef */
}GPIO_InitTypeDef;

/* Exported constants --------------------------------------------------------*/

/** @defgroup GPIO_Exported_Constants
  * @{
  */
  
/** @defgroup GPIO_pins_define 
  * @{
  */
#define GPIO_Pin_0                 ((uint16_t)0x0001)  /*!< Pin 0 selected */
#define GPIO_Pin_1                 ((uint16_t)0x0002)  /*!< Pin 1 selected */
#define GPIO_Pin_2                 ((uint16_t)0x0004)  /*!< Pin 2 selected */
#define GPIO_Pin_3                 ((uint16_t)0x0008)  /*!< Pin 3 selected */
#define GPIO_Pin_4                 ((uint16_t)0x0010)  /*!< Pin 4 selected */
#define GPIO_Pin_5                 ((uint16_t)0x0020)  /*!< Pin 5 selected */
#define GPIO_Pin_6                 ((uint16_t)0x0040)  /*!< Pin 6 selected */
#define GPIO_Pin_7                 ((uint16_t)0x0080)  /*!< Pin 7 selected */
#define GPIO_Pin_8                 ((uint16_t)0x0100)  /*!< Pin 8 selected */
#define GPIO_Pin_9                 ((uint16_t)0x0200)  /*!< Pin 9 selected */
#define GPIO_Pin_10                ((uint16_t)0x0400)  /*!< Pin 10 selected */
#define GPIO_Pin_11                ((uint16_t)0x0800)  /*!< Pin 11 selected */
#define GPIO_Pin_12                ((uint16_t)0x1000)  /*!< Pin 12 selected */
#define GPIO_Pin_13                ((uint16_t)0x2000)  /*!< Pin 13 selected */
#define GPIO_Pin_14                ((uint16_t)0x4000)  /*!< Pin 14 selected */
#define GPIO_Pin_15                ((uint16_t)0x8000)  /*!< Pin 15 selected */
#define GPIO_Pin_All               ((uint16_t)0xFFFF)  /*!< All pins selected */

#define IS_GPIO_PIN(PIN) ((PIN) != (uint16_t)0x00)
#define IS_GET_GPIO_PIN(PIN) (((PIN) == GPIO_Pin_0) || \
                              ((PIN) == GPIO_Pin_1) || \
                              ((PIN) == GPIO_Pin_2) || \
                              ((PIN) == GPIO_Pin_3) || \
                              ((PIN) == GPIO_Pin_4) || \
                              ((PIN) == GPIO_Pin_5) || \
                              ((PIN) == GPIO_Pin_6) || \
                              ((PIN) == GPIO_Pin_7) || \
                              ((PIN) == GPIO_Pin_8) || \
                              ((PIN) == GPIO_Pin_9) || \
                              ((PIN) == GPIO_Pin_10) || \
                              ((PIN) == GPIO_Pin_11) || \
                              ((PIN) == GPIO_Pin_12) || \
                              ((PIN) == GPIO_Pin_13) || \
                              ((PIN) == GPIO_Pin_14) || \
                              ((PIN) == GPIO_Pin_15))
/**
  * @}
  */

/** @defgroup GPIO_Pin_sources 
  * @{
  */ 
#define GPIO_PinSource0            ((uint8_t)0x00)
#define GPIO_PinSource1            ((uint8_t)0x01)
#define GPIO_PinSource2            ((uint8_t)0x02)
#define GPIO_PinSource3            ((uint8_t)0x03)
#define GPIO_PinSource4            ((uint8_t)0x04)
#define GPIO_PinSource5            ((uint8_t)0x05)
#define GPIO_PinSource6            ((uint8_t)0x06)
#define GPIO_PinSource7            ((uint8_t)0x07)
#define GPIO_PinSource8            ((uint8_t)0x08)
#define GPIO_PinSource9            ((uint8_t)0x09)
#define GPIO_PinSource10           ((uint8_t)0x0A)
#define GPIO_PinSource11           ((uint8_t)0x0B)
#define GPIO_PinSource12           ((uint8_t)0x0C)
#define GPIO_PinSource13           ((uint8_t)0x0D)
#define GPIO_PinSource14           ((uint8_t)0x0E)
#define GPIO_PinSource15           ((uint8_t)0x0F)

#define IS_GPIO_PIN_SOURCE(PINSOURCE) (((PINSOURCE) == GPIO_PinSource0) || \
                                       ((PINSOURCE) == GPIO_PinSource1) || \
                                       ((PINSOURCE) == GPIO_PinSource2) || \
                                       ((PINSOURCE) == GPIO_PinSource3) || \
                                       ((PINSOURCE) == GPIO_PinSource4) || \
                                       ((PINSOURCE) == GPIO_PinSource5) || \
                                       ((PINSOURCE) == GPIO_PinSource6) || \
                                       ((PINSOURCE) == GPIO_PinSource7) || \
                                       ((PINSOURCE) == GPIO_PinSource8) || \
                                       ((PINSOURCE) == GPIO_PinSource9) || \
                                       ((PINSOURCE) == GPIO_PinSource10) || \
                                       ((PINSOURCE) == GPIO_PinSource11) || \
                                       ((PINSOURCE) == GPIO_PinSource12) || \
                                       ((PINSOURCE) == GPIO_PinSource13) || \
                                       ((PINSOURCE) == GPIO_PinSource14) || \
                                       ((PINSOURCE) == GPIO_PinSource15))
/**
  * @}
  */

/** @defgroup GPIO_Alternat_function_selection_define 
  * @{
  */

/** 
  * @brief  AF 0 selection  
  */ 
#define GPIO_AF_RTC_50Hz      ((uint8_t)0x00)  /*!< RTC 50/60 Hz Alternate Function mapping */
#define GPIO_AF_MCO           ((uint8_t)0x00)  /*!< MCO Alternate Function mapping */
#define GPIO_AF_RTC_AF1       ((uint8_t)0x00)  /*!< RTC_AF1 Alternate Function mapping */
#define GPIO_AF_WKUP          ((uint8_t)0x00)  /*!< Wakeup (WKUP1, WKUP2 and WKUP3) Alternate Function mapping */
#define GPIO_AF_SWJ           ((uint8_t)0x00)  /*!< SWJ (SW and JTAG) Alternate Function mapping */
#define GPIO_AF_TRACE         ((uint8_t)0x00)  /*!< TRACE Alternate Function mapping */

/** 
  * @brief  AF 1 selection  
  */ 
#define GPIO_AF_TIM2          ((uint8_t)0x01)  /*!< TIM2 Alternate Function mapping */
/** 
  * @brief  AF 2 selection  
  */ 
#define GPIO_AF_TIM3          ((uint8_t)0x02)  /*!< TIM3 Alternate Function mapping */
#define GPIO_AF_TIM4          ((uint8_t)0x02)  /*!< TIM4 Alternate Function mapping */
#define GPIO_AF_TIM5          ((uint8_t)0x02)  /*!< TIM5 Alternate Function mapping */
/** 
  * @brief  AF 3 selection  
  */ 
#define GPIO_AF_TIM9           ((uint8_t)0x03)  /*!< TIM9 Alternate Function mapping */
#define GPIO_AF_TIM10          ((uint8_t)0x03)  /*!< TIM10 Alternate Function mapping */
#define GPIO_AF_TIM11          ((uint8_t)0x03)  /*!< TIM11 Alternate Function mapping */
/** 
  * @brief  AF 4 selection  
  */ 
#define GPIO_AF_I2C1          ((uint8_t)0x04)  /*!< I2C1 Alternate Function mapping */
#define GPIO_AF_I2C2          ((uint8_t)0x04)  /*!< I2C2 Alternate Function mapping */
/** 
  * @brief  AF 5 selection  
  */ 
#define GPIO_AF_SPI1          ((uint8_t)0x05)  /*!< SPI1 Alternate Function mapping */
#define GPIO_AF_SPI2          ((uint8_t)0x05)  /*!< SPI2 Alternate Function mapping */
/** 
  * @brief  AF 6 selection  
  */ 
#define GPIO_AF_SPI3          ((uint8_t)0x06)  /*!< SPI3 Alternate Function mapping */
/** 
  * @brief  AF 7 selection  
  */ 
#define GPIO_AF_USART1        ((uint8_t)0x07)  /*!< USART1 Alternate Function mapping */
#define GPIO_AF_USART2        ((uint8_t)0x07)  /*!< USART2 Alternate Function mapping */
#define GPIO_AF_USART3        ((uint8_t)0x07)  /*!< USART3 Alternate Function mapping */
/** 
  * @brief  AF 8 selection  
  */ 
#define GPIO_AF_UART4         ((uint8_t)0x08)  /*!< UART4 Alternate Function mapping */
#define GPIO_AF_UART5         ((uint8_t)0x08)  /*!< UART5 Alternate Function mapping */
/** 
  * @brief  AF 10 selection  
  */ 
#define GPIO_AF_USB           ((uint8_t)0xA)  /*!< USB Full speed device  Alternate Function mapping */
/** 
  * @brief  AF 11 selection  
  */ 
#define GPIO_AF_LCD           ((uint8_t)0x0B)  /*!< LCD Alternate Function mapping */
/** 
  * @brief  AF 12 selection  
  */ 
#define GPIO_AF_FSMC           ((uint8_t)0x0C)  /*!< FSMC Alternate Function mapping */
#define GPIO_AF_SDIO           ((uint8_t)0x0C)  /*!< SDIO Alternate Function mapping */
/** 
  * @brief  AF 14 selection  
  */ 
#define GPIO_AF_RI            ((uint8_t)0x0E)  /*!< RI Alternate Function mapping */

/** 
  * @brief  AF 15 selection  
  */ 
#define GPIO_AF_EVENTOUT      ((uint8_t)0x0F)  /*!< EVENTOUT Alternate Function mapping */

#define IS_GPIO_AF(AF)   (((AF) == GPIO_AF_RTC_50Hz) || ((AF) == GPIO_AF_MCO)    || \
                          ((AF) == GPIO_AF_RTC_AF1)  || ((AF) == GPIO_AF_WKUP)   || \
                          ((AF) == GPIO_AF_SWJ)      || ((AF) == GPIO_AF_TRACE)  || \
                          ((AF) == GPIO_AF_TIM2)     || ((AF)== GPIO_AF_TIM3)    || \
                          ((AF) == GPIO_AF_TIM4)     || ((AF)== GPIO_AF_TIM9)    || \
                          ((AF) == GPIO_AF_TIM10)    || ((AF)== GPIO_AF_TIM11)   || \
                          ((AF) == GPIO_AF_I2C1)     || ((AF) == GPIO_AF_I2C2)   || \
                          ((AF) == GPIO_AF_SPI1)     || ((AF) == GPIO_AF_SPI2)   || \
                          ((AF) == GPIO_AF_USART1)   || ((AF) == GPIO_AF_USART2) || \
                          ((AF) == GPIO_AF_USART3)   || ((AF) == GPIO_AF_USB)    || \
                          ((AF) == GPIO_AF_LCD)      || ((AF) == GPIO_AF_RI)     || \
                          ((AF) == GPIO_AF_TIM5)     || ((AF) == GPIO_AF_SPI3)   || \
                          ((AF) == GPIO_AF_UART4)    || ((AF) == GPIO_AF_UART5)  || \
                          ((AF) == GPIO_AF_FSMC)     || ((AF) == GPIO_AF_SDIO)   || \
                          ((AF) == GPIO_AF_EVENTOUT))

/**
  * @}
  */

/** @defgroup GPIO_Legacy 
  * @{
  */
    
#define GPIO_Mode_AIN GPIO_Mode_AN

/**
  * @}
  */

/**
  * @}
  */  
  
/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

/*  Function used to set the GPIO configuration to the default reset state ****/
void GPIO_DeInit(GPIO_TypeDef* GPIOx);

/* Initialization and Configuration functions *********************************/
void GPIO_Init(GPIO_TypeDef* GPIOx, GPIO_InitTypeDef* GPIO_InitStruct);
void GPIO_StructInit(GPIO_InitTypeDef* GPIO_InitStruct);
void GPIO_PinLockConfig(GPIO_TypeDef* GPIOx, uint16_t GPIO_Pin);

/* GPIO Read and Write functions **********************************************/
uint8_t GPIO_ReadInputDataBit(GPIO_TypeDef* GPIOx, uint16_t GPIO_Pin);
uint16_t GPIO_ReadInputData(GPIO_TypeDef* GPIOx);
uint8_t GPIO_ReadOutputDataBit(GPIO_TypeDef* GPIOx, uint16_t GPIO_Pin);
uint16_t GPIO_ReadOutputData(GPIO_TypeDef* GPIOx);
void GPIO_SetBits(GPIO_TypeDef* GPIOx, uint16_t GPIO_Pin);
void GPIO_ResetBits(GPIO_TypeDef* GPIOx, uint16_t GPIO_Pin);
void GPIO_WriteBit(GPIO_TypeDef* GPIOx, uint16_t GPIO_Pin, BitAction BitVal);
void GPIO_Write(GPIO_TypeDef* GPIOx, uint16_t PortVal);
void GPIO_ToggleBits(GPIO_TypeDef* GPIOx, uint16_t GPIO_Pin);

/* GPIO Alternate functions configuration functions ***************************/
void GPIO_PinAFConfig(GPIO_TypeDef* GPIOx, uint16_t GPIO_PinSource, uint8_t GPIO_AF);

#ifdef __cplusplus
}
#endif

#endif /*__STM32L1xx_GPIO_H */

/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
