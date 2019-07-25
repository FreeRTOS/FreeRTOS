/**
  ******************************************************************************
  * @file    stm32h745i_discovery.h
  * @author  MCD Application Team
  * @brief   This file contains definitions for STM32H745I-Discovery LEDs,
  *          push-buttons hardware resources.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; Copyright (c) 2019 STMicroelectronics.
  * All rights reserved.</center></h2>
  *
  * This software component is licensed by ST under BSD 3-Clause license,
  * the "License"; You may not use this file except in compliance with the
  * License. You may obtain a copy of the License at:
  *                        opensource.org/licenses/BSD-3-Clause
  *
  ******************************************************************************
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32H745I_DISCOVERY_H
#define __STM32H745I_DISCOVERY_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32h7xx_hal.h"

/** @addtogroup BSP
  * @{
  */

/** @addtogroup STM32H745I_DISCOVERY
  * @{
  */

/** @defgroup STM32H745I_DISCOVERY_LOW_LEVEL STM32H745I_DISCOVERY_LOW_LEVEL
  * @{
  */

/** @defgroup STM32H745I_DISCOVERY_LOW_LEVEL_Exported_Types Exported Types
 * @{
 */
typedef enum
{
  LED1 = 0,
  LED_GREEN = LED1,
  LED2 = 1,
  LED_RED = LED2,
} Led_TypeDef;

typedef enum
{
  BUTTON_WAKEUP = 0,
} Button_TypeDef;

typedef enum
{
  BUTTON_MODE_GPIO = 0,
  BUTTON_MODE_EXTI = 1
} ButtonMode_TypeDef;

typedef enum 
{
  PB_SET = 0, 
  PB_RESET = !PB_SET
} ButtonValue_TypeDef;

typedef enum
{
  DISCO_OK    = 0,
  DISCO_ERROR = 1
} DISCO_Status_TypeDef;

/**
  * @}
  */

/** @defgroup STM32H745I_DISCOVERY_LOW_LEVEL_Exported_Constants Exported Constants
  * @{
  */
/** 
  * @brief  Define for STM32H745I_DISCOVERY board
  */ 
#if !defined (USE_STM32H745I_DISCO)
 #define USE_STM32H745I_DISCO
#endif

#define BUTTON_USER BUTTON_WAKEUP

#define LEDn                             ((uint32_t)2)

#define LED1_GPIO_PORT                   GPIOJ
#define LED1_PIN                         GPIO_PIN_2
#define LED2_GPIO_PORT                   GPIOI
#define LED2_PIN                         GPIO_PIN_13
#define LEDx_GPIO_CLK_ENABLE()           __HAL_RCC_GPIOI_CLK_ENABLE();__HAL_RCC_GPIOJ_CLK_ENABLE()
#define LEDx_GPIO_CLK_DISABLE()          __HAL_RCC_GPIOI_CLK_DISABLE();__HAL_RCC_GPIOJ_CLK_DISABLE()

/**
 * @brief Definition for LCD Timer used to control the Brightnes
 */
#define LCD_TIMx                           TIM8
#define LCD_TIMx_CLK_ENABLE()              __HAL_RCC_TIM8_CLK_ENABLE()
#define LCD_TIMx_CLK_DISABLE()             __HAL_RCC_TIM8_CLK_DISABLE()
#define LCD_TIMx_CHANNEL                   TIM_CHANNEL_3
#define LCD_TIMx_CHANNEL_AF                GPIO_AF3_TIM8
#define LCD_TIMX_PERIOD_VALUE              ((uint32_t)50000) /* Period Value    */
#define LCD_TIMX_PRESCALER_VALUE           ((uint32_t)4)     /* Prescaler Value */


/* Only one User/Wakeup button */
#define BUTTONn                             ((uint8_t)1)

/**
  * @brief Wakeup push-button
  */
#define WAKEUP_BUTTON_PIN                   GPIO_PIN_13
#define WAKEUP_BUTTON_GPIO_PORT             GPIOC
#define WAKEUP_BUTTON_GPIO_CLK_ENABLE()     __HAL_RCC_GPIOC_CLK_ENABLE()
#define WAKEUP_BUTTON_GPIO_CLK_DISABLE()    __HAL_RCC_GPIOC_CLK_DISABLE()
#define WAKEUP_BUTTON_EXTI_IRQn             EXTI15_10_IRQn

/* Define the USER button as an alias of the Wakeup button */
#define USER_BUTTON_PIN                   WAKEUP_BUTTON_PIN
#define USER_BUTTON_GPIO_PORT             WAKEUP_BUTTON_GPIO_PORT
#define USER_BUTTON_GPIO_CLK_ENABLE()     WAKEUP_BUTTON_GPIO_CLK_ENABLE()
#define USER_BUTTON_GPIO_CLK_DISABLE()    WAKEUP_BUTTON_GPIO_CLK_DISABLE()
#define USER_BUTTON_EXTI_IRQn             WAKEUP_BUTTON_EXTI_IRQn

#define BUTTON_GPIO_CLK_ENABLE()            __HAL_RCC_GPIOC_CLK_ENABLE()

/**
  * @brief TS_INT signal from TouchScreen when it is configured in interrupt mode
  */
#define TS_INT_PIN                        ((uint32_t)GPIO_PIN_2)
#define TS_INT_GPIO_PORT                  ((GPIO_TypeDef*)GPIOG)
#define TS_INT_GPIO_CLK_ENABLE()          __HAL_RCC_GPIOG_CLK_ENABLE()
#define TS_INT_GPIO_CLK_DISABLE()         __HAL_RCC_GPIOG_CLK_DISABLE()
#define TS_INT_EXTI_IRQn                  EXTI2_IRQn

/**
  * @brief TouchScreen FT5336 Slave I2C address
  */
#define TS_I2C_ADDRESS                   ((uint16_t)0x70)

/**
  * @brief Audio I2C Slave address
  */
#define AUDIO_I2C_ADDRESS                ((uint16_t)0x34)

/**
  * @brief User can use this section to tailor I2C4/I2C4 instance used and associated
  * resources (audio codec).
  * Definition for I2C4 clock resources
  */
#define DISCOVERY_I2Cx                             I2C4
#define DISCOVERY_I2Cx_CLK_ENABLE()                __HAL_RCC_I2C4_CLK_ENABLE()
#define DISCOVERY_I2Cx_SCL_SDA_GPIO_CLK_ENABLE()   __HAL_RCC_GPIOD_CLK_ENABLE()

#define DISCOVERY_I2Cx_FORCE_RESET()               __HAL_RCC_I2C4_FORCE_RESET()
#define DISCOVERY_I2Cx_RELEASE_RESET()             __HAL_RCC_I2C4_RELEASE_RESET()

/** @brief Definition for I2C4 Pins
  */
#define DISCOVERY_I2Cx_SCL_PIN                     GPIO_PIN_12 /*!< PD12 */
#define DISCOVERY_I2Cx_SDA_PIN                     GPIO_PIN_13 /*!< PD13 */
#define DISCOVERY_I2Cx_SCL_SDA_AF                  GPIO_AF4_I2C4
#define DISCOVERY_I2Cx_SCL_SDA_GPIO_PORT           GPIOD
/** @brief Definition of I2C4 interrupt requests
  */
#define DISCOVERY_I2Cx_EV_IRQn                     I2C4_EV_IRQn
#define DISCOVERY_I2Cx_ER_IRQn                     I2C4_ER_IRQn

/* I2C TIMING Register define when I2C clock source is SYSCLK */
/* I2C TIMING is calculated from APB1 source clock = 200 MHz */
/* 0x40912732 takes in account the big rising and aims a clock of 100khz */
#ifndef DISCOVERY_I2Cx_TIMING  
#define DISCOVERY_I2Cx_TIMING                      ((uint32_t)0x40912732)
#endif /* DISCOVERY_I2Cx_TIMING */
/**
  * @}
  */

/** @defgroup STM32H745I_DISCOVERY_LOW_LEVEL_Exported_Functions Exported Functions
  * @{
  */
uint32_t         BSP_GetVersion(void);
void             BSP_LED_Init(Led_TypeDef Led);
void             BSP_LED_DeInit(Led_TypeDef Led);
void             BSP_LED_On(Led_TypeDef Led);
void             BSP_LED_Off(Led_TypeDef Led);
void             BSP_LED_Toggle(Led_TypeDef Led);
void             BSP_PB_Init(Button_TypeDef Button, ButtonMode_TypeDef Button_Mode);
void             BSP_PB_DeInit(Button_TypeDef Button);
uint32_t         BSP_PB_GetState(Button_TypeDef Button);

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


#ifdef __cplusplus
}
#endif

#endif /* __STM32H745I_DISCOVERY_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
