/**
  ******************************************************************************
  * @file    stm320518_eval.h
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    27-January-2012
  * @brief   This file contains definitions for STM320518_EVAL's Leds, push-buttons
  *          and COM ports hardware resources.
  ******************************************************************************
  * @attention
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * FOR MORE INFORMATION PLEASE READ CAREFULLY THE LICENSE AGREEMENT FILE
  * LOCATED IN THE ROOT DIRECTORY OF THIS FIRMWARE PACKAGE.
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
  ******************************************************************************
  */
  
/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM320518_EVAL_H
#define __STM320518_EVAL_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f0xx.h"
#include "stm32_eval_legacy.h"

/** @addtogroup Utilities
  * @{
  */

/** @addtogroup STM32_EVAL
  * @{
  */

/** @addtogroup STM320518_EVAL
  * @{
  */
      
/** @addtogroup STM320518_EVAL_LOW_LEVEL
  * @{
  */ 

/** @defgroup STM320518_EVAL_LOW_LEVEL_Exported_Types
  * @{
  */
typedef enum 
{
  LED1 = 0,
  LED2 = 1,
  LED3 = 2,
  LED4 = 3
} Led_TypeDef;

typedef enum 
{
  BUTTON_TAMPER = 0,
  BUTTON_KEY = 1,
  BUTTON_RIGHT = 2,
  BUTTON_LEFT = 3,
  BUTTON_UP = 4,
  BUTTON_DOWN = 5,
  BUTTON_SEL = 6
} Button_TypeDef;

typedef enum 
{  
  BUTTON_MODE_GPIO = 0,
  BUTTON_MODE_EXTI = 1
} ButtonMode_TypeDef;

typedef enum 
{ 
  JOY_NONE = 0,
  JOY_SEL = 1,
  JOY_DOWN = 2,
  JOY_LEFT = 3,
  JOY_RIGHT = 4,
  JOY_UP = 5
} JOYState_TypeDef
;

typedef enum 
{
  COM1 = 0,
  COM2 = 1
} COM_TypeDef;   
/**
  * @}
  */ 

/** @defgroup STM320518_EVAL_LOW_LEVEL_Exported_Constants
  * @{
  */ 

/** 
  * @brief  Define for STM320518_EVAL board  
  */ 
#if !defined (USE_STM320518_EVAL)
 #define USE_STM320518_EVAL
#endif

/** @addtogroup STM320518_EVAL_LOW_LEVEL_LED
  * @{
  */
#define LEDn                             4

#define LED1_PIN                         GPIO_Pin_10
#define LED1_GPIO_PORT                   GPIOC
#define LED1_GPIO_CLK                    RCC_AHBPeriph_GPIOC
  
#define LED2_PIN                         GPIO_Pin_11
#define LED2_GPIO_PORT                   GPIOC
#define LED2_GPIO_CLK                    RCC_AHBPeriph_GPIOC
  
#define LED3_PIN                         GPIO_Pin_12
#define LED3_GPIO_PORT                   GPIOC
#define LED3_GPIO_CLK                    RCC_AHBPeriph_GPIOC
  
#define LED4_PIN                         GPIO_Pin_2
#define LED4_GPIO_PORT                   GPIOD
#define LED4_GPIO_CLK                    RCC_AHBPeriph_GPIOD

/**
  * @}
  */ 

/** @addtogroup STM320518_EVAL_LOW_LEVEL_BUTTON
  * @{
  */  
#define BUTTONn                          7

/**
 * @brief Tamper push-button
 */
#define TAMPER_BUTTON_PIN                GPIO_Pin_13
#define TAMPER_BUTTON_GPIO_PORT          GPIOC
#define TAMPER_BUTTON_GPIO_CLK           RCC_AHBPeriph_GPIOC
#define TAMPER_BUTTON_EXTI_LINE          EXTI_Line13
#define TAMPER_BUTTON_EXTI_PORT_SOURCE   EXTI_PortSourceGPIOC
#define TAMPER_BUTTON_EXTI_PIN_SOURCE    EXTI_PinSource13
#define TAMPER_BUTTON_EXTI_IRQn          EXTI4_15_IRQn 

/**
 * @brief Key push-button
 */
#define KEY_BUTTON_PIN                   GPIO_Pin_8
#define KEY_BUTTON_GPIO_PORT             GPIOB
#define KEY_BUTTON_GPIO_CLK              RCC_AHBPeriph_GPIOB
#define KEY_BUTTON_EXTI_LINE             EXTI_Line8
#define KEY_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOB
#define KEY_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource8
#define KEY_BUTTON_EXTI_IRQn             EXTI4_15_IRQn

/**
 * @brief Joystick Right push-button
 */
#define RIGHT_BUTTON_PIN                 GPIO_Pin_8
#define RIGHT_BUTTON_GPIO_PORT           GPIOC
#define RIGHT_BUTTON_GPIO_CLK            RCC_AHBPeriph_GPIOC
#define RIGHT_BUTTON_EXTI_LINE           EXTI_Line8
#define RIGHT_BUTTON_EXTI_PORT_SOURCE    EXTI_PortSourceGPIOC
#define RIGHT_BUTTON_EXTI_PIN_SOURCE     EXTI_PinSource8
#define RIGHT_BUTTON_EXTI_IRQn           EXTI4_15_IRQn

/**
 * @brief Joystick Left push-button
 */
#define LEFT_BUTTON_PIN                  GPIO_Pin_9
#define LEFT_BUTTON_GPIO_PORT            GPIOC
#define LEFT_BUTTON_GPIO_CLK             RCC_AHBPeriph_GPIOC
#define LEFT_BUTTON_EXTI_LINE            EXTI_Line9
#define LEFT_BUTTON_EXTI_PORT_SOURCE     EXTI_PortSourceGPIOC
#define LEFT_BUTTON_EXTI_PIN_SOURCE      EXTI_PinSource9
#define LEFT_BUTTON_EXTI_IRQn            EXTI4_15_IRQn  

/**
 * @brief Joystick Up push-button
 */
#define UP_BUTTON_PIN                    GPIO_Pin_6
#define UP_BUTTON_GPIO_PORT              GPIOC
#define UP_BUTTON_GPIO_CLK               RCC_AHBPeriph_GPIOC
#define UP_BUTTON_EXTI_LINE              EXTI_Line6
#define UP_BUTTON_EXTI_PORT_SOURCE       EXTI_PortSourceGPIOC
#define UP_BUTTON_EXTI_PIN_SOURCE        EXTI_PinSource6
#define UP_BUTTON_EXTI_IRQn              EXTI4_15_IRQn  

/**
 * @brief Joystick Down push-button
 */  
#define DOWN_BUTTON_PIN                  GPIO_Pin_7
#define DOWN_BUTTON_GPIO_PORT            GPIOC
#define DOWN_BUTTON_GPIO_CLK             RCC_AHBPeriph_GPIOC
#define DOWN_BUTTON_EXTI_LINE            EXTI_Line7
#define DOWN_BUTTON_EXTI_PORT_SOURCE     EXTI_PortSourceGPIOC
#define DOWN_BUTTON_EXTI_PIN_SOURCE      EXTI_PinSource7
#define DOWN_BUTTON_EXTI_IRQn            EXTI4_15_IRQn  

/**
 * @brief Joystick Sel push-button
 */
#define SEL_BUTTON_PIN                   GPIO_Pin_0
#define SEL_BUTTON_GPIO_PORT             GPIOA
#define SEL_BUTTON_GPIO_CLK              RCC_AHBPeriph_GPIOA
#define SEL_BUTTON_EXTI_LINE             EXTI_Line0
#define SEL_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOA
#define SEL_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource0
#define SEL_BUTTON_EXTI_IRQn             EXTI0_1_IRQn 

/**
  * @}
  */ 


/** @addtogroup STM320518_EVAL_LOW_LEVEL_COM
  * @{
  */
#define COMn                             1

/**
 * @brief Definition for COM port1, connected to USART1
 */ 
#define EVAL_COM1                        USART1
#define EVAL_COM1_CLK                    RCC_APB2Periph_USART1

#define EVAL_COM1_TX_PIN                 GPIO_Pin_9
#define EVAL_COM1_TX_GPIO_PORT           GPIOA
#define EVAL_COM1_TX_GPIO_CLK            RCC_AHBPeriph_GPIOA
#define EVAL_COM1_TX_SOURCE              GPIO_PinSource9
#define EVAL_COM1_TX_AF                  GPIO_AF_1

#define EVAL_COM1_RX_PIN                 GPIO_Pin_10
#define EVAL_COM1_RX_GPIO_PORT           GPIOA
#define EVAL_COM1_RX_GPIO_CLK            RCC_AHBPeriph_GPIOA
#define EVAL_COM1_RX_SOURCE              GPIO_PinSource10
#define EVAL_COM1_RX_AF                  GPIO_AF_1

#define EVAL_COM1_CTS_PIN                GPIO_Pin_11
#define EVAL_COM1_CTS_GPIO_PORT          GPIOA
#define EVAL_COM1_CTS_GPIO_CLK           RCC_AHBPeriph_GPIOA
#define EVAL_COM1_CTS_SOURCE             GPIO_PinSource11
#define EVAL_COM1_CTS_AF                 GPIO_AF_1

#define EVAL_COM1_RTS_PIN                GPIO_Pin_12
#define EVAL_COM1_RTS_GPIO_PORT          GPIOA
#define EVAL_COM1_RTS_GPIO_CLK           RCC_AHBPeriph_GPIOA
#define EVAL_COM1_RTS_SOURCE             GPIO_PinSource12
#define EVAL_COM1_RTS_AF                 GPIO_AF_1
   
#define EVAL_COM1_IRQn                   USART1_IRQn

/**
  * @}
  */

/** @addtogroup STM320518_EVAL_LOW_LEVEL_SD_SPI
  * @{
  */
/**
  * @brief  SD SPI Interface pins
  */
#define SD_SPI                           SPI1
#define SD_SPI_CLK                       RCC_APB2Periph_SPI1

#define SD_SPI_SCK_PIN                   GPIO_Pin_5                  /* PA.05 */
#define SD_SPI_SCK_GPIO_PORT             GPIOA                       /* GPIOA */
#define SD_SPI_SCK_GPIO_CLK              RCC_AHBPeriph_GPIOA
#define SD_SPI_SCK_SOURCE                GPIO_PinSource5
#define SD_SPI_SCK_AF                    GPIO_AF_0

#define SD_SPI_MISO_PIN                  GPIO_Pin_6                  /* PA.06 */
#define SD_SPI_MISO_GPIO_PORT            GPIOA                       /* GPIOA */
#define SD_SPI_MISO_GPIO_CLK             RCC_AHBPeriph_GPIOA
#define SD_SPI_MISO_SOURCE               GPIO_PinSource6
#define SD_SPI_MISO_AF                   GPIO_AF_0

#define SD_SPI_MOSI_PIN                  GPIO_Pin_7                  /* PA.07 */
#define SD_SPI_MOSI_GPIO_PORT            GPIOA                       /* GPIOA */
#define SD_SPI_MOSI_GPIO_CLK             RCC_AHBPeriph_GPIOA
#define SD_SPI_MOSI_SOURCE               GPIO_PinSource7
#define SD_SPI_MOSI_AF                   GPIO_AF_0

#define SD_CS_PIN                        GPIO_Pin_5                  /* PF.05 */
#define SD_CS_GPIO_PORT                  GPIOF                       /* GPIOF */
#define SD_CS_GPIO_CLK                   RCC_AHBPeriph_GPIOF

   
#define SD_DETECT_PIN                    GPIO_Pin_15                 /* PB.15 */
#define SD_DETECT_EXTI_LINE              EXTI_Line15
#define SD_DETECT_EXTI_PIN_SOURCE        EXTI_PinSource15
#define SD_DETECT_GPIO_PORT              GPIOB                       /* GPIOB */
#define SD_DETECT_GPIO_CLK               RCC_AHBPeriph_GPIOB
#define SD_DETECT_EXTI_PORT_SOURCE       EXTI_PortSourceGPIOB
#define SD_DETECT_EXTI_IRQn              EXTI4_15_IRQn

/**
  * @}
  */


/** @addtogroup STM320518_EVAL_LOW_LEVEL_TSENSOR_I2C
  * @{
  */
/**
  * @brief  LM75 Temperature Sensor I2C Interface pins
  */
#define LM75_I2C                         I2C1
#define LM75_I2C_CLK                     RCC_APB1Periph_I2C1

#define LM75_I2C_SCL_PIN                 GPIO_Pin_6                  /* PB.06 */
#define LM75_I2C_SCL_GPIO_PORT           GPIOB                       /* GPIOB */
#define LM75_I2C_SCL_GPIO_CLK            RCC_AHBPeriph_GPIOB
#define LM75_I2C_SCL_SOURCE              GPIO_PinSource6
#define LM75_I2C_SCL_AF                  GPIO_AF_1

#define LM75_I2C_SDA_PIN                 GPIO_Pin_7                  /* PB.07 */
#define LM75_I2C_SDA_GPIO_PORT           GPIOB                       /* GPIOB */
#define LM75_I2C_SDA_GPIO_CLK            RCC_AHBPeriph_GPIOB
#define LM75_I2C_SDA_SOURCE              GPIO_PinSource7
#define LM75_I2C_SDA_AF                  GPIO_AF_1

#define LM75_I2C_SMBUSALERT_PIN          GPIO_Pin_5                  /* PB.05 */
#define LM75_I2C_SMBUSALERT_GPIO_PORT    GPIOB                       /* GPIOB */
#define LM75_I2C_SMBUSALERT_GPIO_CLK     RCC_AHBPeriph_GPIOB
#define LM75_I2C_SMBUSALERT_SOURCE       GPIO_PinSource5
#define LM75_I2C_SMBUSALERT_AF           GPIO_AF_3

/**
  * @}
  */
   
/** @addtogroup STM320518_EVAL_LOW_LEVEL_I2C_EE
  * @{
  */
/**
  * @brief  I2C EEPROM Interface pins
  */  
#define sEE_I2C                          I2C1
#define sEE_I2C_CLK                      RCC_APB1Periph_I2C1
   
#define sEE_I2C_SCL_PIN                  GPIO_Pin_6                  /* PB.06 */
#define sEE_I2C_SCL_GPIO_PORT            GPIOB                       /* GPIOB */
#define sEE_I2C_SCL_GPIO_CLK             RCC_AHBPeriph_GPIOB
#define sEE_I2C_SCL_SOURCE               GPIO_PinSource6
#define sEE_I2C_SCL_AF                   GPIO_AF_1

#define sEE_I2C_SDA_PIN                  GPIO_Pin_7                  /* PB.07 */
#define sEE_I2C_SDA_GPIO_PORT            GPIOB                       /* GPIOB */
#define sEE_I2C_SDA_GPIO_CLK             RCC_AHBPeriph_GPIOB
#define sEE_I2C_SDA_SOURCE               GPIO_PinSource7
#define sEE_I2C_SDA_AF                   GPIO_AF_1

/**
  * @}
  */

/** @defgroup STM320518_EVAL_LOW_LEVEL_Exported_Functions
  * @{
  */
void STM_EVAL_LEDInit(Led_TypeDef Led);
void STM_EVAL_LEDOn(Led_TypeDef Led);
void STM_EVAL_LEDOff(Led_TypeDef Led);
void STM_EVAL_LEDToggle(Led_TypeDef Led);
void STM_EVAL_PBInit(Button_TypeDef Button, ButtonMode_TypeDef Button_Mode);
uint32_t STM_EVAL_PBGetState(Button_TypeDef Button);
void STM_EVAL_COMInit(COM_TypeDef COM, USART_InitTypeDef* USART_InitStruct);
void SD_LowLevel_DeInit(void);
void SD_LowLevel_Init(void); 
void sFLASH_LowLevel_DeInit(void);
void sFLASH_LowLevel_Init(void);
void LM75_LowLevel_DeInit(void);
void LM75_LowLevel_Init(void);
void sEE_LowLevel_DeInit(void);
void sEE_LowLevel_Init(void); 

/**
  * @}
  */
  
#ifdef __cplusplus
}
#endif

#endif /* __STM320518_EVAL_H */
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

/******************* (C) COPYRIGHT 2012 STMicroelectronics *****END OF FILE****/
