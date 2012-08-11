/**
  ******************************************************************************
  * @file    stm32l152_eval.h
  * @author  MCD Application Team
  * @version V4.4.0RC1
  * @date    07/02/2010
  * @brief   This file contains definitions for STM32L152_EVAL's Leds, push-buttons
  *          and COM ports hardware resources.
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
#ifndef __STM32L152_EVAL_H
#define __STM32L152_EVAL_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32_eval.h"

/** @addtogroup Utilities
  * @{
  */

/** @addtogroup STM32_EVAL
  * @{
  */

/** @addtogroup STM32L152_EVAL
  * @{
  */
      
/** @addtogroup STM32L152_EVAL_LOW_LEVEL
  * @{
  */ 

/** @defgroup STM32L152_EVAL_LOW_LEVEL_Exported_Types
  * @{
  */
/**
  * @}
  */ 

/** @defgroup STM32L152_EVAL_LOW_LEVEL_Exported_Constants
  * @{
  */ 

/** @addtogroup STM32L152_EVAL_LOW_LEVEL_LED
  * @{
  */
#define LEDn                             4

#define LED1_PIN                         GPIO_Pin_0
#define LED1_GPIO_PORT                   GPIOD
#define LED1_GPIO_CLK                    RCC_AHBPeriph_GPIOD  
  
#define LED2_PIN                         GPIO_Pin_1
#define LED2_GPIO_PORT                   GPIOD
#define LED2_GPIO_CLK                    RCC_AHBPeriph_GPIOD  
  
#define LED3_PIN                         GPIO_Pin_4
#define LED3_GPIO_PORT                   GPIOD
#define LED3_GPIO_CLK                    RCC_AHBPeriph_GPIOD  
  
#define LED4_PIN                         GPIO_Pin_5
#define LED4_GPIO_PORT                   GPIOD
#define LED4_GPIO_CLK                    RCC_AHBPeriph_GPIOD

/**
  * @}
  */ 
  
/** @addtogroup STM32L152_EVAL_LOW_LEVEL_BUTTON
  * @{
  */  
#define BUTTONn                          8 

/**
 * @brief Wakeup push-button
 */
#define WAKEUP_BUTTON_PIN                GPIO_Pin_13
#define WAKEUP_BUTTON_GPIO_PORT          GPIOC
#define WAKEUP_BUTTON_GPIO_CLK           RCC_AHBPeriph_GPIOC
#define WAKEUP_BUTTON_EXTI_LINE          EXTI_Line13
#define WAKEUP_BUTTON_EXTI_PORT_SOURCE   EXTI_PortSourceGPIOC
#define WAKEUP_BUTTON_EXTI_PIN_SOURCE    EXTI_PinSource13
#define WAKEUP_BUTTON_EXTI_IRQn          EXTI15_10_IRQn 

/**
 * @brief Tamper push-button
 */
#define TAMPER_BUTTON_PIN                GPIO_Pin_13
#define TAMPER_BUTTON_GPIO_PORT          GPIOC
#define TAMPER_BUTTON_GPIO_CLK           RCC_AHBPeriph_GPIOC
#define TAMPER_BUTTON_EXTI_LINE          EXTI_Line13
#define TAMPER_BUTTON_EXTI_PORT_SOURCE   EXTI_PortSourceGPIOC
#define TAMPER_BUTTON_EXTI_PIN_SOURCE    EXTI_PinSource13
#define TAMPER_BUTTON_EXTI_IRQn          EXTI15_10_IRQn 

/**
 * @brief Key push-button
 */
#define KEY_BUTTON_PIN                   GPIO_Pin_13
#define KEY_BUTTON_GPIO_PORT             GPIOC
#define KEY_BUTTON_GPIO_CLK              RCC_AHBPeriph_GPIOC
#define KEY_BUTTON_EXTI_LINE             EXTI_Line13
#define KEY_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOC
#define KEY_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource13
#define KEY_BUTTON_EXTI_IRQn             EXTI15_10_IRQn

/**
 * @brief Joystick Right push-button
 */
#define RIGHT_BUTTON_PIN                 GPIO_Pin_11
#define RIGHT_BUTTON_GPIO_PORT           GPIOE
#define RIGHT_BUTTON_GPIO_CLK            RCC_AHBPeriph_GPIOE
#define RIGHT_BUTTON_EXTI_LINE           EXTI_Line11
#define RIGHT_BUTTON_EXTI_PORT_SOURCE    EXTI_PortSourceGPIOE
#define RIGHT_BUTTON_EXTI_PIN_SOURCE     EXTI_PinSource11
#define RIGHT_BUTTON_EXTI_IRQn           EXTI15_10_IRQn

/**
 * @brief Joystick Left push-button
 */
#define LEFT_BUTTON_PIN                  GPIO_Pin_12
#define LEFT_BUTTON_GPIO_PORT            GPIOE
#define LEFT_BUTTON_GPIO_CLK             RCC_AHBPeriph_GPIOE
#define LEFT_BUTTON_EXTI_LINE            EXTI_Line12
#define LEFT_BUTTON_EXTI_PORT_SOURCE     EXTI_PortSourceGPIOE
#define LEFT_BUTTON_EXTI_PIN_SOURCE      EXTI_PinSource12
#define LEFT_BUTTON_EXTI_IRQn            EXTI15_10_IRQn  

/**
 * @brief Joystick Up push-button
 */
#define UP_BUTTON_PIN                    GPIO_Pin_9
#define UP_BUTTON_GPIO_PORT              GPIOE
#define UP_BUTTON_GPIO_CLK               RCC_AHBPeriph_GPIOE
#define UP_BUTTON_EXTI_LINE              EXTI_Line9
#define UP_BUTTON_EXTI_PORT_SOURCE       EXTI_PortSourceGPIOE
#define UP_BUTTON_EXTI_PIN_SOURCE        EXTI_PinSource9
#define UP_BUTTON_EXTI_IRQn              EXTI9_5_IRQn  

/**
 * @brief Joystick Down push-button
 */  
#define DOWN_BUTTON_PIN                  GPIO_Pin_10
#define DOWN_BUTTON_GPIO_PORT            GPIOE
#define DOWN_BUTTON_GPIO_CLK             RCC_AHBPeriph_GPIOE
#define DOWN_BUTTON_EXTI_LINE            EXTI_Line10
#define DOWN_BUTTON_EXTI_PORT_SOURCE     EXTI_PortSourceGPIOE
#define DOWN_BUTTON_EXTI_PIN_SOURCE      EXTI_PinSource10
#define DOWN_BUTTON_EXTI_IRQn            EXTI15_10_IRQn  

/**
 * @brief Joystick Sel push-button
 */
#define SEL_BUTTON_PIN                   GPIO_Pin_8
#define SEL_BUTTON_GPIO_PORT             GPIOE
#define SEL_BUTTON_GPIO_CLK              RCC_AHBPeriph_GPIOE
#define SEL_BUTTON_EXTI_LINE             EXTI_Line8
#define SEL_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOE
#define SEL_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource8
#define SEL_BUTTON_EXTI_IRQn             EXTI9_5_IRQn 

/**
  * @}
  */ 

/** @addtogroup STM32L152_EVAL_LOW_LEVEL_COM
  * @{
  */
#define COMn                             2

/**
 * @brief Definition for COM port1, connected to USART2
 */ 
#define EVAL_COM1                        USART2
#define EVAL_COM1_CLK                    RCC_APB1Periph_USART2
#define EVAL_COM1_TX_PIN                 GPIO_Pin_5
#define EVAL_COM1_TX_GPIO_PORT           GPIOD
#define EVAL_COM1_TX_GPIO_CLK            RCC_AHBPeriph_GPIOD
#define EVAL_COM1_TX_SOURCE              GPIO_PinSource5
#define EVAL_COM1_TX_AF                  GPIO_AF_USART2
#define EVAL_COM1_RX_PIN                 GPIO_Pin_6
#define EVAL_COM1_RX_GPIO_PORT           GPIOD
#define EVAL_COM1_RX_GPIO_CLK            RCC_AHBPeriph_GPIOD
#define EVAL_COM1_RX_SOURCE              GPIO_PinSource6
#define EVAL_COM1_RX_AF                  GPIO_AF_USART2
#define EVAL_COM1_IRQn                   USART2_IRQn

/**
 * @brief Definition for COM port2, connected to USART3
 */ 
#define EVAL_COM2                        USART3
#define EVAL_COM2_CLK                    RCC_APB1Periph_USART3

#define EVAL_COM2_TX_PIN                 GPIO_Pin_10
#define EVAL_COM2_TX_GPIO_PORT           GPIOC
#define EVAL_COM2_TX_GPIO_CLK            RCC_AHBPeriph_GPIOC
#define EVAL_COM2_TX_SOURCE              GPIO_PinSource10
#define EVAL_COM2_TX_AF                  GPIO_AF_USART3

#define EVAL_COM2_RX_PIN                 GPIO_Pin_11
#define EVAL_COM2_RX_GPIO_PORT           GPIOC
#define EVAL_COM2_RX_GPIO_CLK            RCC_AHBPeriph_GPIOC
#define EVAL_COM2_RX_SOURCE              GPIO_PinSource11
#define EVAL_COM2_RX_AF                  GPIO_AF_USART3
#define EVAL_COM2_IRQn                   USART3_IRQn

/**
  * @}
  */ 

/** @addtogroup STM32L152_EVAL_LOW_LEVEL_SD_FLASH
  * @{
  */ 
/**
  * @brief  SD Card SPI Interface
  */  
#define SD_SPI                           SPI2
#define SD_SPI_CLK                       RCC_APB1Periph_SPI2
#define SD_SPI_SCK_PIN                   GPIO_Pin_13                 /* PB.13 */
#define SD_SPI_SCK_GPIO_PORT             GPIOB                       /* GPIOB */
#define SD_SPI_SCK_GPIO_CLK              RCC_AHBPeriph_GPIOB
#define SD_SPI_SCK_SOURCE                GPIO_PinSource13
#define SD_SPI_SCK_AF                    GPIO_AF_SPI2
#define SD_SPI_MISO_PIN                  GPIO_Pin_14                 /* PB.14 */
#define SD_SPI_MISO_GPIO_PORT            GPIOB                       /* GPIOB */
#define SD_SPI_MISO_GPIO_CLK             RCC_AHBPeriph_GPIOB
#define SD_SPI_MISO_SOURCE               GPIO_PinSource14
#define SD_SPI_MISO_AF                   GPIO_AF_SPI2
#define SD_SPI_MOSI_PIN                  GPIO_Pin_15                 /* PB.15 */
#define SD_SPI_MOSI_GPIO_PORT            GPIOB                       /* GPIOB */
#define SD_SPI_MOSI_GPIO_CLK             RCC_AHBPeriph_GPIOB
#define SD_SPI_MOSI_SOURCE               GPIO_PinSource15
#define SD_SPI_MOSI_AF                   GPIO_AF_SPI2
#define SD_CS_PIN                        GPIO_Pin_7                  /* PD.07 */
#define SD_CS_GPIO_PORT                  GPIOD                       /* GPIOD */
#define SD_CS_GPIO_CLK                   RCC_AHBPeriph_GPIOD
#define SD_DETECT_PIN                    GPIO_Pin_7                  /* PE.07 */
#define SD_DETECT_GPIO_PORT              GPIOE                       /* GPIOE */
#define SD_DETECT_GPIO_CLK               RCC_AHBPeriph_GPIOE
/**
  * @}
  */ 
  
/** @addtogroup STM32L152_EVAL_LOW_LEVEL_TSENSOR_I2C
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
#define LM75_I2C_SCL_AF                  GPIO_AF_I2C1
#define LM75_I2C_SDA_PIN                 GPIO_Pin_7                  /* PB.07 */
#define LM75_I2C_SDA_GPIO_PORT           GPIOB                       /* GPIOB */
#define LM75_I2C_SDA_GPIO_CLK            RCC_AHBPeriph_GPIOB
#define LM75_I2C_SDA_SOURCE              GPIO_PinSource7
#define LM75_I2C_SDA_AF                  GPIO_AF_I2C1
#define LM75_I2C_SMBUSALERT_PIN          GPIO_Pin_5                  /* PB.05 */
#define LM75_I2C_SMBUSALERT_GPIO_PORT    GPIOB                       /* GPIOB */
#define LM75_I2C_SMBUSALERT_GPIO_CLK     RCC_AHBPeriph_GPIOB
#define LM75_I2C_SMBUSALERT_SOURCE       GPIO_PinSource5
#define LM75_I2C_SMBUSALERT_AF           GPIO_AF_I2C1
/**
  * @}
  */  
/**
  * @}
  */ 
  
/** @defgroup STM32L152_EVAL_LOW_LEVEL_Exported_Macros
  * @{
  */  
/**
  * @}
  */ 


/** @defgroup STM32L152_EVAL_LOW_LEVEL_Exported_Functions
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
void LM75_LowLevel_DeInit(void);
void LM75_LowLevel_Init(void);  
/**
  * @}
  */
  
#ifdef __cplusplus
}
#endif

#endif /* __STM32L152_EVAL_H */
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

/******************* (C) COPYRIGHT 2010 STMicroelectronics *****END OF FILE****/
