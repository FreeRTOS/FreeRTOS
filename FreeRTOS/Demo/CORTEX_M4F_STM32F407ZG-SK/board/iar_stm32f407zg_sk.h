/**
  ******************************************************************************
  * @file    iar_stm32f407zg_sk.h
  * @brief   This file contains definitions for Leds, push-buttons
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
#ifndef __IAR_STM32F407ZG_SK_H
#define __IAR_STM32F407ZG_SK_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f4xx.h"
   
typedef enum 
{
  LED1 = 0,
  LED2 = 1,
  LED3 = 2,
  LED4 = 3
} Led_TypeDef;

typedef enum 
{  
  BUTTON_WAKEUP = 0,
  BUTTON_TAMPER = 1,
  BUTTON_USER = 2,
  BUTTON_RIGHT = 3,
  BUTTON_LEFT = 4,
  BUTTON_UP = 5,
  BUTTON_DOWN = 6,
  BUTTON_SEL = 7
} Button_TypeDef;

typedef enum 
{  
  BUTTON_MODE_GPIO = 0,
  BUTTON_MODE_EXTI = 1
} ButtonMode_TypeDef;

typedef enum 
{
  COM1 = 0,
  COM2 = 1
} COM_TypeDef;   

#define LEDn                             4

#define LED1_PIN                         GPIO_Pin_6
#define LED1_GPIO_PORT                   GPIOF
#define LED1_GPIO_CLK                    RCC_AHB1Periph_GPIOF  
  
#define LED2_PIN                         GPIO_Pin_7
#define LED2_GPIO_PORT                   GPIOF
#define LED2_GPIO_CLK                    RCC_AHB1Periph_GPIOF  
  
#define LED3_PIN                         GPIO_Pin_8
#define LED3_GPIO_PORT                   GPIOF
#define LED3_GPIO_CLK                    RCC_AHB1Periph_GPIOF  
  
#define LED4_PIN                         GPIO_Pin_9
#define LED4_GPIO_PORT                   GPIOF
#define LED4_GPIO_CLK                    RCC_AHB1Periph_GPIOF

/**
  * @}
  */ 
  
/** @addtogroup IAR_STM32F407ZG_SK_LOW_LEVEL_BUTTON
  * @{
  */  
#define BUTTONn                          8 /**/

/**
 * @brief Wakeup push-button
 */
#define WAKEUP_BUTTON_PIN                GPIO_Pin_0
#define WAKEUP_BUTTON_GPIO_PORT          GPIOA
#define WAKEUP_BUTTON_GPIO_CLK           RCC_AHB1Periph_GPIOA
#define WAKEUP_BUTTON_EXTI_LINE          EXTI_Line0
#define WAKEUP_BUTTON_EXTI_PORT_SOURCE   EXTI_PortSourceGPIOA
#define WAKEUP_BUTTON_EXTI_PIN_SOURCE    EXTI_PinSource0
#define WAKEUP_BUTTON_EXTI_IRQn          EXTI0_IRQn 

/**
 * @brief Tamper push-button
 */
#define TAMPER_BUTTON_PIN                GPIO_Pin_13
#define TAMPER_BUTTON_GPIO_PORT          GPIOC
#define TAMPER_BUTTON_GPIO_CLK           RCC_AHB1Periph_GPIOC
#define TAMPER_BUTTON_EXTI_LINE          EXTI_Line13
#define TAMPER_BUTTON_EXTI_PORT_SOURCE   EXTI_PortSourceGPIOC
#define TAMPER_BUTTON_EXTI_PIN_SOURCE    EXTI_PinSource13
#define TAMPER_BUTTON_EXTI_IRQn          EXTI15_10_IRQn 

/**
 * @brief Key push-button
 */
#define USER_BUTTON_PIN                   GPIO_Pin_6
#define USER_BUTTON_GPIO_PORT             GPIOG
#define USER_BUTTON_GPIO_CLK              RCC_AHB1Periph_GPIOG
#define USER_BUTTON_EXTI_LINE             EXTI_Line6
#define USER_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOG
#define USER_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource6
#define USER_BUTTON_EXTI_IRQn             EXTI9_5_IRQn
/**
 * @brief Joystick Right
 */
#define RIGHT_BUTTON_PIN                   GPIO_Pin_3
#define RIGHT_BUTTON_GPIO_PORT             GPIOC
#define RIGHT_BUTTON_GPIO_CLK              RCC_AHB1Periph_GPIOC
#define RIGHT_BUTTON_EXTI_LINE             EXTI_Line3
#define RIGHT_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOC
#define RIGHT_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource3
#define RIGHT_BUTTON_EXTI_IRQn             EXTI3_IRQn
/**
 * @brief Joystick Left
 */
#define LEFT_BUTTON_PIN                   GPIO_Pin_11
#define LEFT_BUTTON_GPIO_PORT             GPIOG
#define LEFT_BUTTON_GPIO_CLK              RCC_AHB1Periph_GPIOG
#define LEFT_BUTTON_EXTI_LINE             EXTI_Line11
#define LEFT_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOG
#define LEFT_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource11
#define LEFT_BUTTON_EXTI_IRQn             EXTI15_10_IRQn
/**
 * @brief Joystick Up
 */
#define UP_BUTTON_PIN                   GPIO_Pin_7
#define UP_BUTTON_GPIO_PORT             GPIOG
#define UP_BUTTON_GPIO_CLK              RCC_AHB1Periph_GPIOG
#define UP_BUTTON_EXTI_LINE             EXTI_Line7
#define UP_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOG
#define UP_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource7
#define UP_BUTTON_EXTI_IRQn             EXTI9_5_IRQn
/**
 * @brief Joystick Down
 */
#define DOWN_BUTTON_PIN                   GPIO_Pin_8
#define DOWN_BUTTON_GPIO_PORT             GPIOG
#define DOWN_BUTTON_GPIO_CLK              RCC_AHB1Periph_GPIOG
#define DOWN_BUTTON_EXTI_LINE             EXTI_Line8
#define DOWN_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOG
#define DOWN_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource8
#define DOWN_BUTTON_EXTI_IRQn             EXTI9_5_IRQn
/**
 * @brief Joystick Sel
 */
#define SEL_BUTTON_PIN                   GPIO_Pin_15
#define SEL_BUTTON_GPIO_PORT             GPIOG
#define SEL_BUTTON_GPIO_CLK              RCC_AHB1Periph_GPIOG
#define SEL_BUTTON_EXTI_LINE             EXTI_Line15
#define SEL_BUTTON_EXTI_PORT_SOURCE      EXTI_PortSourceGPIOG
#define SEL_BUTTON_EXTI_PIN_SOURCE       EXTI_PinSource15
#define SEL_BUTTON_EXTI_IRQn             EXTI15_10_IRQn


/**
  * @}
  */ 

/** @addtogroup IAR_STM32F407ZG_SK_LOW_LEVEL_COM
  * @{
  */
#define COMn                             2

/**
 * @brief Definition for COM port1, connected to USART6
 */ 
#define EVAL_COM1                        USART6
#define EVAL_COM1_CLK                    RCC_APB2Periph_USART6
#define EVAL_COM1_TX_PIN                 GPIO_Pin_6
#define EVAL_COM1_TX_GPIO_PORT           GPIOC
#define EVAL_COM1_TX_GPIO_CLK            RCC_AHB1Periph_GPIOC
#define EVAL_COM1_TX_SOURCE              GPIO_PinSource6
#define EVAL_COM1_TX_AF                  GPIO_AF_USART6
#define EVAL_COM1_RX_PIN                 GPIO_Pin_9
#define EVAL_COM1_RX_GPIO_PORT           GPIOG
#define EVAL_COM1_RX_GPIO_CLK            RCC_AHB1Periph_GPIOG
#define EVAL_COM1_RX_SOURCE              GPIO_PinSource9
#define EVAL_COM1_RX_AF                  GPIO_AF_USART6
#define EVAL_COM1_IRQn                   USART6_IRQn

/**
 * @brief Definition for COM port2, connected to USART3
 */ 
#define EVAL_COM2                        USART3
#define EVAL_COM2_CLK                    RCC_APB1Periph_USART3
#define EVAL_COM2_TX_PIN                 GPIO_Pin_8
#define EVAL_COM2_TX_GPIO_PORT           GPIOD
#define EVAL_COM2_TX_GPIO_CLK            RCC_AHB1Periph_GPIOD
#define EVAL_COM2_TX_SOURCE              GPIO_PinSource8
#define EVAL_COM2_TX_AF                  GPIO_AF_USART3
#define EVAL_COM2_RX_PIN                 GPIO_Pin_9
#define EVAL_COM2_RX_GPIO_PORT           GPIOD
#define EVAL_COM2_RX_GPIO_CLK            RCC_AHB1Periph_GPIOD
#define EVAL_COM2_RX_SOURCE              GPIO_PinSource9
#define EVAL_COM2_RX_AF                  GPIO_AF_USART3
#define EVAL_COM2_RTS_PIN                GPIO_Pin_12
#define EVAL_COM2_RTS_GPIO_PORT          GPIOD
#define EVAL_COM2_RTS_GPIO_CLK           RCC_AHB1Periph_GPIOD
#define EVAL_COM2_RTS_SOURCE             GPIO_PinSource12
#define EVAL_COM2_RTS_AF                 GPIO_AF_USART3
#define EVAL_COM2_CTS_PIN                GPIO_Pin_11
#define EVAL_COM2_CTS_GPIO_PORT          GPIOD
#define EVAL_COM2_CTS_GPIO_CLK           RCC_AHB1Periph_GPIOD
#define EVAL_COM2_CTS_SOURCE             GPIO_PinSource11
#define EVAL_COM2_CTS_AF                 GPIO_AF_USART3
#define EVAL_COM2_IRQn                   USART3_IRQn

/**
  * @BUZZER
  */ 
#define BUZZER_GPIO_PIN                  GPIO_Pin_10
#define BUZZER_GPIO_PORT                 GPIOA
#define BUZZER_GPIO_CLK                  RCC_AHB1Periph_GPIOA
#define BUZZER_PIN_SOURCE                GPIO_PinSource10
#define BUZZER_TIM                       TIM1
#define RCC_APB2PERIPH_BUZZER_TIM        RCC_APB2Periph_TIM1
#define BUZZER_PIN_AF                    GPIO_AF_TIM1

/**
  * @USB OTG
  */ 
#define OTG_FS_VBUS_PIN                    GPIO_Pin_9
#define OTG_FS_VBUS_PORT                   GPIOA
#define OTG_FS_VBUS_CLK                    RCC_AHB1Periph_GPIOA
#define OTG_FS_VBUS_SOURCE                 GPIO_PinSource9

#define USB_FS_VBUSON_PIN                  GPIO_Pin_2
#define USB_FS_VBUSON_PORT                 GPIOC
#define USB_FS_VBUSON_CLK                  RCC_AHB1Periph_GPIOC
#define USB_FS_VBUSON_SOURCE               GPIO_PinSource2

#define USB_FS_FAULT_PIN                   GPIO_Pin_10
#define USB_FS_FAULT_PORT                  GPIOB
#define USB_FS_FAULT_CLK                   RCC_AHB1Periph_GPIOB
#define USB_FS_FAULT_SOURCE                GPIO_PinSource10

/**
  * @USB HOST
  */ 
#define OTG_HS_VBUS_PIN                    GPIO_Pin_13
#define OTG_HS_VBUS_PORT                   GPIOB
#define OTG_HS_VBUS_CLK                    RCC_AHB1Periph_GPIOB
#define OTG_HS_VBUS_SOURCE                 GPIO_PinSource13

#define USB_HS_VBUSON_PIN                  GPIO_Pin_3
#define USB_HS_VBUSON_PORT                 GPIOE
#define USB_HS_VBUSON_CLK                  RCC_AHB1Periph_GPIOE
#define USB_HS_VBUSON_SOURCE               GPIO_PinSource3

#define USB_HS_FAULT_PIN                   GPIO_Pin_13
#define USB_HS_FAULT_PORT                  GPIOD
#define USB_HS_FAULT_CLK                   RCC_AHB1Periph_GPIOD
#define USB_HS_FAULT_SOURCE                GPIO_PinSource13

#define OTG_HS_ID_PIN                      GPIO_Pin_12
#define OTG_HS_ID_PORT                     GPIOB
#define OTG_HS_ID_CLK                      RCC_AHB1Periph_GPIOB
#define OTG_HS_ID_SOURCE                   GPIO_PinSource12

/**
  * @TRIMER
  */ 
#define TRIMER_PIN                      GPIO_Pin_0
#define TRIMER_PORT                     GPIOC
#define TRIMER_CLK                      RCC_AHB1Periph_GPIOC
#define TRIMER_SOURCE                   GPIO_PinSource0
#define TRIMER_CHANNEL                  ADC_Channel_10

/** @addtogroup IAR_STM32F407ZG_SK_LOW_LEVEL_SD_FLASH
  * @{
  */ 
/**
  * @SD
  */ 
#define SD_CP_PIN                       GPIO_Pin_3
#define SD_CP_PORT                      GPIOD
#define SD_CP_CLK                       RCC_AHB1Periph_GPIOD
#define SD_CP_SOURCE                    GPIO_PinSource3

#define SD_WP_PIN                       GPIO_Pin_4
#define SD_WP_PORT                      GPIOE
#define SD_WP_CLK                       RCC_AHB1Periph_GPIOE
#define SD_WP_SOURCE                    GPIO_PinSource4

#define SD_CMD_PIN                      GPIO_Pin_2
#define SD_CMD_PORT                     GPIOD
#define SD_CMD_CLK                      RCC_AHB1Periph_GPIOD
#define SD_CMD_SOURCE                   GPIO_PinSource2

#define SD_D0_PIN                       GPIO_Pin_8
#define SD_D0_PORT                      GPIOC
#define SD_D0_CLK                       RCC_AHB1Periph_GPIOC
#define SD_D0_SOURCE                    GPIO_PinSource8

#define SD_D1_PIN                       GPIO_Pin_9
#define SD_D1_PORT                      GPIOC
#define SD_D1_CLK                       RCC_AHB1Periph_GPIOC
#define SD_D1_SOURCE                    GPIO_PinSource9

#define SD_D2_PIN                       GPIO_Pin_10
#define SD_D2_PORT                      GPIOC
#define SD_D2_CLK                       RCC_AHB1Periph_GPIOC
#define SD_D2_SOURCE                    GPIO_PinSource10

#define SD_D3_PIN                       GPIO_Pin_11
#define SD_D3_PORT                      GPIOC
#define SD_D3_CLK                       RCC_AHB1Periph_GPIOC
#define SD_D3_SOURCE                    GPIO_PinSource11

#define SD_CLK_PIN                      GPIO_Pin_12
#define SD_CLK_PORT                     GPIOC
#define SD_CLK_CLK                      RCC_AHB1Periph_GPIOC
#define SD_CLK_SOURCE                   GPIO_PinSource12
/**
  * @brief  SD FLASH SDIO Interface
  */ 
#define SD_SDIO_DMA_STREAM3	          3
//#define SD_SDIO_DMA_STREAM6           6

#ifdef SD_SDIO_DMA_STREAM3
 #define SD_SDIO_DMA_STREAM            DMA2_Stream3
 #define SD_SDIO_DMA_CHANNEL           DMA_Channel_4
 #define SD_SDIO_DMA_FLAG_FEIF         DMA_FLAG_FEIF3
 #define SD_SDIO_DMA_FLAG_DMEIF        DMA_FLAG_DMEIF3
 #define SD_SDIO_DMA_FLAG_TEIF         DMA_FLAG_TEIF3
 #define SD_SDIO_DMA_FLAG_HTIF         DMA_FLAG_HTIF3
 #define SD_SDIO_DMA_FLAG_TCIF         DMA_FLAG_TCIF3 
#elif defined SD_SDIO_DMA_STREAM6
 #define SD_SDIO_DMA_STREAM            DMA2_Stream6
 #define SD_SDIO_DMA_CHANNEL           DMA_Channel_4
 #define SD_SDIO_DMA_FLAG_FEIF         DMA_FLAG_FEIF6
 #define SD_SDIO_DMA_FLAG_DMEIF        DMA_FLAG_DMEIF6
 #define SD_SDIO_DMA_FLAG_TEIF         DMA_FLAG_TEIF6
 #define SD_SDIO_DMA_FLAG_HTIF         DMA_FLAG_HTIF6
 #define SD_SDIO_DMA_FLAG_TCIF         DMA_FLAG_TCIF6 
#endif /* SD_SDIO_DMA_STREAM3 */

/**
  * @}
  */ 
  
/**
  * @CAN
  */ 
#define CAN_TX_PIN                      GPIO_Pin_9
#define CAN_TX_PORT                     GPIOB
#define CAN_TX_CLK                      RCC_AHB1Periph_GPIOB
#define CAN_TX_AF                       GPIO_AF_CAN1
#define CAN_TX_SOURCE                   GPIO_PinSource9

#define CAN_RX_PIN                      GPIO_Pin_8
#define CAN_RX_PORT                     GPIOB
#define CAN_RX_CLK                      RCC_AHB1Periph_GPIOB
#define CAN_RX_AF                       GPIO_AF_CAN1
#define CAN_RX_SOURCE                   GPIO_PinSource8

#define CAN_CTRL_PIN                    GPIO_Pin_6
#define CAN_CTRL_PORT                   GPIOD
#define CAN_CTRL_CLK                    RCC_AHB1Periph_GPIOD
#define CAN_CTRL_SOURCE                 GPIO_PinSource6

/**
  * @}
  */  
/**
  * @}
  */ 
  
/** @defgroup IAR_STM32F407ZG_SK_LOW_LEVEL_Exported_Macros
  * @{
  */  
/**
  * @}
  */ 


/** @defgroup IAR_STM32F407ZG_SK_LOW_LEVEL_Exported_Functions
  * @{
  */
void STM_EVAL_LEDInit(Led_TypeDef Led);
void STM_EVAL_LEDOn(Led_TypeDef Led);
void STM_EVAL_LEDOff(Led_TypeDef Led);
void STM_EVAL_LEDToggle(Led_TypeDef Led);
void STM_EVAL_PBInit(Button_TypeDef Button, ButtonMode_TypeDef Button_Mode);
uint32_t STM_EVAL_PBGetState(Button_TypeDef Button);
void STM_EVAL_COMInit(COM_TypeDef COM, USART_InitTypeDef* USART_InitStruct); 
/**
  * @}
  */
  
#ifdef __cplusplus
}
#endif

#endif /* __IAR_STM32F407ZG_SK_H */
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
