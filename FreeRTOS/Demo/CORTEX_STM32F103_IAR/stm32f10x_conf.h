/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_conf.h
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : Library configuration file.
********************************************************************************
* History:
* mm/dd/yyyy: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F10x_CONF_H
#define __STM32F10x_CONF_H

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_type.h"

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* Comment the line below to compile the library in release mode */
#define DEBUG

/* Comment the line below to disable the specific peripheral inclusion */
/************************************* ADC ************************************/
//#define _ADC
//#define _ADC1
//#define _ADC2

/************************************* CAN ************************************/
//#define _CAN

/************************************* DMA ************************************/
//#define _DMA
//#define _DMA_Channel1
//#define _DMA_Channel2
//#define _DMA_Channel3
//#define _DMA_Channel4
//#define _DMA_Channel5
//#define _DMA_Channel6
//#define _DMA_Channel7

/************************************* EXTI ***********************************/
#define _EXTI

/************************************* GPIO ***********************************/
#define _GPIO
#define _GPIOA
#define _GPIOB
#define _GPIOC
#define _GPIOD
#define _GPIOE
#define _AFIO

/************************************* I2C ************************************/
//#define _I2C
//#define _I2C1
//#define _I2C2

/************************************* IWDG ***********************************/
//#define _IWDG

/************************************* NVIC ***********************************/
#define _NVIC
#define _SCB

/************************************* BKP ************************************/
//#define _BKP

/************************************* PWR ************************************/
//#define _PWR

/************************************* RCC ************************************/
#define _RCC

/************************************* RTC ************************************/
//#define _RTC

/************************************* SPI ************************************/
#define _SPI
#define _SPI1
#define _SPI2

/************************************* SysTick ********************************/
#define _SysTick

/************************************* TIM ************************************/
//#define _TIM
#define _TIM2
#define _TIM3
//#define _TIM4

/************************************* USART **********************************/
#define _USART
#define _USART1
//#define _USART2
//#define _USART3

/************************************* WWDG ***********************************/
//#define _WWDG

/* In the following line adjust the value of External High Speed oscillator (HSE)
   used in your application */
#define HSE_Value    ((u32)8000000)   /* Value of the External oscillator in Hz*/

/* Exported macro ------------------------------------------------------------*/
#undef assert
#ifdef  DEBUG
/*******************************************************************************
* Macro Name     : assert
* Description    : The assert macro is used for function's parameters check.
*                  It is used only if the library is compiled in DEBUG mode.
* Input          : - expr: If expr is false, it calls assert_failed function
*                    which reports the name of the source file and the source
*                    line number of the call that failed.
*                    If expr is true, it returns no value.
* Return         : None
*******************************************************************************/
  #define assert(expr) ((expr) ? (void)0 : assert_failed(__FILE__, __LINE__))
/* Exported functions ------------------------------------------------------- */
  void assert_failed(u8* file, u32 line);
#else
  #define assert(expr) ((void)0)
#endif /* DEBUG */

/* Exported functions ------------------------------------------------------- */

#endif /* __STM32F10x_CONF_H */

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
