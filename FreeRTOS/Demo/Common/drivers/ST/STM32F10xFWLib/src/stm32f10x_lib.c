/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_lib.c
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file provides all peripherals pointers initialization.
********************************************************************************
* History:
* 04/02/2007: V0.2
* 02/05/2007: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

#define EXT

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_lib.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

#ifdef DEBUG
/*******************************************************************************
* Function Name  : debug
* Description    : This function initialize peripherals pointers.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void debug(void)
{

/************************************* ADC ************************************/
#ifdef _ADC1
  ADC1 = (ADC_TypeDef *)  ADC1_BASE;
#endif /*_ADC1 */

#ifdef _ADC2
  ADC2 = (ADC_TypeDef *)  ADC2_BASE;
#endif /*_ADC2 */

/************************************* BKP ************************************/
#ifdef _BKP
  BKP = (BKP_TypeDef *)  BKP_BASE;
#endif /*_BKP */

/************************************* CAN ************************************/
#ifdef _CAN
  CAN = (CAN_TypeDef *)  CAN_BASE;
#endif /*_CAN */

/************************************* DMA ************************************/
#ifdef _DMA
  DMA = (DMA_TypeDef *)  DMA_BASE;
#endif /*_DMA */

#ifdef _DMA_Channel1
  DMA_Channel1 = (DMA_Channel_TypeDef *)  DMA_Channel1_BASE;
#endif /*_DMA_Channel1 */

#ifdef _DMA_Channel2
  DMA_Channel2 = (DMA_Channel_TypeDef *)  DMA_Channel2_BASE;
#endif /*_DMA_Channel2 */

#ifdef _DMA_Channel3
  DMA_Channel3 = (DMA_Channel_TypeDef *)  DMA_Channel3_BASE;
#endif /*_DMA_Channel3 */

#ifdef _DMA_Channel4
  DMA_Channel4 = (DMA_Channel_TypeDef *)  DMA_Channel4_BASE;
#endif /*_DMA_Channel4 */

#ifdef _DMA_Channel5
  DMA_Channel5 = (DMA_Channel_TypeDef *)  DMA_Channel5_BASE;
#endif /*_DMA_Channel5 */

#ifdef _DMA_Channel6
  DMA_Channel6 = (DMA_Channel_TypeDef *)  DMA_Channel6_BASE;
#endif /*_DMA_Channel6 */

#ifdef _DMA_Channel7
  DMA_Channel7 = (DMA_Channel_TypeDef *)  DMA_Channel7_BASE;
#endif /*_DMA_Channel7 */

/************************************* EXTI ***********************************/
#ifdef _EXTI
  EXTI = (EXTI_TypeDef *)  EXTI_BASE;
#endif /*_EXTI */

/************************************* FLASH and Option Bytes *****************/
#ifdef _FLASH
  FLASH = (FLASH_TypeDef *)  FLASH_BASE;
  OB = (OB_TypeDef *)  OB_BASE;
#endif /*_FLASH */

/************************************* GPIO ***********************************/
#ifdef _GPIOA
  GPIOA = (GPIO_TypeDef *)  GPIOA_BASE;
#endif /*_GPIOA */

#ifdef _GPIOB
  GPIOB = (GPIO_TypeDef *)  GPIOB_BASE;
#endif /*_GPIOB */

#ifdef _GPIOC
  GPIOC = (GPIO_TypeDef *)  GPIOC_BASE;
#endif /*_GPIOC */

#ifdef _GPIOD
  GPIOD = (GPIO_TypeDef *)  GPIOD_BASE;
#endif /*_GPIOD */

#ifdef _GPIOE
  GPIOE = (GPIO_TypeDef *)  GPIOE_BASE;
#endif /*_GPIOE */

#ifdef _AFIO
  AFIO = (AFIO_TypeDef *)  AFIO_BASE;
#endif /*_AFIO */

/************************************* I2C ************************************/
#ifdef _I2C1
  I2C1 = (I2C_TypeDef *)  I2C1_BASE;
#endif /*_I2C1 */

#ifdef _I2C2
  I2C2 = (I2C_TypeDef *)  I2C2_BASE;
#endif /*_I2C2 */

/************************************* IWDG ***********************************/
#ifdef _IWDG
  IWDG = (IWDG_TypeDef *) IWDG_BASE;
#endif /*_IWDG */

/************************************* NVIC ***********************************/
#ifdef _NVIC
  NVIC = (NVIC_TypeDef *)  NVIC_BASE;
#endif /*_NVIC */

#ifdef _SCB
  SCB = (SCB_TypeDef *)  SCB_BASE;
#endif /*_SCB */

/************************************* PWR ************************************/
#ifdef _PWR
  PWR = (PWR_TypeDef *)  PWR_BASE;
#endif /*_PWR */

/************************************* RCC ************************************/
#ifdef _RCC
  RCC = (RCC_TypeDef *)  RCC_BASE;
#endif /*_RCC */

/************************************* RTC ************************************/
#ifdef _RTC
  RTC = (RTC_TypeDef *)  RTC_BASE;
#endif /*_RTC */

/************************************* SPI ************************************/
#ifdef _SPI1
  SPI1 = (SPI_TypeDef *)  SPI1_BASE;
#endif /*_SPI1 */

#ifdef _SPI2
  SPI2 = (SPI_TypeDef *)  SPI2_BASE;
#endif /*_SPI2 */

/************************************* SysTick ********************************/
#ifdef _SysTick
  SysTick = (SysTick_TypeDef *)  SysTick_BASE;
#endif /*_SysTick */

/************************************* TIM1 ***********************************/
#ifdef _TIM1
  TIM1 = (TIM1_TypeDef *)  TIM1_BASE;
#endif /*_TIM1 */

/************************************* TIM ************************************/
#ifdef _TIM2
  TIM2 = (TIM_TypeDef *)  TIM2_BASE;
#endif /*_TIM2 */

#ifdef _TIM3
  TIM3 = (TIM_TypeDef *)  TIM3_BASE;
#endif /*_TIM3 */

#ifdef _TIM4
  TIM4 = (TIM_TypeDef *)  TIM4_BASE;
#endif /*_TIM4 */

/************************************* USART **********************************/
#ifdef _USART1
  USART1 = (USART_TypeDef *) USART1_BASE;
#endif /*_USART1 */

#ifdef _USART2
  USART2 = (USART_TypeDef *) USART2_BASE;
#endif /*_USART2 */

#ifdef _USART3
  USART3 = (USART_TypeDef *) USART3_BASE;
#endif /*_USART3 */

/************************************* WWDG ***********************************/
#ifdef _WWDG
  WWDG = (WWDG_TypeDef *)  WWDG_BASE;
#endif /*_WWDG */
}
#endif

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
