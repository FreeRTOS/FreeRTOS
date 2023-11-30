/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_lib.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all peripherals pointers initialization.
********************************************************************************
* History:
* 07/17/2006 : V1.0
* 03/10/2006 : V0.1
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
#include "75x_lib.h"

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
/************************************* SMI ************************************/
#ifdef _SMI
  SMI = (SMI_TypeDef *)  SMIR_BASE;
#endif /*_SMI */

/************************************* CFG ************************************/
#ifdef _CFG
  CFG = (CFG_TypeDef *)  CFG_BASE;
#endif /*_CFG */

/************************************* MRCC ***********************************/
#ifdef _MRCC
  MRCC = (MRCC_TypeDef *)  MRCC_BASE;
#endif /*_MRCC */

/************************************* ADC ************************************/	
#ifdef _ADC
  ADC = (ADC_TypeDef *)  ADC_BASE;
#endif /*_ADC */

/************************************* TB *************************************/
#ifdef _TB
  TB = (TB_TypeDef *)  TB_BASE;
#endif /*_TB */

/************************************* TIM ************************************/
#ifdef _TIM0
  TIM0 = (TIM_TypeDef *)  TIM0_BASE;
#endif /*_TIM0 */

#ifdef _TIM1
  TIM1 = (TIM_TypeDef *)  TIM1_BASE;
#endif /*_TIM1 */

#ifdef _TIM2
  TIM2 = (TIM_TypeDef *)  TIM2_BASE;
#endif /*_TIM2 */

/************************************* PWM ************************************/
#ifdef _PWM
  PWM = (PWM_TypeDef *)  PWM_BASE;
#endif /*_PWM */

/************************************* WDG ************************************/
#ifdef _WDG
  WDG = (WDG_TypeDef *)  WDG_BASE;
#endif /*_WDG */

/************************************* SSP ************************************/
#ifdef _SSP0
  SSP0 = (SSP_TypeDef *)  SSP0_BASE;
#endif /*_SSP0 */

#ifdef _SSP1
  SSP1 = (SSP_TypeDef *)  SSP1_BASE;
#endif /*_SSP1 */

/************************************* CAN ************************************/
#ifdef _CAN
  CAN = (CAN_TypeDef *)  CAN_BASE;
#endif /*_CAN */

/************************************* I2C ************************************/
#ifdef _I2C
  I2C = (I2C_TypeDef *)  I2C_BASE;
#endif /*_I2C */

/************************************* UART ***********************************/
#ifdef _UART0
  UART0 = (UART_TypeDef *) UART0_BASE;
#endif /*_UART0 */

#ifdef _UART1
  UART1 = (UART_TypeDef *) UART1_BASE;
#endif /*_UART1 */

#ifdef _UART2
  UART2 = (UART_TypeDef *) UART2_BASE;
#endif /*_UART2 */

/************************************* GPIO ***********************************/
#ifdef _GPIO0
  GPIO0 = (GPIO_TypeDef *) GPIO0_BASE;
#endif /*_GPIO0 */

#ifdef _GPIO1
  GPIO1 = (GPIO_TypeDef *) GPIO1_BASE;
#endif /*_GPIO1 */

#ifdef _GPIO2
  GPIO2 = (GPIO_TypeDef *) GPIO2_BASE;
#endif /*_GPIO2 */

#ifdef _GPIOREMAP
  GPIOREMAP = (GPIOREMAP_TypeDef *) GPIOREMAP_BASE;
#endif /*_GPIOREMAP */

/************************************* DMA ************************************/
#ifdef _DMA
  DMA = (DMA_TypeDef *)  DMA_BASE;
#endif /*_DMA */

#ifdef _DMA_Stream0
  DMA_Stream0 = (DMA_Stream_TypeDef *)  DMA_Stream0_BASE;
#endif /*_DMA_Stream0 */

#ifdef _DMA_Stream1  
  DMA_Stream1 = (DMA_Stream_TypeDef *)  DMA_Stream1_BASE;
#endif /*_DMA_Stream1 */  
  
#ifdef _DMA_Stream2
  DMA_Stream2 = (DMA_Stream_TypeDef *)  DMA_Stream2_BASE;
#endif /*_DMA_Stream2 */  

#ifdef _DMA_Stream3
  DMA_Stream3 = (DMA_Stream_TypeDef *)  DMA_Stream3_BASE;
#endif /*_DMA_Stream3 */

/************************************* RTC ************************************/
#ifdef _RTC
  RTC = (RTC_TypeDef *)  RTC_BASE;
#endif /*_RTC */

/************************************* EXTIT **********************************/
#ifdef _EXTIT
  EXTIT = (EXTIT_TypeDef *)  EXTIT_BASE;
#endif /*_EXTIT */

/************************************* EIC ************************************/
#ifdef _EIC
  EIC = (EIC_TypeDef *)  EIC_BASE;
#endif /*_EIC */

}

#endif

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
