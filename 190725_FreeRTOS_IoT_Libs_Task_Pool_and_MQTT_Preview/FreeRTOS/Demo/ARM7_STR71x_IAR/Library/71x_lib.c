/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : 71x_lib.c
* Author             : MCD Application Team
* Date First Issued  : 05/16/2003
* Description        : Peripherals pointers initialization
********************************************************************************
* History:
*  30/11/2004 : V2.0
*  14/07/2004 : V1.3
*  01/01/2004 : V1.2
*******************************************************************************
 THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
 CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
 AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
 OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
 OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
 CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#define EXT

#include "71x_map.h"

#ifdef DEBUG

extern u32 T0TIMI_Addr;

/*******************************************************************************
* Function Name  : debug
* Description    : Initialize the pointers to peripherals
* Input          : none
* Output         : none
* Return         : none
*******************************************************************************/
void debug(void)
{
  #ifdef _ADC12
  ADC12 = (ADC12_TypeDef *)ADC12_BASE;
  #endif

  #ifdef _APB
  #ifdef _APB1
  APB1 = (APB_TypeDef *)APB1_BASE;
  #endif
  #ifdef _APB2
  APB2 = (APB_TypeDef *)APB2_BASE;
  #endif
  #endif

  #ifdef _BSPI
  #ifdef _BSPI0
  BSPI0 = (BSPI_TypeDef *)BSPI0_BASE;
  #endif
  #ifdef _BSPI1
  BSPI1 = (BSPI_TypeDef *)BSPI1_BASE;
  #endif
  #endif

  #ifdef _CAN
  CAN = (CAN_TypeDef *)CAN_BASE;
  #endif

  #ifdef _EIC
  EIC = (EIC_TypeDef *)EIC_BASE;
  #endif

  #ifdef _EMI
  EMI = (EMI_TypeDef *)EMI_BASE;
  #endif

  #ifdef _FLASH
  FLASHR = (FLASHR_TypeDef *)FLASHR_BASE;
  FLASHPR = (FLASHPR_TypeDef *)FLASHPR_BASE;
  #endif

  #ifdef _GPIO
  #ifdef _GPIO0
  GPIO0 = (GPIO_TypeDef *)GPIO0_BASE;
  #endif
  #ifdef _GPIO1
  GPIO1 = (GPIO_TypeDef *)GPIO1_BASE;
  #endif
  #ifdef _GPIO2
  GPIO2 = (GPIO_TypeDef *)GPIO2_BASE;
  #endif
  #endif

  #ifdef _I2C
  #ifdef _I2C0
  I2C0 = (I2C_TypeDef *)I2C0_BASE;
  #endif
  #ifdef _I2C1
  I2C1 = (I2C_TypeDef *)I2C1_BASE;
  #endif
  #endif

  #ifdef _PCU
  PCU = (PCU_TypeDef *)PCU_BASE;
  #endif

  #ifdef _RCCU
  RCCU = (RCCU_TypeDef *)RCCU_BASE;
  #endif

  #ifdef _RTC
  RTC = (RTC_TypeDef *)RTC_BASE;
  #endif

  #ifdef _TIM
  #ifdef _TIM0
  TIM0 = (TIM_TypeDef *)TIM0_BASE;
  #endif
  #ifdef _TIM1
  TIM1 = (TIM_TypeDef *)TIM1_BASE;
  #endif
  #ifdef _TIM2
  TIM2 = (TIM_TypeDef *)TIM2_BASE;
  #endif
  #ifdef _TIM3
  TIM3 = (TIM_TypeDef *)TIM3_BASE;
  #endif
  #endif

  #ifdef _UART
  #ifdef _UART0
  UART0 = (UART_TypeDef *)UART0_BASE;
  #endif
  #ifdef _UART1
  UART1 = (UART_TypeDef *)UART1_BASE;
  #endif
  #ifdef _UART2
  UART2 = (UART_TypeDef *)UART2_BASE;
  #endif
  #ifdef _UART3
  UART3 = (UART_TypeDef *)UART3_BASE;
  #endif
  #endif

  #ifdef _USB
  USB = (USB_TypeDef *)USB_BASE;
  #endif

  #ifdef _WDG
  WDG = (WDG_TypeDef *)WDG_BASE;
  #endif

  #ifdef _XTI
  XTI = (XTI_TypeDef *)XTI_BASE;
  #endif

  #ifdef _IRQVectors
  IRQVectors = (IRQVectors_TypeDef *)&T0TIMI_Addr;
  #endif
}

#endif  /* DEBUG */

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
