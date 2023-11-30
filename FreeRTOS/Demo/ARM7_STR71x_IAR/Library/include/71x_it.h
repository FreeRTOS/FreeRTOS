/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : 71x_it.h
* Author             : MCD Application Team
* Date First Issued  : 05/16/2003
* Description        : Interrupt handlers
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

#ifndef _71x_IT_H
#define _71x_IT_H

#include "71x_lib.h"


void Undefined_Handler   (void);
void FIQ_Handler         (void);
void SWI_Handler         (void);
void Prefetch_Handler    (void);
void Abort_Handler       (void);
void T0TIMI_IRQHandler   (void);
void FLASH_IRQHandler    (void);
void RCCU_IRQHandler     (void);
void RTC_IRQHandler      (void);
void WDG_IRQHandler      (void);
void XTI_IRQHandler      (void);
void USBHP_IRQHandler    (void);
void I2C0ITERR_IRQHandler(void);
void I2C1ITERR_IRQHandler(void);
void UART0_IRQHandler    (void);
void UART1_IRQHandler    (void);
void UART2_IRQHandler    (void);
void UART3_IRQHandler    (void);
void BSPI0_IRQHandler    (void);
void BSPI1_IRQHandler    (void);
void I2C0_IRQHandler     (void);
void I2C1_IRQHandler     (void);
void CAN_IRQHandler      (void);
void ADC12_IRQHandler    (void);
void T1TIMI_IRQHandler   (void);
void T2TIMI_IRQHandler   (void);
void T3TIMI_IRQHandler   (void);
void HDLC_IRQHandler     (void);
void USBLP_IRQHandler    (void);
void T0TOI_IRQHandler    (void);
void T0OC1_IRQHandler    (void);
void T0OC2_IRQHandler    (void);

#endif /* _71x_IT_H */

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
