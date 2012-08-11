/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_it.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file contains the headers of the interrupt
*                      handlers'routines
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
* CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
* A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
* OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
* OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
* CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion ------------------------------------ */
#ifndef _91x_IT_H
#define _91x_IT_H

/* Includes ------------------------------------------------------------------*/
#include "91x_lib.h"

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* Module private variables --------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void Undefined_Handler  (void);
void SWI_Handler        (void);
void Prefetch_Handler   (void);
void Abort_Handler      (void);
void FIQ_Handler      (void);
void WDG_IRQHandler      (void);
void SW_IRQHandler       (void);
void ARMRX_IRQHandler    (void);
void ARMTX_IRQHandler    (void);
void TIM0_IRQHandler     (void);
void TIM1_IRQHandler     (void);
void TIM2_IRQHandler     (void);
void TIM3_IRQHandler     (void);
void USBHP_IRQHandler    (void);
void USBLP_IRQHandler    (void);
void SCU_IRQHandler      (void);
void ENET_IRQHandler    (void);
void DMA_IRQHandler      (void);
void CAN_IRQHandler      (void);
void MC_IRQHandler       (void);
void ADC_IRQHandler      (void);
void UART0_IRQHandler    (void);
void UART1_IRQHandler    (void);
void UART2_IRQHandler    (void);
void I2C0_IRQHandler     (void);
void I2C1_IRQHandler     (void);
void SSP0_IRQHandler     (void);
void SSP1_IRQHandler     (void);
void LVD_IRQHandler      (void);
void RTC_IRQHandler      (void);
void WIU_IRQHandler      (void);
void EXTIT0_IRQHandler   (void);
void EXTIT1_IRQHandler   (void);
void EXTIT2_IRQHandler   (void);
void EXTIT3_IRQHandler   (void);
void USBWU_IRQHandler    (void);
void PFQBC_IRQHandler    (void);

#endif /* _91x_IT_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
