/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_eic.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      EIC software library.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __75x_EIC_H
#define __75x_EIC_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
typedef struct
{
  u8 EIC_IRQChannel;
  u8 EIC_IRQChannelPriority;
  FunctionalState EIC_IRQChannelCmd;
}EIC_IRQInitTypeDef;

typedef struct
{
  u8 EIC_FIQChannel;
  FunctionalState EIC_FIQChannelCmd;
}EIC_FIQInitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* IRQ channels */
#define WAKUP_IRQChannel        0
#define TIM2_OC2_IRQChannel     1
#define TIM2_OC1_IRQChannel     2
#define TIM2_IC12_IRQChannel    3
#define TIM2_UP_IRQChannel      4
#define TIM1_OC2_IRQChannel     5
#define TIM1_OC1_IRQChannel     6
#define TIM1_IC12_IRQChannel    7
#define TIM1_UP_IRQChannel      8
#define TIM0_OC2_IRQChannel     9
#define TIM0_OC1_IRQChannel     10
#define TIM0_IC12_IRQChannel    11
#define TIM0_UP_IRQChannel      12
#define PWM_OC123_IRQChannel    13
#define PWM_EM_IRQChannel       14
#define PWM_UP_IRQChannel       15
#define I2C_IRQChannel          16
#define SSP1_IRQChannel         17
#define SSP0_IRQChannel         18
#define UART2_IRQChannel        19
#define UART1_IRQChannel        20
#define UART0_IRQChannel        21
#define CAN_IRQChannel          22
#define USB_LP_IRQChannel       23
#define USB_HP_IRQChannel       24
#define ADC_IRQChannel          25
#define DMA_IRQChannel          26
#define EXTIT_IRQChannel        27
#define MRCC_IRQChannel         28
#define FLASHSMI_IRQChannel     29
#define RTC_IRQChannel          30
#define TB_IRQChannel           31

/* FIQ channels */
#define EXTIT_Line0_FIQChannel    0x00000001
#define WATCHDOG_FIQChannel       0x00000002

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void EIC_DeInit(void);
void EIC_IRQInit(EIC_IRQInitTypeDef* EIC_IRQInitStruct);
void EIC_FIQInit(EIC_FIQInitTypeDef* EIC_FIQInitStruct);
void EIC_IRQStructInit(EIC_IRQInitTypeDef* EIC_IRQInitStruct);
void EIC_FIQStructInit(EIC_FIQInitTypeDef* EIC_FIQInitStruct);
void EIC_IRQCmd(FunctionalState NewState);
void EIC_FIQCmd(FunctionalState NewState);
u8 EIC_GetCurrentIRQChannel(void);
u8 EIC_GetCurrentIRQChannelPriority(void);
void EIC_CurrentIRQPriorityConfig(u8 NewPriority);
u8 EIC_GetCurrentFIQChannel(void);
void EIC_ClearFIQPendingBit(u8 EIC_FIQChannel);

#endif /* __75x_EIC_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
