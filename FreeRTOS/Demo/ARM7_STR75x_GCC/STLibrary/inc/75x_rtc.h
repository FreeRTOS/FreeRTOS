/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_rtc.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      RTC software library.
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
#ifndef __75x_RTC_H
#define __75x_RTC_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* RTC interrupts define */
#define RTC_IT_Overflow    0x0004  /* Overflow interrupt */
#define RTC_IT_Alarm       0x0002  /* Alarm interrupt */
#define RTC_IT_Second      0x0001  /* Second interrupt */

/* RTC interrupts flags */
#define RTC_FLAG_RTOFF       0x0020  /* RTC Operation OFF flag */
#define RTC_FLAG_RSF         0x0008  /* Registers Synchronized flag */
#define RTC_FLAG_Overflow    0x0004  /* Overflow interrupt flag */
#define RTC_FLAG_Alarm       0x0002  /* Alarm interrupt flag */
#define RTC_FLAG_Second      0x0001  /* Second interrupt flag */

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void RTC_DeInit(void);
void RTC_ITConfig(u16 RTC_IT, FunctionalState NewState);
void RTC_EnterConfigMode(void);
void RTC_ExitConfigMode(void);
u32  RTC_GetCounter(void);
void RTC_SetCounter(u32 CounterValue);
void RTC_SetPrescaler(u32 PrescalerValue);
u32  RTC_GetPrescaler(void);
void RTC_SetAlarm(u32 AlarmValue);
u32  RTC_GetDivider(void);
void RTC_WaitForLastTask(void);
void RTC_WaitForSynchro(void);
FlagStatus RTC_GetFlagStatus(u16 RTC_FLAG);
void RTC_ClearFlag(u16 RTC_FLAG);
ITStatus RTC_GetITStatus(u16 RTC_IT);
void RTC_ClearITPendingBit(u16 RTC_IT);

#endif /* __75x_RTC_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
