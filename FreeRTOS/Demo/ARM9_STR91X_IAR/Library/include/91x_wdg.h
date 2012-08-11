/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_wdg.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file contains all the functions prototypes for the
*                      WDG software library.
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __91x_WDG_H
#define __91x_WDG_H

/* Includes ------------------------------------------------------------------*/
#include "91x_map.h"

/* Exported types ------------------------------------------------------------*/
typedef struct
{
u16 WDG_Mode;
u16 WDG_ClockSource;
u16 WDG_Prescaler;
u16 WDG_Preload;

} WDG_InitTypeDef;

/* Exported constants --------------------------------------------------------*/

/* WDG_Mode */
#define WDG_Mode_Wdg	0x0001	/*WDG configured to run in watchdog mode.*/
#define WDG_Mode_Timer	0xFFFE	/*WDG configured to be in Free-running Timer mode.*/


/* WDG_ClockSource */
#define WDG_ClockSource_Rtc 	0x0004	/* External clock ( 32 khz RTC clock ) will be used as counting clock.*/
#define WDG_ClockSource_Apb	0xFFFB	/*The APB clock signal will be used as counting clock.*/

/* WDG_Prescaler */
/*This member must be  a number between 0x00 and 0xFF.
Specifies the  Prescaler value to divide the clock source.
The clock of the Watchdog Timer Counter is divided by " WDG_Prescaler + 1".*/



/* WDG_Preload */
/*This member must be  a number between 0x0000 and 0xFFFF.
This value is loaded in the WDG Counter when it starts counting.*/


/* WDG Sequence */
#define WDG_KeyValue1      0xA55A
#define WDG_KeyValue2      0x5AA5

/* Exported macro ------------------------------------------------------------*/


/* Exported functions ------------------------------------------------------- */

void WDG_DeInit(void);
void WDG_Init(WDG_InitTypeDef* WDG_InitStruct);
void WDG_StructInit(WDG_InitTypeDef* WDG_InitStruct);
void WDG_Cmd(FunctionalState NewState);
void WDG_ITConfig(FunctionalState NewState);
u16 WDG_GetCounter(void);
FlagStatus WDG_GetFlagStatus(void);
void WDG_ClearFlag(void);
ITStatus WDG_GetITStatus(void);
void WDG_ClearITPendingBit(void);

#endif /* __WDG_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
