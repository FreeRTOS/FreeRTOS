/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_wdg.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      WDG software library.
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
#ifndef __75x_WDG_H
#define __75x_WDG_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
 typedef struct
{
  u16 WDG_Mode;       /* Watchdog or Timer mode */
  u16 WDG_Preload;    /* Preload register */
  u8 WDG_Prescaler;   /* Prescaler register */
}WDG_InitTypeDef;
/* Exported constants --------------------------------------------------------*/

/* WDG/Timer Select */
#define WDG_Mode_WDG       0x0001
#define WDG_Mode_Timer     0xFFFE

/* WDG End of Count interrupt request */
#define WDG_IT_EC          0x0001

/* WDG end of count Flag */
#define WDG_FLAG_EC        0x0001

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
