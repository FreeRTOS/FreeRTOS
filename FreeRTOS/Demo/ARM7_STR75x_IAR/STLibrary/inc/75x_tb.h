/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_tb.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the 
*                      TB software library.
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
#ifndef __75x_TB_H
#define __75x_TB_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
typedef struct
{
  u16 TB_Mode;         /* TB mode */
  u16 TB_ClockSource;  /* TB clock source: CK_TIM or CK_RTC */
  u16 TB_CounterMode;  /* TB counter mode */
  u16 TB_ICAPolarity;  /* TB Input Capture signal Polarity */
  u16 TB_Prescaler;    /* TB Prescaler factor */
  u16 TB_AutoReload;   /* TB AutoReload factor */
} TB_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* TB modes */
#define TB_Mode_IC      0x0002
#define TB_Mode_Timing  0x0001

/* TB clock source */
#define TB_ClockSource_CKTIM 0x0001
#define TB_ClockSource_CKRTC 0x0002

/* TB Input capture polarity */
#define TB_ICAPolarity_Rising   0x7000
#define TB_ICAPolarity_Falling  0x8000

/* TB counter modes */
#define TB_CounterMode_Up             0x0000
#define TB_CounterMode_Down           0x0010
#define TB_CounterMode_CenterAligned  0x0060

/* TB interrupt sources */
#define TB_IT_Update        0x0001
#define TB_IT_IC            0x0004
#define TB_IT_GlobalUpdate  0x8001

/* TB Flags */
#define TB_FLAG_IC      0x0004
#define TB_FLAG_Update  0x0001

/* TB Slave Mode Selection */
#define TB_SMSMode_Trigger  0x0018
#define TB_SMSMode_Gated    0x0010
#define TB_SMSMode_External 0x0008  
#define TB_SMSMode_Reset    0x0000

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void TB_DeInit(void);
void TB_Init(TB_InitTypeDef* TB_InitStruct);
void TB_StructInit(TB_InitTypeDef *TB_InitStruct);
void TB_Cmd(FunctionalState Newstate );
void TB_ITConfig(u16 TB_IT, FunctionalState Newstate);
void TB_SetPrescaler(u16 Prescaler);
void TB_ResetCounter(void);
void TB_DebugCmd(FunctionalState Newstate);
void TB_CounterModeConfig(u16 TB_CounterMode);
void TB_SLaveModeConfig(u16 TB_SMSMode);
u16 TB_GetCounter(void);
u16 TB_GetICAP1(void);
void TB_SetCounter(u16 Counter);
FlagStatus TB_GetFlagStatus(u16 TB_FLAG);
void TB_ClearFlag(u16 TB_FLAG);
ITStatus TB_GetITStatus(u16 TB_IT);
void TB_ClearITPendingBit(u16 TB_IT);

#endif /* __75x_TB_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
