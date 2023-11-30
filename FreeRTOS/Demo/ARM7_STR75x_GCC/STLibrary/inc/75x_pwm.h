/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_pwm.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the 
*                      PWM software library.
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
#ifndef __75x_PWM_H
#define __75x_PWM_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/

typedef struct
{
  u16 PWM_Mode;        /* PWM Mode */
  u16 PWM_Prescaler;   /* Prescaler value */
  u16 PWM_CounterMode; /* Counter mode: Up/Down, Edge aligned or center aligned */
  u16 PWM_Period;      /* Period value */
  u16 PWM_Complementary; /* Complementary PWM selection */
  u16 PWM_OCState;       /* Output compare off-state in Run mode */
  u16 PWM_OCNState;      /* Complementary Output compare off-state in Run mode */
  u16 PWM_Channel;       /* PWM Channel: 1, 2 or 3 */
  u16 PWM_Pulse1;        /* PWM or OCM Channel 1 pulse length */
  u16 PWM_Pulse2;        /* PWM or OCM Channel 2 pulse length */
  u16 PWM_Pulse3;        /* PWM or OCM Channel 3 pulse length */
  u16 PWM_Polarity1;     /* PWM, OCM or OPM Channel 1 polarity */
  u16 PWM_Polarity2;     /* PWM or OCM  Channel 2 polarity */
  u16 PWM_Polarity3;     /* PWM or OCM  Channel 3 polarity */
  u16 PWM_Polarity1N;    /* PWM or OCM  Channel 1N polarity */
  u16 PWM_Polarity2N;    /* PWM or OCM  Channel 2N polarity */
  u16 PWM_Polarity3N;    /* PWM or OCM  Channel 3N polarity */
  u16 PWM_DTRAccess;     /* Enable or disable the configuration of DTR register parameters:
                          DeadTime, Emergency, LOCKLevel, OSSIState, OCState and OCNState */
  u16 PWM_DeadTime;      /* Dead Time value */
  u16 PWM_Emergency;     /* Emergency selection: Enable / Disable */
  u16 PWM_LOCKLevel;     /* LOCK level */
  u16 PWM_OSSIState;     /* Off-State Selection for Idle state */
  u8 PWM_RepetitionCounter; /* Repetition counter value */
} PWM_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* PWM modes */
#define PWM_Mode_OCTiming    0x0001
#define PWM_Mode_OCActive    0x0002
#define PWM_Mode_OCInactive  0x0003
#define PWM_Mode_OCToggle    0x0004
#define PWM_Mode_PWM         0x0005

/* PWM Counter Mode */
#define PWM_CounterMode_Up              0x0000
#define PWM_CounterMode_Down            0x0010
#define PWM_CounterMode_CenterAligned1  0x0020
#define PWM_CounterMode_CenterAligned2  0x0040
#define PWM_CounterMode_CenterAligned3  0x0060

/* PWM Channel */
#define PWM_Channel_1    0x0001
#define PWM_Channel_2    0x0002
#define PWM_Channel_3    0x0004
#define PWM_Channel_ALL  0x0007

/* PWM Polarity channel 1 */
#define PWM_Polarity1_High  0x0001
#define PWM_Polarity1_Low   0x0002

/* PWM Polarity channel 2 */
#define PWM_Polarity2_High  0x0001
#define PWM_Polarity2_Low   0x0002

/* PWM Polarity channel 3 */
#define PWM_Polarity3_High  0x0001
#define PWM_Polarity3_Low   0x0002

/* PWM Polarity channel 1N */
#define PWM_Polarity1N_High  0x0001
#define PWM_Polarity1N_Low   0x0002

/* PWM Polarity channel 2N */
#define PWM_Polarity2N_High  0x0001
#define PWM_Polarity2N_Low   0x0002

/* PWM Polarity channel 3N */
#define PWM_Polarity3N_High  0x0001
#define PWM_Polarity3N_Low   0x0002

/* PWM interrupt sources */
#define PWM_IT_OC1           0x0100
#define PWM_IT_OC2           0x0200
#define PWM_IT_OC3           0x0400
#define PWM_IT_Update        0x0001
#define PWM_IT_GlobalUpdate  0x1001
#define PWM_IT_Emergency     0x8000

/* PWM DMA sources */
#define PWM_DMASource_OC1        0x0100
#define PWM_DMASource_OC2        0x0200
#define PWM_DMASource_OC3        0x0400
#define PWM_DMASource_Update     0x0001

/* PWM DMA Base address */
#define PWM_DMABase_CR    0x0000
#define PWM_DMABase_SCR   0x0800
#define PWM_DMABase_OMR1  0x1800
#define PWM_DMABase_OMR2  0x2000
#define PWM_DMABase_RSR   0x3000
#define PWM_DMABase_RER   0x3800
#define PWM_DMABase_ISR   0x4000
#define PWM_DMABase_CNT   0x4800
#define PWM_DMABase_PSC   0x5000
#define PWM_DMABase_RCR   0x5800
#define PWM_DMABase_ARR   0x6000
#define PWM_DMABase_OCR1  0x6800
#define PWM_DMABase_OCR2  0x7000
#define PWM_DMABase_OCR3  0x7800
#define PWM_DMABase_DTR   0xB800

/* PWM OCM state */
#define PWM_OCRMState_Enable   0x0005
#define PWM_OCRMState_Disable  0x0006

/* PWM Flags */
#define PWM_FLAG_OC1        0x0100
#define PWM_FLAG_OC2        0x0200
#define PWM_FLAG_OC3        0x0400
#define PWM_FLAG_Update     0x0001
#define PWM_FLAG_Emergency  0x8000

/*  PWM_ForcedAction */
#define PWM_ForcedAction_Active    0x000A
#define PWM_ForcedAction_InActive  0x0008

/* PWM TRGO Mode */
#define PWM_TRGOMode_Enable  0x0100
#define PWM_TRGOMode_Update  0x0200
#define PWM_TRGOMode_Reset   0x0000
#define PWM_TRGOMode_OC      0x0300

/* PWM Complementary outputs Enable/Disable */
#define PWM_Complementary_Disable  0x0001
#define PWM_Complementary_Enable   0x0002

/* PWM DTR Access Enable/Disable */
#define PWM_DTRAccess_Enable  0x0001
#define PWM_DTRAccess_Disable 0x0002

/* PWM Emergency input Enable/Disable */
#define PWM_Emergency_Disable  0x0000
#define PWM_Emergency_Enable   0x1000

/* OC states */
#define PWM_OCNState_Disable   0x0001
#define PWM_OCNState_Enable    0x0002
#define PWM_OCNState_OffState  0x0003

/* OCN states */
#define PWM_OCState_Disable   0x0004
#define PWM_OCState_Enable    0x0005
#define PWM_OCState_OffState  0x0006

/* PWM LOCK level */
#define PWM_LOCKLevel_1    0x0400
#define PWM_LOCKLevel_2    0x0800
#define PWM_LOCKLevel_3    0x0C00
#define PWM_LOCKLevel_OFF  0x0000

/* Off State selection for Idle state */
#define PWM_OSSIState_Disable  0x0000
#define PWM_OSSIState_Enable   0x2000

/* Exported macro ------------------------------------------------------------*/
/* Exported functions --------------------------------------------------------*/
void PWM_DeInit(void);
void PWM_Init(PWM_InitTypeDef* PWM_InitStruct);
void PWM_StructInit(PWM_InitTypeDef *PWM_InitStruct);
void PWM_Cmd(FunctionalState Newstate);
void PWM_CtrlPWMOutputs(FunctionalState Newstate); 
void PWM_ITConfig(u16 PWM_IT, FunctionalState Newstate);
void PWM_DMAConfig(u16 PWM_DMASources, u16 PWM_OCRMState, u16 PWM_DMABase);
void PWM_DMACmd(u16 PWM_DMASources, FunctionalState Newstate);
void PWM_SetPrescaler(u16 Prescaler);
void PWM_SetPeriod(u16 Period);
void PWM_SetPulse(u16 PWM_Channel, u16 Pulse);
void PWM_SetPulse1(u16 Pulse);
void PWM_SetPulse2(u16 Pulse);
void PWM_SetPulse3(u16 Pulse);
void PWM_DebugCmd(FunctionalState Newstate);
void PWM_CounterModeConfig(u16 PWM_CounterMode);
void PWM_ForcedOCConfig(u16 PWM_Channel, u16 PWM_ForcedAction);
void PWM_SetDeadTime(u16 DeadTime);
void PWM_ResetCounter(void);
void PWM_TRGOSelection(u16 PWM_TRGOMode);
FlagStatus PWM_GetFlagStatus(u16 PWM_FLAG);
void PWM_ClearFlag(u16 PWM_FLAG);
ITStatus PWM_GetITStatus(u16 PWM_IT);
void PWM_ClearITPendingBit(u16 PWM_IT);

#endif /* __75x_PWM_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
