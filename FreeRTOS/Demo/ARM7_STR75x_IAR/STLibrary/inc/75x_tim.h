/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_tim.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the 
*                      TIM software library.
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
#ifndef __75x_TIM_H
#define __75x_TIM_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
typedef struct
{
  u16 TIM_Mode;              /* Timer Mode */
  u16 TIM_Prescaler;         /* Prescaler value */
  u16 TIM_ClockSource;       /* Timer clock source */
  u16 TIM_ExtCLKEdge;        /* External clock edge */
  u16 TIM_CounterMode;       /* Counter mode: Up/Down, Edge aligned or center aligned */
  u16 TIM_Period;            /* Period value */
  u16 TIM_Channel;           /* Timer Channel: 1, 2 or All */
  u16 TIM_Pulse1;            /* PWM or OCM Channel 1 pulse length */
  u16 TIM_Pulse2;            /* PWM or OCM Channel 2 pulse length */
  u16 TIM_RepetitivePulse;   /* OPM Repetitive pulse state: enable or disable */
  u16 TIM_Polarity1;         /* PWM, OCM or OPM Channel 1 polarity */
  u16 TIM_Polarity2;         /* PWM or OCM  Channel 2 polarity */
  u16 TIM_IC1Selection;      /* Input Capture 1 selection: TI1 or TI2 */
  u16 TIM_IC2Selection;      /* Input Capture 2 selection: TI1 or TI2 */
  u16 TIM_IC1Polarity;       /* Input Capture 1 polarity */
  u16 TIM_IC2Polarity;       /* Input Capture 2 polarity */
  u16 TIM_PWMI_ICSelection;  /* PWM Input Capture selection: TI1 or TI2 */
  u16 TIM_PWMI_ICPolarity;   /* PWM Input Capture Polarity */
} TIM_InitTypeDef;

/* Master and slave synchronized Timer peripherals */
typedef enum
{
  PWM_Master  = 0x01,
  TIM0_Master,
  TIM1_Master,
  TIM2_Master
}Master_TypeDef;

typedef enum
{
  PWM_Slave  = 0x05,
  TIM0_Slave,
  TIM1_Slave,
  TIM2_Slave
}Slave_TypeDef;

/* Exported constants --------------------------------------------------------*/
/* TIM modes */
#define TIM_Mode_OCTiming    0x0001
#define TIM_Mode_OCActive    0x0002
#define TIM_Mode_OCInactive  0x0003
#define TIM_Mode_OCToggle    0x0004
#define TIM_Mode_PWM         0x0005
#define TIM_Mode_PWMI        0x0006
#define TIM_Mode_IC          0x0007
#define TIM_Mode_Encoder1    0x0008
#define TIM_Mode_Encoder2    0x0009
#define TIM_Mode_Encoder3    0x000A
#define TIM_Mode_OPM_PWM     0x000B
#define TIM_Mode_OPM_Toggle  0x000C
#define TIM_Mode_OPM_Active  0x000D

/* TIM Clock Source */
#define TIM_ClockSource_Internal  0x0001
#define TIM_ClockSource_TI11      0x0002
#define TIM_ClockSource_TI12      0x0003
#define TIM_ClockSource_TI22      0x0004
#define TIM_ClockSource_TI21      0x0005

/* TIM External Clock Edge */
#define TIM_ExtCLKEdge_Falling  0x0001
#define TIM_ExtCLKEdge_Rising   0x0002

/* TIM Counter Mode */
#define TIM_CounterMode_Up              0x0000
#define TIM_CounterMode_Down            0x0010
#define TIM_CounterMode_CenterAligned1  0x0020
#define TIM_CounterMode_CenterAligned2  0x0040
#define TIM_CounterMode_CenterAligned3  0x0060

/* TIM Channel */
#define TIM_Channel_1    0x0001
#define TIM_Channel_2    0x0002
#define TIM_Channel_ALL  0x0003

/* TIM Polarity channel 1 */
#define TIM_Polarity1_High  0x0001
#define TIM_Polarity1_Low   0x0002

/* TIM Polarity channel 2 */
#define TIM_Polarity2_High  0x0001
#define TIM_Polarity2_Low   0x0002

#define TIM_RepetitivePulse_Disable  0x0005
#define TIM_RepetitivePulse_Enable   0x0006

/* TIM Input Capture channel 1 Selection */
#define TIM_IC1Selection_TI1  0x0001
#define TIM_IC1Selection_TI2  0x0002

/* TIM Input Capture channel 2 Selection */
#define TIM_IC2Selection_TI1  0x0001
#define TIM_IC2Selection_TI2  0x0002

/* TIM Input Capture channel 1 Polarity */
#define  TIM_IC1Polarity_Falling  0x0001
#define  TIM_IC1Polarity_Rising   0x0002

/* TIM Input Capture channel 2 Polarity */
#define  TIM_IC2Polarity_Falling  0x0001
#define  TIM_IC2Polarity_Rising   0x0002

/* TIM PWM Input IC Selection */
#define TIM_PWMI_ICSelection_TI1  0x0001
#define TIM_PWMI_ICSelection_TI2  0x0002

/*  TIM PWM Input IC Polarity */
#define TIM_PWMI_ICPolarity_Falling  0x0003
#define TIM_PWMI_ICPolarity_Rising   0x0004

/* TIM interrupt sources */
#define TIM_IT_IC1           0x0004
#define TIM_IT_IC2           0x0008
#define TIM_IT_OC1           0x0100
#define TIM_IT_OC2           0x0200
#define TIM_IT_Update        0x0001
#define TIM_IT_GlobalUpdate  0x1001

/* TIM DMA sources */
#define TIM_DMASource_IC1     0x0004
#define TIM_DMASource_IC2     0x0008
#define TIM_DMASource_OC1     0x0100
#define TIM_DMASource_OC2     0x0200
#define TIM_DMASource_Update  0x0001

/* TIM DMA Base address */
#define TIM_DMABase_CR    0x0000
#define TIM_DMABase_SCR   0x0800
#define TIM_DMABase_IMCR  0x1000
#define TIM_DMABase_OMR1  0x1800
#define TIM_DMABase_RSR   0x3000
#define TIM_DMABase_RER   0x3800
#define TIM_DMABase_ISR   0x4000
#define TIM_DMABase_CNT   0x4800
#define TIM_DMABase_PSC   0x5000
#define TIM_DMABase_ARR   0x6000
#define TIM_DMABase_OCR1  0x6800
#define TIM_DMABase_OCR2  0x7000
#define TIM_DMABase_ICR1  0x9800
#define TIM_DMABase_ICR2  0xA000

/* TIM Flags */
#define TIM_FLAG_IC1     0x0004
#define TIM_FLAG_IC2     0x0008
#define TIM_FLAG_OC1     0x0100
#define TIM_FLAG_OC2     0x0200
#define TIM_FLAG_Update  0x0001

/*  TIM_ForcedAction */
#define TIM_ForcedAction_Active    0x000A
#define TIM_ForcedAction_InActive  0x0008

/* TIM synchronization action */
#define TIM_SynchroAction_Enable  0x0100
#define TIM_SynchroAction_Update  0x0200
#define TIM_SynchroAction_Reset   0x0000
#define TIM_SynchroAction_OC      0x0300

/* TIM synchronization mode */
#define TIM_SynchroMode_Gated    0x0010
#define TIM_SynchroMode_Trigger  0x0018
#define TIM_SynchroMode_External 0x0008
#define TIM_SynchroMode_Reset    0x0000

/* OCRM bit states */
#define TIM_OCRMState_Enable   0x0005
#define TIM_OCRMState_Disable  0x0006

/* Exported macro ------------------------------------------------------------*/
/* Exported functions --------------------------------------------------------*/
void TIM_DeInit(TIM_TypeDef *TIMx);
void TIM_Init(TIM_TypeDef* TIMx, TIM_InitTypeDef* TIM_InitStruct);
void TIM_StructInit(TIM_InitTypeDef *TIM_InitStruct);
void TIM_Cmd(TIM_TypeDef *TIMx, FunctionalState Newstate);
void TIM_ITConfig(TIM_TypeDef *TIMx, u16 TIM_IT, FunctionalState Newstate);
void TIM_PreloadConfig(TIM_TypeDef* TIMx, u16 TIM_Channel, FunctionalState Newstate);
void TIM_DMAConfig(u16 TIM_DMASources, u16 TIM_OCRMState, u16 TIM_DMABase);
void TIM_DMACmd(u16 TIM_DMASources, FunctionalState Newstate);
void TIM_ClockSourceConfig(TIM_TypeDef *TIMx, u16 TIM_ClockSource,
                           u16 TIM_ExtCLKEdge);
void TIM_SetPrescaler(TIM_TypeDef* TIMx, u16 Prescaler);
void TIM_SetPeriod(TIM_TypeDef* TIMx, u16 Period);
void TIM_SetPulse(TIM_TypeDef* TIMx, u16 TIM_Channel, u16 Pulse);
u16 TIM_GetICAP1(TIM_TypeDef *TIMx);
u16 TIM_GetICAP2(TIM_TypeDef *TIMx);
u16 TIM_GetPWMIPulse(TIM_TypeDef *TIMx);
u16 TIM_GetPWMIPeriod(TIM_TypeDef *TIMx);
void TIM_DebugCmd(TIM_TypeDef *TIMx, FunctionalState Newstate);
void TIM_CounterModeConfig(TIM_TypeDef* TIMx, u16 TIM_CounterMode);
void TIM_ForcedOCConfig(TIM_TypeDef* TIMx, u16 TIM_Channel,
                        u16 TIM_ForcedAction);
void TIM_ResetCounter(TIM_TypeDef* TIMx);
void TIM_SynchroConfig(Master_TypeDef Master, Slave_TypeDef Slave,
                       u16 TIM_SynchroAction, u16 TIM_SynchroMode);
FlagStatus TIM_GetFlagStatus(TIM_TypeDef* TIMx, u16 TIM_FLAG);
void TIM_ClearFlag(TIM_TypeDef* TIMx, u16 TIM_FLAG);
ITStatus TIM_GetITStatus(TIM_TypeDef* TIMx, u16 TIM_IT);
void TIM_ClearITPendingBit(TIM_TypeDef* TIMx, u16 TIM_IT);

#endif /* __75x_TIM_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
