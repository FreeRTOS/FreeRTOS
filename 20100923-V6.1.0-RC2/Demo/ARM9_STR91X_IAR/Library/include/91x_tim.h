/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_tim.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file contains all the functions prototypes for the
*                      TIM software library.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __91x_TIM_H
#define __91x_TIM_H

/* Includes ------------------------------------------------------------------*/
#include "91x_map.h"
#include "91x_scu.h"

/* Exported types ----------------------------------------------------------- */

/* TIM Init structure define */
typedef struct
{             
  u16 TIM_Mode;            /* Timer mode                                    */
  u16 TIM_OC1_Modes;       /* Output Compare 1 Mode: Timing or Wave         */
  u16 TIM_OC2_Modes;       /* Output Compare 2 Mode: Timing or Wave         */
  u16 TIM_Clock_Source;    /* Timer Clock source APB/SCU/EXTERNAL           */
  u16 TIM_Clock_Edge;      /* Timer Clock Edge: Rising or Falling Edge      */
  u16 TIM_OPM_INPUT_Edge;  /* Timer Input Capture 1 Edge used in OPM Mode   */
  u16 TIM_ICAP1_Edge;      /* Timer Input Capture 1 Edge used in ICAP1 Mode */
  u16 TIM_ICAP2_Edge;      /* Timer Input Capture 2 Edge used in ICAP2 Mode */
  u8  TIM_Prescaler;       /* Timer Prescaler factor                        */
  u16 TIM_Pulse_Level_1;   /* Level applied on the Output Compare Pin 1     */
  u16 TIM_Pulse_Level_2;   /* Level applied on the Output Compare Pin 2     */
  u16 TIM_Period_Level;    /* Level applied during the Period of a PWM Mode */
  u16 TIM_Pulse_Length_1;  /* Pulse 1 Length used in Output Compare 1 Mode  */
  u16 TIM_Pulse_Length_2;  /* Pulse 2 Length used in Output Compare 2 Mode  */
  u16 TIM_Full_Period;     /* Period Length used in PWM Mode                */
} TIM_InitTypeDef;

typedef enum 
{
  TIM_START,
  TIM_STOP,
  TIM_CLEAR
} TIM_CounterOperations;

/* Exported constants --------------------------------------------------------*/

/* TIM MODE */
#define TIM_PWMI      	     0x4000   /* PWM INPUT Mode                     */
#define TIM_OCM_CHANNEL_1    0x0040   /* OUTPUT COMPARE CHANNEL 1 Mode      */
#define TIM_OCM_CHANNEL_2    0x0080   /* OUTPUT COMPARE CHANNEL 2 Mode      */
#define TIM_OCM_CHANNEL_12   0x00C0   /* OUTPUT COMPARE CHANNEL 1 & 2  Mode */
#define TIM_PWM              0x0010   /* PWM Mode                           */
#define TIM_OPM              0x0020   /* ONE PULSE Mode                     */
#define TIM_ICAP_CHANNEL_1   0x0400   /* INPUT CAPTURE 1 Mode               */
#define TIM_ICAP_CHANNEL_2   0x0500   /* INPUT CAPTURE 2 Mode               */
#define TIM_ICAP_CHANNEL_12  0x0600   /* INPUT CAPTURE 1 & 2 Mode           */

/* TIM OUTPUT COMPARE MODE */
#define TIM_WAVE       0x0001
#define TIM_TIMING     0x0002

/* TIM CLOCK SOURCE */
#define TIM_CLK_APB          0xFFFE
#define TIM_CLK_EXTERNAL     0x0001
#define TIM_CLK_SCU          0x0001

/* TIM CLOCK EDGE */
#define TIM_CLK_EDGE_FALLING  0xFFFD
#define TIM_CLK_EDGE_RISING   0x0002

/* TIM OPM INPUT EDGE */
#define TIM_OPM_EDGE_FALLING  0xFFFB
#define TIM_OPM_EDGE_RISING   0x0004

/* TIM ICAPA INPUT EDGE */
#define TIM_ICAP1_EDGE_FALLING  0xFFFB
#define TIM_ICAP1_EDGE_RISING   0x0004

/* TIM ICAPB INPUT EDGE */
#define TIM_ICAP2_EDGE_FALLING  0xFFF7
#define TIM_ICAP2_EDGE_RISING   0x0008

/* TIM OUTPUT LEVEL */
#define TIM_HIGH       0x0200
#define TIM_LOW        0x0300

/* TIM OUTPUT EDGE */
#define TIM_OUTPUT_EDGE_RISING     0x8000
#define TIM_OUTPUT_EDGE_FALLING    0x0800

/* TIM channels */
#define TIM_PWM_OC1_Channel    0x1     /* PWM/Output Compare 1 Channel */
#define TIM_OC2_Channel        0x2     /* Output Compare 2 Channel     */

/* TIM DMA SOURCE */
#define TIM_DMA_IC1        0x0000 /* Input Capture Channel 1 DMA Source  */
#define TIM_DMA_OC1        0x1000 /* OUTPUT Compare Channel 1 DMA Source */
#define TIM_DMA_IC2        0x2000 /* Input Capture Channel 2 DMA Source  */
#define TIM_DMA_OC2        0x3000 /* OUTPUT Compare Channel 2 DMA Source */

/* TIM DMA ENABLE or DISABLE */
#define TIM_DMA_ENABLE      0x0400 /* DMA Enable */
#define TIM_DMA_DISABLE     0xFBFF /* DMA Disable */

/* TIM Interruption Sources*/
#define TIM_IT_IC1   0x8000 /* Input Capture Channel 1 Interrupt Source  */
#define TIM_IT_OC1   0x4000 /* Output Compare Channel 1 Interrupt Source */
#define TIM_IT_TO    0x2000 /* Timer OverFlow Interrupt Source           */
#define TIM_IT_IC2   0x1000 /* Input Capture Channel 2 Interrupt Source  */
#define TIM_IT_OC2   0x0800 /* Output Compare Channel 2 Interrupt Source */

/* TIM Flags */
#define TIM_FLAG_IC1     0x8000 /* Input Capture Channel 1 Flag  */
#define TIM_FLAG_OC1     0x4000 /* Output Compare Channel 1 Flag */
#define TIM_FLAG_TO      0x2000 /* Timer OverFlow Flag           */
#define TIM_FLAG_IC2     0x1000 /* Input Capture Channel 2 Flag  */
#define TIM_FLAG_OC2     0x0800 /* Output Compare Channel 2 Flag */ 

/* Module private variables --------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void TIM_Init(TIM_TypeDef *TIMx, TIM_InitTypeDef *TIM_InitStruct);
void TIM_DeInit(TIM_TypeDef *TIMx);
void TIM_StructInit(TIM_InitTypeDef *TIM_InitStruct);
void TIM_CounterCmd(TIM_TypeDef *TIMx, TIM_CounterOperations TIM_operation);
void TIM_PrescalerConfig(TIM_TypeDef *TIMx, u8 TIM_Prescaler);
u8 TIM_GetPrescalerValue(TIM_TypeDef *TIMx);
u16 TIM_GetCounterValue(TIM_TypeDef *TIMx);
u16 TIM_GetICAP1Value(TIM_TypeDef *TIMx);
u16 TIM_GetICAP2Value(TIM_TypeDef *TIMx);
void TIM_SetPulse(TIM_TypeDef *TIMx,u16 TIM_Channel ,u16 TIM_Pulse);
FlagStatus TIM_GetFlagStatus(TIM_TypeDef *TIMx, u16 TIM_Flag);
void TIM_ClearFlag(TIM_TypeDef *TIMx, u16 TIM_Flag);
u16 TIM_GetPWMIPulse(TIM_TypeDef *TIMx);
u16 TIM_GetPWMIPeriod(TIM_TypeDef *TIMx);
void TIM_ITConfig(TIM_TypeDef *TIMx, u16 TIM_IT, FunctionalState TIM_Newstate);
void TIM_DMAConfig(TIM_TypeDef *TIMx, u16 TIM_DMA_Sources);
void TIM_DMACmd(TIM_TypeDef *TIMx, FunctionalState TIM_Newstate);

#endif /* __91x_TIM_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
