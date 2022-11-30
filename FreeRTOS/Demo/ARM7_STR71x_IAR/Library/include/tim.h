/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : tim.h
* Author             : MCD Application Team
* Date First Issued  : 08/09/2003
* Description        : This file contains all the functions prototypes for the
*                      TIM software library.
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

#ifndef __TIM_H
#define __TIM_H

#include "71x_map.h"

typedef enum { TIM_EXTERNAL,
               TIM_INTERNAL
             } TIM_Clocks;

typedef enum { TIM_RISING,
               TIM_FALLING
             } TIM_Clock_Edges;

typedef enum { TIM_CHANNEL_A,
               TIM_CHANNEL_B
             } TIM_Channels;

typedef enum { TIM_WITH_IT,
               TIM_WITHOUT_IT
             } TIM_IT_Mode;

typedef enum { TIM_TIMING,
               TIM_WAVE
             } TIM_OC_Modes;

typedef enum { TIM_HIGH,
               TIM_LOW
             } TIM_Logic_Levels;

typedef enum { TIM_START,
               TIM_STOP,
               TIM_CLEAR
             } TIM_CounterOperations;

typedef enum { TIM_ICFA = 0x8000,
               TIM_OCFA = 0x4000,
               TIM_TOF  = 0x2000,
               TIM_ICFB = 0x1000,
               TIM_OCFB = 0x0800
             } TIM_Flags;

typedef struct { u16 Pulse;
                 u16 Period;
               } PWMI_parameters;

#define TIM_ECKEN_Mask  0x0001
#define TIM_EXEDG_Mask  0x0002

#define TIM_IEDGA_Mask  0x0004
#define TIM_IEDGB_Mask  0x0008

#define TIM_PWM_Mask    0x0010

#define TIM_OMP_Mask    0x0020

#define TIM_OCAE_Mask   0x0040
#define TIM_OCBE_Mask   0x0080

#define TIM_OLVLA_Mask  0x0100
#define TIM_OLVLB_Mask  0x0200

#define TIM_FOLVA_Mask  0x0400
#define TIM_FOLVB_Mask  0x0800

#define TIM_PWMI_Mask   0x4000

#define TIM_EN_Mask     0x8000

#define TIM_OCBIE_mask  0x0800
#define TIM_ICBIE_Mask  0x1000
#define TIM_TOE_Mask    0x2000
#define TIM_ICAIE_Mask  0x8000
#define TIM_OCAIE_mask  0x4000

#define TIM_ICA_IT   0x8000 // Input Capture Channel A
#define TIM_OCA_IT   0x4000 // Output Compare Channel A
#define TIM_TO_IT    0x2000 // Timer OverFlow
#define TIM_ICB_IT   0x1000 // Input Capture Channel B
#define TIM_OCB_IT   0x0800 // Input Capture Channel A


/*******************************************************************************
* Function Name  : TIM_Init
* Description    : This routine is used to Initialize the TIM peripheral
* Input          : TIM Timer to Initialize
* Return         : None
*******************************************************************************/
void TIM_Init( TIM_TypeDef *TIMx );

/*******************************************************************************
* Function Name  : TIM_ClockSourceConfig
* Description    : This routine is used to configure the TIM clock source
* Input          : (1) TIM Timer
*                : (2) TIM_Clocks : Specifies the TIM source clock
*                       - TIM_INTERNAL : The TIM is clocked by the APB2 frequency
*                                    divided by the prescaler value.
*                       - TIM_EXTERNAL : The TIM is clocked by an external Clock
* Return         : None
*******************************************************************************/
inline void TIM_ClockSourceConfig ( TIM_TypeDef *TIMx, TIM_Clocks Xclock )
{
	if (Xclock==TIM_EXTERNAL) TIMx->CR1|=TIM_ECKEN_Mask; else TIMx->CR1&=~TIM_ECKEN_Mask;
}

/*******************************************************************************
* Function Name  : TIM_ClockSourceValue
* Description    : This routine is used to get the TIM clock source
* Input          : TIM Timer
* Return         : TIM_Clocks : Specifies the TIM source clock
*                       - TIM_INTERNAL : The TIM is clocked by the APB2 frequency
*                                    divided by the prescaler value.
*                       - TIM_EXTERNAL : The TIM is clocked by an external Clock
*******************************************************************************/
inline TIM_Clocks TIM_ClockSourceValue ( TIM_TypeDef *TIMx )
{
	return ( TIMx->CR1 & TIM_ECKEN_Mask) == 0 ? TIM_INTERNAL : TIM_EXTERNAL;
}

/*******************************************************************************
* Function Name  : TIM_PrescalerConfig
* Description    : This routine is used to configure the TIM prescaler value
*                  ( using an internal clock )
* Input          : (1) TIM Timer
*                : (2) Prescaler ( u8 )
* Return         : None
*******************************************************************************/
inline void TIM_PrescalerConfig ( TIM_TypeDef *TIMx, u8 Xprescaler )
{
	TIMx->CR2 = ( TIMx->CR2 & 0xFF00 ) | Xprescaler;
}

/*******************************************************************************
* Function Name  : TIM_PrescalerValue
* Description    : This routine is used to get the TIM prescaler value
*                  ( when using using an internal clock )
* Input          : TIM Timer
* Return         : Prescaler ( u8 )
*******************************************************************************/
inline u8 TIM_PrescalerValue ( TIM_TypeDef *TIMx )
{
	return TIMx->CR2 & 0x00FF;
}

/*******************************************************************************
* Function Name  : TIM_ClockLevelConfig
* Description    : This routine is used to configure the TIM clock level
*                  ( using an external clock )
* Input          : TIM Timer
*                : TIM_Clock_Edges : Specifies the active adge of the external clock
*                  - TIM_RISING  : The rising  edge
*                  - TIM_FALLING : The falling edge
* Return         : None
*******************************************************************************/
inline void TIM_ClockLevelConfig ( TIM_TypeDef *TIMx, TIM_Clock_Edges Xedge )
{
	if (Xedge == TIM_RISING) TIMx->CR1 |= TIM_EXEDG_Mask; else TIMx->CR1 &= ~TIM_EXEDG_Mask;
}

/*******************************************************************************
* Function Name  : TIM_ClockLevelValue
* Description    : This routine is used to get the TIM clock level
* Input          : TIM Timer
* Output         : TIM_Clock_Edges : Specifies the active adge of the external clock
*                  - TIM_RISING  : The rising  edge
*                  - TIM_FALLING : The falling edge
*******************************************************************************/
inline TIM_Clock_Edges TIM_ClockLevelValue ( TIM_TypeDef *TIMx )
{
	return ( TIMx->CR1 & TIM_EXEDG_Mask ) == 0 ? TIM_FALLING : TIM_RISING;
}

/*******************************************************************************
* Function Name  : TIM_ICAPModeConfig
* Description    : This routine is used to configure the input capture feature
* Input          : (1) TIM Timer
*                : (2) Input Capture Channel ( Channel_A or Channel_B )
*                : (3) Active Edge : Rising edge or Falling edge.
* Output         : None
*******************************************************************************/
void TIM_ICAPModeConfig ( TIM_TypeDef  *TIMx,
                          TIM_Channels Xchannel,
                          TIM_Clock_Edges  Xedge );

/*******************************************************************************
* Function Name  : TIM_ICAPValue
* Description    : This routine is used to get the Input Capture value
* Input          : (1) TIM Timer
*                : (2) Input Capture Channel ( Channel_A or Channel_B )
* Output         : None
*******************************************************************************/
inline u16 TIM_ICAPValue ( TIM_TypeDef *TIMx, TIM_Channels Xchannel )
{
	return Xchannel == TIM_CHANNEL_A ? TIMx->ICAR : TIMx->ICBR;
}

/*******************************************************************************
* Function Name  : TIM_OCMPModeConfig
* Description    : This routine is used to configure the output compare feature
* Input          : (1) TIM Timer
*                : (2) OCMP Channel ( Channel_A or Channel_B )
*                : (3) Pulse Length
*                : (4) OC_Mode     : output wave, or only timing.
*                : (5) Level       : Rising edge or Falling edge after the ==
* Output         : None
*******************************************************************************/
void TIM_OCMPModeConfig (  TIM_TypeDef  *TIMx,
                           TIM_Channels Xchannel,
                           u16          XpulseLength,
                           TIM_OC_Modes     Xmode,
                           TIM_Logic_Levels Xlevel );

/*******************************************************************************
* Function Name  : TIM_OPModeConfig
* Description    : This routine is used to configure the one pulse mode
* Input          : (1) TIM Timer
*                : (3) XpulseLength      : Length of the pulse
*                : (4) Level1            : Level during the pulse
*                : (5) Level2            : Level after the pulse
*                : (6) Activation Edge   : High or Low on ICAP A
* Output         : None
*******************************************************************************/
void TIM_OPModeConfig ( TIM_TypeDef  *TIMx,
                        u16          XpulseLength,
                        TIM_Logic_Levels XLevel1,
                        TIM_Logic_Levels XLevel2,
                        TIM_Clock_Edges  Xedge );

/*******************************************************************************
* Function Name  : TIM_PWMOModeConfig
* Description    : This routine is used to configure the PWM in output mode
* Input          : (1) TIM Timer
*                : (2) DutyCycle   : u16
*                : (3) Level 1     : During the Duty Cycle
*                : (4) Level 2     : During the after the pulse
*                : (5) Full period : u16
* Output         : None
*******************************************************************************/
void TIM_PWMOModeConfig ( TIM_TypeDef  *TIMx,
                          u16          XDutyCycle,
                          TIM_Logic_Levels XLevel1,
                          u16          XFullperiod,
                          TIM_Logic_Levels XLevel2
                        );

/*******************************************************************************
* Function Name  : TIM_PWMInputConfig
* Description    : This routine is used to configure the PWM in input mode
* Input          : (1) TIM Timer
*                : (2) First Activation Edge
* Output         : None
*******************************************************************************/
void TIM_PWMIModeConfig ( TIM_TypeDef *TIMx, TIM_Clock_Edges Xedge );

/*******************************************************************************
* Function Name  : TIM_PWMIValue
* Description    : This routine is used to get the PWMI values
* Input          : (1) TIM Timer
* Output         : PWMI_parameters : - u16 Dyty cycle
                                     - u16 Full period
*******************************************************************************/
PWMI_parameters TIM_PWMIValue (TIM_TypeDef *TIMx );

/*******************************************************************************
* Function Name  : TIM_CounterConfig
* Description    : This routine is used to start/stop and clear the selected
*                  timer counter
* Input          : (1) TIM Timer
*                : (2) TIM_CounterOperations
                      TIM_START Enables or resumes the counter
*                     TIM_STOP  Stops the TIM counter
*                     TIM_CLEAR Set the TIM counter value to FFFCh
* Output         : None
*******************************************************************************/
void TIM_CounterConfig ( TIM_TypeDef *TIMx, TIM_CounterOperations Xoperation );

/*******************************************************************************
* Function Name  : TIM_ITConfig
* Description    : This routine is used to configure the TIM IT
* Input          : (1) TIM Timer
*                : (2) TIM interrupt
*                : (2) ENABLE / DISABLE
* Output         : None
*******************************************************************************/
inline void TIM_ITConfig ( TIM_TypeDef *TIMx, u16 New_IT, FunctionalState NewState )
{
	if (NewState == ENABLE) TIMx->CR2 |= New_IT; else TIMx->CR2 &= ~New_IT;
}

/*******************************************************************************
* Function Name  : TIM_FlagStatus
* Description    : This routine is used to check whether a Flag is Set.
* Input          : (1) TIM Timer
*                : (2) The TIM FLag
* Output         : Flag NewState
*******************************************************************************/
inline FlagStatus TIM_FlagStatus ( TIM_TypeDef *TIMx, TIM_Flags Xflag )
{
	return (TIMx->SR & Xflag) == 0 ? RESET : SET;
}

/*******************************************************************************
* Function Name  : TIM_FlagClear
* Description    : This routine is used to clear Flags.
* Input          : (1) TIM Timer
*                : (2) The TIM FLag
* Output         : None
*******************************************************************************/
inline void TIM_FlagClear ( TIM_TypeDef *TIMx, TIM_Flags Xflag )
{
	TIMx->SR &= ~Xflag;
}

/*******************************************************************************
* Function Name  : TIM_CounterValue
* Description    : This routine returns the timer counter value.
* Input          : TIM Timer
* Output         : The counter value
*******************************************************************************/
inline u16 TIM_CounterValue(TIM_TypeDef *TIMx)
{
	return TIMx->CNTR;
}
#endif	// __TIM_H

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
