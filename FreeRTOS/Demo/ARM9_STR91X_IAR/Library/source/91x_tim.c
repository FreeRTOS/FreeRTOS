/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_tim.c
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file provides all the TIM software functions.
********************************************************************************
* History:
* 05/22/2007 : Version 1.2
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

/* Includes ------------------------------------------------------------------*/
#include "91x_tim.h"

/* Include of other module interface headers ---------------------------------*/
/* Local includes ------------------------------------------------------------*/
/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/

/* TIM Bits Masks */

#define TIM_PWM_MASK          0x0010
#define TIM_OPM_MASK          0x0020
#define TIM_OC1_ENABLE_MASK   0x0040
#define TIM_OC1_DISABLE_MASK  0xFFBF
#define TIM_OC2_ENABLE_MASK   0x0080
#define TIM_OC2_DISABLE_MASK  0xFF7F

#define TIM_OLVL1_SET_MASK    0x0100
#define TIM_OLVL1_RESET_MASK  0xFEFF

#define TIM_OLVL2_SET_MASK    0x0200
#define TIM_OLVL2_RESET_MASK  0xFDFF

#define TIM_ENABLE_MASK       0x8000
#define TIM_DISABLE_MASK      0x7FFF

#define TIM_DMA_CLEAR_MASK    0xCFFF

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Interface functions -------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/*******************************************************************************
* Function Name  : TIM_DeInit
* Description    : Initializes TIM peripheral control and registers to their
*                : default reset values.
* Input          : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DeInit(TIM_TypeDef *TIMx)
{ 
  if((TIMx == TIM0)||(TIMx == TIM1))
  {
    SCU_APBPeriphReset(__TIM01, DISABLE);    /* TIM0 & TIM1 Reset's off */
  }
  else
  {
    SCU_APBPeriphReset(__TIM23, DISABLE);    /* TIM2 & TIM3 Reset's off */
  }
  
  /* Set all the TIMx registers to thier default values */ 
  TIMx->OC1R = 0x8000;
  TIMx->OC2R = 0x8000;
  TIMx->CR1  = 0x0;
  TIMx->CR2  = 0x1;
  TIMx->CNTR = 0x1234;
  TIMx->SR   = 0x0;
}

/*******************************************************************************
* Function Name  : TIM_StructInit
* Description    : Fills in a TIM_InitTypeDef structure with the reset value of
*                  each parameter.
* Input          : TIM_InitStruct : pointer to a TIM_InitTypeDef structure
                   which will be initialized.
* Output         : None
* Return         : None.
*******************************************************************************/
void TIM_StructInit(TIM_InitTypeDef *TIM_InitStruct)
{
  TIM_InitStruct->TIM_Mode           = 0x0000;
  TIM_InitStruct->TIM_OC1_Modes      = 0x0000;
  TIM_InitStruct->TIM_OC2_Modes      = 0x0000;
  TIM_InitStruct->TIM_Clock_Source   = 0x0000;
  TIM_InitStruct->TIM_Clock_Edge     = 0x0000;
  TIM_InitStruct->TIM_OPM_INPUT_Edge = 0x0000;
  TIM_InitStruct->TIM_ICAP1_Edge     = 0x0000;
  TIM_InitStruct->TIM_ICAP2_Edge     = 0x0000;
  TIM_InitStruct->TIM_Prescaler      = 0x0000;
  TIM_InitStruct->TIM_Pulse_Level_1  = 0x0000;
  TIM_InitStruct->TIM_Pulse_Level_2  = 0x0000;
  TIM_InitStruct->TIM_Period_Level   = 0x0000;
  TIM_InitStruct->TIM_Pulse_Length_1 = 0x0000;
  TIM_InitStruct->TIM_Pulse_Length_2 = 0x0000;
  TIM_InitStruct->TIM_Full_Period    = 0x0000;
}

/*******************************************************************************
* Function Name  : TIM_Init
* Description    : Initializes TIM  peripheral according to the specified
*                  parameters in the TIM_InitTypeDef structure.
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Input2         : TIM_InitStruct: pointer to a TIM_InitTypeDef structure that
*                  contains the configuration information for the specified
*                  TIM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/

void TIM_Init(TIM_TypeDef *TIMx, TIM_InitTypeDef *TIM_InitStruct)
{
/***************************** Clock configuration ****************************/

  if (TIM_InitStruct->TIM_Clock_Source == TIM_CLK_APB)
  {
    /* APB clock */
    TIMx->CR1 &= TIM_CLK_APB;
  }
  else
  {
    /* External/SCU clock */
    TIMx->CR1 |= TIM_CLK_EXTERNAL;
    if (TIM_InitStruct->TIM_Clock_Edge == TIM_CLK_EDGE_RISING)
    {
      /* Clock rising edge */
      TIMx->CR1 |= TIM_CLK_EDGE_RISING;
    }
    else
    {
      /* Clock falling edge */
      TIMx->CR1 &= TIM_CLK_EDGE_FALLING;
    }
  }

/************************** Prescaler configuration ***************************/

  TIMx->CR2 =( TIMx->CR2 & 0xFF00 )|TIM_InitStruct->TIM_Prescaler ;
  
/********************************** TIM Modes *********************************/

  switch ( TIM_InitStruct->TIM_Mode)
  {
/******************************* PWM Input mode *******************************/

    case TIM_PWMI:

      /* Set the PWMI Bit */
      TIMx->CR1 |= TIM_PWMI;

      /* Set the first edge Level */
      if ( TIM_InitStruct->TIM_ICAP1_Edge == TIM_ICAP1_EDGE_RISING)
      {
        TIMx->CR1 |= TIM_ICAP1_EDGE_RISING;
      }
      else
      {
        TIMx->CR1 &= TIM_ICAP1_EDGE_FALLING;
      }

      /* Set the Second edge Level ( Opposite of the first level ) */
      if ( TIM_InitStruct->TIM_ICAP1_Edge == TIM_ICAP1_EDGE_RISING)
      {
        TIMx->CR1 &= TIM_ICAP2_EDGE_FALLING;
      }
      else
      {
      	TIMx->CR1 |= TIM_ICAP2_EDGE_RISING;
      }

      break;

/************************** Output compare channel 1 **************************/

    case TIM_OCM_CHANNEL_1:

      if (TIM_InitStruct->TIM_Pulse_Level_1 == TIM_HIGH)
      {
        TIMx->CR1 |= TIM_OLVL1_SET_MASK;
      }
      else
      {
        TIMx->CR1 &= TIM_OLVL1_RESET_MASK;
      }
      
      TIMx->OC1R = TIM_InitStruct->TIM_Pulse_Length_1;

      if (TIM_InitStruct->TIM_OC1_Modes == TIM_TIMING)
      {
      	TIMx->CR1 &= TIM_OC1_DISABLE_MASK;
      }
      else
      {
        TIMx->CR1 |= TIM_OC1_ENABLE_MASK;
      }

      break;

/************************** Output compare channel 2 **************************/

    case TIM_OCM_CHANNEL_2:

      if (TIM_InitStruct->TIM_Pulse_Level_2 == TIM_HIGH)
      {
      	TIMx->CR1 |= TIM_OLVL2_SET_MASK;
      }
      else
      {
        TIMx->CR1 &= TIM_OLVL2_RESET_MASK;
      }
       
      TIMx->OC2R = TIM_InitStruct->TIM_Pulse_Length_2;

      if (TIM_InitStruct->TIM_OC2_Modes == TIM_TIMING)
      {
        TIMx->CR1 &= TIM_OC2_DISABLE_MASK;
      }
      else
      {
        TIMx->CR1 |= TIM_OC2_ENABLE_MASK;
      }

      break;

/************************ Output compare channel 1 & 2 ************************/

   case TIM_OCM_CHANNEL_12:

    TIMx->OC2R = TIM_InitStruct->TIM_Pulse_Length_2;
    TIMx->OC1R = TIM_InitStruct->TIM_Pulse_Length_1;

    if (TIM_InitStruct->TIM_OC2_Modes == TIM_TIMING)
    {
      TIMx->CR1 &= TIM_OC2_DISABLE_MASK;
    }
    else
    {
      TIMx->CR1 |= TIM_OC2_ENABLE_MASK;
    }

    if (TIM_InitStruct->TIM_OC1_Modes == TIM_TIMING)
    {
      TIMx->CR1 &= TIM_OC1_DISABLE_MASK;
    }
    else
    {
      TIMx->CR1 |= TIM_OC1_ENABLE_MASK;
    }
    
    if (TIM_InitStruct->TIM_Pulse_Level_1 == TIM_HIGH)
    {
      TIMx->CR1 |= TIM_OLVL1_SET_MASK;
    }
    else
    {
      TIMx->CR1 &= TIM_OLVL1_RESET_MASK;
    }

    if (TIM_InitStruct->TIM_Pulse_Level_2 == TIM_HIGH)
    {
      TIMx->CR1 |= TIM_OLVL2_SET_MASK;
    }
    else
    {
      TIMx->CR1 &= TIM_OLVL2_RESET_MASK;
    }

    break;

/********************************** PWM mode **********************************/

    case TIM_PWM:

      /* Set the Level During the pulse */
      if ( TIM_InitStruct->TIM_Pulse_Level_1 == TIM_HIGH)
      {
        TIMx->CR1 |= TIM_OLVL2_SET_MASK;
      }
      else
      {
        TIMx->CR1 &= TIM_OLVL2_RESET_MASK;
      }

      /* Set the Level after the pulse */
      if (TIM_InitStruct->TIM_Period_Level == TIM_HIGH)
      {
        TIMx->CR1 |= TIM_OLVL1_SET_MASK;
      }
      else
      {
        TIMx->CR1 &= TIM_OLVL1_RESET_MASK;
      }
      
      /* Set the OCAE */
      TIMx->CR1 |= TIM_OC1_ENABLE_MASK;

      /* Set the PWM Bit */
      TIMx->CR1 |= TIM_PWM_MASK;

      /* Set the Duty Cycle value */
      
      TIMx->OC1R = TIM_InitStruct->TIM_Pulse_Length_1 ;

      /* Set the Full Period */
      
      TIMx->OC2R = TIM_InitStruct->TIM_Full_Period ;

      break;

/******************************* One pulse mode *******************************/

    case TIM_OPM:

      /* Set the Level During the pulse */
      if (TIM_InitStruct->TIM_Pulse_Level_1 == TIM_HIGH)
      {
        TIMx->CR1 |= TIM_OLVL2_SET_MASK;
      }

      /* Set the Level after the pulse  */
      if (TIM_InitStruct->TIM_Period_Level == TIM_HIGH)
      {
        TIMx->CR1 |= TIM_OLVL1_SET_MASK;
      }
      
      /* Set the Activation Edge on the ICAP 1 */
      if (TIM_InitStruct->TIM_OPM_INPUT_Edge == TIM_OPM_EDGE_RISING)
      {
        TIMx->CR1 |= TIM_OPM_EDGE_RISING;
      }

      /* Set the Output Compare Function  */
      TIMx->CR1 |= TIM_OC1_ENABLE_MASK;

      /* Set the One pulse mode */
      TIMx->CR1 |= TIM_OPM_MASK;

      /* Set the Pulse length  */
      TIMx->OC1R = TIM_InitStruct->TIM_Pulse_Length_1;

      break;

/*************************** Input capture channel 1 **************************/

    case TIM_ICAP_CHANNEL_1:

      if (TIM_InitStruct->TIM_ICAP1_Edge == TIM_ICAP1_EDGE_RISING)
      {
        TIMx->CR1 |= TIM_ICAP1_EDGE_RISING;
      }
      else
      {
        TIMx->CR1 &= TIM_ICAP1_EDGE_FALLING;
      }

      break;

/*************************** Input capture channel 2 **************************/

    case TIM_ICAP_CHANNEL_2:

      if (TIM_InitStruct->TIM_ICAP2_Edge == TIM_ICAP2_EDGE_RISING)
      {
        TIMx->CR1 |= TIM_ICAP2_EDGE_RISING;
      }
      else
      {
        TIMx->CR1 &= TIM_ICAP2_EDGE_FALLING;
      }

      break;

/************************* Input capture channel 1 & 2 ************************/

    case TIM_ICAP_CHANNEL_12:
      if (TIM_InitStruct->TIM_ICAP2_Edge == TIM_ICAP2_EDGE_RISING)
      {
        TIMx->CR1 |= TIM_ICAP2_EDGE_RISING;
      }
      else
      {
        TIMx->CR1 &= TIM_ICAP2_EDGE_FALLING;
      }

      if (TIM_InitStruct->TIM_ICAP1_Edge == TIM_ICAP1_EDGE_RISING)
      {
        TIMx->CR1 |= TIM_ICAP1_EDGE_RISING;
      }
      else
      {
        TIMx->CR1 &= TIM_ICAP1_EDGE_FALLING;
      }

      break;

    default:
      break;
  }
}

/*******************************************************************************
* Function Name  : TIM_CounterCmd
* Description    : Enables or disables TIMx Counter peripheral.
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Input2         : TIM_operation: specifies the new state of the TIMx Counter.
*                  This parameter can be one of the following values:
*                       - TIM_START: Start the timer counter.
*                       - TIM_STOP : Stop the timer counter.
*                       - TIM_CLEAR: Clear the timer counter.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_CounterCmd(TIM_TypeDef *TIMx, TIM_CounterOperations TIM_operation)
{
  switch (TIM_operation)
  {
    case TIM_START:
      TIMx->CR1 |= TIM_ENABLE_MASK;
      break;

    case TIM_STOP:
      TIMx->CR1 &= TIM_DISABLE_MASK;
      break;

    case TIM_CLEAR:
      TIMx->CNTR = 0x1234;
      break;
    
    default:
      break;
  }
}

/*******************************************************************************
* Function Name  : TIM_PrescalerConfig
* Description    : This routine is used to configure the TIMx prescaler value
*                  (when using the APB clock).
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Input2         : TIM_Prescaler: specifies the prescaler value. This parameter
*                  can be a value from 0x0 to 0xFF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_PrescalerConfig(TIM_TypeDef *TIMx, u8 TIM_Prescaler)
{
  TIMx->CR2 &= 0xFF00;
  TIMx->CR2 |= TIM_Prescaler;

}
/*******************************************************************************
* Function Name  : TIM_GetPrescalerValue
* Description    : This routine is used to get the TIMx prescaler value
*                  (when using the APB clock).
* Input          : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Output         : None
* Return         : The prescaler value.
*******************************************************************************/
u8 TIM_GetPrescalerValue(TIM_TypeDef *TIMx)
{
  return TIMx->CR2 & 0x00FF;
}

/*******************************************************************************
* Function Name  : TIM_GetCounterValue
* Description    : This routine is used to get the TIMx counter value.
* Input          : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Output         : None
* Return         : The counter value.
*******************************************************************************/
u16 TIM_GetCounterValue(TIM_TypeDef *TIMx)
{
  return TIMx->CNTR;
}

/*******************************************************************************
* Function Name  : TIM_GetICAP1Value
* Description    : This routine is used to get the Input Capture 1 value.
* Input          : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Output         : None
* Return         : The Input Capture 1 value.
*******************************************************************************/
u16 TIM_GetICAP1Value(TIM_TypeDef *TIMx)
{
  return TIMx->IC1R;
}

/*******************************************************************************
* Function Name  : TIM_GetICAP2Value
* Description    : This routine is used to get the Input Capture 2 value.
* Input          : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Output         : None
* Return         : The Input Capture 2 value.
*******************************************************************************/
u16 TIM_GetICAP2Value(TIM_TypeDef *TIMx)
{
  return TIMx->IC2R;
}

/*******************************************************************************
* Function Name  : TIM_SetPulse
* Description    : This routine is used to set the pulse value.
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Input2         : TIM_Channel: specifies the needed channel.
*                  This parameter can be one of the following values:
*                       - TIM_PWM_OC1_Channel: PWM/Output Compare 1 Channel
*                       - TIM_OC2_Channel    : Output Compare 2 Channel
* Input3         : TIM_Pulse: specifies the new pulse value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetPulse(TIM_TypeDef *TIMx,u16 TIM_Channel ,u16 TIM_Pulse)
{
  if (TIM_Channel == TIM_PWM_OC1_Channel)
  {
    TIMx->OC1R = TIM_Pulse;
  }
  else
  {
    TIMx->OC2R = TIM_Pulse;
  }
}
/*******************************************************************************
* Function Name  : TIM_GetFlagStatus
* Description    : Checks whether the specified TIMx flag is set or not.
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Input2         : TIM_Flag: specifies the flag to check.
*                  This parameter can be one of the following values:
*                       - TIM_FLAG_IC1: Input Capture Channel 1 Flag
*                       - TIM_FLAG_IC2: Input Capture Channel 2 Flag
*                       - TIM_FLAG_TO : Timer Overflow Flag 
*                       - TIM_FLAG_OC1: Output Compare Channel 1 Flag
*                       - TIM_FLAG_OC2: Output Compare Channel 2 Flag
* Output         : None
* Return         : The NewState of the TIM_Flag (SET or RESET).
*******************************************************************************/
FlagStatus TIM_GetFlagStatus(TIM_TypeDef *TIMx, u16 TIM_Flag)
{
  if((TIMx->SR & TIM_Flag) == RESET)
  {
    return RESET;
  }
  else
  {
    return SET;
  }
}

/*******************************************************************************
* Function Name  : TIM_ClearFlag
* Description    : Clears the TIM Flag passed as a parameter.
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                    peripheral.
* Input2         : TIM_Flag: specifies the flag to clear.
*                  This parameter can be one of the following values:
*                       - TIM_FLAG_IC1: Input Capture Channel 1 Flag
*                       - TIM_FLAG_IC2: Input Capture Channel 2 Flag
*                       - TIM_FLAG_TO : Timer Overflow Flag
*                       - TIM_FLAG_OC1: Output Compare Channel 1 Flag
*                       - TIM_FLAG_OC2: Output Compare Channel 2 Flag
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ClearFlag(TIM_TypeDef *TIMx, u16 TIM_Flag)
{
  /* Clear TIM_Flag */
  TIMx->SR &= ~TIM_Flag;
}

/*******************************************************************************
* Function Name  : TIM_GetPWMIPulse
* Description    : This routine is used to get the Pulse value in PWMI Mode.
* Input          : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Output         : None
* Return         : The pulse value.
*******************************************************************************/
u16 TIM_GetPWMIPulse(TIM_TypeDef *TIMx)
{
  return TIMx->IC2R;
}

/*******************************************************************************
* Function Name  : TIM_GetPWMIPeriod
* Description    : This routine is used to get the Period value in PWMI Mode.
* Input          : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Output         : None
* Return         : The period value.
*******************************************************************************/
u16 TIM_GetPWMIPeriod(TIM_TypeDef *TIMx)
{
  return TIMx->IC1R;
}

/*******************************************************************************
* Function Name  : TIM_ITConfig
* Description    : Configures the Timer interrupt source.
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Input2         : TIM_IT: specifies the TIM interrupt source to be enabled.
*                  This parameter can be one of the following values:
*                       - TIM_IT_IC1: Input Capture 1 Interrupt source.
*                       - TIM_IT_OC1: Output Compare 1 Interrupt source.
*                       - TIM_IT_TO : Timer Overflow Interrupt source.
*                       - TIM_IT_IC2: Input Capture 2 Interrupt source.
*                       - TIM_IT_OC2: Output Compare 2 Interrupt source.
* Input3         : TIM_Newstate: specifies the new state of the  TIMx IT.
*                  This parameter can be one of the following values:
*                       - ENABLE : Enable the needed interrupt.
*                       - DISABLE: Disable the needed interrupt.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ITConfig(TIM_TypeDef *TIMx, u16 TIM_IT, FunctionalState TIM_Newstate)
{
  if(TIM_Newstate == ENABLE)
  {
    TIMx->CR2 = (TIMx->CR2 & 0x00FF) | TIM_IT; 
  }
  else
  {
    TIMx->CR2 &= ~TIM_IT;
  }
}

/*******************************************************************************
* Function Name  : TIM_DMAConfig
* Description    : Configures the Timer DMA source.
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Input2         : TIM_DMA_Souces: specifies the TIM DMA source to be selected.
*                  This parameter can be one of the following values:
*                       - TIM_DMA_IC1: Input Capture 1 DMA source.
*                       - TIM_DMA_OCA1 Output Compare 1 DMA source.
*                       - TIM_DMA_TO: Timer Overflow DMA source.
*                       - TIM_DMA_IC2: Input Capture 2 DMA source.
*                       - TIM_DMA_OC2: Output Compare 2 DMA source.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DMAConfig(TIM_TypeDef *TIMx, u16 TIM_DMA_Sources)
{
  /* Reset the DMAS[1:0] bits */
  TIMx->CR1 &= TIM_DMA_CLEAR_MASK;
  /* Set the DMAS[1:0] bits according to TIM_DMA_Sources parameter */
  TIMx->CR1 |= TIM_DMA_Sources; 
}

/*******************************************************************************
* Function Name  : TIM_DMACmd
* Description    : Enables or disables TIMx DMA peripheral.
* Input1         : TIMx: where x can be from 0 to 3 to select the TIM
*                  peripheral.
* Input2         : TIM_Newstate: new state of the  TIMx DMA peripheral 
*                  This parameter can be one of the following values:
*                       - ENABLE : Enable the TIMx DMA.
*                       - DISABLE: Disable the TIMx DMA.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DMACmd(TIM_TypeDef *TIMx, FunctionalState TIM_Newstate)
{
  if (TIM_Newstate == ENABLE)
  {
    TIMx->CR2 |= TIM_DMA_ENABLE;
  }
  else
  {
    TIMx->CR2 &= TIM_DMA_DISABLE;
  }
}
/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
