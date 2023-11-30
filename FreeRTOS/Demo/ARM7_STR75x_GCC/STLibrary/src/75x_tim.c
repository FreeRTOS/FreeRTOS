/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_tim.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the TIM software functions.
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

/* Includes ------------------------------------------------------------------*/
#include "75x_tim.h" 
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* TIM interrupt masks */
#define TIM_IT_Clear_Mask   0x7FFF
#define TIM_IT_Enable_Mask  0x7FFF

/* TIM Input Capture Selection Set/Reset */
#define TIM_IC1S_Set    0x0001
#define TIM_IC1S_Reset  0x003E

/* TIM Input Capture Selection Set/Reset */
#define TIM_IC2S_Set    0x0002
#define TIM_IC2S_Reset  0x003D

/* TIM_SCR Masks bit */
#define TIM_Encoder_Mask                   0x731C
#define TIM_SlaveModeSelection_Mask        0x7307
#define TIM_TriggerSelection_Mask          0x701F
#define TIM_InternalTriggerSelection_Mask  0x031F

/* TIM Encoder mode Set value */
#define TIM_Encoder1_Set  0x0001
#define TIM_Encoder2_Set  0x0002
#define TIM_Encoder3_Set  0x0003

/* TIM Slave Mode Enable Set/Reset value */
#define TIM_SME_Reset  0x731B
#define TIM_SME_Set    0x0004

/* TIM Internal Trigger Selection value */
#define TIM_ITS_TIM0  0x1000
#define TIM_ITS_TIM1  0x2000
#define TIM_ITS_TIM2  0x3000
#define TIM_ITS_PWM   0x4000

/* TIM Trigger Selection value */
#define TIM_TS_IC1_Set  0x0200
#define TIM_TS_IC2_Set  0x0300

/* TIM Slave Mode selction external clock Set value */
#define TIM_SMS_EXTCLK_Set    0x0008
#define TIM_SMS_RESETCLK_Set  0x0000

/* TIM_CR Masks bit */
#define TIM_DBASE_Mask                0x077F
#define TIM_MasterModeSelection_Mask  0xFC7F
#define TIM_CounterMode_Mask          0xFF8F

/* TIM Update flag selection Set/Reset value */
#define TIM_UFS_Reset  0xFFFE
#define TIM_UFS_Set    0x0001

/* TIM Counter value */
#define TIM_COUNTER_Reset  0x0002
#define TIM_COUNTER_Start  0x0004
#define TIM_COUNTER_Stop   0xFFFB

/* TIM One pulse Mode set value */
#define TIM_OPM_Set    0x0008
#define TIM_OPM_Reset  0xFFF7

/* TIM Debug Mode Set/Reset value */
#define TIM_DBGC_Set    0x0400
#define TIM_DBGC_Reset  0xFB7F

/* TIM Input Capture Enable/Disable value */
#define TIM_IC1_Enable  0x0004
#define TIM_IC2_Enable  0x0010

/* TIM Input Capture Polarity Set/Reset value */
#define TIM_IC1P_Set    0x0008
#define TIM_IC2P_Set    0x0020
#define TIM_IC1P_Reset  0x0037
#define TIM_IC2P_Reset  0x001F

/* TIM Output Compare Polarity Set/Reset value */
#define TIM_OC1P_Set    0x0020
#define TIM_OC2P_Set    0x2000
#define TIM_OC1P_Reset  0x3F1F
#define TIM_OC2P_Reset  0x1F3F

/* TIM Output Compare control mode constant */
#define TIM_OCControl_PWM         0x000C
#define TIM_OCControl_OCToggle    0x0006
#define TIM_OCControl_OCInactive  0x0004
#define TIM_OCControl_OCActive    0x0002
#define TIM_OCControl_OCTiming    0x0000

/* TIM Output Compare mode Enable value */
#define TIM_OC1_Enable  0x0010
#define TIM_OC2_Enable  0x1000

/* TIM Output Compare mode Mask value */
#define TIM_OC1C_Mask  0x3F31
#define TIM_OC2C_Mask  0x313F

/* TIM Preload bit Set/Reset value */
#define TIM_PLD1_Set    0x0001
#define TIM_PLD1_Reset  0xFFFE

#define TIM_PLD2_Set    0x0100
#define TIM_PLD2_Reset  0xFEFF

/* TIM OCRM Set/Reset value */
#define TIM_OCRM_Set    0x0080
#define TIM_OCRM_Reset  0x030D

/* Reset Register Masks */
#define TIM_Pulse2_Reset_Mask     0x0000
#define TIM_Prescaler_Reset_Mask  0x0000
#define TIM_Pulse1_Reset_Mask     0x0000
#define TIM_Period_Reset_Mask     0xFFFF
#define TIM_Counter_Reset         0x0002

/* Private function prototypes -----------------------------------------------*/
static void ICAP_ModuleConfig(TIM_TypeDef* TIMx, TIM_InitTypeDef* TIM_InitStruct);
static void Encoder_ModeConfig(TIM_TypeDef* TIMx, TIM_InitTypeDef* TIM_InitStruct);
static void OCM_ModuleConfig(TIM_TypeDef* TIMx, TIM_InitTypeDef* TIM_InitStruct);

/* Private functions ---------------------------------------------------------*/

/******************************************************************************
* Function Name  : TIM_DeInit
* Description    : Deinitializes TIM peripheral registers to their default reset
*                  values.
* Input          : TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DeInit(TIM_TypeDef *TIMx)
{ 
  if(TIMx == TIM0)
  {
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_TIM0,ENABLE);
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_TIM0,DISABLE);
  }
  else if(TIMx == TIM1)
  {
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_TIM1,ENABLE);
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_TIM1,DISABLE);
  }
  else if(TIMx == TIM2)
  {
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_TIM2,ENABLE);
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_TIM2,DISABLE);
  }
}

/*******************************************************************************
* Function Name  : TIM_Init
* Description    : Initializes the TIMx peripheral according to the specified
*                  parameters in the TIM_InitStruct .
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_InitStruct: pointer to a TIM_InitTypeDef structure that
*                    contains the configuration information for the specified TIM
*                    peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_Init(TIM_TypeDef* TIMx, TIM_InitTypeDef* TIM_InitStruct)
{
  /* Set the prescaler value */
  TIMx->PSC = TIM_InitStruct->TIM_Prescaler;

  /* Select the clock source */
  TIM_ClockSourceConfig(TIMx, TIM_InitStruct->TIM_ClockSource,
                           TIM_InitStruct->TIM_ExtCLKEdge);

  /* Select the counter mode */
  TIMx->CR &= TIM_CounterMode_Mask;
  TIMx->CR |= TIM_InitStruct->TIM_CounterMode;

  /* Set the period value */
  TIMx->ARR = TIM_InitStruct->TIM_Period;

  switch(TIM_InitStruct->TIM_Mode)
  {
    case TIM_Mode_OCTiming: case TIM_Mode_OCActive: case TIM_Mode_OCInactive:
    case TIM_Mode_OCToggle: case TIM_Mode_PWM:
      OCM_ModuleConfig(TIMx, TIM_InitStruct);
    break;

    case TIM_Mode_PWMI: case TIM_Mode_IC:
      ICAP_ModuleConfig(TIMx, TIM_InitStruct);
    break;

    case TIM_Mode_Encoder1: case TIM_Mode_Encoder2: case TIM_Mode_Encoder3:
      Encoder_ModeConfig(TIMx, TIM_InitStruct);
    break;

    case TIM_Mode_OPM_PWM: case TIM_Mode_OPM_Toggle: case TIM_Mode_OPM_Active:

      /* Output module configuration */
      OCM_ModuleConfig(TIMx, TIM_InitStruct);

      /* Input module configuration */
      ICAP_ModuleConfig(TIMx, TIM_InitStruct);
      
      /* Set the slave mode to trigger Mode */
      TIMx->SCR |= TIM_SynchroMode_Trigger;

      /* Repetitive pulse state selection */
      if(TIM_InitStruct->TIM_RepetitivePulse == TIM_RepetitivePulse_Disable)
      {
        TIMx->CR |= TIM_OPM_Set;
      }
      else
      {
        TIMx->CR &= TIM_OPM_Reset;
      }
    break;

    default:
    break;
  }
}

/*******************************************************************************
* Function Name  : TIM_StructInit
* Description    : Fills each TIM_InitStruct member with its default value.
* Input          : TIM_InitStruct : pointer to a TIM_InitTypeDef structure
*                  which will be initialized.
* Output         : None                        
* Return         : None.
*******************************************************************************/
void TIM_StructInit(TIM_InitTypeDef *TIM_InitStruct)
{
  /* Set the default configuration */
  TIM_InitStruct->TIM_Mode = TIM_Mode_OCTiming;
  TIM_InitStruct->TIM_Prescaler = TIM_Prescaler_Reset_Mask;
  TIM_InitStruct->TIM_ClockSource = TIM_ClockSource_Internal;
  TIM_InitStruct->TIM_ExtCLKEdge = TIM_ExtCLKEdge_Rising;
  TIM_InitStruct->TIM_CounterMode = TIM_CounterMode_Up;
  TIM_InitStruct->TIM_Period = TIM_Period_Reset_Mask;
  TIM_InitStruct->TIM_Channel = TIM_Channel_ALL;
  TIM_InitStruct->TIM_Pulse1 = TIM_Pulse1_Reset_Mask;
  TIM_InitStruct->TIM_Pulse2 = TIM_Pulse2_Reset_Mask;
  TIM_InitStruct->TIM_RepetitivePulse = TIM_RepetitivePulse_Disable;
  TIM_InitStruct->TIM_Polarity1 = TIM_Polarity1_Low;
  TIM_InitStruct->TIM_Polarity2 = TIM_Polarity2_Low;
  TIM_InitStruct->TIM_IC1Selection = TIM_IC1Selection_TI1;
  TIM_InitStruct->TIM_IC2Selection = TIM_IC2Selection_TI1;
  TIM_InitStruct->TIM_IC1Polarity = TIM_IC1Polarity_Rising;
  TIM_InitStruct->TIM_IC2Polarity = TIM_IC2Polarity_Rising;
  TIM_InitStruct->TIM_PWMI_ICSelection = TIM_PWMI_ICSelection_TI1;
  TIM_InitStruct->TIM_PWMI_ICPolarity = TIM_PWMI_ICPolarity_Rising;
}

/*******************************************************************************
* Function Name  : TIM_Cmd
* Description    : Enables or disables the specified TIM peripheral.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - Newstate: new state of the TIMx peripheral.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_Cmd(TIM_TypeDef *TIMx, FunctionalState Newstate)
{
 if(Newstate == ENABLE)
  { 
    TIMx->CR |= TIM_COUNTER_Start;
  }
  else
  {
    TIMx->CR &= TIM_COUNTER_Stop;
  }
}

/*******************************************************************************
* Function Name  : TIM_ITConfig
* Description    : Enables or disables the TIM interrupts.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_IT: specifies the TIM interrupts sources to be enabled
*                    or disabled.
*                    This parameter can be any combination of the following values:
*                         - TIM_IT_IC1: Input Capture 1 Interrupt 
*                         - TIM_IT_OC1: Output Compare 1 Interrupt 
*                         - TIM_IT_Update: Timer update Interrupt 
*                         - TIM_IT_GlobalUpdate: Timer global update Interrupt 
*                         - TIM_IT_IC2: Input Capture 2 Interrupt 
*                         - TIM_IT_OC2: Output Compare 2 Interrupt 
*                  - Newstate: new state of the specified TIMx interrupts. 
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ITConfig(TIM_TypeDef *TIMx, u16 TIM_IT, FunctionalState Newstate)
{ 
  u16 TIM_IT_Enable = 0;

  TIM_IT_Enable = TIM_IT & TIM_IT_Enable_Mask;

  if(Newstate == ENABLE)
  {
    /* Update interrupt global source: overflow/undeflow, counter reset operation
    or slave mode controller in reset mode */
    if((TIM_IT & TIM_IT_GlobalUpdate) == TIM_IT_GlobalUpdate)
    {
      TIMx->CR &= TIM_UFS_Reset;
    }
    /* Update interrupt source: counter overflow/underflow */
    else if((TIM_IT & TIM_IT_Update) == TIM_IT_Update)
    {
      TIMx->CR |= TIM_UFS_Set;
    }
    /* Select and enable the interrupts requests */
    TIMx->RSR |= TIM_IT_Enable;
    TIMx->RER |= TIM_IT_Enable;
  }
  /* Disable the interrupts requests */
  else
  {
    TIMx->RSR &= ~TIM_IT_Enable;
    TIMx->RER &= ~TIM_IT_Enable;
  }
}

/*******************************************************************************
* Function Name  : TIM_PreloadConfig
* Description    : Enables or disables TIM peripheral Preload register on OCRx.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_Channel: specifies the TIM channel to be used.
*                    This parameter can be one of the following values:
*                         - TIM_Channel_1: TIM Channel 1 is used
*                         - TIM_Channel_2: TIM Channel 2 is used
*                         - TIM_Channel_ALL: TIM Channel 1and 2 are used
*                  - Newstate: new state of the TIMx peripheral Preload register
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_PreloadConfig(TIM_TypeDef *TIMx, u16 TIM_Channel, FunctionalState Newstate)
{
  if(Newstate == ENABLE)
  {
    switch (TIM_Channel)
    {
      case TIM_Channel_1:
      TIMx->OMR1 |= TIM_PLD1_Set;
      break;
   
      case TIM_Channel_2:
      TIMx->OMR1 |= TIM_PLD2_Set;
      break;

      case TIM_Channel_ALL:
      TIMx->OMR1 |= TIM_PLD1_Set | TIM_PLD2_Set;
      break;

      default:
      break;
   }
  }
  else
  {
    switch (TIM_Channel)
    {
      case TIM_Channel_1:
      TIMx->OMR1 &= TIM_PLD1_Reset;
      break;
   
      case TIM_Channel_2:
      TIMx->OMR1 &= TIM_PLD2_Reset;
      break;

      case TIM_Channel_ALL:
      TIMx->OMR1 &= TIM_PLD1_Reset & TIM_PLD2_Reset;
      break;

      default:
      break;
    }
  }  
}

/*******************************************************************************
* Function Name  : TIM_DMAConfig
* Description    : Configures the TIM0’s DMA interface.
* Input          : - TIM_DMASources: specifies the DMA Request sources.
*                    This parameter can be any combination of the following values:
*                         - TIM_DMASource_OC1: Output Compare 1 DMA source
*                         - TIM_DMASource_OC2: Output Compare 2 DMA source
*                         - TIM_DMASource_IC1: Input Capture 1 DMA source
*                         - TIM_DMASource_IC2: Input Capture 2 DMA source
*                         - TIM_DMASource_Update: Timer Update DMA source
*                  - TIM_OCRMState: the state of output compare request mode.
*                    This parameter can be one of the following values:
*                         - TIM_OCRMState_Enable 
*                         - TIM_OCRMState_Disable 
*                  - TIM_DMABase:DMA Base address.
*                    This parameter can be one of the following values:
*                    TIM_DMABase_CR, TIM_DMABase_SCR, TIM_DMABase_IMCR,
*                    TIM_DMABase_OMR1, TIM_DMABase_RSR,
*                    TIM_DMABase_RER, TIM_DMABase_ISR, TIM_DMABase_CNT, 
*                    TIM_DMABase_PSC, TIM_DMABase_ARR, TIM_DMABase_OCR1, 
*                    TIM_DMABase_OCR2, TIM_DMABase_ICR1, TIM_DMABase_ICR2
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DMAConfig(u16 TIM_DMASources, u16 TIM_OCRMState, u16 TIM_DMABase)
{
  /* Select the DMA requests */
  TIM0->RSR &= TIM_DMASources;

  /* Set the OCRM state */
  if(TIM_OCRMState == TIM_OCRMState_Enable)
  {
    TIM0->RSR |= TIM_OCRM_Set;
  }
  else
  {
    TIM0->RSR &= TIM_OCRM_Reset;
  }

  /* Set the DMA Base address */
  TIM0->CR &= TIM_DBASE_Mask;
  TIM0->CR |= TIM_DMABase;
}

/*******************************************************************************
* Function Name  : TIM_DMACmd
* Description    : Enables or disables the TIM0’s DMA interface.
* Input          : - TIM_DMASources: specifies the DMA Request sources.
*                    This parameter can be any combination of the following values:
*                         - TIM_DMASource_OC1: Output Compare 1 DMA source
*                         - TIM_DMASource_OC2: Output Compare 2 DMA source
*                         - TIM_DMASource_IC1: Input Capture 1 DMA source
*                         - TIM_DMASource_IC2: Input Capture 2 DMA source
*                         - TIM_DMASource_Update: Timer Update DMA source
*                  - Newstate: new state of the DMA Request sources.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DMACmd(u16 TIM_DMASources, FunctionalState Newstate)
{
  if(Newstate == ENABLE)
  {
    TIM0->RER |= TIM_DMASources;
  }
  else
  {
    TIM0->RER &= ~TIM_DMASources;
  }
}

/*******************************************************************************
* Function Name  : TIM_ClockSourceConfig
* Description    : Configures the TIM clock source.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_ClockSource: specifies the TIM clock source to be 
*                    selected.
*                    This parameter can be one of the following values:
*                         - TIM_ClockSource_Internal: CK_TIM internal clock
*                         - TIM_ClockSource_TI11: External input pin TI1 
*                           connected to IC1 channel.
*                         - TIM_ClockSource_TI12: External input pin TI1
*                           connected to IC2 channel.
*                         - TIM_ClockSource_TI22: External input pin TI2
*                           connected to IC2 channel.
*                         - TIM_ClockSource_TI21: External input pin TI2
*                           connected to IC1 channel.
*                  - TIM_ExtCLKEdge: specifies the External input signal edge.
*                    This parameter can be one of the following values:
*                         - TIM_ExtCLKEdge_Falling : Falling edge selected.
*                         - TIM_ExtCLKEdge_Rising : Rising edge selected.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ClockSourceConfig(TIM_TypeDef *TIMx, u16 TIM_ClockSource,
                           u16 TIM_ExtCLKEdge)
{
  if(TIM_ClockSource == TIM_ClockSource_Internal)
  {
    /* CK_TIM is used as clock source */
    TIMx->SCR &= TIM_SME_Reset & TIM_SlaveModeSelection_Mask & TIM_TriggerSelection_Mask;
  }
  else
  /* Input Captures are used as TIM external clock */
  {
    TIMx->SCR &= TIM_SME_Reset & TIM_SlaveModeSelection_Mask & TIM_TriggerSelection_Mask;
    TIMx->SCR |= TIM_SMS_EXTCLK_Set | TIM_SME_Set;

    if((TIM_ClockSource == TIM_ClockSource_TI11) ||
      (TIM_ClockSource == TIM_ClockSource_TI21))
    /* Input Capture 1 is selected */
    {
     /* Input capture  Enable */
      TIMx->IMCR |= TIM_IC1_Enable;
      TIMx->SCR |= TIM_TS_IC1_Set;

      if(TIM_ExtCLKEdge == TIM_ExtCLKEdge_Falling)
      /* Set the corresponding polarity */
      {
        TIMx->IMCR |= TIM_IC1P_Set;
      }
      else
      {   
        TIMx->IMCR &= TIM_IC1P_Reset;
      }
      if(TIM_ClockSource == TIM_ClockSource_TI11)
      {
        /* External signal TI1 connected to IC1 channel */
        TIMx->IMCR &= TIM_IC1S_Reset;
      }
      else
      {
        /* External signal TI2 connected to IC1 channel */
        TIMx->IMCR |= TIM_IC1S_Set;
      }
    }
    else
    /* Input Capture 2 is selected */
    {
      /* Input capture  Enable */
      TIMx->IMCR |= TIM_IC2_Enable;
      TIMx->SCR |= TIM_TS_IC2_Set;

      if(TIM_ExtCLKEdge == TIM_ExtCLKEdge_Falling)
      /* Set the corresponding polarity */
      {
        TIMx->IMCR |= TIM_IC2P_Set;
      }
      else
      {
         TIMx->IMCR &= TIM_IC2P_Reset;
      }
      if(TIM_ClockSource == TIM_ClockSource_TI22)
      {
        /* External signal TI2 connected to IC2 channel */
        TIMx->IMCR &= TIM_IC2S_Reset;
      }
      else
      {
        /* External signal TI1 connected to IC2 channel */
        TIMx->IMCR |= TIM_IC2S_Set;
      }
    }
  }
}

/*******************************************************************************
* Function Name  : TIM_SetPrescaler
* Description    : Sets the TIM prescaler value.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
*                  - Prescaler: TIM prescaler new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetPrescaler(TIM_TypeDef* TIMx, u16 Prescaler)
{
  TIMx->PSC = Prescaler;
}

/*******************************************************************************
* Function Name  : TIM_SetPeriod
* Description    : Sets the TIM period value.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
*                  - Period: TIM period new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetPeriod(TIM_TypeDef* TIMx, u16 Period)
{
  TIMx->ARR = Period;
}

/*******************************************************************************
* Function Name  : TIM_SetPulse
* Description    : Sets the TIM pulse value.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
*                  - TIM_Channel: specifies the TIM channel to be used.
*                    This parameter can be one of the following values:
*                         - TIM_Channel_1: TIM Channel 1 is used
*                         - TIM_Channel_2: TIM Channel 2 is used
*                         - TIM_Channel_ALL: TIM Channel 1and 2 are used
*                  - Pulse: TIM pulse new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetPulse(TIM_TypeDef* TIMx, u16 TIM_Channel, u16 Pulse)
{
  /* Set Channel 1 pulse value */
  if(TIM_Channel == TIM_Channel_1)
  {
    TIMx->OCR1 = Pulse;
  }
  /* Set Channel 2 pulse value */
  else if(TIM_Channel == TIM_Channel_2)
  {
   TIMx->OCR2 = Pulse;
  }
  /* Set Channel 1 and Channel 2 pulse values */
  else if(TIM_Channel == TIM_Channel_ALL)
  {
    TIMx->OCR1 = Pulse;
    TIMx->OCR2 = Pulse;
  }
}

/*******************************************************************************
* Function Name  : TIM_GetICAP1
* Description    : Gets the Input Capture 1 value. 
* Input          : TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
* Output         : None
* Return         : Input Capture 1 Register value.
*******************************************************************************/
u16 TIM_GetICAP1(TIM_TypeDef *TIMx)
{
  return TIMx->ICR1;
}

/*******************************************************************************
* Function Name  : TIM_GetICAP2
* Description    : Gets the Input Capture 2 value.
* Input          : TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
* Output         : None
* Return         : Input Capture 2 Register value
*******************************************************************************/
u16 TIM_GetICAP2(TIM_TypeDef *TIMx)
{
  return TIMx->ICR2;
}

/*******************************************************************************
* Function Name  : TIM_GetPWMIPulse
* Description    : Gets the PWM Input pulse value.
* Input          : TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
* Output         : None
* Return         : Input Capture 2 Register value
*******************************************************************************/
u16 TIM_GetPWMIPulse(TIM_TypeDef *TIMx)
{
  return TIMx->ICR2;
}

/*******************************************************************************
* Function Name  : TIM_GetPWMIPeriod
* Description    : Gets the PWM Input period value.
* Input          : TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
* Output         : None
* Return         : Input Capture 1 Register value
*******************************************************************************/
u16 TIM_GetPWMIPeriod(TIM_TypeDef *TIMx)
{
  return TIMx->ICR1;
}

/*******************************************************************************
* Function Name  : TIM_DebugCmd
* Description    : Enables or disables the specified TIM peripheral Debug control.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
*                  - Newstate: new state of the TIMx Debug control.
                     This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DebugCmd(TIM_TypeDef *TIMx, FunctionalState Newstate)
{
  if(Newstate == ENABLE)
  {
    TIMx->CR |= TIM_DBGC_Set;
  }
  else
  {
    TIMx->CR &= TIM_DBGC_Reset;
  }
}

/*******************************************************************************
* Function Name  : TIM_CounterModeConfig
* Description    : Specifies the Counter Mode to be used.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_CounterMode: specifies the Counter Mode to be used
*                    This parameter can be one of the following values:
*                       - TIM_CounterMode_Up: TIM Up Counting Mode
*                       - TIM_CounterMode_Down: TIM Down Counting Mode
*                       - TIM_CounterMode_CenterAligned1: TIM Center Aligned Mode1
*                       - TIM_CounterMode_CenterAligned2: TIM Center Aligned Mode2
*                       - TIM_CounterMode_CenterAligned3: TIM Center Aligned Mode3
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_CounterModeConfig(TIM_TypeDef* TIMx, u16 TIM_CounterMode)
{
  /* Counter mode configuration */
  TIMx->CR &= TIM_CounterMode_Mask;
  TIMx->CR |= TIM_CounterMode;
}

/*******************************************************************************
* Function Name  : TIM_ForcedOCConfig
* Description    : Forces the TIM output waveform to active or inactive level.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_Channel: specifies the TIM channel to be used.
*                    This parameter can be one of the following values:
*                       - TIM_Channel_1: Timer Channel 1 is used
*                       - TIM_Channel_2: Timer Channel 2 is used
*                       - TIM_Channel_ALL: Timer Channel 1 and 2 are used
*                 - TIM_ForcedAction: specifies the forced Action to be set to
*                  the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM_ForcedAction_Active: Force active level on OCxREF
*                       - TIM_ForcedAction_InActive: Force inactive level on 
*                         OCxREF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ForcedOCConfig(TIM_TypeDef* TIMx, u16 TIM_Channel,u16 TIM_ForcedAction)
{
  /* Channel 1 Forced Output Compare mode configuration */
  if(TIM_Channel == TIM_Channel_1)
  {
    TIMx->OMR1 &= TIM_OC1C_Mask;
    TIMx->OMR1 |= TIM_ForcedAction;
  }
  /* Channel 2 Forced Output Compare mode configuration */
  else
  {
    if(TIM_Channel == TIM_Channel_2)
    {
      TIMx->OMR1 &= TIM_OC2C_Mask;
      TIMx->OMR1 |= (TIM_ForcedAction<<8);
    }
    /* Channel 1 and Channel 2 Forced Output Compare mode configuration */
    else
    {
      TIMx->OMR1 &= TIM_OC1C_Mask & TIM_OC2C_Mask;
      TIMx->OMR1 |= TIM_ForcedAction |(TIM_ForcedAction<<8);
    }
  }
}

/*******************************************************************************
* Function Name  : TIM_ResetCounter
* Description    : Re-intializes the TIM counter and generates an update of the
*                  registers.
* Input          : TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ResetCounter(TIM_TypeDef* TIMx)
{
  /* Re-intialize the TIM counter */
  TIMx->CR |= TIM_COUNTER_Reset;
}

/*******************************************************************************
* Function Name  : TIM_SynchroConfig
* Description    : Synchronizes two Timers in a specified mode.
* Input          : - Master: specifies the peripheral master.
*                    This parameter can be one of the following values:
*                    PWM_Master, TIM0_Master, TIM1_Master or TIM2_Master.
*                  - Slave: specifies the peripheral slave.
*                    This parameter can be one of the following values:
*                    PWM_Slave, TIM0_Slave, TIM1_Slave or TIM2_Slave.
*                  - TIM_SynchroAction: specifies the synchronization Action to 
*                    be used.
*                    This parameter can be one of the following values:
*                         - TIM_SynchroAction_Enable: The CNT_EN bit is used as TRGO
*                         - TIM_SynchroAction_Update: The Update event is used as TRGO
*                         - TIM_SynchroAction_Reset: The CNT_RST bit is used as TRGO
*                         - TIM_SynchroAction_OC: The OC1 signal is used as TRGO
*                  - TIM_SynchroMode: specifies the synchronization Mode to be used.
*                    This parameter can be one of the following values:
*                         - TIM_SynchroMode_Gated: Both start and stop of the 
*                           counter is controlled.
*                         - TIM_SynchroMode_Trigger: Only the start of the 
*                           counter is controlled.
*                         - TIM_SynchroMode_External: The rising edge of selected trigger 
*                           clocks the counter.
*                         - TIM_SynchroMode_Reset: The rising edge of the selected trigger 
*                           signal resets the counter and generates an update of the registers.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SynchroConfig(Master_TypeDef Master, Slave_TypeDef Slave,
                       u16 TIM_SynchroAction, u16 TIM_SynchroMode)
{
  switch (Slave)
  {
    case PWM_Slave:
    {
      PWM->SCR &= TIM_SME_Reset & TIM_TriggerSelection_Mask & TIM_SlaveModeSelection_Mask &
                  TIM_InternalTriggerSelection_Mask;
      PWM->SCR |= TIM_SynchroMode | TIM_SME_Set;

      if(Master == TIM1_Master)
      {
        /* Set the internal trigger */
      	PWM->SCR |= TIM_ITS_TIM1;

        /* Set the synchronization action */
        TIM1->CR &= TIM_MasterModeSelection_Mask;
        TIM1->CR |= TIM_SynchroAction;
      }

      else if(Master == TIM0_Master)
      {
        /* Set the internal trigger */
        PWM->SCR |= TIM_ITS_TIM0;

        /* Set the synchronization action */
        TIM0->CR &= TIM_MasterModeSelection_Mask;
        TIM0->CR |= TIM_SynchroAction;
      }

      else if(Master == TIM2_Master)
      {
        /* Set the internal trigger */
        PWM->SCR |= TIM_ITS_TIM2;

        /* Set the synchronization action */
        TIM2->CR &= TIM_MasterModeSelection_Mask;
        TIM2->CR |= TIM_SynchroAction;
      }
    }
    break;

    case TIM0_Slave:
    {
      TIM0->SCR &= TIM_SME_Reset & TIM_TriggerSelection_Mask & TIM_SlaveModeSelection_Mask &
                   TIM_InternalTriggerSelection_Mask;
      TIM0->SCR |= TIM_SynchroMode | TIM_SME_Set;

      if(Master == PWM_Master)
      {
        /* Set the internal trigger */
        TIM0->SCR |= TIM_ITS_PWM;

        /* Set the synchronization action */
        PWM->CR &= TIM_MasterModeSelection_Mask;
        PWM->CR |= TIM_SynchroAction;
      }

      else if(Master == TIM1_Master)
      {
        /* Set the internal trigger */
        TIM0->SCR |= TIM_ITS_TIM1;

        /* Set the synchronization action */
        TIM1->CR &= TIM_MasterModeSelection_Mask;
        TIM1->CR |= TIM_SynchroAction;
      }

      else if(Master == TIM2_Master)
      {
        /* Set the internal trigger */
        TIM0->SCR |= TIM_ITS_TIM2;

        /* Set the synchronization action */
        TIM2->CR &= TIM_MasterModeSelection_Mask;
        TIM2->CR |= TIM_SynchroAction;
      }
    }
    break;

    case TIM1_Slave:
    {

      TIM1->SCR &= TIM_SME_Reset & TIM_TriggerSelection_Mask & TIM_SlaveModeSelection_Mask &
                   TIM_InternalTriggerSelection_Mask;
      TIM1->SCR |= TIM_SynchroMode | TIM_SME_Set;
     
      if(Master == PWM_Master)
      {
      	 /* Set the internal trigger */
      	 TIM1->SCR |= TIM_ITS_PWM;

        /* Set the synchronization action */
        PWM->CR &= TIM_MasterModeSelection_Mask;
        PWM->CR |= TIM_SynchroAction;
      }
      else if(Master == TIM0_Master)
      {
        /* Set the internal trigger */
        TIM1->SCR |= TIM_ITS_TIM0;

        /* Set the synchronization action */
        TIM0->CR &= TIM_MasterModeSelection_Mask;
        TIM0->CR |= TIM_SynchroAction;
      }

      else if(Master == TIM2_Master)
      {
        /* Set the internal trigger */
        TIM1->SCR |= TIM_ITS_TIM2;

        /* Set the synchronization action */
        TIM2->CR &= TIM_MasterModeSelection_Mask;
        TIM2->CR |= TIM_SynchroAction;
      }
    }
    break;

    case TIM2_Slave:
    {
     
      TIM2->SCR &= TIM_SME_Reset & TIM_TriggerSelection_Mask & TIM_SlaveModeSelection_Mask &
                   TIM_InternalTriggerSelection_Mask;
      TIM2->SCR |= TIM_SynchroMode | TIM_SME_Set;

      if(Master == PWM_Master)
      {
        /* Internal trigger selection */
        TIM2->SCR |= TIM_ITS_PWM;

        /* Set the synchronization action */
        PWM->CR &= TIM_MasterModeSelection_Mask;
        PWM->CR |= TIM_SynchroAction;
      }

      else if(Master == TIM1_Master)
      {
        /* Internal trigger selection */
        TIM2->SCR |= TIM_ITS_TIM1;

        /* Set the synchronization action */
        TIM1->CR &= TIM_MasterModeSelection_Mask;
        TIM1->CR |= TIM_SynchroAction;
      }

      else if(Master == TIM0_Master)
      {
        /* Internal trigger selection */
        TIM2->SCR |= TIM_ITS_TIM0;

        /* Set the synchronization action */
        TIM0->CR &= TIM_MasterModeSelection_Mask;
        TIM0->CR |= TIM_SynchroAction;
      }
    }
    break;

    default:
    break;
  }
}

/*******************************************************************************
* Function Name  : TIM_GetFlagStatus
* Description    : Checks whether the specified TIM flag is set or not.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_FLAG: specifies the flag to check. 
*                    This parameter can be one of the following values:
*                         - TIM_FLAG_IC1: Input Capture 1 Flag
*                         - TIM_FLAG_OC1: Output Compare 1 Flag
*                         - TIM_FLAG_Update: Timer update Flag
*                         - TIM_FLAG_IC2: Input Capture 2 Flag
*                         - TIM_FLAG_OC2: Output Compare 2 Flag
* Output         : None
* Return         : The new state of TIM_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus TIM_GetFlagStatus(TIM_TypeDef* TIMx, u16 TIM_FLAG)
{
  if((TIMx->ISR & TIM_FLAG) != RESET )
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : TIM_ClearFlag
* Description    : Clears the TIMx's pending flags.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_FLAG: specifies the flag bit to clear.
*                    This parameter can be any combination of the following values:
*                         - TIM_FLAG_IC1: Timer Input Capture 1 flag
*                         - TIM_FLAG_OC1: Timer Output Compare 1 flag
*                         - TIM_FLAG_Update: Timer update flag
*                         - TIM_FLAG_IC2: Timer Input Capture 2 flag
*                         - TIM_FLAG_OC2: Timer Output Compare 2 flag
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ClearFlag(TIM_TypeDef* TIMx, u16 TIM_FLAG)
{
  /* Clear the flags */
  TIMx->ISR &= ~TIM_FLAG;
}

/*******************************************************************************
* Function Name  : TIM_GetITStatus
* Description    : Checks whether the specified TIM interrupt has occurred or not.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_IT: specifies the TIM interrupt source to check.
*                    This parameter can be one of the following values:
*                         - TIM_IT_IC1: Input Capture 1 interrupt
*                         - TIM_IT_OC1: Output Compare 1 interrupt
*                         - TIM_IT_Update: Timer update interrupt
*                         - TIM_IT_GlobalUpdate: Timer global update interrupt
*                         - TIM_IT_IC2: Input Capture 2 interrupt
*                         - TIM_IT_OC2: Output Compare 2 interrupt
* Output         : None
* Return         : The new state of TIM_IT(SET or RESET).
*******************************************************************************/
ITStatus TIM_GetITStatus(TIM_TypeDef* TIMx, u16 TIM_IT)
{
  u16 TIM_IT_Check = 0;

  /* Calculates the pending bits to be checked */
  TIM_IT_Check = TIM_IT & TIM_IT_Clear_Mask;
  
  if((TIMx->ISR & TIM_IT_Check) != RESET )
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : TIM_ClearITPendingBit
* Description    : Clears the TIM's interrupt pending bits.
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral.
*                  - TIM_IT: specifies the interrupt pending bit to clear.
*                    This parameter can be one of the following values:
*                         - TIM_IT_IC1: Input Capture 1 Interrupt 
*                         - TIM_IT_OC1: Output Compare 1 Interrupt 
*                         - TIM_IT_Update: Timer update Interrupt 
*                         - TIM_IT_GlobalUpdate: Timer global update Interrupt 
*                         - TIM_IT_IC2: Input Capture 2 Interrupt 
*                         - TIM_IT_OC2: Output Compare 2 Interrupt 
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ClearITPendingBit(TIM_TypeDef* TIMx, u16 TIM_IT)
{
  u16 TIM_IT_Clear = 0;

  /* Calculate the pending bits to be cleared */
  TIM_IT_Clear = TIM_IT & TIM_IT_Clear_Mask;

  /* Clear the pending bits */
  TIMx->ISR &= ~TIM_IT_Clear;
}

/*******************************************************************************
* Function Name  : OCM_ModuleConfig
* Description    : Output Compare Module configuration
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
*                  - TIM_InitStruct: pointer to a TIM_InitTypeDef structure that
*                  contains the configuration information for the specified TIM
*                  peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
static void OCM_ModuleConfig(TIM_TypeDef* TIMx, TIM_InitTypeDef* TIM_InitStruct)
{
  u16 TIM_OCControl = 0x0000;

  if(TIM_InitStruct->TIM_Mode == TIM_Mode_OCTiming)
  {
    TIM_OCControl = TIM_OCControl_OCTiming;
  }
  else
  {
    if((TIM_InitStruct->TIM_Mode == TIM_Mode_OCActive) || 
       (TIM_InitStruct->TIM_Mode == TIM_Mode_OPM_Active))
    {
      TIM_OCControl = TIM_OCControl_OCActive;
    }
    else
    {
      if(TIM_InitStruct->TIM_Mode == TIM_Mode_OCInactive)
      {
        TIM_OCControl = TIM_OCControl_OCInactive;
      }
      else
      {
      	 if((TIM_InitStruct->TIM_Mode == TIM_Mode_OCToggle) ||
            (TIM_InitStruct->TIM_Mode == TIM_Mode_OPM_Toggle))
        {
          TIM_OCControl = TIM_OCControl_OCToggle;
        }
        else
        {
          TIM_OCControl = TIM_OCControl_PWM;

        }
      }
    }
  }

  if(TIM_InitStruct->TIM_Channel == TIM_Channel_1)
  {
    /* Configure Channel 1 on Output Compare mode */
    TIMx->OMR1 &= TIM_OC1C_Mask;
    TIMx->OMR1 |= TIM_OCControl|TIM_OC1_Enable;
    TIMx->OMR1 |= TIM_PLD1_Set;
    TIMx->OCR1 = TIM_InitStruct->TIM_Pulse1;

    /* Set the OC1 wave polarity */
    if(TIM_InitStruct->TIM_Polarity1 == TIM_Polarity1_Low)
    {
      TIMx->OMR1 |= TIM_OC1P_Set;
    }
    else
    {
      TIMx->OMR1 &= TIM_OC1P_Reset;
    }
  }
  else
  {
    if(TIM_InitStruct->TIM_Channel == TIM_Channel_2)
    {
      /* Configure Channel 2 on Output Compare mode */
      TIMx->OMR1 &= TIM_OC2C_Mask;
      TIMx->OMR1 |= TIM_OCControl<<8|TIM_OC2_Enable;
      TIMx->OMR1 |= TIM_PLD2_Set;
      TIMx->OCR2 = TIM_InitStruct->TIM_Pulse2;

      /* Set the OCB wave polarity */
      if(TIM_InitStruct->TIM_Polarity2 == TIM_Polarity2_Low)
      {
        TIMx->OMR1 |= TIM_OC2P_Set;
      }
      else
      {
        TIMx->OMR1 &= TIM_OC2P_Reset;
      }
    }
     /* Configure Channel 1 and Channel 2 on Output Compare mode */
    else
    {
      TIMx->OMR1 &= TIM_OC1C_Mask & TIM_OC2C_Mask; 
      TIMx->OMR1 |= TIM_OCControl|(TIM_OCControl<<8)|TIM_OC1_Enable|TIM_OC2_Enable|
                   TIM_PLD1_Set|TIM_PLD2_Set;

      TIMx->OCR1 = TIM_InitStruct->TIM_Pulse1;
      TIMx->OCR2 = TIM_InitStruct->TIM_Pulse2;

      /* Set the OC1 wave polarity */
      if(TIM_InitStruct->TIM_Polarity1 == TIM_Polarity1_Low)
      {
        TIMx->OMR1 |= TIM_OC1P_Set;
      }
      else
      {
        TIMx->OMR1 &= TIM_OC1P_Reset;
      }

      /* Set the OC2 wave polarity */
      if(TIM_InitStruct->TIM_Polarity2 == TIM_Polarity2_Low)
      {
        TIMx->OMR1 |= TIM_OC2P_Set;
      }
      else
      {
        TIMx->OMR1 &= TIM_OC2P_Reset;
      }
    }
  }
}

/*******************************************************************************
* Function Name  : ICAP_ModuleConfig
* Description    : Input Capture Module configuration
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
*                  - TIM_InitStruct: pointer to a TIM_InitTypeDef structure that
*                  contains the configuration information for the specified TIM
*                  peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
static void ICAP_ModuleConfig(TIM_TypeDef* TIMx, TIM_InitTypeDef* TIM_InitStruct)
{
  if(TIM_InitStruct->TIM_Mode == TIM_Mode_PWMI)
  { /* PWM input mode configuration */
    TIMx->SCR |= TIM_TS_IC1_Set|TIM_SMS_RESETCLK_Set|TIM_SME_Set;

    /* Channel 1 and channel 2 input selection */
    if(TIM_InitStruct->TIM_PWMI_ICSelection == TIM_PWMI_ICSelection_TI1)
    {
      TIMx->IMCR &= TIM_IC1S_Reset;
      TIMx->IMCR |= TIM_IC2S_Set;
    }
    else
    {
      TIMx->IMCR |= TIM_IC1S_Set;
      TIMx->IMCR &= TIM_IC2S_Reset;
    }

    /* Channel polarity */
    if(TIM_InitStruct->TIM_PWMI_ICPolarity == TIM_PWMI_ICPolarity_Rising)
    {
      TIMx->IMCR &= TIM_IC1P_Reset;
      TIMx->IMCR |= TIM_IC2P_Set;
    }
    else
    {
      TIMx->IMCR |= TIM_IC1P_Set;
      TIMx->IMCR &= TIM_IC2P_Reset;
    }

    /* Input capture  Enable */
    TIMx->IMCR |= TIM_IC1_Enable |TIM_IC2_Enable;
  }
  else
  {
    if(TIM_InitStruct->TIM_Channel == TIM_Channel_1)
    {
      /* Input Capture 1 mode configuration */
      TIMx->SCR &= TIM_TriggerSelection_Mask & TIM_SlaveModeSelection_Mask;
      TIMx->SCR |= TIM_TS_IC1_Set|TIM_SMS_RESETCLK_Set|TIM_SME_Set;
      
      /* Channel 1 input selection */
      if(TIM_InitStruct->TIM_IC1Selection == TIM_IC1Selection_TI1)
      {
        TIMx->IMCR &= TIM_IC1S_Reset;
      }
      else
      {
        TIMx->IMCR |= TIM_IC1S_Set;
      }
      /* Channel 1 polarity */
      if(TIM_InitStruct->TIM_IC1Polarity == TIM_IC1Polarity_Rising)
      {
        TIMx->IMCR &= TIM_IC1P_Reset;
      }
      else
      {
        TIMx->IMCR |= TIM_IC1P_Set;
      }

      /* Input capture  Enable */
      TIMx->IMCR |= TIM_IC1_Enable;
    }
    else
    {
      /* Input Capture 2 mode configuration */
      TIMx->SCR &= (TIM_TriggerSelection_Mask & TIM_SlaveModeSelection_Mask);
      TIMx->SCR |= TIM_TS_IC2_Set|TIM_SMS_RESETCLK_Set|TIM_SME_Set;

      /* Channel 2 input selection */
      if(TIM_InitStruct->TIM_IC2Selection == TIM_IC2Selection_TI2)
      {
        TIMx->IMCR &= TIM_IC2S_Reset;
      }
      else
      {
        TIMx->IMCR |= TIM_IC2S_Set;
      }

      /* Channel 2 polarity */
      if(TIM_InitStruct->TIM_IC2Polarity == TIM_IC2Polarity_Rising)
      {
        TIMx->IMCR &= TIM_IC2P_Reset;
      }
      else
      {
        TIMx->IMCR |= TIM_IC2P_Set;
      }

      /* Input capture  Enable */
      TIMx->IMCR |= TIM_IC2_Enable;
    }
  }
}

/*******************************************************************************
* Function Name  : Encoder_ModeConfig
* Description    : Encoder Mode configuration
* Input          : - TIMx: where x can be 0, 1 or 2 to select the TIM peripheral
*                  - TIM_InitStruct: pointer to a TIM_InitTypeDef structure that
*                  contains the configuration information for the specified TIM
*                  peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
static void Encoder_ModeConfig(TIM_TypeDef* TIMx, TIM_InitTypeDef* TIM_InitStruct)
{
  /* Set Encoder mode */
  TIMx->SCR &= TIM_Encoder_Mask;
  
  if(TIM_InitStruct->TIM_Mode == TIM_Mode_Encoder1) 
  {
    TIMx->SCR |= TIM_Encoder1_Set;
  }
  else if (TIM_InitStruct->TIM_Mode == TIM_Mode_Encoder2)
  {
    TIMx->SCR |= TIM_Encoder2_Set;
  }
  else 
  {
    TIMx->SCR |= TIM_Encoder3_Set;
  }

  /* Channel 1 input selection */
  if(TIM_InitStruct->TIM_IC1Selection == TIM_IC1Selection_TI2)
  {
    TIMx->IMCR |= TIM_IC1S_Set;
  }
  else
  {
    TIMx->IMCR &= TIM_IC1S_Reset;
  }

   /* Channel 2 input selection */
   if(TIM_InitStruct->TIM_IC2Selection == TIM_IC2Selection_TI1)
   {
     TIMx->IMCR |= TIM_IC2S_Set;
   }
   else
   {
     TIMx->IMCR &= TIM_IC2S_Reset;
   }

   /* Channel 1 polarity */
   if(TIM_InitStruct->TIM_IC1Polarity == TIM_IC1Polarity_Falling)
   {
     TIMx->IMCR |= TIM_IC1P_Set;
   }
   else
   {
     TIMx->IMCR &= TIM_IC1P_Reset;
   }

   /* Channel 2 polarity */
   if(TIM_InitStruct->TIM_IC2Polarity == TIM_IC2Polarity_Falling)
   {
     TIMx->IMCR |= TIM_IC2P_Set;
   }
   else
   {
     TIMx->IMCR &= TIM_IC2P_Reset;
   }
}
/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
