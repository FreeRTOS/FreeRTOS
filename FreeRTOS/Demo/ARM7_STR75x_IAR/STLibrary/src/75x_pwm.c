/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_pwm.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the PWM software functions.
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
#include "75x_pwm.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* PWM interrupt masks */
#define PWM_IT_Clear_Mask    0x7FFF
#define PWM_IT_Enable_Mask   0xEFFF

/* PWM_CR Masks bit */
#define PWM_CounterMode_Mask           0xFF8F
#define PWM_DBASE_Mask                 0x077F
#define PWM_MasterModeSelection_Mask   0xFC7F

/* PWM Update flag selection Set/Reset value */
#define PWM_UFS_Reset 0xFFFE
#define PWM_UFS_Set   0x0001

/* PWM Counter value */
#define PWM_COUNTER_Reset  0x0002
#define PWM_COUNTER_Start  0x0004
#define PWM_COUNTER_Stop   0xFFFB

/* PWM Debug Mode Set/Reset value */
#define PWM_DBGC_Set    0x0400
#define PWM_DBGC_Reset  0xFBFF

/* PWM Output Compare Polarity Set/Reset value */
#define PWM_OC1P_Set    0x0020
#define PWM_OC1P_Reset  0xFFDF

#define PWM_OC1NP_Set    0x0080
#define PWM_OC1NP_Reset  0xFF7F

#define PWM_OC2P_Set    0x2000
#define PWM_OC2P_Reset  0xDFFF

#define PWM_OC2NP_Set    0x8000
#define PWM_OC2NP_Reset  0x7FFF

#define PWM_OC3P_Set     0x0020
#define PWM_OC3P_Reset   0xFFDF

#define PWM_OC3NP_Set    0x0080
#define PWM_OC3NP_Reset  0xFF7F

/* PWM Output Compare control mode constant */
#define PWM_OCControl_PWM         0x000C
#define PWM_OCControl_OCToggle    0x0006
#define PWM_OCControl_OCInactive  0x0004
#define PWM_OCControl_OCActive    0x0002
#define PWM_OCControl_OCTiming    0x0000

/* PWM Output Compare mode Enable value */
#define PWM_OC1_Enable  0x0010
#define PWM_OC2_Enable  0x1000
#define PWM_OC3_Enable  0x0010

#define PWM_OC1_Disable  0xFFEF
#define PWM_OC2_Disable  0xEFFF
#define PWM_OC3_Disable  0xFFEF

#define PWM_OC1N_Enable  0x0040
#define PWM_OC2N_Enable  0x4000
#define PWM_OC3N_Enable  0x0040

#define PWM_OC1N_Disable  0xFFBF
#define PWM_OC2N_Disable  0xBFFF
#define PWM_OC3N_Disable  0xFFBF

/* PWM Output Compare mode Mask value */
#define PWM_OC1C_Mask  0xFFF1
#define PWM_OC2C_Mask  0xF1FF
#define PWM_OC3C_Mask  0xFFF1

/* PWM Preload bit Set/Reset value */
#define PWM_PLD1_Set    0x0001
#define PWM_PLD2_Set   0x0100
#define PWM_PLD3_Set   0x0001

/* PWM OCRM Set/Reset value */
#define PWM_OCMR_Set    0x0080
#define PWM_OCMR_Reset  0xFF7F

/* PWM_DTR bit Masks value */
#define PWM_DTR_Mask   0xFC00
#define PWM_LOCK_Mask  0xF3FF

/* PWM MOE Set value */
#define PWM_MOE_Set    0x8000
#define PWM_MOE_Reset  0x7FFF

/* PWM OSSR bit Set/Reset value */
#define PWM_OSSR_Set    0x4000
#define PWM_OSSR_Reset  0xBFFF

/* Reset Register Masks */
#define PWM_Prescaler_Reset_Mask          0x0000
#define PWM_Pulse1_Reset_Mask             0x0000
#define PWM_Pulse2_Reset_Mask             0x0000
#define PWM_Pulse3_Reset_Mask             0x0000
#define PWM_Period_Reset_Mask             0xFFFF
#define PWM_RepetitionCounter_Reset_Mask  0x0000
#define PWM_DeadTime_Reset_Mask           0x0000

/* Private function prototypes -----------------------------------------------*/
static void OCM_ModuleConfig(PWM_InitTypeDef* PWM_InitStruct);

/* Private functions ---------------------------------------------------------*/

/******************************************************************************
* Function Name  : PWM_DeInit
* Description    : Deinitializes PWM peripheral registers to their default reset
*                  values.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_DeInit(void)
{
  /* Enters and exits the PWM peripheral to and from reset */
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_PWM,ENABLE);
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_PWM,DISABLE);
}

/*******************************************************************************
* Function Name  : PWM_Init
* Description    : Initializes the PWM peripheral according to the specified
*                  parameters in the PWM_InitStruct .
* Input          : PWM_InitStruct: pointer to a PWM_InitTypeDef structure that
*                  contains the configuration information for the PWM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_Init(PWM_InitTypeDef* PWM_InitStruct)
{
  /* Sets the prescaler value */
  PWM->PSC = PWM_InitStruct->PWM_Prescaler;

  /* Selects the counter mode */
  PWM->CR &= PWM_CounterMode_Mask;
  PWM->CR |= PWM_InitStruct->PWM_CounterMode;

  /* Sets the period value */
  PWM->ARR = PWM_InitStruct->PWM_Period;
  
  /* Sets the repetition counter */
  PWM->RCR &= PWM_RepetitionCounter_Reset_Mask;
  PWM->RCR |= PWM_InitStruct->PWM_RepetitionCounter;
  
  /* Configures the PWM according to the PWM_InitTypeDef structure parameters */
  OCM_ModuleConfig(PWM_InitStruct);
}

/*******************************************************************************
* Function Name  : PWM_StructInit
* Description    : Fills each PWM_InitStruct member with its default value.
* Input          : PWM_InitStruct : pointer to a PWM_InitTypeDef structure which
*                  will be initialized.
* Output         : None                        
* Return         : None.
*******************************************************************************/
void PWM_StructInit(PWM_InitTypeDef *PWM_InitStruct)
{
  /* Sets the default configuration */
  PWM_InitStruct->PWM_Mode = PWM_Mode_OCTiming;
  PWM_InitStruct->PWM_Prescaler = PWM_Prescaler_Reset_Mask;
  PWM_InitStruct->PWM_CounterMode = PWM_CounterMode_Up;
  PWM_InitStruct->PWM_Period = PWM_Period_Reset_Mask;
  PWM_InitStruct->PWM_Complementary = PWM_Complementary_Disable;
  PWM_InitStruct->PWM_OCState = PWM_OCState_Disable;
  PWM_InitStruct->PWM_OCNState = PWM_OCNState_Disable;
  PWM_InitStruct->PWM_Channel = PWM_Channel_1;
  PWM_InitStruct->PWM_Pulse1 = PWM_Pulse1_Reset_Mask;
  PWM_InitStruct->PWM_Pulse2 = PWM_Pulse2_Reset_Mask;
  PWM_InitStruct->PWM_Pulse3 = PWM_Pulse3_Reset_Mask;
  PWM_InitStruct->PWM_Polarity1 = PWM_Polarity1_High;
  PWM_InitStruct->PWM_Polarity2 = PWM_Polarity2_High;
  PWM_InitStruct->PWM_Polarity3 = PWM_Polarity3_High;
  PWM_InitStruct->PWM_Polarity1N = PWM_Polarity1N_High;
  PWM_InitStruct->PWM_Polarity2N = PWM_Polarity2N_High;
  PWM_InitStruct->PWM_Polarity3N = PWM_Polarity3N_High;
  PWM_InitStruct->PWM_DTRAccess = PWM_DTRAccess_Disable;
  PWM_InitStruct->PWM_DeadTime = PWM_DeadTime_Reset_Mask;
  PWM_InitStruct->PWM_Emergency = PWM_Emergency_Disable;
  PWM_InitStruct->PWM_LOCKLevel = PWM_LOCKLevel_OFF;
  PWM_InitStruct->PWM_OSSIState = PWM_OSSIState_Disable;
  PWM_InitStruct->PWM_RepetitionCounter = PWM_RepetitionCounter_Reset_Mask;
}

/*******************************************************************************
* Function Name  : PWM_Cmd
* Description    : Enables or disables the PWM peripheral.
* Input          : Newstate: new state of the PWM peripheral.
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_Cmd(FunctionalState Newstate)
{
 if(Newstate == ENABLE)
  {
    PWM->CR |= PWM_COUNTER_Start;
  }
  else
  {
    PWM->CR &= PWM_COUNTER_Stop;
  }
}

/*******************************************************************************
* Function Name  : PWM_CtrlPWMOutputs
* Description    : Enables or disables PWM peripheral Main Outputs.
* Input          : Newstate: new state of the PWM peripheral Main Outputs. 
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_CtrlPWMOutputs(FunctionalState Newstate)
{
 if(Newstate == ENABLE)
  {
    PWM->DTR |= PWM_MOE_Set;
  }
  else
  {
    PWM->DTR &= PWM_MOE_Reset;
  }
}

/*******************************************************************************
* Function Name  : PWM_ITConfig
* Description    : Enables or disables the PWM interrupts.
* Input          : - PWM_IT: specifies the PWM interrupts sources to be enabled
*                    or disabled.
*                    This parameter can be any combination of the following values:
*                         - PWM_IT_OC1: PWM Output Compare 1 Interrupt source
*                         - PWM_IT_OC2: PWM Output Compare 2 Interrupt source
*                         - PWM_IT_OC3: PWM Output Compare 3 Interrupt source
*                         - PWM_IT_Update: PWM update Interrupt source
*                         - PWM_IT_Emergency: PWM Emergency interrupt source
*                         - PWM_IT_GlobalUpdate: PWM global update Interrupt
*                           source
*                  - Newstate: new state of PWM interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_ITConfig(u16 PWM_IT, FunctionalState Newstate)
{ 
  u16 PWM_IT_Enable = 0;

  PWM_IT_Enable = PWM_IT & PWM_IT_Enable_Mask;

  if(Newstate == ENABLE)
  {
    /* Update interrupt global source: overflow/undeflow, counter reset operation
    or slave mode controller in reset mode */
    if ((PWM_IT & PWM_IT_GlobalUpdate) == PWM_IT_GlobalUpdate)
    {
      PWM->CR &= PWM_UFS_Reset;
    }
    /* Update interrupt source: counter overflow/underflow */
    else if ((PWM_IT & PWM_IT_Update) == PWM_IT_Update)
    {
      PWM->CR |= PWM_UFS_Set;
    }
    /* Select and enable the interrupts requests */
    PWM->RSR |= PWM_IT_Enable;
    PWM->RER |= PWM_IT_Enable;
  }
  /* Disable the interrupts requests */
  else
  {
    PWM->RSR &= ~PWM_IT_Enable;
    PWM->RER &= ~PWM_IT_Enable;
  }
}

/*******************************************************************************
* Function Name  : PWM_DMAConfig
* Description    : Configures the PWM’s DMA interface.
* Input          : - PWM_DMASources: specifies the DMA Request sources.
*                    This parameter can be any combination of the following values:
*                         - PWM_DMASource_OC1: PWM Output Compare 1 DMA source
*                         - PWM_DMASource_OC2: PWM Output Compare 2 DMA source
*                         - PWM_DMASource_OC3: PWM Output Compare 3 DMA source
*                         - PWM_DMASource_Update: PWM Update DMA source
*                  - PWM_OCRMState: the state of output compare request mode.
*                    This parameter can be one of the following values:
*                         - PWM_OCRMState_Enable 
*                         - PWM_OCRMState_Disable 
*                  - PWM_DMABase:DMA Base address.
*                    This parameter can be one of the following values:
*                    PWM_DMABase_CR, PWM_DMABase_SCR, PWM_DMABase_OMR1, 
*                    PWM_DMABase_OMR2, PWM_DMABase_RSR, PWM_DMABase_RER, 
*                    PWM_DMABase_ISR, PWM_DMABase_CNT, PWM_DMABase_PSC,
*                    PWM_DMABase_RCR, PWM_DMABase_ARR, PWM_DMABase_OCR1,
*                    PWM_DMABase_OCR2, PWM_DMABase_OCR3 ,PWM_DMABase_DTR.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_DMAConfig(u16 PWM_DMASources, u16 PWM_OCRMState, u16 PWM_DMABase)
{
  /* Select the DMA requests */
  PWM->RSR &= ~PWM_DMASources;
  
  /* Sets the OCRM state */
  if(PWM_OCRMState == PWM_OCRMState_Enable)
  {
    PWM->RSR |= PWM_OCMR_Set;
  }
  else
  {
    PWM->RSR &= PWM_OCMR_Reset;
  }

  /* Sets the DMA Base address */
  PWM->CR &= PWM_DBASE_Mask;
  PWM->CR |= PWM_DMABase;
}

/*******************************************************************************
* Function Name  : PWM_DMACmd
* Description    : Enables or disables the PWM’s DMA interface.
* Input          : - PWM_DMASources: specifies the DMA Request sources.
*                    This parameter can be any combination of the following values:
*                         - PWM_DMASource_OC1: PWM Output Compare 1 DMA source
*                         - PWM_DMASource_OC2: PWM Output Compare 2 DMA source
*                         - PWM_DMASource_OC3: PWM Output Compare 3 DMA source
*                         - PWM_DMASource_Update: PWM Update DMA source
*                  - Newstate: new state of the DMA Request sources.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_DMACmd(u16 PWM_DMASources, FunctionalState Newstate)
{
  if(Newstate == ENABLE)
  {
    PWM->RER |= PWM_DMASources;
  }
  else
  {
    PWM->RER &= ~PWM_DMASources;
  }
}

/*******************************************************************************
* Function Name  : PWM_SetPrescaler
* Description    : Sets the PWM prescaler value.
* Input          : Prescaler: PWM prescaler new value.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_SetPrescaler(u16 Prescaler)
{
  PWM->PSC = Prescaler;
}

/*******************************************************************************
* Function Name  : PWM_SetPeriod
* Description    : Sets the PWM period value.
* Input          : Period: PWM period new value.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_SetPeriod(u16 Period)
{
  PWM->ARR = Period;
}

/*******************************************************************************
* Function Name  : PWM_SetPulse
* Description    : Sets the PWM pulse value.
* Input          : - PWM_Channel: specifies the PWM channel to be used.
*                    This parameter can be one of the following values:
*                         - PWM_Channel_1: PWM Channel 1 is used
*                         - PWM_Channel_2: PWM Channel 2 is used
*                         - PWM_Channel_3: PWM Channel 3 is used
*                         - PWM_Channel_ALL: PWM Channel 1, Channel 2 and 3 are used
*                  - Pulse: PWM pulse new value.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_SetPulse(u16 PWM_Channel, u16 Pulse)
{
  /* Sets Channel 1 pulse value */
  if(PWM_Channel == PWM_Channel_1)
  {
    PWM->OCR1 = Pulse;
  }
  /* Sets Channel 2 pulse value */
  else if(PWM_Channel == PWM_Channel_2)
  {
    PWM->OCR2 = Pulse;
  }
  /* Sets Channel 3 pulse value */
  else if(PWM_Channel == PWM_Channel_3)
  {
    PWM->OCR3 = Pulse;
  }
  /* Sets Channel 1, Channel 2 and Channel 3 pulse values */
  else if(PWM_Channel == PWM_Channel_ALL)
  {
    PWM->OCR1 = Pulse;
    PWM->OCR2 = Pulse;
    PWM->OCR3 = Pulse;
  }
}

/*******************************************************************************
* Function Name  : PWM_SetPulse1
* Description    : Sets the PWM Channel 1 pulse value.
* Input          : - Pulse: PWM Channel 1 pulse new value.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_SetPulse1(u16 Pulse)
{
  PWM->OCR1 = Pulse;
}

/*******************************************************************************
* Function Name  : PWM_SetPulse2
* Description    : Sets the PWM Channel 2 pulse value.
* Input          : - Pulse: PWM Channel 2 pulse new value.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_SetPulse2(u16 Pulse)
{
  PWM->OCR2 = Pulse;
}

/*******************************************************************************
* Function Name  : PWM_SetPulse3
* Description    : Sets the PWM Channel 3 pulse value.
* Input          : - Pulse: PWM Channel 3 pulse new value.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_SetPulse3(u16 Pulse)
{
  PWM->OCR3 = Pulse;
}

/*******************************************************************************
* Function Name  : PWM_DebugCmd
* Description    : Enables or disables PWM peripheral Debug control.
* Input          : Newstate: new state of the PWM Debug control.
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_DebugCmd(FunctionalState Newstate)
{
  if(Newstate == ENABLE)
  {
    PWM->CR |= PWM_DBGC_Set;
  }
  else
  {
    PWM->CR &= PWM_DBGC_Reset;
  }
}

/*******************************************************************************
* Function Name  : PWM_CounterModeConfig
* Description    : Specifies the Counter Mode to be used.
* Input          : PWM_CounterMode: specifies the Counter Mode to be used
*                  This parameter can be one of the following values:
*                         - PWM_CounterMode_Up: PWM Up Counting Mode
*                         - PWM_CounterMode_Down: PWM Down Counting Mode
*                         - PWM_CounterMode_CenterAligned1: PWM Center Aligned1 Mode
*                         - PWM_CounterMode_CenterAligned2: PWM Center Aligned2 Mode
*                         - PWM_CounterMode_CenterAligned3: PWM Center Aligned3 Mode
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_CounterModeConfig(u16 PWM_CounterMode)
{
  /* Counter mode configuration */
  PWM->CR &= PWM_CounterMode_Mask;
  PWM->CR |= PWM_CounterMode;
}

/*******************************************************************************
* Function Name  : PWM_ForcedOCConfig
* Description    : Forces the PWM output waveform to active or inactive level.
* Input          : - PWM_Channel: specifies the PWM channel to be used.
*                    This parameter can be one of the following values:
*                         - PWM_Channel_1: PWM Channel 1 is used
*                         - PWM_Channel_2: PWM Channel 2 is used
*                         - PWM_Channel_3: PWM Channel 3 is used
*                         - PWM_Channel_ALL: PWM Channel 1, Channel 2 and 3 are used
*                  - PWM_ForcedAction: specifies the forced Action to be set to the
*                    output waveform.
*                    This parameter can be one of the following values:
*                         - PWM_ForcedAction_Active: Force active level on OCxREF
*                         - PWM_ForcedAction_InActive: Force inactive level on 
*                           OCxREF
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_ForcedOCConfig(u16 PWM_Channel, u16 PWM_ForcedAction)
{
  /* Channel 1 Forced Output Compare mode configuration */
  if(PWM_Channel == PWM_Channel_1)
  {
    PWM->OMR1 &= PWM_OC1C_Mask;
    PWM->OMR1 |= PWM_ForcedAction;
  }
  /* Channel 2 Forced Output Compare mode configuration */
  else
  {
    if(PWM_Channel == PWM_Channel_2)
    {
      PWM->OMR1 &= PWM_OC2C_Mask;
      PWM->OMR1 |= (PWM_ForcedAction<<8);
    }
    else
    {
      /* Channel 3 Forced Output Compare mode configuration */
      if(PWM_Channel == PWM_Channel_3)
      {
        PWM->OMR2 &= PWM_OC3C_Mask;
        PWM->OMR2 |= PWM_ForcedAction;
      }
      /* Channel 1, Channel 2 and Channel 3 Forced Output Compare mode 
      configuration */
      else
      {
        PWM->OMR1 &= PWM_OC1C_Mask;
        PWM->OMR1 |= PWM_ForcedAction;

        PWM->OMR1 &= PWM_OC2C_Mask;
        PWM->OMR1 |= (PWM_ForcedAction<<8);
        
        PWM->OMR2 &= PWM_OC3C_Mask;
        PWM->OMR2 |= PWM_ForcedAction;
      }
    }
  }
}

/*******************************************************************************
* Function Name  : PWM_SetDeadTime
* Description    : Inserts dead time between the OCx and OCNx.
* Input          : DeadTime: PWM Dead Time value.
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_SetDeadTime(u16 DeadTime)
{
  /* Sets the dead time value */
  PWM->DTR &= PWM_DTR_Mask;
  PWM->DTR |= DeadTime;
}

/*******************************************************************************
* Function Name  : PWM_ResetCounter
* Description    : Re-intializes the PWM counter and generates an update of the
*                  registers.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_ResetCounter(void)
{
  /* Resets the PWM counter */
  PWM->CR |= PWM_COUNTER_Reset;
}

/*******************************************************************************
* Function Name  : PWM_TRGOSelection
* Description    : Sets the PWM Master Mode selection bits.
* Input          : PWM_TRGOMode: specifies the TRGO source.
*                  This parameter can be one of the following values:
*                         - PWM_TRGOMode_Enable: The CNT_EN bit is used as TRGO
*                         - PWM_TRGOMode_Update: The Update event is used as TRGO
*                         - PWM_TRGOMode_Reset: The CNT_RST bit is used as TRGO
*                         - PWM_TRGOMode_OC: The OC1 signal is used as TRGO
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_TRGOSelection(u16 PWM_TRGOMode)
{
  /* Sets the synchronization action */
  PWM->CR &= PWM_MasterModeSelection_Mask;
  PWM->CR |= PWM_TRGOMode;
}

/*******************************************************************************
* Function Name  : PWM_GetFlagStatus
* Description    : Checks whether the specified PWM flag is set or not.
* Input          : PWM_FLAG: specifies the flag to check.
*                  This parameter can be one of the following values:
*                         - PWM_FLAG_OC1: Output Compare 1 Flag
*                         - PWM_FLAG_OC2: Output Compare 2 Flag
*                         - PWM_FLAG_OC3: Output Compare 3 Flag
*                         - PWM_FLAG_Update: PWM update Flag
*                         - PWM_FLAG_Emergency: PWM Emergency Flag
* Output         : None
* Return         : The new state of the PWM_FLAG(SET or RESET).
*******************************************************************************/
FlagStatus PWM_GetFlagStatus(u16 PWM_FLAG)
{
  if((PWM->ISR & PWM_FLAG) != RESET )
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : PWM_ClearFlag
* Description    : Clears the PWM’s pending flags. 
* Input          : PWM_FLAG: specifies the flag to clear. 
*                  This parameter can be any combination of the following values:
*                         - PWM_FLAG_OC1: Output Compare 1 flag
*                         - PWM_FLAG_OC2: Output Compare 2 flag
*                         - PWM_FLAG_OC3: Output Compare 3 flag
*                         - PWM_FLAG_Update: PWM update flag
*                         - PWM_FLAG_Emergency: PWM Emergency flag
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_ClearFlag(u16 PWM_FLAG)
{
  /* Clears the flags */
  PWM->ISR &= ~PWM_FLAG;
}

/*******************************************************************************
* Function Name  : PWM_GetITStatus
* Description    : Checks whether the PWM interrupt has occurred or not.
* Input          : PWM_IT: specifies the PWM interrupt source to check. 
*                  This parameter can be one of the following values:
*                         - PWM_IT_OC1: PWM Output Compare 1 Interrupt source
*                         - PWM_IT_OC2: PWM Output Compare 2 Interrupt source
*                         - PWM_IT_OC3: PWM Output Compare 3 Interrupt source
*                         - PWM_IT_Update: PWM update Interrupt source
*                         - PWM_IT_Emergency: PWM Emergency interrupt source
*                         - PWM_IT_GlobalUpdate: PWM global update Interrupt
*                           source
* Output         : None
* Return         : The new state of the PWM_IT(SET or RESET).
*******************************************************************************/
ITStatus PWM_GetITStatus(u16 PWM_IT)
{
  u16 PWM_IT_Check = 0;

  /* Calculates the pending bits to be checked */
  PWM_IT_Check = PWM_IT & PWM_IT_Clear_Mask;
  
  if((PWM->ISR & PWM_IT_Check) != RESET )
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : PWM_ClearITPendingBit
* Description    : Clears the PWM's interrupt pending bits.
* Input          : PWM_IT: specifies the pending bit to clear.
*                  This parameter can be any combination of the following values:
*                         - PWM_IT_OC1: PWM Output Compare 1 Interrupt source
*                         - PWM_IT_OC2: PWM Output Compare 2 Interrupt source
*                         - PWM_IT_OC3: PWM Output Compare 3 Interrupt source
*                         - PWM_IT_Update: PWM update Interrupt source
*                         - PWM_IT_Emergency: PWM Emergency interrupt source
*                         - PWM_IT_GlobalUpdate: PWM global update Interrupt
*                           source
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_ClearITPendingBit(u16 PWM_IT)
{
  u16 PWM_IT_Clear = 0;

  /* Calculates the pending bits to be cleared */
  PWM_IT_Clear = PWM_IT & PWM_IT_Clear_Mask;

  /* Clears the pending bits */
  PWM->ISR &= ~PWM_IT_Clear;
  
}

/*******************************************************************************
* Function Name  : OCM_ModuleConfig
* Description    : Output Compare Module configuration.
* Input          : PWM_InitStruct: pointer to a PWM_InitTypeDef structure that
*                  contains the configuration information for the PWM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
static void OCM_ModuleConfig(PWM_InitTypeDef* PWM_InitStruct)
{
  u16 PWM_OCControl = 0x0000;
  u16 DTR_REG = 0x0000;
    
  if(PWM_InitStruct->PWM_Mode == PWM_Mode_OCTiming)
  {
    PWM_OCControl = PWM_OCControl_OCTiming;
  }
  else
  {
    if(PWM_InitStruct->PWM_Mode == PWM_Mode_OCActive)
    {
      PWM_OCControl = PWM_OCControl_OCActive;
    }
    else
    {
      if(PWM_InitStruct->PWM_Mode == PWM_Mode_OCInactive)
      {
        PWM_OCControl = PWM_OCControl_OCInactive;
      }
      else
      {
        if(PWM_InitStruct->PWM_Mode == PWM_Mode_OCToggle)
        {
          PWM_OCControl = PWM_OCControl_OCToggle;
        }
        else
        {
          PWM_OCControl = PWM_OCControl_PWM;

        }
      }
    }
  }

  /* Read DTR register */
  DTR_REG = PWM->DTR & 0x8000;

/*Channel 1 Configuration-----------------------------------------------------*/
    if(PWM_InitStruct->PWM_Channel == PWM_Channel_1)
    {
      /* PWM Output Complementary Configuration */
      if(PWM_InitStruct->PWM_Complementary == PWM_Complementary_Enable)
      {
        /* Configures Channel 1 on Output Compare mode */
         PWM->OMR1 &= PWM_OC1C_Mask;
         PWM->OMR1 |= PWM_OCControl|PWM_OC1_Enable|PWM_OC1N_Enable|PWM_PLD1_Set;
         PWM->OCR1 = PWM_InitStruct->PWM_Pulse1;
         
        /* Sets the OC1 wave polarity */
        if(PWM_InitStruct->PWM_Polarity1 == PWM_Polarity1_Low)
        {
           PWM->OMR1 |= PWM_OC1P_Set;
        }
        else
        {
           PWM->OMR1 &= PWM_OC1P_Reset;
        }

        /* Sets the OC1N wave polarity */
        if(PWM_InitStruct->PWM_Polarity1N == PWM_Polarity1N_Low)
        {
           PWM->OMR1 |= PWM_OC1NP_Set;
        }
        else
        {
           PWM->OMR1 &= PWM_OC1NP_Reset;
        }
      }/* End complementary case */
      /* Single PWM Output configuratuion */
      else
      {
        switch(PWM_InitStruct->PWM_OCState)
        {
          case PWM_OCState_Enable:
          {
            /* Configures Channel 1 on Output Compare mode */
            PWM->OMR1 &= PWM_OC1C_Mask;
            PWM->OMR1 |= PWM_OCControl|PWM_OC1_Enable;
            PWM->OMR1 |= PWM_PLD1_Set;
            PWM->OCR1 = PWM_InitStruct->PWM_Pulse1;

            /* Sets the OC1 wave polarity */
            if(PWM_InitStruct->PWM_Polarity1 == PWM_Polarity1_Low)
            {
              PWM->OMR1 |= PWM_OC1P_Set;
            }
            else
            {
              PWM->OMR1 &= PWM_OC1P_Reset;
            }
          }
          break;
          case PWM_OCState_Disable:
          {
            /* OC1E = 0 and OSSR = 0 sets the polarity */
            PWM->OMR1 &= PWM_OC1_Disable;
            DTR_REG &= PWM_OSSR_Reset;
          }
          break;
          case PWM_OCState_OffState:
          {
            /* OC1E = 0 and OSSR = 1 and sets the polarity */
            PWM->OMR1 &= PWM_OC1_Disable;
            DTR_REG |= PWM_OSSR_Set;
            
            /* Sets the OC1 wave polarity */
            if(PWM_InitStruct->PWM_Polarity1 == PWM_Polarity1_Low)
            {
              PWM->OMR1 |= PWM_OC1P_Set;
            }
            else
            {
              PWM->OMR1 &= PWM_OC1P_Reset;
            }
          }
          break;
        }

        switch(PWM_InitStruct->PWM_OCNState)
        {
          case PWM_OCNState_Enable:
          {
            /* Configures Channel 1N on Output Compare mode */
            PWM->OMR1 &= PWM_OC1C_Mask;
            PWM->OMR1 |= PWM_OCControl |PWM_OC1N_Enable |PWM_PLD1_Set; 
            PWM->OCR1 = PWM_InitStruct->PWM_Pulse1;

            /* Sets the OC1N wave polarity */
            if(PWM_InitStruct->PWM_Polarity1N == PWM_Polarity1N_Low)
            {
              PWM->OMR1 |= PWM_OC1NP_Set;
            }
            else
            {
              PWM->OMR1 &= PWM_OC1NP_Reset;
            }
          }
          break;
          case PWM_OCNState_Disable:
          {
            /* OC1N = 0 OSSR = 0 */
            PWM->OMR1 &= PWM_OC1N_Disable;
            DTR_REG &= PWM_OSSR_Reset;
          }
          break;
          case PWM_OCNState_OffState:
          {
            /* OC1N = 0 OSSR = 1 and sets the polarity */
            PWM->OMR1 &= PWM_OC1N_Disable;
            DTR_REG |= PWM_OSSR_Set;

            if(PWM_InitStruct->PWM_Polarity1N == PWM_Polarity1N_Low)
            {
              PWM->OMR1 |= PWM_OC1NP_Set;
            }
            else
            {
              PWM->OMR1 &= PWM_OC1NP_Reset;
            }
          }
          break;
        } 
      } /* End not complementary case */
    }/* end channel 1 */

/*Channel 2 Configuration-----------------------------------------------------*/
      if(PWM_InitStruct->PWM_Channel == PWM_Channel_2)
      {
        /* PWM Output Complementary Configuration */
        if(PWM_InitStruct->PWM_Complementary == PWM_Complementary_Enable)
        {
          /* Configures Channel 2 on Output Compare mode */
          PWM->OMR1 &= PWM_OC2C_Mask;
          PWM->OMR1 |= (PWM_OCControl<<8)|PWM_OC2_Enable|PWM_OC2N_Enable|PWM_PLD2_Set;
          PWM->OCR2 = PWM_InitStruct->PWM_Pulse2;

        /* Set the OC2 wave polarity */
        if(PWM_InitStruct->PWM_Polarity2 == PWM_Polarity2_Low)
        {
           PWM->OMR1 |= PWM_OC2P_Set;
        }
        else
        {
           PWM->OMR1 &= PWM_OC2P_Reset;
        }

        /* Sets the OC2N wave polarity */
        if(PWM_InitStruct->PWM_Polarity2N == PWM_Polarity2N_Low)
        {
           PWM->OMR1 |= PWM_OC2NP_Set;
        }
        else
        {
           PWM->OMR1 &= PWM_OC2NP_Reset;
        }

        }/* End complentary case */
        else
        /* Single PWM Output configuratuion */
        {
          switch(PWM_InitStruct->PWM_OCState)
          {
            case PWM_OCState_Enable:
            {
              /* Configures Channel 2 on Output Compare mode */
              PWM->OMR1 &= PWM_OC2C_Mask;
              PWM->OMR1 |= (PWM_OCControl<<8)|PWM_OC2_Enable|PWM_PLD2_Set;
              PWM->OCR2 = PWM_InitStruct->PWM_Pulse2;

              /* Sets the OC2 wave polarity */
              if(PWM_InitStruct->PWM_Polarity2 == PWM_Polarity2_Low)
              {
                PWM->OMR1 |= PWM_OC2P_Set;
              }
              else
              {
                PWM->OMR1 &= PWM_OC2P_Reset;
              }
            }
            break;
            case PWM_OCState_Disable:
            {
              /* OC2E = 0 and OSSR = 0  */
              PWM->OMR1 &= PWM_OC2_Disable;
              DTR_REG &= PWM_OSSR_Reset;
            }
            break;
            case PWM_OCState_OffState:
            {
              /* OC2E = 0 and OSSR = 1 sets the polarity */
              PWM->OMR1 &= PWM_OC2_Disable;
              DTR_REG |= PWM_OSSR_Set;
              
              /* Sets the OC2 wave polarity */
              if(PWM_InitStruct->PWM_Polarity2 == PWM_Polarity2_Low)
              {
                PWM->OMR1 |= PWM_OC2P_Set;
              }
              else
              {
                PWM->OMR1 &= PWM_OC2P_Reset;
              }
            }
            break;
          }
          switch(PWM_InitStruct->PWM_OCNState)
          {
            case PWM_OCNState_Enable:
            {
              /* Configures Channel 2N on Output Compare mode */
              PWM->OMR1 &= PWM_OC2C_Mask;
              PWM->OMR1 |= (PWM_OCControl<<8)|PWM_OC2N_Enable|PWM_PLD2_Set;
              PWM->OCR2 = PWM_InitStruct->PWM_Pulse2;

              /* Sets the OC2 wave polarity */
              if(PWM_InitStruct->PWM_Polarity2N == PWM_Polarity2N_Low)
              {
                PWM->OMR1 |= PWM_OC2NP_Set;
              }
              else
              {
                PWM->OMR1 &= PWM_OC2NP_Reset;
              }
            }
            break;
            case PWM_OCNState_Disable:
            {
              /* OC2N = 0 OSSR = 0 */
              PWM->OMR1 &= PWM_OC2N_Disable;
              DTR_REG &= PWM_OSSR_Reset;
            }
            break;
            case PWM_OCNState_OffState:
            {
              /* OC2N = 0 OSSR = 1 and sets the polarity */
              PWM->OMR1 &= PWM_OC2N_Disable;
              DTR_REG |= PWM_OSSR_Set;
              
              if(PWM_InitStruct->PWM_Polarity2N == PWM_Polarity2N_Low)
              {
                PWM->OMR1 |= PWM_OC2NP_Set;
              }
              else
              {
                PWM->OMR1 &= PWM_OC2NP_Reset;
              }
            }
            break;
          }
        } /* End not complementary case */
      }/* end channel 2 */

/*Channel 3 Configuration-----------------------------------------------------*/
      if(PWM_InitStruct->PWM_Channel == PWM_Channel_3)
      {
        /* PWM Output Complementary Configuration */
        if(PWM_InitStruct->PWM_Complementary == PWM_Complementary_Enable)
        {
          /* Configures Channel 3 on Output Compare mode */
           PWM->OMR2 &= PWM_OC3C_Mask;
           PWM->OMR2 |= PWM_OCControl|PWM_OC3_Enable|PWM_OC3N_Enable|PWM_PLD3_Set;
           PWM->OCR3 = PWM_InitStruct->PWM_Pulse3;

          /* Sets the OC3 wave polarity */
          if(PWM_InitStruct->PWM_Polarity3 == PWM_Polarity3_Low)
          {
            PWM->OMR2 |= PWM_OC3P_Set;
          }
          else
          {
            PWM->OMR2 &= PWM_OC3P_Reset;
          }

          /* Sets the OC3N wave polarity */
          if(PWM_InitStruct->PWM_Polarity3N == PWM_Polarity3N_Low)
          {
            PWM->OMR2 |= PWM_OC3NP_Set;
          }
          else
          {
            PWM->OMR2 &= PWM_OC3NP_Reset;
          }
        }/* End complementary case */
        else
        /* Single PWM Output configuratuion */
        {
          switch(PWM_InitStruct->PWM_OCState)
          {
            case PWM_OCState_Enable:
            {
              /* Configures Channel 3 on Output Compare mode */
              PWM->OMR2 &= PWM_OC3C_Mask;
              PWM->OMR2 |= PWM_OCControl|PWM_OC3_Enable|PWM_PLD3_Set;
              PWM->OCR3 = PWM_InitStruct->PWM_Pulse3;

              /* Sets the OCC wave polarity */
              if(PWM_InitStruct->PWM_Polarity3 == PWM_Polarity3_Low)
              {
                PWM->OMR2 |= PWM_OC3P_Set;
              }
              else
              {
                PWM->OMR2 &= PWM_OC3P_Reset;
              }
            }
            break;
            case PWM_OCState_Disable:
            {
              /* OC3E = 0 and OSSR = 0  */
              PWM->OMR2 &= PWM_OC3_Disable;
              DTR_REG &= PWM_OSSR_Reset;
            }
            break;
            case PWM_OCState_OffState:
            {
              /* OC3E = 0 and OSSR = 1 sets the polarity */
              PWM->OMR2 &= PWM_OC3_Disable;
              DTR_REG |= PWM_OSSR_Set;

              if(PWM_InitStruct->PWM_Polarity3 == PWM_Polarity3_Low)
              {
                PWM->OMR2 |= PWM_OC3P_Set;
              }
              else
              {
                PWM->OMR2 &= PWM_OC3P_Reset;
              }
            }
            break;
          }

          switch(PWM_InitStruct->PWM_OCNState)
          {
            case PWM_OCNState_Enable:
            {
              /* Configures Channel 3N on Output Compare mode */
              PWM->OMR2 &= PWM_OC3C_Mask;
              PWM->OMR2 |= PWM_OCControl |PWM_OC3N_Enable|PWM_PLD3_Set;
              PWM->OCR3 = PWM_InitStruct->PWM_Pulse3;

              /* Sets the OC3 wave polarity */
              if(PWM_InitStruct->PWM_Polarity3N == PWM_Polarity3N_Low)
              {
                PWM->OMR2 |= PWM_OC3NP_Set;
              }
              else
              {
                PWM->OMR2 &= PWM_OC3NP_Reset;
              }
            }
            break;
            case PWM_OCNState_Disable:
            {
              /* OC3N = 0 OSSR = 0 */
              PWM->OMR2 &= PWM_OC3N_Disable;
              DTR_REG &= PWM_OSSR_Reset;
            }
            break;
            case PWM_OCNState_OffState:
            {
              /* OC3N = 0 OSSR = 1 and sets the polarity */
              PWM->OMR2 &= PWM_OC3N_Disable;
              DTR_REG |= PWM_OSSR_Set;

              if(PWM_InitStruct->PWM_Polarity3N == PWM_Polarity3N_Low)
              {
                PWM->OMR2 |= PWM_OC3NP_Set;
              }
              else
              {
                PWM->OMR2 &= PWM_OC3NP_Reset;
              }
            }
            break;
          }
        } /* End not complementary case */
      }/* end channel 3 */

  if(PWM_InitStruct->PWM_DTRAccess == PWM_DTRAccess_Enable)
  {
    DTR_REG |= PWM_InitStruct->PWM_LOCKLevel | PWM_InitStruct->PWM_Emergency |
              PWM_InitStruct->PWM_DeadTime | PWM_InitStruct->PWM_OSSIState;
    PWM->DTR = DTR_REG;
  } 
}
/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
