/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_tb.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the TB software functions.
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
#include "75x_tb.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
#define TB_IT_Enable_Mask   0x7FFF
#define TB_IT_Clear_Mask    0x7FFF
#define TB_IC_Enable        0x0004
#define TB_ICPolarity_Set   0x0008
#define TB_ICPolarity_Reset 0xFFF7
#define TB_UFS_Reset        0xFFFE
#define TB_UFS_Set          0x0001

/* TB debug state */
#define TB_DBGC_Set    0x0400
#define TB_DBGC_Reset  0xFB7F

/* TB counter state */
#define TB_COUNTER_Reset  0x0002
#define TB_COUNTER_Start  0x0004
#define TB_COUNTER_Stop   0xFFFB

#define TB_SMS_EXTCLK_Set   0x0008
#define TB_SMS_RESETCLK_Set 0x0000

/* TB Slave Mode Enable Set/Reset value */
#define TB_SME_Reset  0x731B
#define TB_SME_Set    0x0004

/* TB Trigger Selection value */
#define TB_TS_IC1_Set  0x0200

/* TB SCR Masks bit */
#define TB_SlaveModeSelection_Mask        0x7307
#define TB_TriggerSelection_Mask          0x701F

/* Reset Register Masks */
#define TB_Prescaler_Reset_Mask   0x0000
#define TB_CounterMode_Mask       0xFF8F
#define TB_AutoReload_Reset_Mask  0xFFFF

/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

 /******************************************************************************
* Function Name  : TB_DeInit
* Description    : Deinitializes the TB peripheral registers to their default
*                  reset values.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TB_DeInit(void)
{
 /* Enters and exits the TB peripheral to and from reset */
 MRCC_PeripheralSWResetConfig(MRCC_Peripheral_TB,ENABLE);
 MRCC_PeripheralSWResetConfig(MRCC_Peripheral_TB,DISABLE);
}

/*******************************************************************************
* Function Name  : TB_Init
* Description    : Initializes TB  peripheral according to the specified
*                  parameters in the TB_InitStruct.
* Input          : TB_InitStruct: pointer to a TB_InitTypeDef structure that
*                  contains the configuration information for the TB peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TB_Init(TB_InitTypeDef* TB_InitStruct)
{
  /* Set the TB prescaler value */
  TB->PSC = TB_InitStruct->TB_Prescaler;

  /* Set the TB period value */
  TB->ARR = TB_InitStruct->TB_AutoReload;

  /* Set the corresponding counter mode */
  TB->CR = (TB->CR & TB_CounterMode_Mask) | TB_InitStruct->TB_CounterMode;

  /* Set the corresponding clock source */
  if(TB_InitStruct->TB_ClockSource == TB_ClockSource_CKRTC)
  {  
    TB->SCR &= TB_SME_Reset & TB_SlaveModeSelection_Mask & TB_TriggerSelection_Mask;
    TB->SCR |= TB_SMS_EXTCLK_Set | TB_SME_Set | TB_TS_IC1_Set;
  }
  else
  {
    TB->SCR &= TB_SME_Reset & TB_SlaveModeSelection_Mask & TB_TriggerSelection_Mask;
  }

  if(TB_InitStruct->TB_Mode == TB_Mode_IC)
  {
    /* Set the corresponding value in TB SCR register */
    TB->SCR &= TB_SME_Reset & TB_SlaveModeSelection_Mask & TB_TriggerSelection_Mask;
    TB->SCR |= TB_SMS_RESETCLK_Set | TB_SME_Set | TB_TS_IC1_Set;

    /* Set the IC1 enable bit */
    TB->IMCR |= TB_IC_Enable;

    /* Set the input signal polarity */
    if (TB_InitStruct->TB_ICAPolarity == TB_ICAPolarity_Falling)
    {
      TB->IMCR |= TB_ICPolarity_Set;
    }
    else
    {
      TB->IMCR &= TB_ICPolarity_Reset;
    }
  }
}

/*******************************************************************************
* Function Name  : TB_StructInit
* Description    : Fills each TB_InitStruct member with its default value
* Input          : TB_InitStruct : pointer to a TB_InitTypeDef structure which
*                  will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void TB_StructInit(TB_InitTypeDef *TB_InitStruct)
{
  TB_InitStruct->TB_Mode = TB_Mode_Timing;
  TB_InitStruct->TB_ClockSource = TB_ClockSource_CKTIM;
  TB_InitStruct->TB_CounterMode = TB_CounterMode_Up;
  TB_InitStruct->TB_ICAPolarity = TB_ICAPolarity_Rising;
  TB_InitStruct->TB_Prescaler = TB_Prescaler_Reset_Mask;
  TB_InitStruct->TB_AutoReload = TB_AutoReload_Reset_Mask;
}

/*******************************************************************************
* Function Name  : TB_Cmd
* Description    : Enables or disables the TB peripheral.
* Input          : Newstate: new state of the TB peripheral. This parameter can
*                  be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TB_Cmd(FunctionalState Newstate)
{
  if(Newstate == ENABLE)
  {
    TB->CR |= TB_COUNTER_Start;
  }
  else
  {
    TB->CR &= TB_COUNTER_Stop;
  }
}

/*******************************************************************************
* Function Name  : TB_ITConfig
* Description    : Enables or disables the specified TB interrupt.
* Input          : - TB_IT: specifies the TB interrupt sources to be enabled or
*                    disabled.
*                    This parameter can be any combination of the following values:
*                         - TB_IT_Update: TB Update interrupt
*                         - TB_IT_GlobalUpdate: TB Global Update interrupt
*                         - TB_IT_IC: TB Input Capture interrupt
*                  - Newstate:  new state of the specified TB interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TB_ITConfig(u16 TB_IT, FunctionalState Newstate)
{
  u16 TB_IT_Enable = 0;

  TB_IT_Enable = TB_IT & TB_IT_Enable_Mask;

  if(Newstate == ENABLE)
  {
   /* Update interrupt global source: overflow/undeflow, counter reset operation
   or slave mode controller in reset mode */
   if ((TB_IT & TB_IT_GlobalUpdate) == TB_IT_GlobalUpdate)
   {
     TB->CR &= TB_UFS_Reset;
    }
   /* Update interrupt source: counter overflow/underflow */
   else if ((TB_IT & TB_IT_Update) == TB_IT_Update)
   {
    TB->CR |= TB_UFS_Set;
   }
   /* Select and enable the interrupts requests */
   TB->RSR |= TB_IT_Enable;
   TB->RER |= TB_IT_Enable;
  }
  /* Disable the interrupts requests */
  else
  {
   TB->RSR &= ~TB_IT_Enable;
   TB->RER &= ~TB_IT_Enable;
  }
}

/*******************************************************************************
* Function Name  : TB_SetPrescaler
* Description    : Sets the TB Prescaler value.
* Input          : Prescaler: specifies the TB Prescaler value.
* Output         : None
* Return         : None
*******************************************************************************/
void TB_SetPrescaler(u16 Prescaler)
{
  /* Sets the prescaler value */
  TB->PSC = Prescaler;
}

/*******************************************************************************
* Function Name  : TB_ResetCounter
* Description    : Re-intializes the counter and generates an update of the
*                  registers.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TB_ResetCounter(void)
{
  /* Re-intializes TB counter */
  TB->CR |= TB_COUNTER_Reset;
}

/*******************************************************************************
* Function Name  : TB_DebugCmd
* Description    : Enables or disables TB peripheral Debug control.
* Input          : Newstate: new state of the TB Debug control.
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TB_DebugCmd(FunctionalState Newstate)
{
  if(Newstate == ENABLE)
  {
    TB->CR |= TB_DBGC_Set;
  }
  else
  {
    TB->CR &= TB_DBGC_Reset;
  }
}

/*******************************************************************************
* Function Name  : TB_CounterModeConfig
* Description    : Configures the TB Counter Mode.
* Input          : TB_CounterMode: specifies the TB counter mode to be used.
*                  This parameter can be one of the following values:
*                         - TB_CounterMode_Up: TB Up Counting Mode
*                         - TB_CounterMode_Down: TB Down Counting Mode
*                         - TB_CounterMode_CenterAligned: TB Center Aligned Mode
* Output         : None
* Return         : None
*******************************************************************************/
void TB_CounterModeConfig(u16 TB_CounterMode)
{
  /* Counter mode configuration */
  TB->CR &= TB_CounterMode_Mask;
  TB->CR |= TB_CounterMode;
}

/*******************************************************************************
* Function Name  : TB_SLaveModeConfig
* Description    : Configures the TB slave Mode.
* Input          : TB_SMSMode: specifies the TB slave mode to be used.
*                  This parameter can be one of the following values:
*                         - TB_SMSMode_Trigger: The counter starts at a rising 
*                           edge of the trigger 
*                         - TB_SMSMode_Gated: The counter clock is enabled when 
*                           trigger signal is high
*                         - TB_SMSMode_External: The rising edge of selected trigger
*                           clocks the counter
*                         - TB_SMSMode_Reset: The rising edge of the selected 
*                           trigger signal resets the counter
* Output         : None
* Return         : None
*******************************************************************************/
void TB_SLaveModeConfig(u16 TB_SMSMode)
{
  TB->SCR &= TB_SME_Reset & TB_SlaveModeSelection_Mask & TB_TriggerSelection_Mask;
  TB->SCR |= TB_SME_Set | TB_SMSMode | TB_TS_IC1_Set; 
}
/*******************************************************************************
* Function Name  : TB_GetCounter
* Description    : Gets the TB Counter value.
* Input          : None
* Output         : None
* Return         : The TB counter register value.
*******************************************************************************/
u16 TB_GetCounter(void)
{
  return TB->CNT;
}

/*******************************************************************************
* Function Name  : TB_GetICAP1
* Description    : Gets the TB Input capture value.
* Input          : None
* Output         : None
* Return         : The TB ICR1 register value.
*******************************************************************************/
u16 TB_GetICAP1(void)
{
  return TB->ICR1;
}

/*******************************************************************************
* Function Name  : TB_SetCounter
* Description    : Sets the TB Counter value.
* Input          : Counter: specifies the TB Counter value.
* Output         : None
* Return         : None
*******************************************************************************/
void TB_SetCounter(u16 Counter)
{
  TB->CNT = Counter;
}

/*******************************************************************************
* Function Name  : TB_GetFlagStatus
* Description    : Checks whether the specified TB flag is set or not.
* Input          : TB_FLAG: specifies the flag to check.
*                  This parameter can be one of the following values:
*                         - TB_FLAG_IC: TB Input Capture flag
*                         - TB_FLAG_Update: TB update flag
* Output         : None
* Return         : The new state of the TB_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus TB_GetFlagStatus(u16 TB_FLAG)
{
  if((TB->ISR & TB_FLAG) != RESET )
  {
   return SET;
  }
  else
  {
   return RESET;
  }
}

/*******************************************************************************
* Function Name  : TB_ClearFlag
* Description    : Clears the TB’s pending flags.
* Input          : TB_FLAG: specifies the flag to clear.
*                  This parameter can be any combination of the following values:
*                         - TB_FLAG_IC: TB Input Capture flag
*                         - TB_FLAG_Update: TB update flag
* Output         : None
* Return         : None
*******************************************************************************/
void TB_ClearFlag(u16 TB_FLAG)
{
  /* Clears the flags */
  TB->ISR &= ~TB_FLAG;
}

/*******************************************************************************
* Function Name  : TB_GetITStatus
* Description    : Checks whether the specified TB interrupt has occurred or not.
* Input          : TB_IT: specifies the interrupt to check.
*                  This parameter can be one of the following values:
*                       - TB_IT_Update: TB Update interrupt
*                       - TB_IT_GlobalUpdate: TB Global Update interrupt
*                       - TB_IT_IC: TB Input Capture interrupt
* Output         : None
* Return         : The new state of the TB_IT (SET or RESET).
*******************************************************************************/
ITStatus TB_GetITStatus(u16 TB_IT)
{
  u16 TB_IT_Check = 0;

  /* Calculates the pending bits to be checked */
  TB_IT_Check = TB_IT & TB_IT_Clear_Mask;
  
  if((TB->ISR & TB_IT_Check) != RESET )
  {
   return SET;
  }
  else
  {
   return RESET;
  }
}

/*******************************************************************************
* Function Name  : TB_ClearITPendingBit
* Description    : Clears the TB's interrupt pending bits.
* Input          : TB_IT: specifies the interrupt pending bit to clear.
*                  This parameter can be any combination of the following values:
*                         - TB_IT_Update: TB Update interrupt
*                         - TB_IT_GlobalUpdate: TB Global Update interrupt
*                         - TB_IT_IC: TB Input Capture interrupt
* Output         : None
* Return         : None
*******************************************************************************/
void TB_ClearITPendingBit(u16 TB_IT)
{
  u16 TB_IT_Clear = 0;

  /* Calculates the pending bits to be cleared */
  TB_IT_Clear = TB_IT & TB_IT_Clear_Mask;

  /* Clears the pending bits */
  TB->ISR &= ~TB_IT_Clear;
}
/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
