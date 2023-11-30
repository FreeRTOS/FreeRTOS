/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_rtc.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the RTC software functions.
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
#include "75x_rtc.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define RTC_CNF_Enable_Mask      0x0010      /* Configuration Flag Enable Mask */
#define RTC_CNF_Disable_Mask     0xFFEF      /* Configuration Flag Disable Mask */
#define RTC_LSB_Mask             0x0000FFFF  /* RTC LSB Mask */
#define RTC_MSB_Mask             0xFFFF0000  /* RTC MSB Mask */
#define RTC_Prescaler_MSB_Mask   0x000F0000  /* RTC Prescaler MSB Mask */

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/*******************************************************************************
* Function Name  : RTC_DeInit
* Description    : Deinitializes the RTC peripheral registers to their
*                  default reset values.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_DeInit(void)
{
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_RTC,ENABLE);
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_RTC,DISABLE);
}

/*******************************************************************************
* Function Name  : RTC_ITConfig
* Description    : Enables or disables the specified RTC interrupts.
* Input          : - RTC_IT: specifies the RTC interrupts sources to be enabled
*                    or disabled.
*                    This parameter can be a combination of one or more of the
*                    following values:
*                       - RTC_IT_Overflow: Overflow interrupt
*                       - RTC_IT_Alarm: Alarm interrupt
*                       - RTC_IT_Second: Second interrupt
*                 - NewState: new state of the specified RTC interrupts.
*                   This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_ITConfig(u16 RTC_IT, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    RTC->CRH |= RTC_IT;
  }
  else
  {
    RTC->CRH &= ~RTC_IT;
  }
}

/*******************************************************************************
* Function Name  : RTC_EnterConfigMode
* Description    : Enters the RTC configuration mode.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_EnterConfigMode(void)
{
  /* Set the CNF flag to enter in the Configuration Mode */
  RTC->CRL |= RTC_CNF_Enable_Mask;
}

/*******************************************************************************
* Function Name  : RTC_ExitConfigMode
* Description    : Exits from the RTC configuration mode.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_ExitConfigMode(void)
{
  /* Reset the CNF flag to exit from the Configuration Mode */
  RTC->CRL &= RTC_CNF_Disable_Mask;
}

/*******************************************************************************
* Function Name  : RTC_GetCounter
* Description    : Gets the RTC counter value.
* Input          : None
* Output         : None
* Return         : RTC counter value.
*******************************************************************************/
u32 RTC_GetCounter(void)
{
  u16 Tmp = 0;
  Tmp = RTC->CNTL;
  
  return (((u32)RTC->CNTH << 16 ) |Tmp) ;
}

/*******************************************************************************
* Function Name  : RTC_SetCounter
* Description    : Sets the RTC counter value.
* Input          : RTC counter new value.
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_SetCounter(u32 CounterValue)
{
  RTC_EnterConfigMode();
  
/* COUNTER Config ------------------------------------------------------------*/
  /* Set RTC COUNTER MSB word */
  RTC->CNTH =(CounterValue & RTC_MSB_Mask) >> 16;
  /* Set RTC COUNTER LSB word */
  RTC->CNTL =(CounterValue & RTC_LSB_Mask);
  
  RTC_ExitConfigMode();
}

/*******************************************************************************
* Function Name  : RTC_SetPrescaler
* Description    : Sets the RTC prescaler value.
* Input          : RTC prescaler new value.
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_SetPrescaler(u32 PrescalerValue)
{
  RTC_EnterConfigMode();
  
/* PRESCALER Config ----------------------------------------------------------*/
  /* Set RTC PRESCALER MSB word */
  RTC->PRLH = (PrescalerValue & RTC_Prescaler_MSB_Mask) >> 16;
  /* Set RTC PRESCALER LSB word */
  RTC->PRLL = (PrescalerValue & RTC_LSB_Mask);
  
  RTC_ExitConfigMode();
}

/*******************************************************************************
* Function Name  : RTC_GetPrescaler
* Description    : Gets the RTC prescaler value.
* Input          : None
* Output         : None
* Return         : RTC prescaler value.
*******************************************************************************/
u32 RTC_GetPrescaler(void)
{
  u16 Tmp = 0;
  Tmp = RTC->PRLL;
  
  return (((u32)(RTC->PRLH & 0x000F) << 16 ) | Tmp);
}

/*******************************************************************************
* Function Name  : RTC_SetAlarm
* Description    : Sets the RTC alarm value.
* Input          : RTC alarm new value.
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_SetAlarm(u32 AlarmValue)
{
  RTC_EnterConfigMode();
  
/* ALARM Config --------------------------------------------------------------*/
  /* Set the ALARM MSB word */
  RTC->ALRH = (AlarmValue & RTC_MSB_Mask) >> 16;
  /* Set the ALARM LSB word */
  RTC->ALRL = (AlarmValue & RTC_LSB_Mask);
  
  RTC_ExitConfigMode();
}

/*******************************************************************************
* Function Name  : RTC_GetDivider
* Description    : Gets the RTC divider value.
* Input          : None
* Output         : None
* Return         : RTC Divider value.
*******************************************************************************/
u32 RTC_GetDivider(void)
{
  u16 Tmp = 0;
  Tmp = RTC->DIVL ;
  return (((u32)(RTC->DIVH & 0x000F) << 16 ) | Tmp);
}

/*******************************************************************************
* Function Name  : RTC_WaitForLastTask
* Description    : Waits until last write operation on RTC registers has finished.
*                  This function must be called before any write to RTC registers.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_WaitForLastTask(void)
{
  /* Loop until RTOFF flag is set */
  while ((RTC->CRL & RTC_FLAG_RTOFF) == RESET);
}

/*******************************************************************************
* Function Name  : RTC_WaitForSynchro
* Description    : Waits until the RTC registers (RTC_CNT, RTC_ALR and RTC_PRL) 
*                  are synchronized with RTC APB clock.
*                  This function must be called before any read operation after 
*                  an APB reset or an APB clock stop.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_WaitForSynchro(void)
{
  /* Clear RSF flag */
  RTC->CRL &= ~RTC_FLAG_RSF;
  
  /* Loop until RSF flag is set */
  while((RTC->CRL & RTC_FLAG_RSF)== RESET);
}

/*******************************************************************************
* Function Name  : RTC_GetFlagStatus
* Description    : Checks whether the specified RTC flag is set or not.
* Input          : RTC_FLAG: specifies the flag to check.
*                  This parameter can be one the following values:
*                        - RTC_FLAG_RTOFF: RTC Operation OFF flag
*                        - RTC_FLAG_RSF: Registers Synchronized flag
*                        - RTC_FLAG_Overflow: Overflow interrupt flag
*                        - RTC_FLAG_Alarm: Alarm interrupt flag
*                        - RTC_FLAG_Second: Second interrupt flag
* Output         : None
* Return         : The new state of RTC_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus RTC_GetFlagStatus(u16 RTC_FLAG)
{
  if((RTC->CRL & RTC_FLAG) != RESET)
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : RTC_ClearFlag
* Description    : Clears the RTC’s pending flags.
* Input          : RTC_FLAG: specifies the flag to clear.
*                    This parameter can be a combination of one or more of
*                    the following values:
*                        - RTC_FLAG_RSF: Registers Synchronized flag. This flag
*                          is cleared only after an APB reset or an APB Clock stop.
*                        - RTC_FLAG_Overflow: Overflow interrupt flag
*                        - RTC_FLAG_Alarm: Alarm interrupt flag
*                        - RTC_FLAG_Second: Second interrupt flag
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_ClearFlag(u16 RTC_FLAG)
{
  /* Clear the coressponding RTC flag */
  RTC->CRL &= ~RTC_FLAG;
}

/*******************************************************************************
* Function Name  : RTC_GetITStatus
* Description    : Checks whether the specified RTC interrupt has occured or not.
* Input          : RTC_IT: specifies the RTC interrupts sources to check.
*                   This parameter can be a combination of one or more of
*                   the following values:
*                       - RTC_IT_Overflow: Overflow interrupt
*                       - RTC_IT_Alarm: Alarm interrupt
*                       - RTC_IT_Second: Second interrupt
* Output         : None
* Return         : The new state of the RTC_IT (SET or RESET).
*******************************************************************************/
ITStatus RTC_GetITStatus(u16 RTC_IT)
{
  if(((RTC->CRH & RTC_IT) != RESET)&& ((RTC->CRL & RTC_IT) != RESET))
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : RTC_ClearITPendingBit
* Description    : Clears the RTC’s interrupt pending bits.
* Input          : RTC_IT: specifies the interrupt pending bit to clear. 
*                   This parameter can be any combination of one or more of
*                   the following values:
*                       - RTC_IT_Overflow: Overflow interrupt
*                       - RTC_IT_Alarm: Alarm interrupt
*                       - RTC_IT_Second: Second interrupt
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_ClearITPendingBit(u16 RTC_IT)
{
  /* Clear the coressponding RTC pending bit */
  RTC->CRL &= ~RTC_IT;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
