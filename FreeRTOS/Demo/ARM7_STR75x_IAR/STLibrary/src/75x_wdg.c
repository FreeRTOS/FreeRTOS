/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_wdg.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the WDG software functions.
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
#include "75x_wdg.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Registers reset value */
#define WDG_Preload_Mask     0xFFFF
#define WDG_Prescaler_Mask   0xFF

/* WDG Start/Stop counter */
#define WDG_Counter_Start_Mask  0x0002
#define WDG_Counter_Stop_Mask   0xFFFD

/* WDG Sequence */
#define WDG_KeyValue1_Mask      0xA55A
#define WDG_KeyValue2_Mask      0x5AA5

/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/******************************************************************************
* Function Name  : WDG_DeInit
* Description    : Deinitializes the WDG peripheral registers to their default 
*                  reset values.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_DeInit(void)
{
  /* Reset all the WDG registers */
  WDG->CR = 0x0000;
  WDG->PR = 0x00FF;
  WDG->VR = 0xFFFF;
  WDG->CNT = 0xFFFF;
  WDG->SR = 0x0000;
  WDG->MR = 0x0000;
  WDG->KR = 0x0000;
}

/*******************************************************************************
* Function Name  : WDG_Init
* Description    : Initializes WDG  peripheral according to the specified
*                  parameters in the WDG_InitStruct.
* Input          : WDG_InitStruct: pointer to a WDG_InitTypeDef structure that
*                  contains the configuration information for the WDG peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_Init(WDG_InitTypeDef* WDG_InitStruct)
{
  /* Configure WDG Prescaler register value */
  WDG->PR = WDG_InitStruct->WDG_Prescaler;

  /* Configure WDG Pre-load register value */
  WDG->VR = WDG_InitStruct->WDG_Preload ;
  
  if(WDG_InitStruct->WDG_Mode == WDG_Mode_WDG)
  {
    /* Select WDG mode */
    WDG->CR |= WDG_Mode_WDG ;
  }
  else
  {
    /* Select Timer mode */
    WDG->CR &= WDG_Mode_Timer;    
  }
}

/*******************************************************************************
* Function Name  : WDG_StructInit
* Description    : Fills each WDG_InitStruct member with its default value.
* Input          : WDG_InitStruct : pointer to a WDG_InitTypeDef structure
*                  which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_StructInit(WDG_InitTypeDef *WDG_InitStruct)
{
  /* Initialize mode */
  WDG_InitStruct->WDG_Mode = WDG_Mode_Timer;

  /* Initialize Preload */
  WDG_InitStruct->WDG_Preload = WDG_Preload_Mask ;

  /* Initialize Prescaler */
  WDG_InitStruct->WDG_Prescaler = WDG_Prescaler_Mask;
}

/*******************************************************************************
* Function Name  : WDG_Cmd
* Description    : Enables or disables the WDG peripheral.
* Input          : NewState: new state of the WDG peripheral. 
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_Cmd(FunctionalState NewState)
{
  if((WDG->CR & WDG_Mode_WDG) == 0)
  {
    /* Timer mode */
    if(NewState == ENABLE)
    {
      /* Start timer by setting SC bit in Control register */
      WDG->CR |= WDG_Counter_Start_Mask;
    }
    else 
    {
      /* Stop timer by clearing SC bit in Control register */
      WDG->CR &= WDG_Counter_Stop_Mask;
    }
  }
  else
  {
    /* Watchdog mode */
    if(NewState == ENABLE)
    {
      WDG->KR = WDG_KeyValue1_Mask;
      WDG->KR = WDG_KeyValue2_Mask;
    }
  }
}

/*******************************************************************************
* Function Name  : WDG_ITConfig
* Description    : Enables or disables the WDG End of Count(EC) interrupt.
* Input          : Newstate:  new state of the WDG End of Count(EC) interrupt.
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_ITConfig(FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable the End of Count interrupt */
    WDG->MR |= WDG_IT_EC;
  }
  else
  {
    /* Disable the End of Count interrupt */
    WDG->MR &= ~WDG_IT_EC;
  }
}

/*******************************************************************************
* Function Name  : WDG_GetCounter
* Description    : Gets the WDG’s current counter value.
* Input          : None
* Output         : None
* Return         : The WDG current counter value
*******************************************************************************/
u16 WDG_GetCounter(void)
{
   return WDG->CNT;
}

/*******************************************************************************
* Function Name  : WDG_GetFlagStatus
* Description    : Checks whether the WDG End of Count(EC) flag is set or not.
* Input          : None
* Output         : None
* Return         : The new state of WDG End of Count(EC) flag (SET or RESET).
*******************************************************************************/
FlagStatus WDG_GetFlagStatus(void)
{
  if((WDG->SR & WDG_FLAG_EC) != RESET )
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : WDG_ClearFlag
* Description    : Clears the WDG’s End of Count(EC) pending flag. 
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_ClearFlag(void)
{
  /* Clear the EC pending bit */
  WDG->SR &= ~WDG_FLAG_EC;
}

/*******************************************************************************
* Function Name  : WDG_GetITStatus
* Description    : Checks whether the WDG End of Count(EC) interrupt has 
*                  occurred or not.
* Input          : None
* Output         : None
* Return         : The new state of WDG End of Count(EC) interrupt (SET or RESET).
*******************************************************************************/
ITStatus WDG_GetITStatus(void)
{
  if(((WDG->SR & WDG_IT_EC) != RESET )&&((WDG->MR & WDG_IT_EC) != RESET ))
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : WDG_ClearITPendingBit
* Description    : Clears the WDG's End of Count(EC) interrupt pending bit.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_ClearITPendingBit(void)
{
 /* Clear the EC pending bit */
  WDG->SR &= ~WDG_IT_EC;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
