/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_wdg.c
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file provides all the WDG software functions.
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "91x_wdg.h"
#include "91x_scu.h"
/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/


/* WDG End of Count interrupt Flag */
#define WDG_FLAG_EC  0x0001


/* WDG End of Count interrupt request */
#define WDG_IT_EC    0x0001



/* WDG Start/Stop counter */
#define WDG_Counter_Start  0x0002
#define WDG_Counter_Stop   0xFFFD


/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Registers reset value */
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

  SCU_APBPeriphReset(__WDG, ENABLE);  /*WDG peripheral under Reset */
  SCU_APBPeriphReset(__WDG, DISABLE);  /*WDG peripheral Reset off*/
  
}

/*******************************************************************************
* Function Name  : WDG_StructInit
* Description    : Fills the WDG_InitTypeDef structure member with its reset
*                  value.
* Input          : WDG_InitStruct : pointer to a WDG_InitTypeDef structure
*                  which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_StructInit(WDG_InitTypeDef *WDG_InitStruct)
{
  /* Select the Watchdog running mode*/
  WDG_InitStruct->WDG_Mode = WDG_Mode_Timer;

  /* Select the source clock */
  WDG_InitStruct-> WDG_ClockSource = WDG_ClockSource_Apb;

   /* Initialize Prescaler */
  WDG_InitStruct->WDG_Prescaler =0xFF;

  /* Initialize Preload */
  WDG_InitStruct->WDG_Preload =0xFFFF;


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


 if(WDG_InitStruct->WDG_ClockSource == WDG_ClockSource_Apb)
  {
    /* Select The APB clock as clock source */
    WDG->CR &= WDG_ClockSource_Apb;
  }

  else
  {
    /* Select the RTC clock as source */
    WDG->CR |= WDG_ClockSource_Rtc ;
  }


  /* Configure WDG Prescaler register value */
  WDG->PR = WDG_InitStruct->WDG_Prescaler;

  /* Configure WDG Pre-load register value */
  WDG->VR = WDG_InitStruct->WDG_Preload ;


  if(WDG_InitStruct->WDG_Mode == WDG_Mode_Timer)
  {
    /* Select Timer mode */
    WDG->CR &= WDG_Mode_Timer;
  }
  else
  {
    /* Select WDG mode */
    WDG->CR |= WDG_Mode_Wdg ;
  }


}

/*******************************************************************************
* Function Name  : WDG_Cmd
* Description    : Enables or disables the WDG peripheral.
* Input          : NewState: new state of the WDG peripheral (Newstate can be
*                  ENABLE or DISABLE)
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_Cmd(FunctionalState NewState )
{
  if((WDG->CR & WDG_Mode_Wdg) == 0)
  {
    /* Timer mode */
    if(NewState == ENABLE)
    {
      /* Start timer by setting SC bit in Control register */
      WDG->CR |= WDG_Counter_Start;
    }
    else
    {
      /* Stop timer by clearning SC bit in Control register */
      WDG->CR &= WDG_Counter_Stop;
    }
  }
  else
  {
    /* Watchdog mode */
    if(NewState == ENABLE)
    {
      WDG->KR = WDG_KeyValue1;
      WDG->KR = WDG_KeyValue2;
    }
  }
}

/*******************************************************************************
* Function Name  : WDG_ITConfig
* Description    : Enables or disables the WDG End of Count(EC) interrupt.
* Input          : Newstate:  new state of the End of Count(EC) WDG interrupt.
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
* Function Name  : WDG_GetITStatus
* Description    : Checks whether the WDG End of Count(EC) interrupt is occured or not.
* Input          : None
* Output         : None
* Return         : The new state of WDG_IT (SET or RESET).
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

/*******************************************************************************
* Function Name  : WDG_ClearFlag
* Description    : Clears the WDG's End of Count(EC) Flag.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void WDG_ClearFlag(void)
{
 /* Clear the EC Flag */

  WDG->SR &= ~WDG_FLAG_EC;

}


/*******************************************************************************
* Function Name  : WDG_GetFlagStatus
* Description    : Checks whether the WDG End of Count(EC) flag is set or not.
* Input          : None
* Output         : None
* Return         : The new state of the WDG_FLAG (SET or RESET).
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



/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
