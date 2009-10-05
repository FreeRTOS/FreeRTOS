/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : wdg.h
* Author             : MCD Application Team
* Date First Issued  : 25/08/2003
* Description        : This file contains all the functions prototypes for the
*                      WDG software library.
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
#ifndef __WDG_H
#define __WDG_H

#include "71x_map.h"
#include "rccu.h"

/*******************************************************************************
* Function Name  : WDG_Enable
* Description    : Enable the Watchdog Mode
* Input          : None
* Return         : None
*******************************************************************************/
inline void WDG_Enable ( void )
{
  WDG->CR |= 0x01;
}

/*******************************************************************************
* Function Name  : WDG_CntRefresh
* Description    : Refresh and update the WDG counter to avoid a system reset.
* Input          : None
* Return         : None
*******************************************************************************/
inline void WDG_CntRefresh ( void )
{
  //write the first value in the key register
  WDG->KR = 0xA55A;
  //write the consecutive value
  WDG->KR = 0x5AA5;
}

/*******************************************************************************
* Function Name  : WDG_PrescalerConfig
* Description    : Set the counter prescaler value.
*                  Divide the counter clock by (Prescaler + 1)
* Input          : Prescaler data value (8 bit)
* Return         : None
*******************************************************************************/
inline void WDG_PrescalerConfig ( u8 Prescaler )
{
  WDG->PR = Prescaler;
}

/*******************************************************************************
* Function Name  : WDG_CntReloadUpdate
* Description    : Update the counter pre-load value.
* Input          : Pre-load data value (16 bit)
* Return         : None
*******************************************************************************/
inline void WDG_CntReloadUpdate ( u16 PreLoadValue )
{
  WDG->VR = PreLoadValue;
}

/*******************************************************************************
* Function Name  : WDG_PeriodValueConfig
* Description    : Set the prescaler and counter reload value based on the
*                  time needed
* Input          : Amount of time (us) needed, peripheral clock2 value
* Return         : None
*******************************************************************************/
void WDG_PeriodValueConfig ( u32 Time );

/*******************************************************************************
* Function Name  : WDG_CntOnOffConfig
* Description    : Start or stop the free auto-reload timer to countdown.
* Input          : ENABLE or DISABLE
* Return         : None
*******************************************************************************/
inline void WDG_CntOnOffConfig ( FunctionalState NewState )
{
  if (NewState == ENABLE) WDG->CR |= 0x0002; else WDG->CR &= ~0x0002;
}

/*******************************************************************************
* Function Name  : WDG_ECITConfig
* Description    : Enable or Disable the end of count interrupt
* Input          : ENABLE or DISABLE
* Return         : None
*******************************************************************************/
inline void WDG_ECITConfig (FunctionalState NewState)
{
  if (NewState == ENABLE) WDG->MR |= 0x0001; else WDG->MR &= ~0x0001;
}

/*******************************************************************************
* Function Name  : WDG_ECFlagClear
* Description    : Clear the end of count flag
* Input          : None
* Return         : None
*******************************************************************************/
inline void WDG_ECFlagClear ( void )
{
  WDG->SR = 0x0000;
}

/*******************************************************************************
* Function Name  : WDG_ECStatus
* Description    : Return the end of count status
* Input          : None
* Return         : NewState value
*******************************************************************************/
inline u16 WDG_ECStatus ( void )
{
  return WDG->SR;
}

#endif // __WDG_H

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
