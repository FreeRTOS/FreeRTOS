/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : eic.h
* Author             : MCD Application Team
* Date First Issued  : 25/06/2003
* Description        : This file contains all the functions prototypes for the
*                      EIC software library.
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
#ifndef __eic_H
#define __eic_H

#include "71x_map.h"

typedef enum
{
  T0TIMI_IRQChannel    = 0,
  FLASH_IRQChannel     = 1,
  RCCU_IRQChannel      = 2,
  RTC_IRQChannel       = 3,
  WDG_IRQChannel       = 4,
  XTI_IRQChannel       = 5,
  USBHP_IRQChannel     = 6,
  I2C0ITERR_IRQChannel = 7,
  I2C1ITERR_IRQChannel = 8,
  UART0_IRQChannel     = 9,
  UART1_IRQChannel     = 10,
  UART2_IRQChannel     = 11,
  UART3_IRQChannel     = 12,
  SPI0_IRQChannel      = 13,
  SPI1_IRQChannel      = 14,
  I2C0_IRQChannel      = 15,
  I2C1_IRQChannel      = 16,
  CAN_IRQChannel       = 17,
  ADC_IRQChannel       = 18,
  T1TIMI_IRQChannel    = 19,
  T2TIMI_IRQChannel    = 20,
  T3TIMI_IRQChannel    = 21,
  HDLC_IRQChannel      = 25,
  USBLP_IRQChannel     = 26,
  T0TOI_IRQChannel     = 29,
  T0OC1_IRQChannel     = 30,
  T0OC2_IRQChannel     = 31
} IRQChannel_TypeDef;

typedef enum
{
  T0TIMI_FIQChannel     = 0x00000001,
  WDG_FIQChannel        = 0x00000002,
  WDGT0TIMI_FIQChannels = 0x00000003
} FIQChannel_TypeDef;

/*******************************************************************************
* Function Name  : EIC_Init
* Description    : Initialise the EIC using the load PC instruction
*                 (PC = PC +offset)
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_Init(void);

/*******************************************************************************
* Function Name  : EIC_IRQConfig
* Description    : Enable or Disable IRQ interrupts
* Input 1        : New status : can be ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
inline void EIC_IRQConfig(FunctionalState NewState)
{
  if (NewState==ENABLE) EIC->ICR |= 0x0001; else EIC->ICR &= ~0x0001;
}

/*******************************************************************************
* Function Name  : EIC_FIQConfig
* Description    : Enable or Disable FIQ interrupts
* Input 1        : New status : can be ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
inline void EIC_FIQConfig(FunctionalState NewState)
{
  if (NewState==ENABLE) EIC->ICR |= 0x0002; else EIC->ICR &= ~0x0002;
}

/*******************************************************************************
* Function Name  : EIC_IRQChannelConfig
* Description    : Configure the IRQ Channel
* Input 1        : IRQ channel name
* Input 2        : Channel New status : can be ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
inline void EIC_IRQChannelConfig(IRQChannel_TypeDef IRQChannel, FunctionalState NewState)
{
  if (NewState==ENABLE) EIC->IER |= 0x0001 << IRQChannel;
  else EIC->IER &= ~(0x0001 << IRQChannel);
}

/*******************************************************************************
* Function Name  : EIC_FIQChannelConfig
* Description    : Configure the FIQ Channel
* Input 1        : FIQ channel name
* Input 2        : Channel New status : can be ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
inline void EIC_FIQChannelConfig(FIQChannel_TypeDef FIQChannel,
                          FunctionalState NewState)
{
  if (NewState==ENABLE) EIC->FIR |= FIQChannel;
  else EIC->FIR &= ~FIQChannel;
}

/*******************************************************************************
* Function Name  : EIC_IRQChannelPriorityConfig
* Description    : Configure the selected IRQ channel priority
* Input 1        : IRQ channel name
* Input 2        : IRQ channel priority
* Output         : None
* Return         : None
*******************************************************************************/
inline void EIC_IRQChannelPriorityConfig(IRQChannel_TypeDef IRQChannel, u8 Priority)
{
  EIC->SIR[IRQChannel] = (EIC->SIR[IRQChannel]&0xFFFF0000) | (u16)Priority & 0x000F;
}

/*******************************************************************************
* Function Name  : EIC_CurrentPriorityLevelConfig
* Description    : Change the current priority level of the srved IRQ routine
* Input 1        : New priority
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_CurrentPriorityLevelConfig(u8 NewPriorityLevel);

/*******************************************************************************
* Function Name  : EIC_CurrentPriorityLevelValue
* Description    : Return the current priority level of the current served IRQ
*                  routine
* Input          : None
* Output         : None
* Return         : The current priority level
*******************************************************************************/
inline u8 EIC_CurrentPriorityLevelValue(void)
{
  return EIC->CIPR & 0xF;
}

/*******************************************************************************
* Function Name  : EIC_CurrentIRQChannelValue
* Description    : Return the current served IRQ channel number
* Input 0        : None
* Output         : None
* Return         : The current served IRQ channel number
*******************************************************************************/
inline IRQChannel_TypeDef EIC_CurrentIRQChannelValue(void)
{
  return (IRQChannel_TypeDef)(EIC->CICR & 0x1F);
}

/*******************************************************************************
* Function Name  : EIC_CurrentFIQChannelValue
* Description    : Return the current served FIQ channel number
* Input          : None
* Output         : None
* Return         : The current served FIQ channel number
*******************************************************************************/
inline FIQChannel_TypeDef EIC_CurrentFIQChannelValue(void)
{
   return (FIQChannel_TypeDef)((EIC->FIR >> 2) & 0x0003);
}

/*******************************************************************************
* Function Name  : EIC_FIPendingBitClear
* Description    : Clear the FIQ pending bit
* Input 1        : FIQ channel
* Output         : None
* Return         : None
*******************************************************************************/
inline void EIC_FIQPendingBitClear(FIQChannel_TypeDef FIQChannel)
{
  EIC->FIR = (EIC->FIR & 0x0003) | (FIQChannel << 2);
}

#endif /* __eic_H */

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
