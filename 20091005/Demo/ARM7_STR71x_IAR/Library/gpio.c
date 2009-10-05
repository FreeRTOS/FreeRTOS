/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : gpio.c
* Author             : MCD Application Team
* Date First Issued  : 06/08/2003
* Description        : This file provides all the GPIO software functions
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

#include "gpio.h"

/*******************************************************************************
* Function Name  : GPIO_Config
* Description    : Configure the GPIO port pins
* Input 1        : GPIOx (x can be 0,1 or 2) the desired port
* Input 2        : Port_Pins : pins placements
* Input 3        : Pins Mode
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_Config (GPIO_TypeDef *GPIOx, u16 Port_Pins, GpioPinMode_TypeDef GPIO_Mode)
{
  switch (GPIO_Mode)
  {
    case GPIO_HI_AIN_TRI:
      GPIOx->PC0&=~Port_Pins;
      GPIOx->PC1&=~Port_Pins;
      GPIOx->PC2&=~Port_Pins;
      break;

    case GPIO_IN_TRI_TTL:
      GPIOx->PC0|=Port_Pins;
      GPIOx->PC1&=~Port_Pins;
      GPIOx->PC2&=~Port_Pins;
      break;

    case GPIO_IN_TRI_CMOS:
      GPIOx->PC0&=~Port_Pins;
      GPIOx->PC1|=Port_Pins;
      GPIOx->PC2&=~Port_Pins;
      break;

    case GPIO_IPUPD_WP:
      GPIOx->PC0|=Port_Pins;
      GPIOx->PC1|=Port_Pins;
      GPIOx->PC2&=~Port_Pins;
      break;

    case GPIO_OUT_OD:
      GPIOx->PC0&=~Port_Pins;
      GPIOx->PC1&=~Port_Pins;
      GPIOx->PC2|=Port_Pins;
      break;

    case GPIO_OUT_PP:
      GPIOx->PC0|=Port_Pins;
      GPIOx->PC1&=~Port_Pins;
      GPIOx->PC2|=Port_Pins;
      break;

    case GPIO_AF_OD:
      GPIOx->PC0&=~Port_Pins;
      GPIOx->PC1|=Port_Pins;
      GPIOx->PC2|=Port_Pins;
      break;

    case GPIO_AF_PP:
      GPIOx->PC0|=Port_Pins;
      GPIOx->PC1|=Port_Pins;
      GPIOx->PC2|=Port_Pins;
      break;
  }
}

/*******************************************************************************
* Function Name  : GPIO_BitWrite
* Description    : Set or reset the selected port pin
* Input 1        : Selected GPIO port
* Input 2        : Pin number
* Input 3        : bit value
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_BitWrite(GPIO_TypeDef *GPIOx, u8 Port_Pin, u8 Port_Val)
{
  if (Port_Val&0x01) GPIOx->PD |= 1<<Port_Pin; else GPIOx->PD &= ~(1<<Port_Pin);
}

/*******************************************************************************
* Function Name  : GPIO_ByteWrite
* Description    : Write byte value to the selected PD register
* Input 1        : Selected GPIO port
* Input 2        : GPIO_MSB or GPIO_LSB
* Input 3        : Byte value
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_ByteWrite(GPIO_TypeDef *GPIOx, u8 Port_Byte, u8 Port_Val)
{
  GPIOx->PD = Port_Byte ? (GPIOx->PD&0x00FF) | ((u16)Port_Val<<8)
                        : (GPIOx->PD&0xFF00) | Port_Val;
}

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
