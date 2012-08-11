/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_gpio.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file contains all the functions prototypes for the
*                      GPIO software library.
********************************************************************************
* History:
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

/* Define to prevent recursive inclusion ------------------------------------ */

#ifndef _91x_GPIO_H
#define _91x_GPIO_H

/* Includes ------------------------------------------------------------------*/
#include "91x_map.h"

/* GPIO Init structure definition */
typedef struct
{
  u8 GPIO_Pin;
  u8 GPIO_Direction;
  u8 GPIO_Type;
  u8 GPIO_IPConnected;
  u16 GPIO_Alternate;
}GPIO_InitTypeDef;

/* Bit_SET and Bit_RESET enumeration */
typedef enum
{ Bit_RESET = 0,
  Bit_SET
}BitAction;


/* Exported constants --------------------------------------------------------*/
#define GPIO_Pin_None 0x00
#define GPIO_Pin_0    0x01
#define GPIO_Pin_1    0x02
#define GPIO_Pin_2    0x04
#define GPIO_Pin_3    0x08
#define GPIO_Pin_4    0x10
#define GPIO_Pin_5    0x20
#define GPIO_Pin_6    0x40
#define GPIO_Pin_7    0x80
#define GPIO_Pin_All  0xFF

#define GPIO_PinInput  0x00
#define GPIO_PinOutput 0x01

#define GPIO_Type_PushPull      0x00
#define GPIO_Type_OpenCollector 0x01

#define GPIO_IPConnected_Disable 0x00
#define GPIO_IPConnected_Enable  0x01

#define GPIO_InputAlt1  0x00
#define GPIO_OutputAlt1 0x01
#define GPIO_OutputAlt2 0x02
#define GPIO_OutputAlt3 0x03

#define GPIO_ANAChannel0   0x01
#define GPIO_ANAChannel1   0x02
#define GPIO_ANAChannel2   0x04
#define GPIO_ANAChannel3   0x08
#define GPIO_ANAChannel4   0x10
#define GPIO_ANAChannel5   0x20
#define GPIO_ANAChannel6   0x40
#define GPIO_ANAChannel7   0x80
#define GPIO_ANAChannelALL 0xFF

void GPIO_DeInit(GPIO_TypeDef* GPIOx);
void GPIO_Init(GPIO_TypeDef* GPIOx, GPIO_InitTypeDef* GPIO_InitStruct);
void GPIO_StructInit(GPIO_InitTypeDef* GPIO_InitStruct);
u8 GPIO_ReadBit(GPIO_TypeDef* GPIOx, u8 GPIO_Pin);
u8 GPIO_Read(GPIO_TypeDef* GPIOx);
void GPIO_WriteBit(GPIO_TypeDef* GPIOx, u8 GPIO_Pin, BitAction BitVal);
void GPIO_Write(GPIO_TypeDef* GPIOx, u8 PortVal);
void GPIO_EMIConfig(FunctionalState NewState);
void GPIO_ANAPinConfig(u8 GPIO_ANAChannel, FunctionalState NewState);

#endif /* _91x_GPIO_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
