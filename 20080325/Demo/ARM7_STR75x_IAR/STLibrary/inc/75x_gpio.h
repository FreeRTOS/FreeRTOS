/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_gpio.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      GPIO software library.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __75x_GPIO_H
#define __75x_GPIO_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* Configuration Mode enumeration */
typedef enum
{ GPIO_Mode_AIN = 1,
  GPIO_Mode_IN_FLOATING,
  GPIO_Mode_IPD,
  GPIO_Mode_IPU,
  GPIO_Mode_Out_OD,
  GPIO_Mode_Out_PP,
  GPIO_Mode_AF_OD,
  GPIO_Mode_AF_PP
}GPIOMode_TypeDef;

/* GPIO Init structure definition */
typedef struct
{
  u32 GPIO_Pin;
  GPIOMode_TypeDef GPIO_Mode;
}GPIO_InitTypeDef;

/* Bit_SET and Bit_RESET enumeration */
typedef enum
{ Bit_RESET = 0,
  Bit_SET
}BitAction;


/* Exported constants --------------------------------------------------------*/
/* GPIO pins define */
#define GPIO_Pin_None        0x00000000  /* No pin selected */
#define GPIO_Pin_0           0x00000001  /* Pin 0 selected */
#define GPIO_Pin_1           0x00000002  /* Pin 1 selected */
#define GPIO_Pin_2           0x00000004  /* Pin 2 selected */
#define GPIO_Pin_3           0x00000008  /* Pin 3 selected */
#define GPIO_Pin_4           0x00000010  /* Pin 4 selected */
#define GPIO_Pin_5           0x00000020  /* Pin 5 selected */
#define GPIO_Pin_6           0x00000040  /* Pin 6 selected */
#define GPIO_Pin_7           0x00000080  /* Pin 7 selected */
#define GPIO_Pin_8           0x00000100  /* Pin 8 selected */
#define GPIO_Pin_9           0x00000200  /* Pin 9 selected */
#define GPIO_Pin_10          0x00000400  /* Pin 10 selected */
#define GPIO_Pin_11          0x00000800  /* Pin 11 selected */
#define GPIO_Pin_12          0x00001000  /* Pin 12 selected */
#define GPIO_Pin_13          0x00002000  /* Pin 13 selected */
#define GPIO_Pin_14          0x00004000  /* Pin 14 selected */
#define GPIO_Pin_15          0x00008000  /* Pin 15 selected */
#define GPIO_Pin_16          0x00010000  /* Pin 16 selected */
#define GPIO_Pin_17          0x00020000  /* Pin 17 selected */
#define GPIO_Pin_18          0x00040000  /* Pin 18 selected */
#define GPIO_Pin_19          0x00080000  /* Pin 19 selected */
#define GPIO_Pin_20          0x00100000  /* Pin 20 selected */
#define GPIO_Pin_21          0x00200000  /* Pin 21 selected */
#define GPIO_Pin_22          0x00400000  /* Pin 22 selected */
#define GPIO_Pin_23          0x00800000  /* Pin 23 selected */
#define GPIO_Pin_24          0x01000000  /* Pin 24 selected */
#define GPIO_Pin_25          0x02000000  /* Pin 25 selected */
#define GPIO_Pin_26          0x04000000  /* Pin 26 selected */
#define GPIO_Pin_27          0x08000000  /* Pin 27 selected */
#define GPIO_Pin_28          0x10000000  /* Pin 28 selected */
#define GPIO_Pin_29          0x20000000  /* Pin 29 selected */
#define GPIO_Pin_30          0x40000000  /* Pin 30 selected */
#define GPIO_Pin_31          0x80000000  /* Pin 31 selected */
#define GPIO_Pin_All         0xFFFFFFFF  /* All pins selected */

/* GPIO Remap define */
#define GPIO_Remap_SMI_CS3_EN  0x23 /* SMI CS3 Enable */
#define GPIO_Remap_SMI_CS2_EN  0x22 /* SMI CS2 Enable */
#define GPIO_Remap_SMI_CS1_EN  0x21 /* SMI CS1 Enable */
#define GPIO_Remap_SMI_EN      0x20 /* SMI Enable */
#define GPIO_Remap_DBGOFF      0x45 /* JTAG Disable */
#define GPIO_Remap_UART1       0x44 /* UART1 Alternate Function mapping */
#define GPIO_Remap_UART2       0x43 /* UART2 Alternate Function mapping */
#define GPIO_Remap_SSP1        0x42 /* SSP1 Alternate Function mapping */
#define GPIO_Remap_TIM2        0x41 /* TIM2 Alternate Function mapping */
#define GPIO_Remap_TIM0        0x40 /* TIM0 Alternate Function mapping */


/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void GPIO_DeInit(GPIO_TypeDef* GPIOx);
void GPIO_Init(GPIO_TypeDef* GPIOx, GPIO_InitTypeDef* GPIO_InitStruct);
void GPIO_StructInit(GPIO_InitTypeDef* GPIO_InitStruct);
u32  GPIO_Read(GPIO_TypeDef* GPIOx);
u8   GPIO_ReadBit(GPIO_TypeDef* GPIOx, u32 GPIO_Pin);
void GPIO_Write(GPIO_TypeDef* GPIOx, u32 PortVal);
void GPIO_WriteBit(GPIO_TypeDef* GPIOx,u32 GPIO_Pin, BitAction BitVal);
void GPIO_PinMaskConfig(GPIO_TypeDef* GPIOx, u32 GPIO_Pin, FunctionalState NewState);
u32  GPIO_GetPortMask(GPIO_TypeDef* GPIOx);
void GPIO_PinRemapConfig(u16 GPIO_Remap, FunctionalState NewState);

#endif /* __75x_GPIO_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
