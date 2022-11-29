/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : lcd.h
* Author             : MCD Application Team
* Date First Issued  : mm/dd/yyyy
* Description        : This file contains all the functions prototypes for the
*                      lcd software driver.
********************************************************************************
* History:
* mm/dd/yyyy
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __LCD_H
#define __LCD_H

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_lib.h"

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* LCD Registers */
#define R0             0x00
#define R1             0x01
#define R2             0x02
#define R3             0x03
#define R5             0x05
#define R6             0x06
#define R13            0x0D
#define R14            0x0E
#define R15            0x0F
#define R16            0x10
#define R17            0x11
#define R18            0x12
#define R19            0x13
#define R20            0x14
#define R21            0x15
#define R22            0x16
#define R23            0x17
#define R24            0x18
#define R25            0x19
#define R26            0x1A
#define R27            0x1B
#define R28            0x1C
#define R29            0x1D
#define R30            0x1E
#define R31            0x1F
#define R32            0x20
#define R36            0x24
#define R37            0x25
#define R40            0x28
#define R43            0x2B
#define R45            0x2D
#define R49            0x31
#define R50            0x32
#define R51            0x33
#define R52            0x34
#define R53            0x35
#define R55            0x37
#define R59            0x3B
#define R60            0x3C
#define R61            0x3D
#define R62            0x3E
#define R63            0x3F
#define R64            0x40
#define R65            0x41
#define R66            0x42
#define R67            0x43
#define R68            0x44
#define R69            0x45
#define R70            0x46
#define R71            0x47
#define R72            0x48
#define R73            0x49
#define R74            0x4A
#define R75            0x4B
#define R76            0x4C
#define R77            0x4D
#define R78            0x4E
#define R79            0x4F
#define R80            0x50
#define R118           0x76
#define R134           0x86
#define R135           0x87
#define R136           0x88
#define R137           0x89
#define R139           0x8B
#define R140           0x8C
#define R141           0x8D
#define R143           0x8F
#define R144           0x90
#define R145           0x91
#define R146           0x92
#define R147           0x93
#define R148           0x94
#define R149           0x95
#define R150           0x96
#define R151           0x97
#define R152           0x98
#define R153           0x99
#define R154           0x9A
#define R157           0x9D
#define R192           0xC0
#define R193           0xC1

/* LCD Control pins */
#define CtrlPin_NCS    GPIO_Pin_2   /* PB.02 */
#define CtrlPin_RS     GPIO_Pin_7   /* PD.07 */
#define CtrlPin_NWR    GPIO_Pin_15  /* PD.15 */

/* LCD color */
#define White          0xFFFF
#define Black          0x0000
#define Blue           0x001F
#define Orange         0x051F
#define Red            0xF800
#define Magenta        0xF81F
#define Green          0x07E0
#define Cyan           0x7FFF
#define Yellow         0xFFE0

#define Line0          0
#define Line1          24
#define Line2          48
#define Line3          72
#define Line4          96
#define Line5          120
#define Line6          144
#define Line7          168
#define Line8          192
#define Line9          216

#define Horizontal     0x00
#define Vertical       0x01

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
/*----- High layer function -----*/
void LCD_Init(void);
void LCD_SetTextColor(vu16 Color);
void LCD_SetBackColor(vu16 Color);
void LCD_ClearLine(u8 Line);
void LCD_Clear(void);
void LCD_SetCursor(u8 Xpos, u16 Ypos);
void LCD_DrawChar(u8 Xpos, u16 Ypos, uc16 *c);
void LCD_DisplayChar(u8 Line, u16 Column, u8 Ascii);
void LCD_DisplayStringLine(u8 Line, u8 *ptr);
void LCD_DisplayString(u8 Line, u8 *ptr);
void LCD_ScrollText(u8 Line, u8 *ptr);
void LCD_SetDisplayWindow(u8 Xpos, u16 Ypos, u8 Height, u16 Width);
void LCD_DrawLine(u8 Xpos, u16 Ypos, u16 Length, u8 Direction);
void LCD_DrawRect(u8 Xpos, u16 Ypos, u8 Height, u16 Width);
void LCD_DrawCircle(u8 Xpos, u16 Ypos, u16 Radius);
void LCD_DrawMonoPict(uc32 *Pict);
void LCD_DrawBMP(u32 BmpAddress);

/*----- Medium layer function -----*/
void LCD_WriteReg(u8 LCD_Reg, u8 LCD_RegValue);
u8 LCD_ReadReg(u8 LCD_Reg);
void LCD_WriteRAM(u16 RGB_Code);
u16  LCD_ReadRAM(void);
void LCD_PowerOn(void);
void LCD_DisplayOn(void);
void LCD_DisplayOff(void);

/*----- Low layer function -----*/
void LCD_CtrlLinesConfig(void);
void LCD_CtrlLinesWrite(GPIO_TypeDef* GPIOx, u16 CtrlPins, BitAction BitVal);
void LCD_SPIConfig(void);

#endif /* __LCD_H */

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
