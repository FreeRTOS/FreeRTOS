/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : lcd.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      lcd software driver.
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

/* Define to prevent recursive inclusion ---------------------------------------*/
#ifndef __LCD_H
#define __LCD_H

/* Includes --------------------------------------------------------------------*/
#include "75x_lib.h"

/* Exported types --------------------------------------------------------------*/

  /* Data lines configuration mode */
  typedef enum
  {
    Input,
    Output
  } DataConfigMode_TypeDef;

  /* Text color mode */
  typedef enum
  {
    BlackText=0,
    WhiteText=1
  } TextColorMode_TypeDef;

  /* Dot On/Off mode */
  typedef enum
  {
    Dot_On,
    Dot_Off
  } DotMode_TypeDef;

/* Exported constants ----------------------------------------------------------*/

/* LCD Control pins */
#define CtrlPin_E2           0x00000001
#define CtrlPin_E1           0x00000002
#define CtrlPin_RW           0x00000004
#define CtrlPin_DI           0x00000008

/* LCD Commands */
#define DISPLAY_ON             0xAF
#define DISPLAY_OFF            0xAE
#define START_LINE             0xC0
#define START_COLUMN           0x00
#define CLOCKWISE_OUTPUT       0xA0
#define DYNAMIC_DRIVE 	       0xA4
#define DUTY_CYCLE             0xA9
#define READ_MODIFY_WRITE_OFF  0xEE
#define SOFTWARE_RESET         0xE2

/* LCD Lines when LCD is managed as 2*17 characters */
#define Line1    0x0
#define Line2    0x2

/* Exported macro --------------------------------------------------------------*/
/* Exported functions ----------------------------------------------------------*/
/*----- Low layer function -----*/
void LCD_CtrlLinesConfig(void);
void LCD_CtrlLinesWrite(GPIO_TypeDef* GPIOx, u32 CtrlPins, BitAction BitVal);
void LCD_DataLinesConfig(DataConfigMode_TypeDef Mode);
void LCD_DataLinesWrite(GPIO_TypeDef* GPIOx, u32 PortVal);

/*----- Medium layer function -----*/
void LCD_CheckMasterStatus(void);
void LCD_CheckSlaveStatus(void);
void LCD_SendMasterCmd(u8 Cmd);
void LCD_SendSlaveCmd(u8 Cmd);
void LCD_SendMasterData(u8 Data);
u32 LCD_ReadMasterData(void);
void LCD_SendSlaveData(u8 Data);
u32 LCD_ReadSlaveData(void);
void LCD_SetMasterPage(u8 Page); 	
void LCD_SetSlavePage(u8 Page);
void LCD_SetMasterColumn(u8 Address);
void LCD_SetSlaveColumn(u8 Address);
void LCD_DrawChar(u8 Line, u8 Column, u8 Width, u8 *Bmp);
u8 LCD_HexToAsciiLow(u8 byte);
u8 LCD_HexToAsciiHigh(u8 byte);
void LCD_SetTextColor(TextColorMode_TypeDef TextColor);

/*----- High layer function -----*/
void LCD_Init(void);
/* LCD managed as 2 Lines, 17 characters each one (2Lines*17Char) */
void LCD_ClearLine(u8 Line);
void LCD_DisplayChar(u8 Line, u8 Column, u8 Ascii, TextColorMode_TypeDef CharMode);
void LCD_DisplayString(u8 Line, u8 *ptr, TextColorMode_TypeDef CharMode);
void LCD_Printf(u8* ptr, ...);
/* LCD managed as 122*32 dots */
void LCD_ClearMaster(void);
void LCD_ClearSlave(void);
void LCD_Clear(void);
void LCD_DrawMasterGraphic(u8 *Bmp);
void LCD_DrawSlaveGraphic(u8 *Bmp);
void LCD_DrawGraphic(u8 *Bmp);
void LCD_ScrollGraphic(u8 *Bmp, u32 nCount);
void LCD_DrawPixel(u8 XPos, u8 YPos, DotMode_TypeDef Mode);
void LCD_DrawLine(u8 XPos1, u8 YPos1, u8 XPos2, u8 YPos2);
void LCD_DrawBox(u8 XPos, u8 YPos, u8 Dx, u8 Dy);

#endif /*__LCD_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE******/
