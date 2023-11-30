/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : lcd.c
* Author             : MCD Application Team
* Date First Issued  : mm/dd/yyyy
* Description        : This file includes the LCD driver for AM-240320LTNQW00H
*                      liquid Crystal Display Module of STM32F10x-EVAL.
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

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_type.h"
#include "lcd.h"
#include "spi_flash.h"

#include "FreeRTOS.h"
#include "task.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
     /* ASCII Table: each character is 16 column (16dots large)
        and 24 raw (24 dots high) */
     const uc16 ASCII_Table[] =
       {
         /* Space ' ' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '!' */
         0x0000, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0000, 0x0000,
         0x0180, 0x0180, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '"' */
         0x0000, 0x0000, 0x00CC, 0x00CC, 0x00CC, 0x00CC, 0x00CC, 0x00CC,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '#' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0C60, 0x0C60,
         0x0C60, 0x0630, 0x0630, 0x1FFE, 0x1FFE, 0x0630, 0x0738, 0x0318,
         0x1FFE, 0x1FFE, 0x0318, 0x0318, 0x018C, 0x018C, 0x018C, 0x0000,
         /* '$' */
         0x0000, 0x0080, 0x03E0, 0x0FF8, 0x0E9C, 0x1C8C, 0x188C, 0x008C,
         0x0098, 0x01F8, 0x07E0, 0x0E80, 0x1C80, 0x188C, 0x188C, 0x189C,
         0x0CB8, 0x0FF0, 0x03E0, 0x0080, 0x0080, 0x0000, 0x0000, 0x0000,
         /* '%' */
         0x0000, 0x0000, 0x0000, 0x180E, 0x0C1B, 0x0C11, 0x0611, 0x0611,
         0x0311, 0x0311, 0x019B, 0x018E, 0x38C0, 0x6CC0, 0x4460, 0x4460,
         0x4430, 0x4430, 0x4418, 0x6C18, 0x380C, 0x0000, 0x0000, 0x0000,
         /* '&' */
         0x0000, 0x01E0, 0x03F0, 0x0738, 0x0618, 0x0618, 0x0330, 0x01F0,
         0x00F0, 0x00F8, 0x319C, 0x330E, 0x1E06, 0x1C06, 0x1C06, 0x3F06,
         0x73FC, 0x21F0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* ''' */
         0x0000, 0x0000, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '(' */
         0x0000, 0x0200, 0x0300, 0x0180, 0x00C0, 0x00C0, 0x0060, 0x0060,
         0x0030, 0x0030, 0x0030, 0x0030, 0x0030, 0x0030, 0x0030, 0x0030,
         0x0060, 0x0060, 0x00C0, 0x00C0, 0x0180, 0x0300, 0x0200, 0x0000,
         /* ')' */
         0x0000, 0x0020, 0x0060, 0x00C0, 0x0180, 0x0180, 0x0300, 0x0300,
         0x0600, 0x0600, 0x0600, 0x0600, 0x0600, 0x0600, 0x0600, 0x0600,
         0x0300, 0x0300, 0x0180, 0x0180, 0x00C0, 0x0060, 0x0020, 0x0000,
         /* '*' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x00C0, 0x00C0,
         0x06D8, 0x07F8, 0x01E0, 0x0330, 0x0738, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '+' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0180, 0x3FFC, 0x3FFC, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* ',' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0180, 0x0180, 0x0100, 0x0100, 0x0080, 0x0000, 0x0000,
         /* '-' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x07E0, 0x07E0, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '.' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x00C0, 0x00C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '/' */
         0x0000, 0x0C00, 0x0C00, 0x0600, 0x0600, 0x0600, 0x0300, 0x0300,
         0x0300, 0x0380, 0x0180, 0x0180, 0x0180, 0x00C0, 0x00C0, 0x00C0,
         0x0060, 0x0060, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '0' */
         0x0000, 0x03E0, 0x07F0, 0x0E38, 0x0C18, 0x180C, 0x180C, 0x180C,
         0x180C, 0x180C, 0x180C, 0x180C, 0x180C, 0x180C, 0x0C18, 0x0E38,
         0x07F0, 0x03E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '1' */
         0x0000, 0x0100, 0x0180, 0x01C0, 0x01F0, 0x0198, 0x0188, 0x0180,
         0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '2' */
         0x0000, 0x03E0, 0x0FF8, 0x0C18, 0x180C, 0x180C, 0x1800, 0x1800,
         0x0C00, 0x0600, 0x0300, 0x0180, 0x00C0, 0x0060, 0x0030, 0x0018,
         0x1FFC, 0x1FFC, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '3' */
         0x0000, 0x01E0, 0x07F8, 0x0E18, 0x0C0C, 0x0C0C, 0x0C00, 0x0600,
         0x03C0, 0x07C0, 0x0C00, 0x1800, 0x1800, 0x180C, 0x180C, 0x0C18,
         0x07F8, 0x03E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '4' */
         0x0000, 0x0C00, 0x0E00, 0x0F00, 0x0F00, 0x0D80, 0x0CC0, 0x0C60,
         0x0C60, 0x0C30, 0x0C18, 0x0C0C, 0x3FFC, 0x3FFC, 0x0C00, 0x0C00,
         0x0C00, 0x0C00, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '5' */
         0x0000, 0x0FF8, 0x0FF8, 0x0018, 0x0018, 0x000C, 0x03EC, 0x07FC,
         0x0E1C, 0x1C00, 0x1800, 0x1800, 0x1800, 0x180C, 0x0C1C, 0x0E18,
         0x07F8, 0x03E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '6' */
         0x0000, 0x07C0, 0x0FF0, 0x1C38, 0x1818, 0x0018, 0x000C, 0x03CC,
         0x0FEC, 0x0E3C, 0x1C1C, 0x180C, 0x180C, 0x180C, 0x1C18, 0x0E38,
         0x07F0, 0x03E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '7' */
         0x0000, 0x1FFC, 0x1FFC, 0x0C00, 0x0600, 0x0600, 0x0300, 0x0380,
         0x0180, 0x01C0, 0x00C0, 0x00E0, 0x0060, 0x0060, 0x0070, 0x0030,
         0x0030, 0x0030, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '8' */
         0x0000, 0x03E0, 0x07F0, 0x0E38, 0x0C18, 0x0C18, 0x0C18, 0x0638,
         0x07F0, 0x07F0, 0x0C18, 0x180C, 0x180C, 0x180C, 0x180C, 0x0C38,
         0x0FF8, 0x03E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '9' */
         0x0000, 0x03E0, 0x07F0, 0x0E38, 0x0C1C, 0x180C, 0x180C, 0x180C,
         0x1C1C, 0x1E38, 0x1BF8, 0x19E0, 0x1800, 0x0C00, 0x0C00, 0x0E1C,
         0x07F8, 0x01F0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* ':' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0180, 0x0180,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0180, 0x0180, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* ';' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0180, 0x0180,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0180, 0x0180, 0x0100, 0x0100, 0x0080, 0x0000, 0x0000, 0x0000,
         /* '<' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x1000, 0x1C00, 0x0F80, 0x03E0, 0x00F8, 0x0018, 0x00F8, 0x03E0,
         0x0F80, 0x1C00, 0x1000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '=' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x1FF8, 0x0000, 0x0000, 0x0000, 0x1FF8, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '>' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0008, 0x0038, 0x01F0, 0x07C0, 0x1F00, 0x1800, 0x1F00, 0x07C0,
         0x01F0, 0x0038, 0x0008, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '?' */
         0x0000, 0x03E0, 0x0FF8, 0x0C18, 0x180C, 0x180C, 0x1800, 0x0C00,
         0x0600, 0x0300, 0x0180, 0x00C0, 0x00C0, 0x00C0, 0x0000, 0x0000,
         0x00C0, 0x00C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '@' */
         0x0000, 0x0000, 0x07E0, 0x1818, 0x2004, 0x29C2, 0x4A22, 0x4411,
         0x4409, 0x4409, 0x4409, 0x2209, 0x1311, 0x0CE2, 0x4002, 0x2004,
         0x1818, 0x07E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'A' */
         0x0000, 0x0380, 0x0380, 0x06C0, 0x06C0, 0x06C0, 0x0C60, 0x0C60,
         0x1830, 0x1830, 0x1830, 0x3FF8, 0x3FF8, 0x701C, 0x600C, 0x600C,
         0xC006, 0xC006, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'B' */
         0x0000, 0x03FC, 0x0FFC, 0x0C0C, 0x180C, 0x180C, 0x180C, 0x0C0C,
         0x07FC, 0x0FFC, 0x180C, 0x300C, 0x300C, 0x300C, 0x300C, 0x180C,
         0x1FFC, 0x07FC, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'C' */
         0x0000, 0x07C0, 0x1FF0, 0x3838, 0x301C, 0x700C, 0x6006, 0x0006,
         0x0006, 0x0006, 0x0006, 0x0006, 0x0006, 0x6006, 0x700C, 0x301C,
         0x1FF0, 0x07E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'D' */
         0x0000, 0x03FE, 0x0FFE, 0x0E06, 0x1806, 0x1806, 0x3006, 0x3006,
         0x3006, 0x3006, 0x3006, 0x3006, 0x3006, 0x1806, 0x1806, 0x0E06,
         0x0FFE, 0x03FE, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'E' */
         0x0000, 0x3FFC, 0x3FFC, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C,
         0x1FFC, 0x1FFC, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C,
         0x3FFC, 0x3FFC, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'F' */
         0x0000, 0x3FF8, 0x3FF8, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018,
         0x1FF8, 0x1FF8, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018,
         0x0018, 0x0018, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'G' */
         0x0000, 0x0FE0, 0x3FF8, 0x783C, 0x600E, 0xE006, 0xC007, 0x0003,
         0x0003, 0xFE03, 0xFE03, 0xC003, 0xC007, 0xC006, 0xC00E, 0xF03C,
         0x3FF8, 0x0FE0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'H' */
         0x0000, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C,
         0x3FFC, 0x3FFC, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C,
         0x300C, 0x300C, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'I' */
         0x0000, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'J' */
         0x0000, 0x0600, 0x0600, 0x0600, 0x0600, 0x0600, 0x0600, 0x0600,
         0x0600, 0x0600, 0x0600, 0x0600, 0x0600, 0x0618, 0x0618, 0x0738,
         0x03F0, 0x01E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'K' */
         0x0000, 0x3006, 0x1806, 0x0C06, 0x0606, 0x0306, 0x0186, 0x00C6,
         0x0066, 0x0076, 0x00DE, 0x018E, 0x0306, 0x0606, 0x0C06, 0x1806,
         0x3006, 0x6006, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'L' */
         0x0000, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018,
         0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018,
         0x1FF8, 0x1FF8, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'M' */
         0x0000, 0xE00E, 0xF01E, 0xF01E, 0xF01E, 0xD836, 0xD836, 0xD836,
         0xD836, 0xCC66, 0xCC66, 0xCC66, 0xC6C6, 0xC6C6, 0xC6C6, 0xC6C6,
         0xC386, 0xC386, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'N' */
         0x0000, 0x300C, 0x301C, 0x303C, 0x303C, 0x306C, 0x306C, 0x30CC,
         0x30CC, 0x318C, 0x330C, 0x330C, 0x360C, 0x360C, 0x3C0C, 0x3C0C,
         0x380C, 0x300C, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'O' */
         0x0000, 0x07E0, 0x1FF8, 0x381C, 0x700E, 0x6006, 0xC003, 0xC003,
         0xC003, 0xC003, 0xC003, 0xC003, 0xC003, 0x6006, 0x700E, 0x381C,
         0x1FF8, 0x07E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'P' */
         0x0000, 0x0FFC, 0x1FFC, 0x380C, 0x300C, 0x300C, 0x300C, 0x300C,
         0x180C, 0x1FFC, 0x07FC, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C,
         0x000C, 0x000C, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'Q' */
         0x0000, 0x07E0, 0x1FF8, 0x381C, 0x700E, 0x6006, 0xE003, 0xC003,
         0xC003, 0xC003, 0xC003, 0xC003, 0xE007, 0x6306, 0x3F0E, 0x3C1C,
         0x3FF8, 0xF7E0, 0xC000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'R' */
         0x0000, 0x0FFE, 0x1FFE, 0x3806, 0x3006, 0x3006, 0x3006, 0x3806,
         0x1FFE, 0x07FE, 0x0306, 0x0606, 0x0C06, 0x1806, 0x1806, 0x3006,
         0x3006, 0x6006, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'S' */
         0x0000, 0x03E0, 0x0FF8, 0x0C1C, 0x180C, 0x180C, 0x000C, 0x001C,
         0x03F8, 0x0FE0, 0x1E00, 0x3800, 0x3006, 0x3006, 0x300E, 0x1C1C,
         0x0FF8, 0x07E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'T' */
         0x0000, 0x7FFE, 0x7FFE, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'U' */
         0x0000, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C,
         0x300C, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C, 0x300C, 0x1818,
         0x1FF8, 0x07E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'V' */
         0x0000, 0x6003, 0x3006, 0x3006, 0x3006, 0x180C, 0x180C, 0x180C,
         0x0C18, 0x0C18, 0x0E38, 0x0630, 0x0630, 0x0770, 0x0360, 0x0360,
         0x01C0, 0x01C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'W' */
         0x0000, 0x6003, 0x61C3, 0x61C3, 0x61C3, 0x3366, 0x3366, 0x3366,
         0x3366, 0x3366, 0x3366, 0x1B6C, 0x1B6C, 0x1B6C, 0x1A2C, 0x1E3C,
         0x0E38, 0x0E38, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'X' */
         0x0000, 0xE00F, 0x700C, 0x3018, 0x1830, 0x0C70, 0x0E60, 0x07C0,
         0x0380, 0x0380, 0x03C0, 0x06E0, 0x0C70, 0x1C30, 0x1818, 0x300C,
         0x600E, 0xE007, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'Y' */
         0x0000, 0xC003, 0x6006, 0x300C, 0x381C, 0x1838, 0x0C30, 0x0660,
         0x07E0, 0x03C0, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'Z' */
         0x0000, 0x7FFC, 0x7FFC, 0x6000, 0x3000, 0x1800, 0x0C00, 0x0600,
         0x0300, 0x0180, 0x00C0, 0x0060, 0x0030, 0x0018, 0x000C, 0x0006,
         0x7FFE, 0x7FFE, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '[' */
         0x0000, 0x03E0, 0x03E0, 0x0060, 0x0060, 0x0060, 0x0060, 0x0060,
         0x0060, 0x0060, 0x0060, 0x0060, 0x0060, 0x0060, 0x0060, 0x0060,
         0x0060, 0x0060, 0x0060, 0x0060, 0x0060, 0x03E0, 0x03E0, 0x0000,
         /* '\' */
         0x0000, 0x0030, 0x0030, 0x0060, 0x0060, 0x0060, 0x00C0, 0x00C0,
         0x00C0, 0x01C0, 0x0180, 0x0180, 0x0180, 0x0300, 0x0300, 0x0300,
         0x0600, 0x0600, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* ']' */
         0x0000, 0x03E0, 0x03E0, 0x0300, 0x0300, 0x0300, 0x0300, 0x0300,
         0x0300, 0x0300, 0x0300, 0x0300, 0x0300, 0x0300, 0x0300, 0x0300,
         0x0300, 0x0300, 0x0300, 0x0300, 0x0300, 0x03E0, 0x03E0, 0x0000,
         /* '^' */
         0x0000, 0x0000, 0x01C0, 0x01C0, 0x0360, 0x0360, 0x0360, 0x0630,
         0x0630, 0x0C18, 0x0C18, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '_' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0xFFFF, 0xFFFF, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* ''' */
         0x0000, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'a' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x03F0, 0x07F8,
         0x0C1C, 0x0C0C, 0x0F00, 0x0FF0, 0x0CF8, 0x0C0C, 0x0C0C, 0x0F1C,
         0x0FF8, 0x18F0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'b' */
         0x0000, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x03D8, 0x0FF8,
         0x0C38, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x0C38,
         0x0FF8, 0x03D8, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'c' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x03C0, 0x07F0,
         0x0E30, 0x0C18, 0x0018, 0x0018, 0x0018, 0x0018, 0x0C18, 0x0E30,
         0x07F0, 0x03C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'd' */
         0x0000, 0x1800, 0x1800, 0x1800, 0x1800, 0x1800, 0x1BC0, 0x1FF0,
         0x1C30, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1C30,
         0x1FF0, 0x1BC0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'e' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x03C0, 0x0FF0,
         0x0C30, 0x1818, 0x1FF8, 0x1FF8, 0x0018, 0x0018, 0x1838, 0x1C30,
         0x0FF0, 0x07C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'f' */
         0x0000, 0x0F80, 0x0FC0, 0x00C0, 0x00C0, 0x00C0, 0x07F0, 0x07F0,
         0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0,
         0x00C0, 0x00C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'g' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0DE0, 0x0FF8,
         0x0E18, 0x0C0C, 0x0C0C, 0x0C0C, 0x0C0C, 0x0C0C, 0x0C0C, 0x0E18,
         0x0FF8, 0x0DE0, 0x0C00, 0x0C0C, 0x061C, 0x07F8, 0x01F0, 0x0000,
         /* 'h' */
         0x0000, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x07D8, 0x0FF8,
         0x1C38, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818,
         0x1818, 0x1818, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'i' */
         0x0000, 0x00C0, 0x00C0, 0x0000, 0x0000, 0x0000, 0x00C0, 0x00C0,
         0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0,
         0x00C0, 0x00C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'j' */
         0x0000, 0x00C0, 0x00C0, 0x0000, 0x0000, 0x0000, 0x00C0, 0x00C0,
         0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0,
         0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00F8, 0x0078, 0x0000,
         /* 'k' */
         0x0000, 0x000C, 0x000C, 0x000C, 0x000C, 0x000C, 0x0C0C, 0x060C,
         0x030C, 0x018C, 0x00CC, 0x006C, 0x00FC, 0x019C, 0x038C, 0x030C,
         0x060C, 0x0C0C, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'l' */
         0x0000, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0,
         0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0,
         0x00C0, 0x00C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'm' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x3C7C, 0x7EFF,
         0xE3C7, 0xC183, 0xC183, 0xC183, 0xC183, 0xC183, 0xC183, 0xC183,
         0xC183, 0xC183, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'n' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0798, 0x0FF8,
         0x1C38, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818,
         0x1818, 0x1818, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'o' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x03C0, 0x0FF0,
         0x0C30, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x0C30,
         0x0FF0, 0x03C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'p' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x03D8, 0x0FF8,
         0x0C38, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x0C38,
         0x0FF8, 0x03D8, 0x0018, 0x0018, 0x0018, 0x0018, 0x0018, 0x0000,
         /* 'q' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x1BC0, 0x1FF0,
         0x1C30, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1C30,
         0x1FF0, 0x1BC0, 0x1800, 0x1800, 0x1800, 0x1800, 0x1800, 0x0000,
         /* 'r' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x07B0, 0x03F0,
         0x0070, 0x0030, 0x0030, 0x0030, 0x0030, 0x0030, 0x0030, 0x0030,
         0x0030, 0x0030, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 's' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x03E0, 0x03F0,
         0x0E38, 0x0C18, 0x0038, 0x03F0, 0x07C0, 0x0C00, 0x0C18, 0x0E38,
         0x07F0, 0x03E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 't' */
         0x0000, 0x0000, 0x0080, 0x00C0, 0x00C0, 0x00C0, 0x07F0, 0x07F0,
         0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0,
         0x07C0, 0x0780, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'u' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x1818, 0x1818,
         0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1818, 0x1C38,
         0x1FF0, 0x19E0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'v' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x180C, 0x0C18,
         0x0C18, 0x0C18, 0x0630, 0x0630, 0x0630, 0x0360, 0x0360, 0x0360,
         0x01C0, 0x01C0, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'w' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x41C1, 0x41C1,
         0x61C3, 0x6363, 0x6363, 0x6363, 0x3636, 0x3636, 0x3636, 0x1C1C,
         0x1C1C, 0x1C1C, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'x' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x381C, 0x1C38,
         0x0C30, 0x0660, 0x0360, 0x0360, 0x0360, 0x0360, 0x0660, 0x0C30,
         0x1C38, 0x381C, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* 'y' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x3018, 0x1830,
         0x1830, 0x1870, 0x0C60, 0x0C60, 0x0CE0, 0x06C0, 0x06C0, 0x0380,
         0x0380, 0x0380, 0x0180, 0x0180, 0x01C0, 0x00F0, 0x0070, 0x0000,
         /* 'z' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x1FFC, 0x1FFC,
         0x0C00, 0x0600, 0x0300, 0x0180, 0x00C0, 0x0060, 0x0030, 0x0018,
         0x1FFC, 0x1FFC, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         /* '{' */
         0x0000, 0x0300, 0x0180, 0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x00C0,
         0x00C0, 0x0060, 0x0060, 0x0030, 0x0060, 0x0040, 0x00C0, 0x00C0,
         0x00C0, 0x00C0, 0x00C0, 0x00C0, 0x0180, 0x0300, 0x0000, 0x0000,
         /* '|' */
         0x0000, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0180, 0x0000,
         /* '}' */
         0x0000, 0x0060, 0x00C0, 0x01C0, 0x0180, 0x0180, 0x0180, 0x0180,
         0x0180, 0x0300, 0x0300, 0x0600, 0x0300, 0x0100, 0x0180, 0x0180,
         0x0180, 0x0180, 0x0180, 0x0180, 0x00C0, 0x0060, 0x0000, 0x0000,
         /* '~' */
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x10F0, 0x1FF8, 0x0F08, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
         0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
      };
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
  /* Global variables to set the written text color */
static  vu16 TextColor = 0x0000, BackColor = 0xFFFF;

/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
static u32 StrLength(u8 *Str);

/*******************************************************************************
* Function Name  : LCD_Init
* Description    : Initializes LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_Init(void)
{
/* Configure the LCD Control pins --------------------------------------------*/
  LCD_CtrlLinesConfig();

/* Configure the SPI2 interface ----------------------------------------------*/
  LCD_SPIConfig();

/* Enable the LCD Oscillator -------------------------------------------------*/
  LCD_WriteReg(R1, 0x10);
  LCD_WriteReg(R0, 0xA0);
  LCD_WriteReg(R3, 0x01);
  vTaskDelay( 10 / portTICK_PERIOD_MS ); /* Delay 10 ms */
  LCD_WriteReg(R3, 0x00);
  LCD_WriteReg(R43, 0x04);

  LCD_WriteReg(R40, 0x18);
  LCD_WriteReg(R26, 0x05);
  LCD_WriteReg(R37, 0x05);
  LCD_WriteReg(R25, 0x00);

/* LCD Power On --------------------------------------------------------------*/
  LCD_WriteReg(R28, 0x73);
  LCD_WriteReg(R36, 0x74);
  LCD_WriteReg(R30, 0x01);
  LCD_WriteReg(R24, 0xC1);
  vTaskDelay( 10 / portTICK_PERIOD_MS ); /* Delay 10 ms */
  LCD_WriteReg(R24, 0xE1);
  LCD_WriteReg(R24, 0xF1);
  vTaskDelay( 60 / portTICK_PERIOD_MS ); /* Delay 60 ms */
  LCD_WriteReg(R24, 0xF5);
  vTaskDelay( 60 / portTICK_PERIOD_MS ); /* Delay 60 ms */
  LCD_WriteReg(R27, 0x09);
  vTaskDelay( 10 / portTICK_PERIOD_MS ); /* Delay 10 ms */
  LCD_WriteReg(R31, 0x11);
  LCD_WriteReg(R32, 0x0E);
  LCD_WriteReg(R30, 0x81);
  vTaskDelay( 10 / portTICK_PERIOD_MS ); /* Delay 10 ms */

/* Chip Set ------------------------------------------------------------------*/
  LCD_WriteReg(R157, 0x00);
  LCD_WriteReg(R192, 0x00);

  LCD_WriteReg(R14, 0x00);
  LCD_WriteReg(R15, 0x00);
  LCD_WriteReg(R16, 0x00);
  LCD_WriteReg(R17, 0x00);
  LCD_WriteReg(R18, 0x00);
  LCD_WriteReg(R19, 0x00);
  LCD_WriteReg(R20, 0x00);
  LCD_WriteReg(R21, 0x00);
  LCD_WriteReg(R22, 0x00);
  LCD_WriteReg(R23, 0x00);

  LCD_WriteReg(R52, 0x01);
  LCD_WriteReg(R53, 0x00);

  LCD_WriteReg(R75, 0x00);
  LCD_WriteReg(R76, 0x00);
  LCD_WriteReg(R78, 0x00);
  LCD_WriteReg(R79, 0x00);
  LCD_WriteReg(R80, 0x00);

  LCD_WriteReg(R60, 0x00);
  LCD_WriteReg(R61, 0x00);
  LCD_WriteReg(R62, 0x01);
  LCD_WriteReg(R63, 0x3F);
  LCD_WriteReg(R64, 0x02);
  LCD_WriteReg(R65, 0x02);
  LCD_WriteReg(R66, 0x00);
  LCD_WriteReg(R67, 0x00);
  LCD_WriteReg(R68, 0x00);
  LCD_WriteReg(R69, 0x00);
  LCD_WriteReg(R70, 0xEF);
  LCD_WriteReg(R71, 0x00);
  LCD_WriteReg(R72, 0x00);
  LCD_WriteReg(R73, 0x01);
  LCD_WriteReg(R74, 0x3F);

  LCD_WriteReg(R29, 0x08);  /* R29:Gate scan direction setting */

  LCD_WriteReg(R134, 0x00);
  LCD_WriteReg(R135, 0x30);
  LCD_WriteReg(R136, 0x02);
  LCD_WriteReg(R137, 0x05);

  LCD_WriteReg(R141, 0x01);  /* R141:Register set-up mode for one line clock */
  LCD_WriteReg(R139, 0x20);  /* R139:One line SYSCLK number in one-line */
  LCD_WriteReg(R51, 0x01);  /* R51:N line inversion setting */
  LCD_WriteReg(R55, 0x01);  /* R55:Scanning method setting */
  LCD_WriteReg(R118, 0x00);

/* Gamma Set -----------------------------------------------------------------*/
  LCD_WriteReg(R143, 0x10);
  LCD_WriteReg(R144, 0x67);
  LCD_WriteReg(R145, 0x07);
  LCD_WriteReg(R146, 0x65);
  LCD_WriteReg(R147, 0x07);
  LCD_WriteReg(R148, 0x01);
  LCD_WriteReg(R149, 0x76);
  LCD_WriteReg(R150, 0x56);
  LCD_WriteReg(R151, 0x00);
  LCD_WriteReg(R152, 0x06);
  LCD_WriteReg(R153, 0x03);
  LCD_WriteReg(R154, 0x00);

/* Display On ----------------------------------------------------------------*/
  LCD_WriteReg(R1, 0x50);
  LCD_WriteReg(R5, 0x04);

  LCD_WriteReg(R0, 0x80);
  LCD_WriteReg(R59, 0x01);
  vTaskDelay( 40 / portTICK_PERIOD_MS );  /* Delay 40 ms */
  LCD_WriteReg(R0, 0x20);
}

/*******************************************************************************
* Function Name  : LCD_SetTextColor
* Description    : Sets the Text color.
* Input          : - Color: specifies the Text color code RGB(5-6-5).
* Output         : - TextColor: Text color global variable used by LCD_DrawChar
*                  and LCD_DrawPicture functions.
* Return         : None
*******************************************************************************/
void LCD_SetTextColor(vu16 Color)
{
  TextColor = Color;
}

/*******************************************************************************
* Function Name  : LCD_SetBackColor
* Description    : Sets the Background color.
* Input          : - Color: specifies the Background color code RGB(5-6-5).
* Output         : - BackColor: Background color global variable used by
*                  LCD_DrawChar and LCD_DrawPicture functions.
* Return         : None
*******************************************************************************/
void LCD_SetBackColor(vu16 Color)
{
  BackColor = Color;
}

/*******************************************************************************
* Function Name  : LCD_ClearLine
* Description    : Clears the selected line.
* Input          : - Line: the Line to be cleared.
*                    This parameter can be one of the following values:
*                       - Linex: where x can be 0..9
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_ClearLine(u8 Line)
{
  LCD_DisplayStringLine(Line, "                    ");
}

/*******************************************************************************
* Function Name  : LCD_Clear
* Description    : Clears the hole LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_Clear(void)
{
  u32 index = 0;

  LCD_SetCursor(0x00, 0x013F);

  for(index = 0; index < 0x12C00; index++)
  {
    LCD_WriteRAM(White);
  }
}

/*******************************************************************************
* Function Name  : LCD_SetCursor
* Description    : Sets the cursor position.
* Input          : - Xpos: specifies the X position.
*                  - Ypos: specifies the Y position.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SetCursor(u8 Xpos, u16 Ypos)
{
  LCD_WriteReg(R66, Xpos);
  LCD_WriteReg(R67, ((Ypos & 0x100)>> 8));
  LCD_WriteReg(R68, (Ypos & 0xFF));
}

/*******************************************************************************
* Function Name  : LCD_DrawChar
* Description    : Draws a character on LCD.
* Input          : - Xpos: the Line where to display the character shape.
*                    This parameter can be one of the following values:
*                       - Linex: where x can be 0..9
*                  - Ypos: start column address.
*                  - c: pointer to the character data.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DrawChar(u8 Xpos, u16 Ypos, uc16 *c)
{
  u32 index = 0, i = 0;
  u8 Xaddress = 0;

  Xaddress = Xpos;

  LCD_SetCursor(Xaddress, Ypos);

  for(index = 0; index < 24; index++)
  {
    for(i = 0; i < 16; i++)
    {
      if((c[index] & (1 << i)) == 0x00)
      {
        LCD_WriteRAM(BackColor);
      }
      else
      {
        LCD_WriteRAM(TextColor);
      }
    }
    Xaddress++;
    LCD_SetCursor(Xaddress, Ypos);
  }
}

/*******************************************************************************
* Function Name  : LCD_DisplayChar
* Description    : Displays one character (16dots width, 24dots height).
* Input          : - Line: the Line where to display the character shape .
*                    This parameter can be one of the following values:
*                       - Linex: where x can be 0..9
*                  - Column: start column address.
*                  - Ascii: character ascii code, must be between 0x20 and 0x7E.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DisplayChar(u8 Line, u16 Column, u8 Ascii)
{
  Ascii -= 32;
  LCD_DrawChar(Line, Column, &ASCII_Table[Ascii * 24]);
}

/*******************************************************************************
* Function Name  : LCD_DisplayStringLine
* Description    : Displays a maximum of 20 char on the LCD.
* Input          : - Line: the Line where to display the character shape .
*                    This parameter can be one of the following values:
*                       - Linex: where x can be 0..9
*                  - *ptr: pointer to string to display on LCD.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DisplayStringLine(u8 Line, u8 *ptr)
{
  u32 i = 0;
  u16 refcolumn = 319;

  /* Send the string character by character on lCD */
  while ((*ptr != 0) & (i < 20))
  {
    /* Display one character on LCD */
    LCD_DisplayChar(Line, refcolumn, *ptr);
    /* Decrement the column position by 16 */
    refcolumn -= 16;
    /* Point on the next character */
    ptr++;
    /* Increment the character counter */
    i++;
  }
}

/*******************************************************************************
* Function Name  : LCD_DisplayString
* Description    : Displays a maximum of 200 char on the LCD.
* Input          : - Line: the starting Line where to display the character shape.
*                    This parameter can be one of the following values:
*                       - Linex: where x can be 0..9
*                  - *ptr: pointer to string to display on LCD.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DisplayString(u8 Line, u8 *ptr)
{
  u32 i = 0, column = 0, index = 0, spaceindex = 0;
  u16 refcolumn = 319;
  u32 length = 0;

  /* Get the string length */
  length = StrLength(ptr);
  if(length > 200)
  {
    /* Set the Cursor position */
    LCD_SetCursor(Line, 0x013F);
    /* Clear the Selected Line */
    LCD_ClearLine(Line);
    LCD_DisplayStringLine(Line, "   String too long  ");
  }
  else
  {
    /* Set the Cursor position */
    LCD_SetCursor(Line, 0x013F);
    /* Clear the Selected Line */
    LCD_ClearLine(Line);

    while(length--)
    {
      if(index == 20)
      {
        if(*ptr == 0x20)
        {
          ptr++;
        }
        else
        {
          for(i = 0; i < spaceindex; i++)
          {
            LCD_DisplayChar(Line, column, ' ');
            column -= 16;
          }
          ptr -= (spaceindex - 1);
          length += (spaceindex - 1);
        }
        Line += 24;
        /* Clear the Selected Line */
        LCD_ClearLine(Line);
        refcolumn = 319;
        index = 0;
      }
      /* Display one character on LCD */
      LCD_DisplayChar(Line, refcolumn, *ptr);

      /* Increment character number in one line */
      index++;

      /* Decrement the column position by 16 */
      refcolumn -= 16;
      /* Point on the next character */
      ptr++;
      /* Increment the number of character after the last space */
      spaceindex++;
      if(*ptr == 0x20)
      {
        spaceindex = 0;
        column = refcolumn - 16;
      }
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_ScrollText
* Description    :
* Input          :
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_ScrollText(u8 Line, u8 *ptr)
{
  u32 i = 0, length = 0, x = 0;
  u16 refcolumn = 319;

  /* Get the string length */
  length = StrLength(ptr);

  while(1)
  {
    /* Send the string character by character on lCD */
    while ((*ptr != 0) & (i < 20))
    {
      /* Display one character on LCD */
      LCD_DisplayChar(Line, refcolumn, *ptr);
      /* Decrement the column position by 16 */
      refcolumn -= 16;
      /* Point on the next character */
      ptr++;
      /* Increment the character counter */
      i++;
    }
    vTaskDelay( 100 / portTICK_PERIOD_MS );
    i = 0;
    //LCD_ClearLine(Line);
    ptr -= length;
    x++;
    if(refcolumn < 16)
    {
      x = 0;
    }
    refcolumn = 319 - (x * 16);
  }
}

/*******************************************************************************
* Function Name  : LCD_SetDisplayWindow
* Description    : Sets a display window
* Input          : - Xpos: specifies the X position.
*                  - Ypos: specifies the Y position.
*                  - Height: display window height.
*                  - Width: display window width.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SetDisplayWindow(u8 Xpos, u16 Ypos, u8 Height, u16 Width)
{
  LCD_WriteReg(R1, 0xD0);
  LCD_WriteReg(R5, 0x14);

  LCD_WriteReg(R69, Xpos);
  LCD_WriteReg(R70, (Xpos + Height + 1));

  LCD_WriteReg(R71, ((Ypos & 0x100)>> 8));
  LCD_WriteReg(R72, (Ypos & 0xFF));

  LCD_WriteReg(R73, (((Ypos + Width + 1) & 0x100)>> 8));
  LCD_WriteReg(R74, ((Ypos + Width + 1) & 0xFF));

  LCD_SetCursor(Xpos, Ypos);
}

/*******************************************************************************
* Function Name  : LCD_DrawLine
* Description    : Displays a line.
* Input          : - Xpos: specifies the X position.
*                  - Ypos: specifies the Y position.
*                  - Length: line length.
*                  - Direction: line direction.
*                    This parameter can be one of the following values: Vertical
*                    or Horizontal.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DrawLine(u8 Xpos, u16 Ypos, u16 Length, u8 Direction)
{
  u32 i = 0;

  LCD_SetCursor(Xpos, Ypos);

  if(Direction == Horizontal)
  {
    for(i = 0; i < Length; i++)
    {
      LCD_WriteRAM(TextColor);
    }
  }
  else
  {
   for(i = 0; i < Length; i++)
    {

      LCD_WriteRAM(TextColor);
      Xpos++;
      LCD_SetCursor(Xpos, Ypos);
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawRect
* Description    : Displays a rectangle.
* Input          : - Xpos: specifies the X position.
*                  - Ypos: specifies the Y position.
*                  - Height: display rectangle height.
*                  - Width: display rectangle width.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DrawRect(u8 Xpos, u16 Ypos, u8 Height, u16 Width)
{
  LCD_DrawLine(Xpos, Ypos, Width, Horizontal);
  LCD_DrawLine((Xpos + Height), Ypos, Width, Horizontal);

  LCD_DrawLine(Xpos, Ypos, Height, Vertical);
  LCD_DrawLine(Xpos, (Ypos - Width + 1), Height, Vertical);
}

/*******************************************************************************
* Function Name  : LCD_DrawCircle
* Description    : Displays a circle.
* Input          : - Xpos: specifies the X position.
*                  - Ypos: specifies the Y position.
*                  - Height: display rectangle height.
*                  - Width: display rectangle width.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DrawCircle(u8 Xpos, u16 Ypos, u16 Radius)
{
  s32	D;	/* Decision Variable */
  u32	CurX;	/* Current X Value */
  u32	CurY;	/* Current Y Value */

  D = 3 - (Radius << 1);
  CurX = 0;
  CurY = Radius;

  while (CurX <= CurY)
  {
    LCD_SetCursor(Xpos + CurX, Ypos + CurY);
    LCD_WriteRAM(TextColor);
    LCD_SetCursor(Xpos + CurX, Ypos - CurY);
    LCD_WriteRAM(TextColor);
    LCD_SetCursor(Xpos - CurX, Ypos + CurY);
    LCD_WriteRAM(TextColor);
    LCD_SetCursor(Xpos - CurX, Ypos - CurY);
    LCD_WriteRAM(TextColor);
    LCD_SetCursor(Xpos + CurY, Ypos + CurX);
    LCD_WriteRAM(TextColor);
    LCD_SetCursor(Xpos + CurY, Ypos - CurX);
    LCD_WriteRAM(TextColor);
    LCD_SetCursor(Xpos - CurY, Ypos + CurX);
    LCD_WriteRAM(TextColor);
    LCD_SetCursor(Xpos - CurY, Ypos - CurX);
    LCD_WriteRAM(TextColor);

    if (D < 0)
    {
      D += (CurX << 2) + 6;
    }
    else
    {
      D += ((CurX - CurY) << 2) + 10;
      CurY--;
    }
    CurX++;
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawMonoPict
* Description    : Displays a monocolor picture.
* Input          : - Pict: pointer to the picture array.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DrawMonoPict(uc32 *Pict)
{
  u32 index = 0, i = 0;

  LCD_SetCursor(0, 319);

  for(index = 0; index < 2400; index++)
  {
    for(i = 0; i < 32; i++)
    {
      if((Pict[index] & (1 << i)) == 0x00)
      {
        LCD_WriteRAM(BackColor);
      }
      else
      {
        LCD_WriteRAM(TextColor);
      }
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawBMP
* Description    : Displays a bitmap picture loaded in the SPI Flash.
* Input          : - BmpAddress: Bmp picture address in the SPI Flash.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DrawBMP(u32 BmpAddress)
{
  u32 i = 0;

  LCD_WriteReg(R1, 0xD0);
  LCD_WriteReg(R5, 0x04);

  LCD_SetCursor(239, 0x013F);

  SPI_FLASH_StartReadSequence(BmpAddress);

  /* Disable SPI1  */
  SPI_Cmd(SPI1, DISABLE);
  /* SPI in 16-bit mode */
  SPI_DataSizeConfig(SPI1, SPI_DataSize_16b);
  /* Enable SPI1  */
  SPI_Cmd(SPI1, ENABLE);

  for(i = 0; i < 76800; i++)
  {
    LCD_WriteRAM(__REV_HalfWord(SPI_FLASH_SendHalfWord(0xA5A5)));
  }

  /* Deselect the FLASH: Chip Select high */
  SPI_FLASH_ChipSelect(1);

  /* Disable SPI1  */
  SPI_Cmd(SPI1, DISABLE);
  /* SPI in 8-bit mode */
  SPI_DataSizeConfig(SPI1, SPI_DataSize_8b);
  /* Enable SPI1  */
  SPI_Cmd(SPI1, ENABLE);
}

/*******************************************************************************
* Function Name  : LCD_WriteReg
* Description    : Writes to the selected LCD register.
* Input          : - LCD_Reg: address of the selected register.
*                  - LCD_RegValue: value to write to the selected register.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_WriteReg(u8 LCD_Reg, u8 LCD_RegValue)
{
  u16 tmp = 0;

  LCD_CtrlLinesWrite(GPIOD, CtrlPin_NWR, Bit_RESET);
  LCD_CtrlLinesWrite(GPIOD, CtrlPin_RS, Bit_RESET);
  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_RESET);

  tmp = LCD_Reg << 8;
  tmp |= LCD_RegValue;

  SPI_SendData(SPI2, tmp);
  while(SPI_GetFlagStatus(SPI2, SPI_FLAG_TXE) == RESET)
  {
  }

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);
}

/*******************************************************************************
* Function Name  : LCD_ReadReg
* Description    : Reads the selected LCD Register.
* Input          : None
* Output         : None
* Return         : LCD Register Value.
*******************************************************************************/
u8 LCD_ReadReg(u8 LCD_Reg)
{
  u16 tmp = 0;

  LCD_CtrlLinesWrite(GPIOD, CtrlPin_NWR, Bit_RESET);
  LCD_CtrlLinesWrite(GPIOD, CtrlPin_RS, Bit_RESET);
  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_RESET);

  while(SPI_GetFlagStatus(SPI2, SPI_FLAG_TXE) == RESET)
  {
  }
  SPI_SendData(SPI2, LCD_Reg);

  LCD_CtrlLinesWrite(GPIOD, CtrlPin_NWR, Bit_SET);

  while(SPI_GetFlagStatus(SPI2, SPI_FLAG_TXE) == RESET)
  {
  }
  SPI_SendData(SPI2, 0xFF);

  while(SPI_GetFlagStatus(SPI2, SPI_FLAG_RXNE)== RESET)
  {
  }
  tmp = SPI_ReceiveData(SPI2);

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);
  return tmp;
}

/*******************************************************************************
* Function Name  : LCD_WriteRAM
* Description    : Writes to the LCD RAM.
* Input          : - RGB_Code: the pixel color in RGB mode (5-6-5).
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_WriteRAM(u16 RGB_Code)
{
  LCD_CtrlLinesWrite(GPIOD, CtrlPin_NWR, Bit_RESET);
  LCD_CtrlLinesWrite(GPIOD, CtrlPin_RS, Bit_SET);
  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_RESET);

  SPI_SendData(SPI2, RGB_Code);
  while(SPI_GetFlagStatus(SPI2, SPI_FLAG_TXE) == RESET)
  {
  }

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);
}

/*******************************************************************************
* Function Name  : LCD_ReadRAM
* Description    : Reads the LCD RAM.
* Input          : None
* Output         : None
* Return         : LCD RAM Value.
*******************************************************************************/
u16  LCD_ReadRAM(void)
{
  u16 tmp = 0;

  LCD_CtrlLinesWrite(GPIOD, CtrlPin_NWR, Bit_SET);
  LCD_CtrlLinesWrite(GPIOD, CtrlPin_RS, Bit_SET);
  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_RESET);

  while(SPI_GetFlagStatus(SPI2, SPI_FLAG_TXE) == RESET)
  {
  }
  SPI_SendData(SPI2, 0xFF);
  while(SPI_GetFlagStatus(SPI2, SPI_FLAG_RXNE)==RESET)
  {
  }
  tmp = SPI_ReceiveData(SPI2);

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);

  return tmp;
}

/*******************************************************************************
* Function Name  : LCD_PowerOn
* Description    :
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_PowerOn(void)
{
  /* Power On Set */
  LCD_WriteReg(R28, 0x73);
  LCD_WriteReg(R36, 0x74);
  LCD_WriteReg(R30, 0x01);
  LCD_WriteReg(R24, 0xC1);
  vTaskDelay( 10 / portTICK_PERIOD_MS ); /* Delay 10 ms */
  LCD_WriteReg(R24, 0xE1);
  LCD_WriteReg(R24, 0xF1);
  vTaskDelay( 60 / portTICK_PERIOD_MS ); /* Delay 60 ms */
  LCD_WriteReg(R24, 0xF5);
  vTaskDelay( 60 / portTICK_PERIOD_MS ); /* Delay 60 ms */
  LCD_WriteReg(R27, 0x09);
  vTaskDelay( 10 / portTICK_PERIOD_MS ); /* Delay 10 ms */
  LCD_WriteReg(R31, 0x11);
  LCD_WriteReg(R32, 0x0E);
  LCD_WriteReg(R30, 0x81);
  vTaskDelay( 10 / portTICK_PERIOD_MS ); /* Delay 10 ms */
}

/*******************************************************************************
* Function Name  : LCD_DisplayOn
* Description    : Enables the Display.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DisplayOn(void)
{
  LCD_WriteReg(R1, 0x50);
  LCD_WriteReg(R5, 0x04);

  /* Display On */
  LCD_WriteReg(R0, 0x80);
  LCD_WriteReg(R59, 0x01);
  vTaskDelay( 40 / portTICK_PERIOD_MS );                 /* Delay 40 ms */
  LCD_WriteReg(R0, 0x20);
}

/*******************************************************************************
* Function Name  : LCD_DisplayOff
* Description    : Disables the Display.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DisplayOff(void)
{
  /* Display Off */
  LCD_WriteReg(R0, 0xA0);
  vTaskDelay( 40 / portTICK_PERIOD_MS );                 /* Delay 40 ms */
  LCD_WriteReg(R59, 0x00);
}

/*******************************************************************************
* Function Name  : LCD_CtrlLinesConfig
* Description    : Configures LCD control lines in Output Push-Pull mode.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_CtrlLinesConfig(void)
{
  GPIO_InitTypeDef GPIO_InitStructure;

  /* Configure NCS (PB.02) in Output Push-Pull mode */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_2;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
  GPIO_Init(GPIOB, &GPIO_InitStructure);

  /* Configure NWR(RNW), RS (PD.15, PD.07) in Output Push-Pull mode */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_7 | GPIO_Pin_15;
  GPIO_Init(GPIOD, &GPIO_InitStructure);
}

/*******************************************************************************
* Function Name  : LCD_CtrlLinesWrite
* Description    : Sets or reset LCD control lines.
* Input          : - GPIOx: where x can be B or D to select the GPIO peripheral.
*                  - CtrlPins: the Control line. This parameter can be:
*                       - CtrlPin_NCS: Chip Select pin (PB.02)
*                       - CtrlPin_NWR: Read/Write Selection pin (PD.15)
*                       - CtrlPin_RS: Register/RAM Selection pin (PD.07)
*                  - BitVal: specifies the value to be written to the selected bit.
*                    This parameter can be:
*                       - Bit_RESET: to clear the port pin
*                       - Bit_SET: to set the port pin
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_CtrlLinesWrite(GPIO_TypeDef* GPIOx, u16 CtrlPins, BitAction BitVal)
{
  /* Set or Reset the control line */
  GPIO_WriteBit(GPIOx, CtrlPins, BitVal);
}

/*******************************************************************************
* Function Name  : LCD_SPIConfig
* Description    : Configures the SPI2 interface.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SPIConfig(void)
{
  SPI_InitTypeDef    SPI_InitStructure;
  GPIO_InitTypeDef   GPIO_InitStructure;

  /* Enable GPIOA clock */
  RCC_APB2PeriphClockCmd(RCC_APB2Periph_GPIOB, ENABLE);

  /* Enable SPI2 clock  */
  RCC_APB1PeriphClockCmd(RCC_APB1Periph_SPI2, ENABLE);

  /* Configure SPI2 pins: NSS, SCK, MISO and MOSI */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_12 | GPIO_Pin_13 | GPIO_Pin_14 | GPIO_Pin_15;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF_PP;
  GPIO_Init(GPIOB, &GPIO_InitStructure);

  /* SPI2 Config */
  SPI_InitStructure.SPI_Direction = SPI_Direction_2Lines_FullDuplex;
  SPI_InitStructure.SPI_Mode = SPI_Mode_Master;
  SPI_InitStructure.SPI_DataSize = SPI_DataSize_16b;
  SPI_InitStructure.SPI_CPOL = SPI_CPOL_Low;
  SPI_InitStructure.SPI_CPHA = SPI_CPHA_1Edge;
  SPI_InitStructure.SPI_NSS = SPI_NSS_Soft;
  SPI_InitStructure.SPI_BaudRatePrescaler = SPI_BaudRatePrescaler_2;
  SPI_InitStructure.SPI_FirstBit = SPI_FirstBit_MSB;
  SPI_Init(SPI2, &SPI_InitStructure);

  /* SPI2 enable */
  SPI_Cmd(SPI2, ENABLE);
}

/*******************************************************************************
* Function Name  : StrLength
* Description    : Returns length of string.
* Input          : - Str: Character Pointer.
* Output         : None
* Return         : String length.
*******************************************************************************/
static u32 StrLength(u8 *Str)
{
  u32 Index = 0;

  /* Increment the Index unless the end of string */
  for(Index = 0; *Str != '\0'; Str++, Index++)
  {
  }

  return Index;
}

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
