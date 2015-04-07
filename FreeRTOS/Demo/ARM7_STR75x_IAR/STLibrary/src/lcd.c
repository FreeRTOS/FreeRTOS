/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : lcd.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file includes the LCD driver for GXM12232-2SL liquid
*                      Crystal Display Module of STR75x-EVAL.
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
#include "lcd.h"

/* Private typedef -----------------------------------------------------------*/

  /* Peripherals InitStructure define */
GPIO_InitTypeDef GPIO_InitStructure;

/* Private define ------------------------------------------------------------*/
#define LCD_GPIO_Pins 0x3FC00
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
  /* Global variable to set the written text color: used for LCD_Printf */
  TextColorMode_TypeDef TextMode = BlackText;

  /* ASCII Table: each character is 7 column (7dots large) on two pages (16dots high)  */
  /* 7 column character: Two 8bit data to display one column*/
  const u8 AsciiDotsTable[1778] = {
  /* ASCII 0   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 1   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 2   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 3   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 4   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 5   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 6   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 7   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 8   */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 9   */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 10  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 11  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 12  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 13  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 14  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 15  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 16  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 17  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 18  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 19  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 20  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 21  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 22  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 23  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 24  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 25  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 26  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 27  */  0x1f,0xe0,0x10,0x20,0x10,0x20,0x10,0x20,0x10,0x20,0x1f,0xe0,0x00,0x00,
  /* ASCII 28  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 29  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 30  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 31  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 32  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 33  */  0x00,0x00,0x00,0x00,0x00,0x00,0x13,0xe0,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 34  */  0x00,0x00,0x00,0xe0,0x00,0x20,0x00,0x00,0x00,0xe0,0x00,0x20,0x00,0x00,
  /* ASCII 35  */  0x00,0x00,0x35,0x00,0x0f,0x80,0x35,0x60,0x0f,0x80,0x05,0x60,0x00,0x00,
  /* ASCII 36  */  0x00,0x00,0x0d,0x80,0x0a,0x40,0x3a,0x60,0x06,0x40,0x00,0x00,0x00,0x00,
  /* ASCII 37  */  0x00,0x00,0x02,0x40,0x02,0xa0,0x0a,0x40,0x15,0x00,0x09,0x00,0x00,0x00,
  /* ASCII 38  */  0x00,0x00,0x0c,0x00,0x13,0x00,0x14,0x80,0x08,0x80,0x14,0x00,0x00,0x00,
  /* ASCII 39  */  0x00,0x00,0x00,0x00,0x00,0x00,0x01,0xe0,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 40  */  0x00,0x00,0x00,0x00,0x00,0x00,0x1f,0x80,0x60,0x60,0x00,0x00,0x00,0x00,
  /* ASCII 41  */  0x00,0x00,0x00,0x00,0x60,0x60,0x1f,0x80,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 42  */  0x00,0x00,0x00,0x40,0x03,0x40,0x00,0xe0,0x03,0x40,0x00,0x40,0x00,0x00,
  /* ASCII 43  */  0x02,0x00,0x02,0x00,0x02,0x00,0x1f,0xc0,0x02,0x00,0x02,0x00,0x02,0x00,
  /* ASCII 44  */  0x00,0x00,0x00,0x00,0x60,0x00,0x38,0x00,0x08,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 45  */  0x00,0x00,0x02,0x00,0x02,0x00,0x02,0x00,0x02,0x00,0x02,0x00,0x00,0x00,
  /* ASCII 46  */  0x00,0x00,0x00,0x00,0x18,0x00,0x18,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 47  */  0x00,0x00,0x20,0x00,0x18,0x00,0x06,0x00,0x01,0x80,0x00,0x60,0x00,0x00,
  /* ASCII 48  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x10,0x20,0x10,0x20,0x0f,0xc0,0x00,0x00,
  /* ASCII 49  */  0x00,0x00,0x10,0x00,0x10,0x20,0x1f,0xe0,0x10,0x00,0x10,0x00,0x00,0x00,
  /* ASCII 50  */  0x00,0x00,0x18,0x40,0x14,0x20,0x12,0x20,0x11,0x20,0x18,0xc0,0x00,0x00,
  /* ASCII 51  */  0x00,0x00,0x08,0x40,0x10,0x20,0x11,0x20,0x11,0x20,0x0e,0xc0,0x00,0x00,
  /* ASCII 52  */  0x00,0x00,0x06,0x00,0x05,0x00,0x04,0xc0,0x14,0x20,0x1f,0xe0,0x14,0x00,
  /* ASCII 53  */  0x00,0x00,0x08,0x00,0x11,0xe0,0x11,0x20,0x11,0x20,0x0e,0x20,0x00,0x00,
  /* ASCII 54  */  0x00,0x00,0x0f,0x80,0x11,0x40,0x11,0x20,0x11,0x20,0x0e,0x20,0x00,0x00,
  /* ASCII 55  */  0x00,0x00,0x00,0x60,0x00,0x20,0x18,0x20,0x07,0x20,0x00,0xe0,0x00,0x00,
  /* ASCII 56  */  0x00,0x00,0x0e,0xc0,0x11,0x20,0x11,0x20,0x11,0x20,0x0e,0xc0,0x00,0x00,
  /* ASCII 57  */  0x00,0x00,0x11,0xc0,0x12,0x20,0x12,0x20,0x0a,0x20,0x07,0xc0,0x00,0x00,
  /* ASCII 58  */  0x00,0x00,0x00,0x00,0x19,0x80,0x19,0x80,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 59  */  0x00,0x00,0x00,0x00,0x30,0x00,0x19,0x80,0x09,0x80,0x00,0x00,0x00,0x00,
  /* ASCII 60  */  0x02,0x00,0x05,0x00,0x05,0x00,0x08,0x80,0x10,0x40,0x10,0x40,0x00,0x00,
  /* ASCII 61  */  0x00,0x00,0x05,0x00,0x05,0x00,0x05,0x00,0x05,0x00,0x05,0x00,0x00,0x00,
  /* ASCII 62  */  0x10,0x40,0x10,0x40,0x08,0x80,0x05,0x00,0x05,0x00,0x02,0x00,0x00,0x00,
  /* ASCII 63  */  0x00,0x00,0x00,0x00,0x10,0x80,0x14,0x40,0x02,0x40,0x01,0x80,0x00,0x00,
  /* ASCII 64  */  0x00,0x00,0x1f,0xe0,0x20,0x10,0x23,0x10,0x24,0x90,0x17,0xe0,0x00,0x00,
  /* ASCII 65  */  0x10,0x00,0x1c,0x00,0x17,0xa0,0x04,0x60,0x17,0x80,0x1c,0x00,0x10,0x00,
  /* ASCII 66  */  0x10,0x20,0x1f,0xe0,0x11,0x20,0x11,0x20,0x11,0x20,0x0e,0xc0,0x00,0x00,
  /* ASCII 67  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x10,0x20,0x10,0x20,0x08,0x60,0x00,0x00,
  /* ASCII 68  */  0x10,0x20,0x1f,0xe0,0x10,0x20,0x10,0x20,0x08,0x40,0x07,0x80,0x00,0x00,
  /* ASCII 69  */  0x10,0x20,0x1f,0xe0,0x11,0x20,0x13,0xa0,0x10,0x20,0x18,0x60,0x00,0x00,
  /* ASCII 70  */  0x00,0x00,0x10,0x20,0x1f,0xe0,0x11,0x20,0x03,0xa0,0x00,0x20,0x00,0x60,
  /* ASCII 71  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x10,0x20,0x12,0x20,0x0e,0x60,0x02,0x00,
  /* ASCII 72  */  0x10,0x20,0x1f,0xe0,0x11,0x20,0x01,0x00,0x11,0x20,0x1f,0xe0,0x10,0x20,
  /* ASCII 73  */  0x00,0x00,0x10,0x20,0x10,0x20,0x1f,0xe0,0x10,0x20,0x10,0x20,0x00,0x00,
  /* ASCII 74  */  0x00,0x00,0x0e,0x00,0x10,0x20,0x10,0x20,0x0f,0xe0,0x00,0x20,0x00,0x00,
  /* ASCII 75  */  0x10,0x20,0x1f,0xe0,0x12,0x20,0x03,0x00,0x04,0xa0,0x18,0x60,0x10,0x20,
  /* ASCII 76  */  0x00,0x00,0x10,0x20,0x1f,0xe0,0x10,0x20,0x10,0x00,0x1c,0x00,0x00,0x00,
  /* ASCII 77  */  0x10,0x20,0x1f,0xe0,0x10,0xe0,0x03,0x00,0x10,0xe0,0x1f,0xe0,0x10,0x20,
  /* ASCII 78  */  0x10,0x20,0x1f,0xe0,0x10,0xe0,0x07,0x00,0x18,0x20,0x1f,0xe0,0x00,0x20,
  /* ASCII 79  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x10,0x20,0x10,0x20,0x0f,0xc0,0x00,0x00,
  /* ASCII 80  */  0x00,0x00,0x10,0x20,0x1f,0xe0,0x12,0x20,0x02,0x20,0x01,0xc0,0x00,0x00,
  /* ASCII 81  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x30,0x20,0x30,0x20,0x2f,0xc0,0x00,0x00,
  /* ASCII 82  */  0x10,0x20,0x1f,0xe0,0x12,0x20,0x02,0x20,0x06,0x20,0x09,0xc0,0x10,0x00,
  /* ASCII 83  */  0x00,0x00,0x18,0xc0,0x09,0x20,0x11,0x20,0x11,0x40,0x0e,0x60,0x00,0x00,
  /* ASCII 84  */  0x00,0x60,0x00,0x20,0x10,0x20,0x1f,0xe0,0x10,0x20,0x00,0x20,0x00,0x60,
  /* ASCII 85  */  0x00,0x20,0x0f,0xe0,0x10,0x20,0x10,0x00,0x10,0x20,0x0f,0xe0,0x00,0x20,
  /* ASCII 86  */  0x00,0x20,0x00,0xe0,0x07,0x20,0x18,0x00,0x07,0x20,0x00,0xe0,0x00,0x20,
  /* ASCII 87  */  0x00,0x20,0x0f,0xe0,0x10,0x20,0x0f,0x00,0x10,0x20,0x0f,0xe0,0x00,0x20,
  /* ASCII 88  */  0x10,0x20,0x18,0x60,0x04,0x80,0x03,0x00,0x04,0x80,0x18,0x60,0x10,0x20,
  /* ASCII 89  */  0x00,0x20,0x00,0x60,0x11,0xa0,0x1e,0x00,0x11,0xa0,0x00,0x60,0x00,0x20,
  /* ASCII 90  */  0x00,0x00,0x18,0x60,0x14,0x20,0x13,0x20,0x10,0xa0,0x18,0x60,0x00,0x00,
  /* ASCII 91  */  0x00,0x00,0x00,0x00,0x7f,0xe0,0x40,0x20,0x40,0x20,0x00,0x00,0x00,0x00,
  /* ASCII 92  */  0x00,0x00,0x00,0x20,0x01,0xc0,0x06,0x00,0x38,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 93  */  0x00,0x00,0x00,0x00,0x40,0x20,0x40,0x20,0x7f,0xe0,0x00,0x00,0x00,0x00,
  /* ASCII 94  */  0x00,0x00,0x01,0x00,0x00,0x80,0x00,0x60,0x00,0x80,0x01,0x00,0x00,0x00,
  /* ASCII 95  */  0x80,0x00,0x80,0x00,0x80,0x00,0x80,0x00,0x80,0x00,0x80,0x00,0x80,0x00,
  /* ASCII 96  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x20,0x00,0x40,0x00,0x00,0x00,0x00,
  /* ASCII 97  */  0x00,0x00,0x0d,0x00,0x12,0x80,0x12,0x80,0x12,0x80,0x1f,0x00,0x10,0x00,
  /* ASCII 98  */  0x10,0x20,0x1f,0xe0,0x11,0x00,0x10,0x80,0x10,0x80,0x0f,0x00,0x00,0x00,
  /* ASCII 99  */  0x00,0x00,0x0f,0x00,0x10,0x80,0x10,0x80,0x10,0x80,0x09,0x80,0x00,0x00,
  /* ASCII 100 */  0x00,0x00,0x0f,0x00,0x10,0x80,0x10,0x80,0x11,0x20,0x1f,0xe0,0x10,0x00,
  /* ASCII 101 */  0x00,0x00,0x0f,0x00,0x12,0x80,0x12,0x80,0x12,0x80,0x13,0x00,0x00,0x00,
  /* ASCII 102 */  0x00,0x00,0x10,0x80,0x1f,0xc0,0x10,0xa0,0x10,0xa0,0x10,0xa0,0x00,0x00,
  /* ASCII 103 */  0x00,0x00,0x0f,0x00,0x50,0x80,0x50,0x80,0x51,0x00,0x3f,0x80,0x00,0x80,
  /* ASCII 104 */  0x10,0x20,0x1f,0xe0,0x11,0x00,0x00,0x80,0x10,0x80,0x1f,0x00,0x10,0x00,
  /* ASCII 105 */  0x00,0x00,0x10,0x80,0x10,0x80,0x1f,0xa0,0x10,0x00,0x10,0x00,0x00,0x00,
  /* ASCII 106 */  0x00,0x00,0x40,0x80,0x40,0x80,0x40,0xa0,0x3f,0x80,0x00,0x00,0x00,0x00,
  /* ASCII 107 */  0x10,0x20,0x1f,0xe0,0x02,0x00,0x16,0x80,0x19,0x80,0x10,0x80,0x00,0x00,
  /* ASCII 108 */  0x00,0x00,0x10,0x00,0x10,0x20,0x1f,0xe0,0x10,0x00,0x10,0x00,0x00,0x00,
  /* ASCII 109 */  0x10,0x80,0x1f,0x80,0x10,0x80,0x1f,0x00,0x10,0x80,0x1f,0x00,0x10,0x00,
  /* ASCII 110 */  0x10,0x80,0x1f,0x80,0x11,0x00,0x00,0x80,0x10,0x80,0x1f,0x00,0x10,0x00,
  /* ASCII 111 */  0x00,0x00,0x0f,0x00,0x10,0x80,0x10,0x80,0x10,0x80,0x0f,0x00,0x00,0x00,
  /* ASCII 112 */  0x40,0x80,0x7f,0x80,0x51,0x00,0x10,0x80,0x10,0x80,0x0f,0x00,0x00,0x00,
  /* ASCII 113 */  0x00,0x00,0x0f,0x00,0x10,0x80,0x10,0x80,0x51,0x00,0x7f,0x80,0x40,0x80,
  /* ASCII 114 */  0x00,0x00,0x10,0x80,0x1f,0x80,0x11,0x00,0x10,0x80,0x10,0x80,0x00,0x00,
  /* ASCII 115 */  0x00,0x00,0x19,0x00,0x12,0x80,0x12,0x80,0x12,0x80,0x0d,0x80,0x00,0x00,
  /* ASCII 116 */  0x00,0x00,0x00,0x80,0x0f,0xc0,0x10,0x80,0x10,0x80,0x10,0x80,0x08,0x00,
  /* ASCII 117 */  0x00,0x80,0x0f,0x80,0x10,0x00,0x10,0x00,0x08,0x80,0x1f,0x80,0x10,0x00,
  /* ASCII 118 */  0x00,0x80,0x03,0x80,0x0c,0x80,0x10,0x00,0x0c,0x80,0x03,0x80,0x00,0x80,
  /* ASCII 119 */  0x00,0x80,0x0f,0x80,0x10,0x80,0x0e,0x00,0x10,0x80,0x0f,0x80,0x00,0x80,
  /* ASCII 120 */  0x10,0x80,0x19,0x80,0x06,0x00,0x06,0x00,0x19,0x80,0x10,0x80,0x00,0x00,
  /* ASCII 121 */  0x00,0x80,0x41,0x80,0x46,0x80,0x78,0x00,0x4c,0x80,0x03,0x80,0x00,0x80,
  /* ASCII 122 */  0x00,0x00,0x19,0x80,0x14,0x80,0x12,0x80,0x11,0x80,0x18,0x80,0x00,0x00,
  /* ASCII 123 */  0x00,0x00,0x00,0x00,0x04,0x00,0x3b,0xc0,0x40,0x20,0x00,0x00,0x00,0x00,
  /* ASCII 124 */  0x00,0x00,0x00,0x00,0x00,0x00,0x3f,0xe0,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 125 */  0x00,0x00,0x00,0x00,0x40,0x20,0x3b,0xc0,0x04,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 126 */  0x00,0x00,0x04,0x00,0x02,0x00,0x04,0x00,0x04,0x00,0x02,0x00,0x00,0x00};

/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : LCD_DataLinesConfig
* Description    : Configure data lines D0~D7 (P2.10~P2.17) in Input Floating mode
*                  for read from LCD or in Output Push-Pull mode for write on LCD
* Input          : - Mode: specifies the configuration mode for data lines D0~D7
*                       - Input: configure in Input Floating mode
*                       - Output: configure in Output Push-Pul mode
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DataLinesConfig(DataConfigMode_TypeDef Mode)
{
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_10 | GPIO_Pin_11 | GPIO_Pin_12 | GPIO_Pin_13 |
                                GPIO_Pin_14 | GPIO_Pin_15 | GPIO_Pin_16 | GPIO_Pin_17;
  if (Mode == Input)
  {
    /* Configure D0~D7 lines (P2.10~2.17) in Input Floating mode */
    GPIO_InitStructure.GPIO_Mode = GPIO_Mode_IN_FLOATING;
  }
  else
  {
    /* Configure D0~D7 lines (P2.10~2.17) in Output Push-Pull mode */
    GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
  }
  GPIO_Init(GPIO2, &GPIO_InitStructure);
}

/*******************************************************************************
* Function Name  : LCD_DataLinesWrite
* Description    : Write a value on D0~D7 (P2.10~P2.17)
* Input          : - GPIOx: GPIO port to write on. It could be
*                  - PortVal: value to write
* Output         : None
* Return         : None.
*******************************************************************************/
void LCD_DataLinesWrite(GPIO_TypeDef* GPIOx, u32 PortVal)
{
  u32 Tmp = 0;

  /* Store the PM register value */
  Tmp = GPIO_GetPortMask(GPIOx);
  /* Mask the corresponding GPIO pins */
  GPIO_PinMaskConfig(GPIOx, LCD_GPIO_Pins, DISABLE);
  GPIO_PinMaskConfig(GPIOx, ~LCD_GPIO_Pins, ENABLE);
  /* Write in the hole register */
  GPIO_Write(GPIOx, (PortVal<<10));

  GPIO_PinMaskConfig(GPIOx, ~LCD_GPIO_Pins, DISABLE);
  /* Return the initial PM register value */
  GPIO_PinMaskConfig(GPIOx, Tmp, ENABLE);

}

/*******************************************************************************
* Function Name  : LCD_CtrlLinesConfig
* Description    : Configure control lines E2, E1, RW, DI (P2.0~P2.3) in
*                  Output Push-Pull mode.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_CtrlLinesConfig(void)
{
  /* Configure E2, E1, RW, DI lines (P2.0~2.3) in Output Push-Pull mode */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_0 | GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
  GPIO_Init(GPIO2, &GPIO_InitStructure);
}

/*******************************************************************************
* Function Name  : LCD_CtrlLinesWrite
* Description    : Set or reset control lines E2, E1, RW, DI (P2.0~P2.3).
* Input          : - GPIOx: where x can be 0,1 or 2 to select the GPIO peripheral.
*                  - CtrlPins: the Control line. This parameter can be:
*                       - CtrlPin_E2: Enabe clock signal for Slave
*                       - CtrlPin_E1: Enabe clock signal for Master
*                       - CtrlPin_RW: Read/Write control line
*                       - CtrlPin_DI:
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_CtrlLinesWrite(GPIO_TypeDef* GPIOx, u32 CtrlPins, BitAction BitVal)
{
  /* Set or Reset the control line */
  if(BitVal != Bit_RESET)
  {
    GPIOx->PD |= CtrlPins;
  }
  else
  {
    GPIOx->PD &= ~CtrlPins;
  }
}

/*******************************************************************************
* Function Name  : LCD_CheckMasterStatus
* Description    : Check whether master LCD is busy or not
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_CheckMasterStatus(void)			
{
  u8 MasterStatus = 0;

  /* Configure Data lines as Input */
  LCD_DataLinesConfig(Input);
  /* Start the master read sequence */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET);   /* E1 = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_RW, Bit_SET);     /* RW = 1 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_DI, Bit_RESET);   /* DI = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_SET);     /* E1 = 1 */
  MasterStatus = GPIO_Read(GPIO2);
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET);   /* E1 = 0 */
	
  /* Wait until BF is cleared: D7 line */
  while ((MasterStatus & 0x20000))
  {
    LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_SET);   /* E1 = 1 */
    MasterStatus = GPIO_Read(GPIO2);
    LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET); /* E1 = 0 */
  }
}

/*******************************************************************************
* Function Name  : LCD_CheckSlaveStatus
* Description    : Check whether slave LCD is busy or not
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_CheckSlaveStatus(void)			
{
  u8 SlaveStatus = 0;

  /* Configure Data lines as Input */
  LCD_DataLinesConfig(Input);
  /* Start the slave read sequence */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET);   /* E2 = 0 */	
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_RW, Bit_SET);     /* RW = 1 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_DI, Bit_RESET);   /* DI = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_SET);     /* E2 = 1 */
  SlaveStatus = GPIO_Read(GPIO2);
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET);   /* E2 = 0 */
	
  /* Wait until BF is cleared: D7 line */
  while ((SlaveStatus & 0x20000))
  {
    LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_SET);   /* E2 = 1 */
    SlaveStatus = GPIO_Read(GPIO2);
    LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET); /* E2 = 0 */
  }
}

/*******************************************************************************
* Function Name  : LCD_SendMasterCmd
* Description    : Send one byte command to master LCD.
* Input          : - Cmd: the user expected command to send to master LCD
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SendMasterCmd(u8 Cmd)
{
  /* Check the master status */
  LCD_CheckMasterStatus();
  /* Configure Data lines as Output */
  LCD_DataLinesConfig(Output);
  /* Start the master send command sequence */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET);  /* E1 = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_RW, Bit_RESET);  /* RW = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_DI, Bit_RESET);  /* DI = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_SET);    /* E1 = 1 */
  /* Write master command */
  LCD_DataLinesWrite(GPIO2, (u32)Cmd);
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET);  /* E1 = 0 */
}

/*******************************************************************************
* Function Name  : LCD_SendSlaveCmd
* Description    : Send one byte command to slave LCD
* Input          : - Cmd: the user expected command to send to slave LCD.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SendSlaveCmd(u8 Cmd)
{
  /* Check the slave status */
  LCD_CheckSlaveStatus();
  /* Configure Data lines as Output */
  LCD_DataLinesConfig(Output);
  /* Start the slave send command sequence */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET);  /* E2 = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_RW, Bit_RESET);  /* RW = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_DI, Bit_RESET);  /* DI = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_SET);    /* E2 = 1 */
  /* Write slave command */
  LCD_DataLinesWrite(GPIO2, (u32)Cmd);
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET);  /* E2 = 0 */
}

/*******************************************************************************
* Function Name  : LCD_SendMasterData
* Description    : Display one byte data to master LCD.
* Input          : - Data: the user expected data to display on master LCD.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SendMasterData(u8 Data)
{
  /* Check the master status */
  LCD_CheckMasterStatus();
  /* Configure Data lines as Output */
  LCD_DataLinesConfig(Output);
  /* Start the master send data sequence */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET);  /* E1 = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_RW, Bit_RESET);  /* RW = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_DI, Bit_SET);    /* DI = 1 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_SET);    /* E1 = 1 */
  /* Write data to the master */
  LCD_DataLinesWrite(GPIO2, (u32)Data);
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET);  /* E1 = 0 */
}

/*******************************************************************************
* Function Name  : LCD_ReadMasterData
* Description    : Read master byte data displayed on master LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
u32 LCD_ReadMasterData(void)
{
  u32 MasterData = 0;

  /* Check the master status */
  LCD_CheckMasterStatus();
  /* Configure Data lines as Input */
  LCD_DataLinesConfig(Input);
  /* Start the master read data sequence */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET);  /* E1 = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_RW, Bit_SET);    /* RW = 1 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_DI, Bit_SET);    /* DI = 1 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_SET);    /* E1 = 1 */
  /* Read data from the master */
  MasterData = ((GPIO_Read(GPIO2)&0x3FC00)>>10);
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E1, Bit_RESET);  /* E1 = 0 */
  /* Read the master returned data */
  return MasterData;
}

/*******************************************************************************
* Function Name  : LCD_SendSlaveData
* Description    : Display one byte data to slave LCD.
* Input          : - Data: the user expected data to display on slave LCD.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SendSlaveData(u8 Data)
{
  /* Check the slave status */
  LCD_CheckSlaveStatus();
  /* Configure Data lines as Output */
  LCD_DataLinesConfig(Output);
  /* Start the slave send data sequence */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET);  /* E2 = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_RW, Bit_RESET);  /* RW = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_DI, Bit_SET);    /* DI = 1 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_SET);    /* E2 = 1 */
  /* Write data to the slave */
  LCD_DataLinesWrite(GPIO2, (u32)Data);
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET);  /* E2 = 0 */
}

/*******************************************************************************
* Function Name  : LCD_ReadSlaveData
* Description    : Read slave byte data displayed on slave LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
u32 LCD_ReadSlaveData(void)
{
  u32 SlaveData = 0;

  /* Check the slave status */
  LCD_CheckSlaveStatus();
  /* Configure Data lines as Input */
  LCD_DataLinesConfig(Input);
  /* Start the slave read data sequence */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET);  /* E2 = 0 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_RW, Bit_SET);    /* RW = 1 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_DI, Bit_SET);    /* DI = 1 */
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_SET);    /* E2 = 1 */
  /* Read data from the slave */
  SlaveData = ((GPIO_Read(GPIO2)&0x3FC00)>>10);
  LCD_CtrlLinesWrite(GPIO2, CtrlPin_E2, Bit_RESET);  /* E2 = 0 */
  /* Read the slave returned data */
  return SlaveData;
}

/*******************************************************************************
* Function Name  : LCD_Init
* Description    : Initialize master and slave LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_Init(void)
{
  /* Enable GPIO Clock */
  MRCC_PeripheralClockConfig(MRCC_Peripheral_GPIO, ENABLE);

  /* Configure control lines signals as output mode */
  LCD_CtrlLinesConfig();	

  /* Master LCD Init */
  LCD_SendMasterCmd(SOFTWARE_RESET);
  LCD_SendMasterCmd(DISPLAY_OFF);
  LCD_SendMasterCmd(DYNAMIC_DRIVE);
  LCD_SendMasterCmd(DUTY_CYCLE);
  LCD_SendMasterCmd(CLOCKWISE_OUTPUT);
  LCD_SendMasterCmd(READ_MODIFY_WRITE_OFF);
  LCD_SendMasterCmd(START_COLUMN);          /* Set master column address to 0 */
  LCD_SendMasterCmd(START_LINE);            /* Set master display start line to 0 */
  LCD_SendMasterCmd(DISPLAY_ON );

  /* Slave LCD Init */
  LCD_SendSlaveCmd(SOFTWARE_RESET);
  LCD_SendSlaveCmd(DISPLAY_OFF);
  LCD_SendSlaveCmd(DYNAMIC_DRIVE);
  LCD_SendSlaveCmd(DUTY_CYCLE);
  LCD_SendSlaveCmd(CLOCKWISE_OUTPUT);
  LCD_SendSlaveCmd(READ_MODIFY_WRITE_OFF);
  LCD_SendSlaveCmd(START_COLUMN );          /* Set slave column address to 0 */
  LCD_SendSlaveCmd(START_LINE);             /* Set slave display start line to 0 */
  LCD_SendSlaveCmd(DISPLAY_ON);

  /* Clear LCD */	
  LCD_Clear();
  /* Set current Page to 0 for Master and Slave LCDs */	
  LCD_SetSlavePage(0);
  LCD_SetMasterPage(0);
}

/*******************************************************************************
* Function Name  : LCD_SetSlavePage
* Description    : Set the display page of slave LCD, the page range is 0 to 3,
*                  make sure the input will not exceed this range ,otherwise it
*                  will reach a undecided result.
* Input          : - Page: specifies the expected display page of slave LCD
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SetSlavePage(u8 Page)
{
  /* Set Slave page */
  LCD_SendSlaveCmd(0xB8|Page);
}

/*******************************************************************************
* Function Name  : LCD_SetMasterPage
* Description    : Set the display page of master LCD, the page range is 0 to 3,
*                  make sure the input will not exceed this range ,otherwise it
*                  will reach a undecided result.
* Input          : - Page: specifies the expected display page of master LCD
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SetMasterPage(u8 Page)
{
  /* Set Master page */
  LCD_SendMasterCmd(0xB8|Page);
}

/*******************************************************************************
* Function Name  : SetAddress
* Description    : Set the display column of slave LCD. Column range is 0 to 61.
* Input          : - Address: specifies the expected display column of slave LCD
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SetSlaveColumn(u8 Address)
{
  /* Set Slave column address */
  LCD_SendSlaveCmd(Address&0x7F);
}

/*******************************************************************************
* Function Name  : LCD_SetMasterColumn
* Description    : Set the display column of master LCD. Column range is 0 to 61.
* Input          : - Address: specifies the expected display column of slave LCD
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SetMasterColumn(u8 Address)
{
  /* Set Master column address */
  LCD_SendMasterCmd(Address&0x7F);
}

/*******************************************************************************
* Function Name  : LCD_SetTextColor
* Description    : Set the text color for LCD.
* Input          : - TextColor: BlackText: character on black, bottom on white.
*                               WhiteText: character on white, bottom on black.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SetTextColor(TextColorMode_TypeDef TextColor)
{
  if(TextColor)
  {
    /* Set White Text color */
    TextMode=WhiteText;
  }
  else
  {
    /* Set Black Text color */
    TextMode=BlackText;
  }
}

/*******************************************************************************
* Function Name  : LCD_Clear
* Description    : Clear the Master and Slave LCDs display.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_Clear(void)
{
  u8 Page = 0, Column = 0;	

  /* Clear master and slave LCDs page by page */
  for (Page=0; Page<4; Page++)
  {
    /* Set master and slave page by page */
    LCD_SetMasterPage(Page);
    LCD_SetSlavePage(Page);
    /* Set master and slave column address */
    LCD_SetMasterColumn(0);
    LCD_SetSlaveColumn(0);
    /* Send empty data to master and slave column address on the selected page */
    for (Column=0; Column<61; Column++)
    {
      LCD_SendSlaveData(0);
      LCD_SendMasterData(0);
    }
  }
}
	
/*******************************************************************************
* Function Name  : LCD_ClearLine
* Description    : Clear the selected line of the LCD.
* Input          : - Line: the Line to clear.
*                      - Line1 (Page0&1): clear the first line
*                      - Line2 (Page2&3): clear the second line
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_ClearLine(u8 Line)
{
  u8 Page = 0, Column = 0;	

  /* Clear the slected master and slave line */
  for (Page=Line; Page<Line+2; Page++)
  {
    /* Set master and slave page by page */
    LCD_SetMasterPage(Page);
    LCD_SetSlavePage(Page);
    /* Set master and slave column address */
    LCD_SetMasterColumn(0);
    LCD_SetSlaveColumn(0);
    /* Send empty data to master and slave column address on the selected page */
    for (Column=0; Column<61; Column++)
    {
      LCD_SendSlaveData(0);
      LCD_SendMasterData(0);
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_ClearMaster
* Description    : Clear the master LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_ClearMaster(void)
{
  u8 Page = 0, Column = 0;
	
  /* Clear all master LCD pages */
  for (Page=0; Page<4; Page++)
  {
    /* Set master page by page */
    LCD_SetMasterPage(Page);
    /* Set master column address */
    LCD_SetMasterColumn(0);
    /* Send empty data to master column address on the selected page */
    for (Column=0; Column<61; Column++)
    {
      LCD_SendMasterData(0);
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_ClearSlave
* Description    : Clear the slave LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_ClearSlave()
{
  u8 Page = 0, Column = 0;	

  /* Clear all slave LCD pages */
  for (Page=0; Page<4; Page++)
  {
    /* Set slave page by page */
    LCD_SetSlavePage(Page);
    /* Set slave column address */
    LCD_SetSlaveColumn(0);
    /* Send empty data to slave column address on the selected page */
    for (Column=0; Column<61; Column++)
    {
      LCD_SendSlaveData(0);
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawChar
* Description    : Draw a character in LCD.
*                  Note:
*                  the LCD can only display two line character,so page 0 and 1
*                  is to display the first line, page2 and page 3 is to display
*                  the second line.
* Input          : - Line: the Line where to display the character shape .
*                      - Line1 (Page0&1): display character on the first line
*                      - Line2 (Page2&3): display character on the second line
*                  - Column: start column address.
*                  - Width: the number of column (dots) of a character width.
*                  - Bmp: the pointer of the dot matrix data.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DrawChar(u8 Line, u8 Column, u8 Width, u8 *Bmp)
{
  u8 X = 0, ActualColumn = 0, Window = 0, i = 0;

  /* Draw the character column by column: width times */
  for(X = Column; X<(Column+Width); X++)
  {
    if(X > 121)
    {
      /* Return if column exceeded 121 */
      return;
    }
    if (X > 60) 	
    {
      /* To be displayed on slave LCD (Window = 1) */
      Window = 1;
      /* Get the Slave relative start column */
      ActualColumn = X%61;
    }
    else
    {	
      /* To be displayed on master LCD (Window = 0) */
      ActualColumn = X;
    }

    /* Switch window, display the character upper part */
    if (Window)
    {
      /* Display it on slave LCD */
      LCD_SetSlavePage(Line);
      LCD_SetSlaveColumn(ActualColumn);
      LCD_SendSlaveData(Bmp[i]);
    }
    else
    {
      /* Display it on master LCD */
      LCD_SetMasterPage(Line);
      LCD_SetMasterColumn(ActualColumn);
      LCD_SendMasterData(Bmp[i]);
    }
    /* Switch window, diplay the character lower part  */
    if (Window)
    {
      /* Display it on slave LCD */
      LCD_SetSlavePage(Line+1);
      LCD_SetSlaveColumn(ActualColumn);
      LCD_SendSlaveData(Bmp[i+1]);
    }
    else
    {
      /* Display it on master LCD */
      LCD_SetMasterPage(Line+1);
      LCD_SetMasterColumn(ActualColumn);
      LCD_SendMasterData(Bmp[i+1]);
    }
    /* Increment by 2 the character table index */
    i+=2;
  }
}

/*******************************************************************************
* Function Name  : LCD_DisplayChar
* Description    : Display one character (7dots large, 16dots high).
*                  Note:
*                  the LCD can only display two line character,so page 0 and 1
*                  is to display the first line, page2 and page 3 is to display
*                  the second line.
* Input          : - Line: the Line where to display the character.
*                      - Line1 (Page0&1): display character on the first line
*                      - Line2 (Page2&3): display character on the second line
*                  - Column: start column address.
*                  - Ascii: character ascii code.
*                  - CharMode: BlackText: character on black, bottom on white.
*                              WhiteText: character on white, bottom on black.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DisplayChar(u8 Line, u8 Column, u8 Ascii, TextColorMode_TypeDef CharMode)
{
  u8  DotBuffer[14], i = 0;

  /* Display the character lower and upper 8bit parts (2*7columns) */
  for (i=0;i<14;i++)
  {
    /* Character displayed as white Text on black buttom  */
    if(CharMode)
    {
      if(i%2==0)
      {
        DotBuffer[i] = ~AsciiDotsTable[Ascii*14+i+1];
      }
      else
      {
        DotBuffer[i] = ~AsciiDotsTable[Ascii*14+i-1];	
      }
    }
    /* Character displayed as black Text on white buttom  */
    else
    {
      if(i%2==0)
      {
        DotBuffer[i] = AsciiDotsTable[Ascii*14+i+1];			
      }
      else
      {
        DotBuffer[i] = AsciiDotsTable[Ascii*14+i-1];	
      }
    }
  }
  /* Display the asc code after conversion */
  LCD_DrawChar(Line, Column, 7, DotBuffer);
}

/*******************************************************************************
* Function Name  : LCD_HexToAsciiLow
* Description    : This function is used to convert the low nibble of an
*                  unsigned byte (0-F hex) to ASCII.
* Input          : - byte: byte to convert to ASCII.
* Output         : None
* Return         : ASCII value result of the conversion.
*******************************************************************************/
u8 LCD_HexToAsciiLow(u8 byte)
{
  /* Keep lower nibble only */
  byte = byte & 0x0F;
  /* If the ascii is a number */	
  if (byte <= 0x09)
  {
    /* Add 0x30 to its ascii */
    return(byte + 0x30);
  }
  else
  {
    /* Add 0x37 to its ascii */
    return (byte + 0x37);
  }
}

/*******************************************************************************
* Function Name  : LCD_HexToAsciiHigh
* Description    : This function is used to convert the high nibble of an
*                  unsigned byte (0-F hex) to ASCII.
* Input          : - byte: byte to convert to ASCII.
* Output         : None
* Return         : ASCII value result of the conversion.
*******************************************************************************/
u8 LCD_HexToAsciiHigh(u8 byte)
{
  /* Keep upper nibble only */
  byte = byte & 0xF0;	
  byte = byte >> 4;
  /* If the ascii is a number */
  if (byte <= 0x09)
  {
    /* Add 0x30 to display its ascii */
    return(byte + 0x30);
  }
  else
  {
    /* Add 0x37 to display its ascii */
    return (byte + 0x37);
  }
}

/*******************************************************************************
* Function Name  : LCD_DisplayString
* Description    : This function is used to display a 17char max string of
*                  characters on the LCD display on the selected line.
*                  Note:
*                  this function is the user interface to use the LCD driver.
* Input          : - *ptr: pointer to string to display on LCD.
*                  - Line: the Line where to display the character.
*                      - Line1 (Page0&1): display character on the first line
*                      - Line2 (Page2&3): display character on the second line
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DisplayString(u8 Line, u8 *ptr, TextColorMode_TypeDef CharMode)
{
  u8 RefColumn = 0, i = 0;

  /* Send the string character by character on lCD */
  while ((*ptr!=0)&(i<17))
  {
    /* Display one character on LCD */
    LCD_DisplayChar(Line, RefColumn, *ptr, CharMode);
    /* Increment the column position by 7 */
    RefColumn+=7;
    /* Point on the next character */
    ptr++;
    /* Increment the character counter */
    i++;
    /* If we reach the maximum Line character */
    if(i==17)
    {
      LCD_DisplayChar(Line, RefColumn-1, 0x1f, CharMode); /* Add missed columns */
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_Printf
* Description    : This function is used to display a string of characters
*                  on the LCD display.
*                  Note:
*                  this function is the user interface to use the LCD driver.
* Input          : - *ptr: pointer to string to display on LCD.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_Printf(u8 *ptr, ...)
{
  u8 RefColumn = 0, RefPage = 0, i = 0, c1 = 0;
  u16  var = 0, c2 = 0, c3 = 0, c4 = 0, c5 = 0;
  u32 WordVar = 0;

  /* Store pointer on LCD_Printf second parameter (String) */
  u8 *var_ptr=(u8 *)(&ptr+1);

  /* Send String */
  while (*ptr != 0)
  {
    c1 = *ptr;
    /* Limited to AsciiDotsTable code table */
    if(c1 <= 128)
    {
      /* Carriage return */
      if ( *ptr == '\r')
      {
        ptr++;
        RefColumn = 0;
      }
      /* Jump to Line2 */
      else if( *ptr == '\n')
      {
        /* Point on the string to display */
        ptr++;
        /* Clear Line2 */
        LCD_ClearLine(Line2);
        /* Point on first Line2 column */
        RefColumn = 0;
        /* Increment RefPage by 2 */
        RefPage+=2;
      }
      /* Display value on the passed format */
      else if( *ptr == '%')
      {
        ptr++;
        /* Display decimal value */
	if (*ptr == 'd')
	{
	  ptr++;
          /* Get the word value to display */
          WordVar = ((*var_ptr)|(*(var_ptr+1)<<8)|(*(var_ptr+2)<<16));
          c1=WordVar/10000;
          c2=(WordVar%10000)/1000;
          c3=(WordVar%1000)/100;
          c4=(WordVar%100)/10;
          c5=(WordVar%10);
          /* Display the ten miles digit */
          if (c1!=0)
          {
            LCD_DisplayChar(RefPage, RefColumn, c1+0x30, TextMode);
	    RefColumn+=7;
          }
          /* Display the miles digit */
          if (!((c1==0)&(c2==0)))
          {
          LCD_DisplayChar(RefPage, RefColumn, c2+0x30, TextMode);
	  RefColumn+=7;
          }
          /* Display the hundred digit */
          if (!((c1==0)&(c2==0)&(c3==0)))
          {
          LCD_DisplayChar(RefPage, RefColumn, c3+0x30, TextMode);
	  RefColumn+=7;
          }
          /* Display the tens digit */
          if (!((c1==0)&(c2==0)&(c3==0)&(c4==0)))
          {
          LCD_DisplayChar(RefPage, RefColumn, c4+0x30, TextMode);
	  RefColumn+=7;
          }
          /* Display the rest */
          LCD_DisplayChar(RefPage, RefColumn, c5+0x30, TextMode);
	  RefColumn+=7;
        }
        /* Display 16bits Hex value */
        else if (*ptr == 'x')
        {
          ptr++;
          /* Display 8bits MSB */
          var_ptr = var_ptr +1;
          var = *var_ptr;
          c1 = LCD_HexToAsciiHigh(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          c1 = LCD_HexToAsciiLow(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          /* Display 8bits LSB */
          var_ptr = var_ptr -1;
          var = *var_ptr;
          var_ptr = var_ptr +4;
          c1 = LCD_HexToAsciiHigh(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          c1 = LCD_HexToAsciiLow(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
        }
        /* Display 32bits Hex value */
        else if (*ptr == 'w')
        {
          ptr++;
          /* Display 16bits MSB */
          var_ptr = var_ptr +3;
          var = *var_ptr;
          c1 = LCD_HexToAsciiHigh(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          c1 = LCD_HexToAsciiLow(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          var_ptr = var_ptr -1;
          var = *var_ptr;
          c1 = LCD_HexToAsciiHigh(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          c1 = LCD_HexToAsciiLow(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          /* Display 16bits LSB */
          var_ptr = var_ptr -1;
          var = *var_ptr;
          var_ptr = var_ptr +4;
          c1 = LCD_HexToAsciiHigh(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          c1 = LCD_HexToAsciiLow(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          var_ptr = var_ptr -5;
          var = *var_ptr;
          var_ptr = var_ptr +4;
          c1 = LCD_HexToAsciiHigh(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          c1 = LCD_HexToAsciiLow(var);
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
        }
        else
        {
          /* Display '%' character which is followed by (d, x or w) */
          ptr--;
          c1 = *ptr;
          LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
          RefColumn+=7;
          ptr++;
          i++;
          if(i==17)
          {
            /* Add missed columns */
            LCD_DisplayChar(RefPage, RefColumn-1, 0x1f, TextMode);
            RefColumn = 0;
            RefPage+=2;
          }
        }
      }
      else
      {	
        /* Display characters different from (\r, \n, %) */ 			
        LCD_DisplayChar(RefPage, RefColumn, c1, TextMode);
        RefColumn+=7;
        ptr++;
        i++;
        if(i==17)
        {
          /* Add missed columns */
          LCD_DisplayChar(RefPage, RefColumn-1, 0x1f, TextMode);
          LCD_ClearLine(Line2);
          RefColumn = 0;
          RefPage+=2;
        }
      }
    }
  }
  /* Display spaces if string doesn't reach the max LCD characters size */
  while(RefColumn<119)
  {
    /* Display Spaces */
    LCD_DisplayChar(RefPage, RefColumn, 0x20, TextMode);
    RefColumn+=7;
    /* Add missed columns */
    LCD_DisplayChar(RefPage, RefColumn, 0x1f, TextMode);
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawMasterGraphic
* Description    : Draw a Graphic image on master LCD.
* Input          : - Bmp: the pointer of the dot matrix data.
* Output         : None
* Return         : None.
*******************************************************************************/
void LCD_DrawMasterGraphic(u8 *Bmp)
{
  u8 j = 0, k = 0, ActPage = 0;

  /* Draw graphic on master: 61 Column *4 Pages */
  while(j<244)
  {
    /* Draw on master page by page */
    LCD_SetMasterPage(ActPage);
    for(k=0; k<61; k++)
    {
      LCD_SetMasterColumn(k);
      LCD_SendMasterData(*Bmp++);
      j++;
    }
    ActPage++;
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawSlaveGraphic
* Description    : Draw a Graphic image on slave LCD.
* Input          : - Bmp: the pointer of the dot matrix data.
* Output         : None
* Return         : None.
*******************************************************************************/
void LCD_DrawSlaveGraphic(u8 *Bmp)
{
  u8 j = 0, k = 0, ActPage = 0;

  /* Draw graphic on slave: 61 Column *4 Pages */
  while(j<244)
  {
    /* Draw on slave page by page */
    LCD_SetSlavePage(ActPage);
    for(k=0; k<61; k++)
    {
      LCD_SetSlaveColumn(k);
      LCD_SendSlaveData(*Bmp++);
      j++;
    }
    ActPage++;
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawGraphic
* Description    : Draw a Graphic image on LCD.
* Input          : - Bmp: the pointer of the dot matrix data.
* Output         : None
* Return         : None.
*******************************************************************************/
void LCD_DrawGraphic(u8 *Bmp)
{
  u8 Pos = 0, ActPage = 0;
  u16 j = 0, k = 0;

  /* Draw graphic on LCD: 122 Column *4 Pages */
  while(j<488)
  {
    if(!Pos)
    {
      /* Draw on master page by page */
      LCD_SetMasterPage(ActPage);
      for(k=0; k<61; k++)
      {
        LCD_SetMasterColumn(k);
        LCD_SendMasterData(*Bmp++);
        j++;
      }
      Pos=1;
    }
    else
    {
      /* Draw on slave page by page */
      LCD_SetSlavePage(ActPage);
      for(k=0; k<61; k++)
      {
        LCD_SetSlaveColumn(k);
        LCD_SendSlaveData(*Bmp++);
        j++;
      }
      ActPage++;
      Pos=0;
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_ScrollGraphic
* Description    : Scroll a Graphic image on LCD.
* Input          : - Bmp: the pointer of the dot matrix data.
*                  - nCount: specifies the delay time length.
* Output         : None
* Return         : None.
*******************************************************************************/
void LCD_ScrollGraphic(u8 *Bmp, u32 nCount)
{
  u8 Pos = 0, ActPage = 0;
  u16 j = 0, k = 0;
  u32 Counter = 0;

  /* Draw graphic on LCD: 122 Column *4 Pages */
  while(j<488)
  {
    if(!Pos)
    {
      /* Draw on master page by page */
      LCD_SetMasterPage(ActPage);
      for(k=0; k<61; k++)
      {
        LCD_SetMasterColumn(k);
        LCD_SendMasterData(*Bmp++);
        Counter = nCount;
        /* Set a delay */
        for(; Counter != 0; Counter--);
        j++;
      }
      Pos=1;
    }
    else
    {
      /* Draw on slave page by page */
      LCD_SetSlavePage(ActPage);
      for(k=0; k<61; k++)
      {
        LCD_SetSlaveColumn(k);
        Counter = nCount;
        /* Set a delay */
        for(; Counter != 0; Counter--);
        LCD_SendSlaveData(*Bmp++);
        j++;
      }
      ActPage++;
      Pos=0;
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawPixel
* Description    : Draw a Graphic image on slave LCD.
* Input          : - XPos: the dot line number of the pixel.
*                      - 1->61 : displayed on master LCD
*                      - 62->122: displayed on slave LCD
*                  - YPos: column address of the pixel from 1->32.
*                  - Mode: Dot_On: Pixel turned on (black).
*                          Dot_Off: Pixel turned off (black).
* Output         : None
* Return         : None.
*******************************************************************************/
void LCD_DrawPixel(u8 XPos, u8 YPos, DotMode_TypeDef Mode)
{
  u8 Page = 0, Position = 0;
  u16 Mask = 0;
  u32 MasterDataIn = 0, MasterDataOut = 0, SlaveDataIn = 0, SlaveDataOut = 0;

  /* Pixel page */
  Page = (XPos-1)/8;
  /* Pixel column  */
  Position = (YPos-1)/61; /* 0:Master, 1:Slave */
  /* Mask for the pixel */
  Mask= 1<<((XPos-1)%8);
  /* If Position=0 draw pixel on master LCD */
  if(!Position)
  {
    LCD_SetMasterPage(Page);
    LCD_SetMasterColumn(YPos-1);
    MasterDataIn = LCD_ReadMasterData();
    MasterDataIn = LCD_ReadMasterData();
    LCD_SetMasterColumn(YPos-1);
    if(Mode==Dot_On)
    {
      MasterDataOut = MasterDataIn | Mask;
    }
    else
    {
      MasterDataOut = MasterDataIn & (~Mask);
    }
    LCD_SendMasterData(MasterDataOut);
  }
  /* If Position=1 draw pixel on slave LCD */
  else
  {
    LCD_SetSlavePage(Page);
    LCD_SetSlaveColumn(YPos-62);
    SlaveDataIn = LCD_ReadSlaveData();
    SlaveDataIn = LCD_ReadSlaveData();
    LCD_SetSlaveColumn(YPos-62);
    if(Mode==Dot_On)
    {
      SlaveDataOut = SlaveDataIn | Mask;
    }
    else
    {
      SlaveDataOut = SlaveDataIn & (~Mask);
    }
    LCD_SendSlaveData(SlaveDataOut);
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawLine
* Description    : Draw a line on master and slave LCDs.
* Input          : - XPos1: the dot line number of the source point .
*                  - XPos2: the dot line number of the destination point .
*                  - YPos1: the dot column number of the source point.
*                  - YPos2: the dot column number of the destination point.
* Output         : None
* Return         : None.
*******************************************************************************/
void LCD_DrawLine(u8 XPos1, u8 YPos1, u8 XPos2, u8 YPos2)
{
  u8 XPos = 0, YPos = 0;

  /* Use XPos1, YPos1, XPos2 and YPos2 */
  if((XPos2>=XPos1)&(YPos2>=YPos1))
  {
    for(XPos=XPos1; XPos<=XPos2; XPos++)
    {
      for(YPos=YPos1; YPos<=YPos2; YPos++)
      {
        LCD_DrawPixel(XPos, YPos, Dot_On);
      }
    }
  }
  else if((XPos2<XPos1)&(YPos2>=YPos1))
  {
    for(XPos=XPos2; XPos<=XPos1; XPos++)
    {
      for(YPos=YPos1; YPos<=YPos2; YPos++)
      {
        LCD_DrawPixel(XPos, YPos, Dot_On);
      }
    }
  }
  else if((XPos2>=XPos1)&(YPos2<YPos1))
  {
    for(XPos=XPos1; XPos<=XPos2; XPos++)
    {
      for(YPos=YPos2; YPos<=YPos1; YPos++)
      {
        LCD_DrawPixel(XPos, YPos, Dot_On);
      }
    }
  }
  else /*if((XPos2<XPos1)&(YPos2<YPos1))*/
  {
    for(XPos=XPos2; XPos<=XPos1; XPos++)
    {
      for(YPos=YPos2; YPos<=YPos1; YPos++)
      {
        LCD_DrawPixel(XPos, YPos, Dot_On);
      }
    }
  }
}

/*******************************************************************************
* Function Name  : LCD_DrawBox
* Description    : Draw a Box on master and slave LCDs.
* Input          : - XPos: the dot line number of the source point .
*                  - YPos: the dot column number of the source point.
*                  - Dx: Box large.
*                  - Dy: Box width.
* Output         : None
* Return         : None.
*******************************************************************************/
void LCD_DrawBox(u8 XPos, u8 YPos, u8 Dx, u8 Dy)
{
  /* Use XPos, YPos, Dx and Dy */
  LCD_DrawLine(XPos, YPos, XPos, YPos+Dy);
  LCD_DrawLine(XPos, YPos, XPos+Dx, YPos);
  LCD_DrawLine(XPos+Dx, YPos, XPos+Dx, YPos+Dy);
  LCD_DrawLine(XPos, YPos+Dy, XPos+Dx, YPos+Dy);
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE******/

