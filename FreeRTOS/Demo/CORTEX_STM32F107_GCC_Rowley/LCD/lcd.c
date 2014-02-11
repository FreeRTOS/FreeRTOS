/******************** (C) COPYRIGHT 2008 STMicroelectronics ********************
* File Name          : lcd.c
* Author             : MCD Application Team
* Version            : VX.Y.Z
* Date               : mm/dd/yyyy
* Description        : This file includes the LCD driver for AM-240320L8TNQW00H
*                      (LCD_ILI9320) Liquid Crystal Display Module of STM3210D-EVAL
*                      board.
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "FreeRTOS.h"
#include "task.h"

#include    <stdio.h>
#include    <string.h>
#include    <ctype.h>
#include    <stdlib.h>
#include    <stdarg.h>

#include    <stm32f10x_conf.h>
#include    <stm32f10x_lib.h>

#include    "STM3210D_lcd.h"
#include 	"fonts.h"

extern void timerDly(unsigned int);

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define START_BYTE      0x70
#define SET_INDEX       0x00
#define READ_STATUS     0x01
#define LCD_WRITE_REG   0x02
#define LCD_READ_REG    0x03

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
  /* Global variables to set the written text color */
static  vu16 TextColor = 0x0000, BackColor = 0xFFFF;

/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

#define timerDly( x )	vTaskDelay( ( x * 10 ) / portTICK_PERIOD_MS );
#define vBlockToWait( x )

/*******************************************************************************
* Function Name  : LCD_Setup
* Description    : Setups the LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_Setup(void)
{
/* Configure the LCD Control pins --------------------------------------------*/
  LCD_CtrlLinesConfig();

/* Configure the SPI3 interface ----------------------------------------------*/
  LCD_SPIConfig();

  timerDly(5); /* Delay 50 ms */
  /* Start Initial Sequence ------------------------------------------------*/
  LCD_WriteReg(R229, 0x8000); /* Set the internal vcore voltage */
  LCD_WriteReg(R0,  0x0001); /* Start internal OSC. */
  LCD_WriteReg(R1,  0x0100); /* set SS and SM bit */
  LCD_WriteReg(R2,  0x0700); /* set 1 line inversion */
  LCD_WriteReg(R3,  0x1030); /* set GRAM write direction and BGR=1. */
  LCD_WriteReg(R4,  0x0000); /* Resize register */
  LCD_WriteReg(R8,  0x0202); /* set the back porch and front porch */
  LCD_WriteReg(R9,  0x0000); /* set non-display area refresh cycle ISC[3:0] */
  LCD_WriteReg(R10, 0x0000); /* FMARK function */
  LCD_WriteReg(R12, 0x0000); /* RGB interface setting */
  LCD_WriteReg(R13, 0x0000); /* Frame marker Position */
  LCD_WriteReg(R15, 0x0000); /* RGB interface polarity */

  /* Power On sequence -----------------------------------------------------*/
  LCD_WriteReg(R16, 0x0000); /* SAP, BT[3:0], AP, DSTB, SLP, STB */
  LCD_WriteReg(R17, 0x0000); /* DC1[2:0], DC0[2:0], VC[2:0] */
  LCD_WriteReg(R18, 0x0000); /* VREG1OUT voltage */
  LCD_WriteReg(R19, 0x0000); /* VDV[4:0] for VCOM amplitude */
  timerDly(20);                 /* Dis-charge capacitor power voltage (200ms) */
  LCD_WriteReg(R16, 0x17B0); /* SAP, BT[3:0], AP, DSTB, SLP, STB */
  LCD_WriteReg(R17, 0x0137); /* DC1[2:0], DC0[2:0], VC[2:0] */
  timerDly(5);                  /* Delay 50 ms */
  LCD_WriteReg(R18, 0x0139); /* VREG1OUT voltage */
  timerDly(5);                  /* Delay 50 ms */
  LCD_WriteReg(R19, 0x1d00); /* VDV[4:0] for VCOM amplitude */
  LCD_WriteReg(R41, 0x0013); /* VCM[4:0] for VCOMH */
  timerDly(5);                  /* Delay 50 ms */
  LCD_WriteReg(R32, 0x0000); /* GRAM horizontal Address */
  LCD_WriteReg(R33, 0x0000); /* GRAM Vertical Address */

  /* Adjust the Gamma Curve ------------------------------------------------*/
  LCD_WriteReg(R48, 0x0006);
  LCD_WriteReg(R49, 0x0101);
  LCD_WriteReg(R50, 0x0003);
  LCD_WriteReg(R53, 0x0106);
  LCD_WriteReg(R54, 0x0b02);
  LCD_WriteReg(R55, 0x0302);
  LCD_WriteReg(R56, 0x0707);
  LCD_WriteReg(R57, 0x0007);
  LCD_WriteReg(R60, 0x0600);
  LCD_WriteReg(R61, 0x020b);

  /* Set GRAM area ---------------------------------------------------------*/
  LCD_WriteReg(R80, 0x0000); /* Horizontal GRAM Start Address */
  LCD_WriteReg(R81, 0x00EF); /* Horizontal GRAM End Address */
  LCD_WriteReg(R82, 0x0000); /* Vertical GRAM Start Address */
  LCD_WriteReg(R83, 0x013F); /* Vertical GRAM End Address */

  LCD_WriteReg(R96,  0x2700); /* Gate Scan Line */
  LCD_WriteReg(R97,  0x0001); /* NDL,VLE, REV */
  LCD_WriteReg(R106, 0x0000); /* set scrolling line */

  /* Partial Display Control -----------------------------------------------*/
  LCD_WriteReg(R128, 0x0000);
  LCD_WriteReg(R129, 0x0000);
  LCD_WriteReg(R130, 0x0000);
  LCD_WriteReg(R131, 0x0000);
  LCD_WriteReg(R132, 0x0000);
  LCD_WriteReg(R133, 0x0000);

  /* Panel Control ---------------------------------------------------------*/
  LCD_WriteReg(R144, 0x0010);
  LCD_WriteReg(R146, 0x0000);
  LCD_WriteReg(R147, 0x0003);
  LCD_WriteReg(R149, 0x0110);
  LCD_WriteReg(R151, 0x0000);
  LCD_WriteReg(R152, 0x0000);

  /* Set GRAM write direction and BGR = 1 */
  /* I/D=01 (Horizontal : increment, Vertical : decrement) */
  /* AM=1 (address is updated in vertical writing direction) */
  LCD_WriteReg(R3, 0x1018);

  LCD_WriteReg(R7, 0x0173); /* 262K color and display ON */
}

/*******************************************************************************
* Function Name  : STM3210D_LCD_Init
* Description    : Initializes the LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void STM3210D_LCD_Init(void)
{
  /* Setups the LCD */
  LCD_Setup();
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
  LCD_DisplayStringLine(Line, ( unsigned char * ) "                    ");
}

/*******************************************************************************
* Function Name  : LCD_Clear
* Description    : Clears the hole LCD.
* Input          : Color: the color of the background.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_Clear(u16 Color)
{
  vu32 index = 0;

  LCD_SetCursor(0x00, 0x013F);

  LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */

  for(index = 0; index < 76800; index++)
  {
    LCD_WriteRAM(Color);
  }

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);

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
 LCD_WriteReg(R32, Xpos);
 LCD_WriteReg(R33, Ypos);
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
  vu32 index = 0, i = 0;
  vu8 Xaddress = 0;

  Xaddress = Xpos;

  LCD_SetCursor(Xaddress, Ypos);

  for(index = 0; index < 24; index++)
  {
    LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */

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
    LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);
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
  vu32 i = 0;
  vu16 refcolumn = 319;

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
* Function Name  : LCD_SetDisplayWindow
* Description    : Sets a display window
* Input          : - Xpos: specifies the X buttom left position.
*                  - Ypos: specifies the Y buttom left position.
*                  - Height: display window height.
*                  - Width: display window width.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SetDisplayWindow(u8 Xpos, u16 Ypos, u8 Height, u16 Width)
{
  /* Horizontal GRAM Start Address */
  if(Xpos >= Height)
  {
    LCD_WriteReg(R80, (Xpos - Height + 1));
  }
  else
  {
    LCD_WriteReg(R80, 0);
  }
  /* Horizontal GRAM End Address */
  LCD_WriteReg(R81, Xpos);
  /* Vertical GRAM Start Address */
  if(Ypos >= Width)
  {
    LCD_WriteReg(R82, (Ypos - Width + 1));
  }
  else
  {
    LCD_WriteReg(R82, 0);
  }
  /* Vertical GRAM End Address */
  LCD_WriteReg(R83, Ypos);
  LCD_SetCursor(Xpos, Ypos);
}

/*******************************************************************************
* Function Name  : LCD_WindowModeDisable
* Description    : Disables LCD Window mode.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_WindowModeDisable(void)
{
  LCD_SetDisplayWindow(239, 0x13F, 240, 320);
  LCD_WriteReg(R3, 0x1018);
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
    LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */

    for(i = 0; i < Length; i++)
    {
      LCD_WriteRAM(TextColor);
    }
    LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);
  }
  else
  {
    for(i = 0; i < Length; i++)
    {
      LCD_WriteRAMWord(TextColor);
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
  s32  D;/* Decision Variable */
  u32  CurX;/* Current X Value */
  u32  CurY;/* Current Y Value */

  D = 3 - (Radius << 1);
  CurX = 0;
  CurY = Radius;

  while (CurX <= CurY)
  {
    LCD_SetCursor(Xpos + CurX, Ypos + CurY);
    LCD_WriteRAMWord(TextColor);

    LCD_SetCursor(Xpos + CurX, Ypos - CurY);
    LCD_WriteRAMWord(TextColor);

    LCD_SetCursor(Xpos - CurX, Ypos + CurY);
    LCD_WriteRAMWord(TextColor);

    LCD_SetCursor(Xpos - CurX, Ypos - CurY);
    LCD_WriteRAMWord(TextColor);

    LCD_SetCursor(Xpos + CurY, Ypos + CurX);
    LCD_WriteRAMWord(TextColor);

    LCD_SetCursor(Xpos + CurY, Ypos - CurX);
    LCD_WriteRAMWord(TextColor);

    LCD_SetCursor(Xpos - CurY, Ypos + CurX);
    LCD_WriteRAMWord(TextColor);

    LCD_SetCursor(Xpos - CurY, Ypos - CurX);
    LCD_WriteRAMWord(TextColor);

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
  LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */

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
  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);

}

///*******************************************************************************
//* Function Name  : LCD_DrawBMP
//* Description    : Displays a bitmap picture loaded in the SPI Flash.
//* Input          : - BmpAddress: Bmp picture address in the SPI Flash.
//* Output         : None
//* Return         : None
//*******************************************************************************/
//void LCD_DrawBMP(u32 BmpAddress)
//{
//  u32 i = 0, size = 0;
//
//  /* Read bitmap size */
//  SPI_FLASH_BufferRead((u8*)&size, BmpAddress + 2, 4);
//
//  /* get bitmap data address offset */
//  SPI_FLASH_BufferRead((u8*)&i, BmpAddress + 10, 4);
//
//  size = (size - i)/2;
//
//  SPI_FLASH_StartReadSequence(BmpAddress + i);
//
//  /* Disable SPI1  */
//  SPI_Cmd(SPI1, DISABLE);
//  /* SPI in 16-bit mode */
//  SPI_DataSizeConfig(SPI1, SPI_DataSize_16b);
//
//  /* Enable SPI1  */
//  SPI_Cmd(SPI1, ENABLE);
//
//  /* Set GRAM write direction and BGR = 1 */
//  /* I/D=00 (Horizontal : decrement, Vertical : decrement) */
//  /* AM=1 (address is updated in vertical writing direction) */
//  LCD_WriteReg(R3, 0x1008);
//
//  LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */
//
//  /* Read bitmap data from SPI Flash and send them to LCD */
//  for(i = 0; i < size; i++)
//  {
//    LCD_WriteRAM(__REV_HalfWord(SPI_FLASH_SendHalfWord(0xA5A5)));
//  }
//
//  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);
//
//  /* Deselect the FLASH: Chip Select high */
//  SPI_FLASH_CS_HIGH();
//
//  /* Disable SPI1  */
//  SPI_Cmd(SPI1, DISABLE);
//  /* SPI in 8-bit mode */
//  SPI_DataSizeConfig(SPI1, SPI_DataSize_8b);
//
//  /* Enable SPI1  */
//  SPI_Cmd(SPI1, ENABLE);
//
//  /* Set GRAM write direction and BGR = 1 */
//  /* I/D = 01 (Horizontal : increment, Vertical : decrement) */
//  /* AM = 1 (address is updated in vertical writing direction) */
//  LCD_WriteReg(R3, 0x1018);
//}

/*******************************************************************************
* Function Name  : LCD_DrawBMP
* Description    : Displays a bitmap picture loaded in the SPI Flash.
* Input          : - BmpAddress: Bmp picture address in the SPI Flash.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_DrawBMP(uc16 *BmpAddress)
{
  u32 i = 0, size = 0;

  /* Read bitmap size */
  size = BmpAddress[1] | (BmpAddress[2] << 16);

  /* get bitmap data address offset */
  i = BmpAddress[5] | (BmpAddress[6] << 16);

  size = (size - i)/2;

  BmpAddress += i/2;
  /* Set GRAM write direction and BGR = 1 */
  /* I/D=00 (Horizontal : decrement, Vertical : decrement) */
  /* AM=1 (address is updated in vertical writing direction) */
  LCD_WriteReg(R3, 0x1008);

  LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */

  /* Read bitmap data from SPI Flash and send them to LCD */
  for(i = 0; i < size; i++)
  {
    LCD_WriteRAM(BmpAddress[i]);
  }

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);

  /* Set GRAM write direction and BGR = 1 */
  /* I/D = 01 (Horizontal : increment, Vertical : decrement) */
  /* AM = 1 (address is updated in vertical writing direction) */
  LCD_WriteReg(R3, 0x1018);
}

/*******************************************************************************
* Function Name  : LCD_nCS_StartByte
* Description    : Reset LCD control line(/CS) and Send Start-Byte
* Input          : - Start_Byte: the Start-Byte to be sent
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_nCS_StartByte(u8 Start_Byte)
{
  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_RESET);

  SPI_I2S_SendData(SPI3, Start_Byte);
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
  }
}

/*******************************************************************************
* Function Name  : LCD_WriteRegIndex
* Description    : Writes index to select the LCD register.
* Input          : - LCD_Reg: address of the selected register.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_WriteRegIndex(u8 LCD_Reg)
{
  /* Reset LCD control line(/CS) and Send Start-Byte */
  LCD_nCS_StartByte(START_BYTE | SET_INDEX);

  /* Write 16-bit Reg Index (High Byte is 0) */
  SPI_I2S_SendData(SPI3, 0x00);
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
  }
  SPI_I2S_SendData(SPI3, LCD_Reg);
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
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
u16 LCD_ReadReg(u8 LCD_Reg)
{
  vu16 tmp = 0;
  vu8 i = 0;

  /* SPI3 prescaler: 4 */
  SPI3->CR1 &= 0xFFC7;
  SPI3->CR1 |= 0x0008;

  /* Write 16-bit Index (then Read Reg) */
  LCD_WriteRegIndex(LCD_Reg);

  /* Read 16-bit Reg */
  /* Reset LCD control line(/CS) and Send Start-Byte */
  LCD_nCS_StartByte(START_BYTE | LCD_READ_REG);

  for(i = 0; i < 5; i++)
  {
    SPI_I2S_SendData(SPI3, 0xFF);

    while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
    {
		vBlockToWait( 1 );
    }
    /* One byte of invalid dummy data read after the start byte */
    while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_RXNE) == RESET)
    {
		vBlockToWait( 1 );
    }
    SPI_I2S_ReceiveData(SPI3);
  }

  SPI_I2S_SendData(SPI3, 0xFF);
  /* Read upper byte */
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
  }
  /* Read lower byte */
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_RXNE) == RESET)
  {
	vBlockToWait( 1 );
  }
  tmp = SPI_I2S_ReceiveData(SPI3);


  SPI_I2S_SendData(SPI3, 0xFF);
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
  }
  /* Read lower byte */
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_RXNE) == RESET)
  {
	vBlockToWait( 1 );
  }
  tmp = ((tmp & 0xFF) << 8) | SPI_I2S_ReceiveData(SPI3);

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);

  /* SPI3 prescaler: 2 */
  SPI3->CR1 &= 0xFFC7;

  return tmp;
}

/*******************************************************************************
* Function Name  : LCD_WriteRAM_Prepare
* Description    : Prepare to write to the LCD RAM.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_WriteRAM_Prepare(void)
{
  LCD_WriteRegIndex(R34); /* Select GRAM Reg */

  /* Reset LCD control line(/CS) and Send Start-Byte */
  LCD_nCS_StartByte(START_BYTE | LCD_WRITE_REG);
}

/*******************************************************************************
* Function Name  : LCD_WriteRAMWord
* Description    : Writes 1 word to the LCD RAM.
* Input          : - RGB_Code: the pixel color in RGB mode (5-6-5).
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_WriteRAMWord(u16 RGB_Code)
{
  LCD_WriteRAM_Prepare();

  LCD_WriteRAM(RGB_Code);

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);
}

/*******************************************************************************
* Function Name  : LCD_WriteReg
* Description    : Writes to the selected LCD register.
* Input          : - LCD_Reg: address of the selected register.
*                  - LCD_RegValue: value to write to the selected register.
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_WriteReg(u8 LCD_Reg, u16 LCD_RegValue)
{
  /* Write 16-bit Index (then Write Reg) */
  LCD_WriteRegIndex(LCD_Reg);

  /* Write 16-bit Reg */
  /* Reset LCD control line(/CS) and Send Start-Byte */
  LCD_nCS_StartByte(START_BYTE | LCD_WRITE_REG);

  SPI_I2S_SendData(SPI3, LCD_RegValue>>8);
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
  }
  SPI_I2S_SendData(SPI3, (LCD_RegValue & 0xFF));
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
  }

  LCD_CtrlLinesWrite(GPIOB, CtrlPin_NCS, Bit_SET);
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
  SPI_I2S_SendData(SPI3, RGB_Code >> 8);
  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
  }
  SPI_I2S_SendData(SPI3, RGB_Code & 0xFF);

  while(SPI_I2S_GetFlagStatus(SPI3, SPI_I2S_FLAG_BSY) != RESET)
  {
	vBlockToWait( 1 );
  }
}

/*******************************************************************************
* Function Name  : LCD_PowerOn
* Description    : Power on the LCD.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_PowerOn(void)
{
  /* Power On sequence ---------------------------------------------------------*/
  LCD_WriteReg(R16, 0x0000); /* SAP, BT[3:0], AP, DSTB, SLP, STB */
  LCD_WriteReg(R17, 0x0000); /* DC1[2:0], DC0[2:0], VC[2:0] */
  LCD_WriteReg(R18, 0x0000); /* VREG1OUT voltage */
  LCD_WriteReg(R19, 0x0000); /* VDV[4:0] for VCOM amplitude */
  timerDly(20);                 /* Dis-charge capacitor power voltage (200ms) */
  LCD_WriteReg(R16, 0x17B0); /* SAP, BT[3:0], AP, DSTB, SLP, STB */
  LCD_WriteReg(R17, 0x0137); /* DC1[2:0], DC0[2:0], VC[2:0] */
  timerDly(5);                  /* delay 50 ms */
  LCD_WriteReg(R18, 0x0139); /* VREG1OUT voltage */
  timerDly(5);                  /* delay 50 ms */
  LCD_WriteReg(R19, 0x1d00); /* VDV[4:0] for VCOM amplitude */
  LCD_WriteReg(R41, 0x0013); /* VCM[4:0] for VCOMH */
  timerDly(5);                  /* delay 50 ms */
  LCD_WriteReg(R7, 0x0173);  /* 262K color and display ON */
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
  /* Display On */
  LCD_WriteReg(R7, 0x0173); /* 262K color and display ON */

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
  LCD_WriteReg(R7, 0x0);
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
//  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_7 | GPIO_Pin_15;
//  GPIO_Init(GPIOD, &GPIO_InitStructure);

//  LCD_CtrlLinesWrite(GPIOD, CtrlPin_NWR, Bit_SET);
//  LCD_CtrlLinesWrite(GPIOD, CtrlPin_RS, Bit_SET);
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
* Description    : Configures the SPI3 interface.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LCD_SPIConfig(void)
{
  SPI_InitTypeDef    SPI_InitStructure;
  GPIO_InitTypeDef   GPIO_InitStructure;

  /* Enable GPIOC clock */
  RCC_APB2PeriphClockCmd(RCC_APB2Periph_GPIOC | RCC_APB2Periph_AFIO, ENABLE);

  //GPIO_PinRemapConfig(GPIO_Remap_SPI3, ENABLE);
  AFIO->MAPR |= GPIO_Remap_SPI3;

  /* Enable SPI3 clock  */
  RCC_APB1PeriphClockCmd(RCC_APB1Periph_SPI3, ENABLE);

  /* Configure SPI3 pins: SCK, MISO and MOSI */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_10 | GPIO_Pin_11 | GPIO_Pin_12;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF_PP;
  GPIO_Init(GPIOC, &GPIO_InitStructure);

  SPI_I2S_DeInit(SPI3);

  /* SPI3 Config */
  SPI_InitStructure.SPI_Direction = SPI_Direction_2Lines_FullDuplex;
  SPI_InitStructure.SPI_Mode = SPI_Mode_Master;
  SPI_InitStructure.SPI_DataSize = SPI_DataSize_8b;
  SPI_InitStructure.SPI_CPOL = SPI_CPOL_High;
  SPI_InitStructure.SPI_CPHA = SPI_CPHA_2Edge;
  SPI_InitStructure.SPI_NSS = SPI_NSS_Soft;
  SPI_InitStructure.SPI_BaudRatePrescaler = SPI_BaudRatePrescaler_2;
  SPI_InitStructure.SPI_FirstBit = SPI_FirstBit_MSB;
  SPI_Init(SPI3, &SPI_InitStructure);

  /* SPI3 enable */
  SPI_Cmd(SPI3, ENABLE);
}

/******************* (C) COPYRIGHT 2008 STMicroelectronics *****END OF FILE****/
