/**
  ******************************************************************************
  * @file    stm32l152_eval_lcd.c
  * @author  MCD Application Team
  * @version V4.4.0RC1
  * @date    07/02/2010
  * @brief   This file includes the LCD driver for AM-240320L8TNQW00H (LCD_ILI9320),
  *          AM-240320LDTNQW00H (LCD_SPFD5408B) Liquid Crystal Display Module
  *          of STM32L152-EVAL board.
  ******************************************************************************
  * @copy
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2010 STMicroelectronics</center></h2>
  */

/* Includes ------------------------------------------------------------------*/
#include "stm32l152_eval_lcd.h"
#include "../Common/fonts.c"

/** @addtogroup Utilities
  * @{
  */

/** @addtogroup STM32_EVAL
  * @{
  */

/** @addtogroup STM32L152_EVAL
  * @{
  */

/** @defgroup STM32L152_EVAL_LCD
  * @brief   This file includes the LCD driver for AM-240320L8TNQW00H (LCD_ILI9320),
  *          AM-240320LDTNQW00H (LCD_SPFD5408B) Liquid Crystal Display Module
  *          of STM32L152-EVAL board.
  * @{
  */

/** @defgroup STM32L152_EVAL_LCD_Private_Types
  * @{
  */
/**
  * @}
  */

/** @defgroup STM32L152_EVAL_LCD_Private_Defines
  * @{
  */
#define LCD_ILI9320        0x9320
#define LCD_SPFD5408       0x5408
#define START_BYTE         0x70
#define SET_INDEX          0x00
#define READ_STATUS        0x01
#define LCD_WRITE_REG      0x02
#define LCD_READ_REG       0x03
#define MAX_POLY_CORNERS   200
#define POLY_Y(Z)          ((int32_t)((Points + Z)->X))
#define POLY_X(Z)          ((int32_t)((Points + Z)->Y))
/**
  * @}
  */

/** @defgroup STM32L152_EVAL_LCD_Private_Macros
  * @{
  */
#define ABS(X)  ((X) > 0 ? (X) : -(X))
/**
  * @}
  */

/** @defgroup STM32L152_EVAL_LCD_Private_Variables
  * @{
  */
static sFONT *LCD_Currentfonts;
/* Global variables to set the written text color */
static __IO uint16_t TextColor = 0x0000, BackColor = 0xFFFF;
static __IO uint32_t LCDType = LCD_SPFD5408;
/**
  * @}
  */

/** @defgroup STM32L152_EVAL_LCD_Private_Function_Prototypes
  * @{
  */
#ifndef USE_Delay
static void delay(__IO uint32_t nCount);
#endif /* USE_Delay*/

static void PutPixel(int16_t x, int16_t y);
static void LCD_PolyLineRelativeClosed(pPoint Points, uint16_t PointCount, uint16_t Closed);

/**
  * @}
  */

/** @defgroup STM32L152_EVAL_LCD_Private_Functions
  * @{
  */

/**
  * @brief  DeInitializes the LCD.
  * @param  None
  * @retval None
  */
void STM32L152_LCD_DeInit(void)
{
  GPIO_InitTypeDef GPIO_InitStructure;

  /*!< LCD Display Off */
  LCD_DisplayOff();

  /*!< LCD_SPI disable */
  SPI_Cmd(LCD_SPI, DISABLE);

  /*!< LCD_SPI DeInit */
  SPI_DeInit(LCD_SPI);

  /*!< Disable SPI clock  */
  RCC_APB1PeriphClockCmd(LCD_SPI_CLK, DISABLE);

  /* Configure NCS in Output Push-Pull mode */
  GPIO_InitStructure.GPIO_Pin = LCD_NCS_PIN;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_IN;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;
  GPIO_Init(LCD_NCS_GPIO_PORT, &GPIO_InitStructure);

  /* Configure SPI pins: SCK, MISO and MOSI */
  GPIO_InitStructure.GPIO_Pin = LCD_SPI_SCK_PIN;
  GPIO_Init(LCD_SPI_SCK_GPIO_PORT, &GPIO_InitStructure);

  GPIO_InitStructure.GPIO_Pin = LCD_SPI_MISO_PIN;
  GPIO_Init(LCD_SPI_MISO_GPIO_PORT, &GPIO_InitStructure);

  GPIO_InitStructure.GPIO_Pin = LCD_SPI_MOSI_PIN;
  GPIO_Init(LCD_SPI_MOSI_GPIO_PORT, &GPIO_InitStructure);
}

/**
  * @brief  Setups the LCD.
  * @param  None
  * @retval None
  */
void LCD_Setup(void)
{
/* Configure the LCD Control pins --------------------------------------------*/
  LCD_CtrlLinesConfig();

/* Configure the LCD_SPI interface ----------------------------------------------*/
  LCD_SPIConfig();

  if(LCDType == LCD_SPFD5408)
  {
    /* Start Initial Sequence --------------------------------------------------*/
    LCD_WriteReg(LCD_REG_227, 0x3008); /* Set internal timing */
    LCD_WriteReg(LCD_REG_231, 0x0012); /* Set internal timing */
    LCD_WriteReg(LCD_REG_239, 0x1231); /* Set internal timing */
    LCD_WriteReg(LCD_REG_1, 0x0100);   /* Set SS and SM bit */
    LCD_WriteReg(LCD_REG_2, 0x0700);   /* Set 1 line inversion */
    LCD_WriteReg(LCD_REG_3, 0x1030);   /* Set GRAM write direction and BGR=1. */
    LCD_WriteReg(LCD_REG_4, 0x0000);   /* Resize register */
    LCD_WriteReg(LCD_REG_8, 0x0202);   /* Set the back porch and front porch */
    LCD_WriteReg(LCD_REG_9, 0x0000);   /* Set non-display area refresh cycle ISC[3:0] */
    LCD_WriteReg(LCD_REG_10, 0x0000);  /* FMARK function */
    LCD_WriteReg(LCD_REG_12, 0x0000);  /* RGB interface setting */
    LCD_WriteReg(LCD_REG_13, 0x0000);  /* Frame marker Position */
    LCD_WriteReg(LCD_REG_15, 0x0000);  /* RGB interface polarity */
    /* Power On sequence -------------------------------------------------------*/
    LCD_WriteReg(LCD_REG_16, 0x0000);  /* SAP, BT[3:0], AP, DSTB, SLP, STB */
    LCD_WriteReg(LCD_REG_17, 0x0000);  /* DC1[2:0], DC0[2:0], VC[2:0] */
    LCD_WriteReg(LCD_REG_18, 0x0000);  /* VREG1OUT voltage */
    LCD_WriteReg(LCD_REG_19, 0x0000);  /* VDV[4:0] for VCOM amplitude */
    _delay_(20);                /* Dis-charge capacitor power voltage (200ms) */
    LCD_WriteReg(LCD_REG_17, 0x0007);  /* DC1[2:0], DC0[2:0], VC[2:0] */
    _delay_(5);                 /* Delay 50 ms */
    LCD_WriteReg(LCD_REG_16, 0x12B0);  /* SAP, BT[3:0], AP, DSTB, SLP, STB */
    _delay_(5);                  /* Delay 50 ms */
    LCD_WriteReg(LCD_REG_18, 0x01BD);  /* External reference voltage= Vci */
    _delay_(5);                 /* Delay 50 ms */
    LCD_WriteReg(LCD_REG_19, 0x1400);       /* VDV[4:0] for VCOM amplitude */
    LCD_WriteReg(LCD_REG_41, 0x000E);  /* VCM[4:0] for VCOMH */
    _delay_(5);                 /* Delay 50 ms */
    LCD_WriteReg(LCD_REG_32, 0x0000);  /* GRAM horizontal Address */
    LCD_WriteReg(LCD_REG_33, 0x013F);  /* GRAM Vertical Address */
    /* Adjust the Gamma Curve --------------------------------------------------*/
    LCD_WriteReg(LCD_REG_48, 0x0007);
    LCD_WriteReg(LCD_REG_49, 0x0302);
    LCD_WriteReg(LCD_REG_50, 0x0105);
    LCD_WriteReg(LCD_REG_53, 0x0206);
    LCD_WriteReg(LCD_REG_54, 0x0808);
    LCD_WriteReg(LCD_REG_55, 0x0206);
    LCD_WriteReg(LCD_REG_56, 0x0504);
    LCD_WriteReg(LCD_REG_57, 0x0007);
    LCD_WriteReg(LCD_REG_60, 0x0105);
    LCD_WriteReg(LCD_REG_61, 0x0808);
    /* Set GRAM area -----------------------------------------------------------*/
    LCD_WriteReg(LCD_REG_80, 0x0000);  /* Horizontal GRAM Start Address */
    LCD_WriteReg(LCD_REG_81, 0x00EF);  /* Horizontal GRAM End Address */
    LCD_WriteReg(LCD_REG_82, 0x0000);  /* Vertical GRAM Start Address */
    LCD_WriteReg(LCD_REG_83, 0x013F);  /* Vertical GRAM End Address */
    LCD_WriteReg(LCD_REG_96,  0xA700); /* Gate Scan Line */
    LCD_WriteReg(LCD_REG_97,  0x0001); /* NDL,VLE, REV */
    LCD_WriteReg(LCD_REG_106, 0x0000); /* Set scrolling line */
    /* Partial Display Control -------------------------------------------------*/
    LCD_WriteReg(LCD_REG_128, 0x0000);
    LCD_WriteReg(LCD_REG_129, 0x0000);
    LCD_WriteReg(LCD_REG_130, 0x0000);
    LCD_WriteReg(LCD_REG_131, 0x0000);
    LCD_WriteReg(LCD_REG_132, 0x0000);
    LCD_WriteReg(LCD_REG_133, 0x0000);
    /* Panel Control -----------------------------------------------------------*/
    LCD_WriteReg(LCD_REG_144, 0x0010);
    LCD_WriteReg(LCD_REG_146, 0x0000);
    LCD_WriteReg(LCD_REG_147, 0x0003);
    LCD_WriteReg(LCD_REG_149, 0x0110);
    LCD_WriteReg(LCD_REG_151, 0x0000);
    LCD_WriteReg(LCD_REG_152, 0x0000);
    /* Set GRAM write direction and BGR = 1
       I/D=01 (Horizontal : increment, Vertical : decrement)
       AM=1 (address is updated in vertical writing direction) */
    LCD_WriteReg(LCD_REG_3, 0x1018);
    LCD_WriteReg(LCD_REG_7, 0x0112);   /* 262K color and display ON */
  }
  else if(LCDType == LCD_ILI9320)
  {
    _delay_(5); /* Delay 50 ms */
    /* Start Initial Sequence ------------------------------------------------*/
    LCD_WriteReg(LCD_REG_229, 0x8000); /* Set the internal vcore voltage */
    LCD_WriteReg(LCD_REG_0,  0x0001); /* Start internal OSC. */
    LCD_WriteReg(LCD_REG_1,  0x0100); /* set SS and SM bit */
    LCD_WriteReg(LCD_REG_2,  0x0700); /* set 1 line inversion */
    LCD_WriteReg(LCD_REG_3,  0x1030); /* set GRAM write direction and BGR=1. */
    LCD_WriteReg(LCD_REG_4,  0x0000); /* Resize register */
    LCD_WriteReg(LCD_REG_8,  0x0202); /* set the back porch and front porch */
    LCD_WriteReg(LCD_REG_9,  0x0000); /* set non-display area refresh cycle ISC[3:0] */
    LCD_WriteReg(LCD_REG_10, 0x0000); /* FMARK function */
    LCD_WriteReg(LCD_REG_12, 0x0000); /* RGB interface setting */
    LCD_WriteReg(LCD_REG_13, 0x0000); /* Frame marker Position */
    LCD_WriteReg(LCD_REG_15, 0x0000); /* RGB interface polarity */
    /* Power On sequence -----------------------------------------------------*/
    LCD_WriteReg(LCD_REG_16, 0x0000); /* SAP, BT[3:0], AP, DSTB, SLP, STB */
    LCD_WriteReg(LCD_REG_17, 0x0000); /* DC1[2:0], DC0[2:0], VC[2:0] */
    LCD_WriteReg(LCD_REG_18, 0x0000); /* VREG1OUT voltage */
    LCD_WriteReg(LCD_REG_19, 0x0000); /* VDV[4:0] for VCOM amplitude */
    _delay_(20);                      /* Dis-charge capacitor power voltage (200ms) */
    LCD_WriteReg(LCD_REG_16, 0x17B0); /* SAP, BT[3:0], AP, DSTB, SLP, STB */
    LCD_WriteReg(LCD_REG_17, 0x0137); /* DC1[2:0], DC0[2:0], VC[2:0] */
    _delay_(5);                       /* Delay 50 ms */
    LCD_WriteReg(LCD_REG_18, 0x0139); /* VREG1OUT voltage */
    _delay_(5);                       /* Delay 50 ms */
    LCD_WriteReg(LCD_REG_19, 0x1d00); /* VDV[4:0] for VCOM amplitude */
    LCD_WriteReg(LCD_REG_41, 0x0013); /* VCM[4:0] for VCOMH */
    _delay_(5);                       /* Delay 50 ms */
    LCD_WriteReg(LCD_REG_32, 0x0000); /* GRAM horizontal Address */
    LCD_WriteReg(LCD_REG_33, 0x0000); /* GRAM Vertical Address */
    /* Adjust the Gamma Curve ------------------------------------------------*/
    LCD_WriteReg(LCD_REG_48, 0x0006);
    LCD_WriteReg(LCD_REG_49, 0x0101);
    LCD_WriteReg(LCD_REG_50, 0x0003);
    LCD_WriteReg(LCD_REG_53, 0x0106);
    LCD_WriteReg(LCD_REG_54, 0x0b02);
    LCD_WriteReg(LCD_REG_55, 0x0302);
    LCD_WriteReg(LCD_REG_56, 0x0707);
    LCD_WriteReg(LCD_REG_57, 0x0007);
    LCD_WriteReg(LCD_REG_60, 0x0600);
    LCD_WriteReg(LCD_REG_61, 0x020b);

    /* Set GRAM area ---------------------------------------------------------*/
    LCD_WriteReg(LCD_REG_80, 0x0000); /* Horizontal GRAM Start Address */
    LCD_WriteReg(LCD_REG_81, 0x00EF); /* Horizontal GRAM End Address */
    LCD_WriteReg(LCD_REG_82, 0x0000); /* Vertical GRAM Start Address */
    LCD_WriteReg(LCD_REG_83, 0x013F); /* Vertical GRAM End Address */
    LCD_WriteReg(LCD_REG_96,  0x2700); /* Gate Scan Line */
    LCD_WriteReg(LCD_REG_97,  0x0001); /* NDL,VLE, REV */
    LCD_WriteReg(LCD_REG_106, 0x0000); /* set scrolling line */
    /* Partial Display Control -----------------------------------------------*/
    LCD_WriteReg(LCD_REG_128, 0x0000);
    LCD_WriteReg(LCD_REG_129, 0x0000);
    LCD_WriteReg(LCD_REG_130, 0x0000);
    LCD_WriteReg(LCD_REG_131, 0x0000);
    LCD_WriteReg(LCD_REG_132, 0x0000);
    LCD_WriteReg(LCD_REG_133, 0x0000);
    /* Panel Control ---------------------------------------------------------*/
    LCD_WriteReg(LCD_REG_144, 0x0010);
    LCD_WriteReg(LCD_REG_146, 0x0000);
    LCD_WriteReg(LCD_REG_147, 0x0003);
    LCD_WriteReg(LCD_REG_149, 0x0110);
    LCD_WriteReg(LCD_REG_151, 0x0000);
    LCD_WriteReg(LCD_REG_152, 0x0000);
    /* Set GRAM write direction and BGR = 1 */
    /* I/D=01 (Horizontal : increment, Vertical : decrement) */
    /* AM=1 (address is updated in vertical writing direction) */
    LCD_WriteReg(LCD_REG_3, 0x1018);
    LCD_WriteReg(LCD_REG_7, 0x0173); /* 262K color and display ON */
  }
}


/**
  * @brief  Initializes the LCD.
  * @param  None
  * @retval None
  */
void STM32L152_LCD_Init(void)
{
  /* Setups the LCD */
  LCD_Setup();

  /* Try to read new LCD controller ID 0x5408 */
  if (LCD_ReadReg(LCD_REG_0) == LCD_SPFD5408)
  {
    LCDType = LCD_SPFD5408;
  }
  else
  {
    LCDType = LCD_ILI9320;
    /* Setups the LCD */
    LCD_Setup();
  }

  LCD_SetFont(&LCD_DEFAULT_FONT);
}

/**
  * @brief  Sets the LCD Text and Background colors.
  * @param  _TextColor: specifies the Text Color.
  * @param  _BackColor: specifies the Background Color.
  * @retval None
  */
void LCD_SetColors(__IO uint16_t _TextColor, __IO uint16_t _BackColor)
{
  TextColor = _TextColor;
  BackColor = _BackColor;
}

/**
  * @brief  Gets the LCD Text and Background colors.
  * @param  _TextColor: pointer to the variable that will contain the Text
            Color.
  * @param  _BackColor: pointer to the variable that will contain the Background
            Color.
  * @retval None
  */
void LCD_GetColors(__IO uint16_t *_TextColor, __IO uint16_t *_BackColor)
{
  *_TextColor = TextColor; *_BackColor = BackColor;
}

/**
  * @brief  Sets the Text color.
  * @param  Color: specifies the Text color code RGB(5-6-5).
  * @retval None
  */
void LCD_SetTextColor(__IO uint16_t Color)
{
  TextColor = Color;
}


/**
  * @brief  Sets the Background color.
  * @param  Color: specifies the Background color code RGB(5-6-5).
  * @retval None
  */
void LCD_SetBackColor(__IO uint16_t Color)
{
  BackColor = Color;
}

/**
  * @brief  Sets the Text Font.
  * @param  fonts: specifies the font to be used.
  * @retval None
  */
void LCD_SetFont(sFONT *fonts)
{
  LCD_Currentfonts = fonts;
}

/**
  * @brief  Gets the Text Font.
  * @param  None.
  * @retval the used font.
  */
sFONT *LCD_GetFont(void)
{
  return LCD_Currentfonts;
}

/**
  * @brief  Clears the selected line.
  * @param  Line: the Line to be cleared.
  *   This parameter can be one of the following values:
  *     @arg Linex: where x can be 0..n
  * @retval None
  */
void LCD_ClearLine(uint8_t Line)
{
  uint16_t refcolumn = LCD_PIXEL_WIDTH - 1;

  /* Send the string character by character on lCD */
  while (((refcolumn + 1) & 0xFFFF) >= LCD_Currentfonts->Width)
  {
    /* Display one character on LCD */
    LCD_DisplayChar(Line, refcolumn, ' ');
    /* Decrement the column position by 16 */
    refcolumn -= LCD_Currentfonts->Width;
  }
}


/**
  * @brief  Clears the hole LCD.
  * @param  Color: the color of the background.
  * @retval None
  */
void LCD_Clear(uint16_t Color)
{
  uint32_t index = 0;

  LCD_SetCursor(0x00, 0x013F);

  LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */

  for(index = 0; index < 76800; index++)
  {
    LCD_WriteRAM(Color);
  }

  LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);

}


/**
  * @brief  Sets the cursor position.
  * @param  Xpos: specifies the X position.
  * @param  Ypos: specifies the Y position.
  * @retval None
  */
void LCD_SetCursor(uint8_t Xpos, uint16_t Ypos)
{
  LCD_WriteReg(LCD_REG_32, Xpos);
  LCD_WriteReg(LCD_REG_33, Ypos);
}


/**
  * @brief  Draws a character on LCD.
  * @param  Xpos: the Line where to display the character shape.
  * @param  Ypos: start column address.
  * @param  c: pointer to the character data.
  * @retval None
  */
void LCD_DrawChar(uint8_t Xpos, uint16_t Ypos, const uint16_t *c)
{
  uint32_t index = 0, i = 0;
  uint8_t Xaddress = 0;

  Xaddress = Xpos;

  LCD_SetCursor(Xaddress, Ypos);

  for(index = 0; index < LCD_Currentfonts->Height; index++)
  {
    LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */

    for(i = 0; i < LCD_Currentfonts->Width; i++)
    {
      if((((c[index] & ((0x80 << ((LCD_Currentfonts->Width / 12 ) * 8 ) ) >> i)) == 0x00) &&(LCD_Currentfonts->Width <= 12))||
        (((c[index] & (0x1 << i)) == 0x00)&&(LCD_Currentfonts->Width > 12 )))

      {
        LCD_WriteRAM(BackColor);
      }
      else
      {
        LCD_WriteRAM(TextColor);
      }
    }

    LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);
    Xaddress++;
    LCD_SetCursor(Xaddress, Ypos);
  }
}


/**
  * @brief  Displays one character (16dots width, 24dots height).
  * @param  Line: the Line where to display the character shape .
  *   This parameter can be one of the following values:
  *     @arg Linex: where x can be 0..9
  * @param  Column: start column address.
  * @param  Ascii: character ascii code, must be between 0x20 and 0x7E.
  * @retval None
  */
void LCD_DisplayChar(uint8_t Line, uint16_t Column, uint8_t Ascii)
{
  Ascii -= 32;
  LCD_DrawChar(Line, Column, &LCD_Currentfonts->table[Ascii * LCD_Currentfonts->Height]);
}


/**
  * @brief  Displays a maximum of 20 char on the LCD.
  * @param  Line: the Line where to display the character shape .
  *   This parameter can be one of the following values:
  *     @arg Linex: where x can be 0..9
  * @param  *ptr: pointer to string to display on LCD.
  * @retval None
  */
void LCD_DisplayStringLine(uint8_t Line, uint8_t *ptr)
{
  uint16_t refcolumn = LCD_PIXEL_WIDTH - 1;

  /* Send the string character by character on lCD */
  while ((*ptr != 0) & (((refcolumn + 1) & 0xFFFF) >= LCD_Currentfonts->Width))
  {
    /* Display one character on LCD */
    LCD_DisplayChar(Line, refcolumn, *ptr);
    /* Decrement the column position by 16 */
    refcolumn -= LCD_Currentfonts->Width;
    /* Point on the next character */
    ptr++;
  }
}


/**
  * @brief  Sets a display window
  * @param  Xpos: specifies the X buttom left position.
  * @param  Ypos: specifies the Y buttom left position.
  * @param  Height: display window height.
  * @param  Width: display window width.
  * @retval None
  */
void LCD_SetDisplayWindow(uint8_t Xpos, uint16_t Ypos, uint8_t Height, uint16_t Width)
{
  /* Horizontal GRAM Start Address */
  if(Xpos >= Height)
  {
    LCD_WriteReg(LCD_REG_80, (Xpos - Height + 1));
  }
  else
  {
    LCD_WriteReg(LCD_REG_80, 0);
  }
  /* Horizontal GRAM End Address */
  LCD_WriteReg(LCD_REG_81, Xpos);
  /* Vertical GRAM Start Address */
  if(Ypos >= Width)
  {
    LCD_WriteReg(LCD_REG_82, (Ypos - Width + 1));
  }
  else
  {
    LCD_WriteReg(LCD_REG_82, 0);
  }
  /* Vertical GRAM End Address */
  LCD_WriteReg(LCD_REG_83, Ypos);

  LCD_SetCursor(Xpos, Ypos);
}


/**
  * @brief  Disables LCD Window mode.
  * @param  None
  * @retval None
  */
void LCD_WindowModeDisable(void)
{
  LCD_SetDisplayWindow(239, 0x13F, 240, 320);
  LCD_WriteReg(LCD_REG_3, 0x1018);
}

/**
  * @brief  Displays a line.
  * @param  Xpos: specifies the X position.
  * @param  Ypos: specifies the Y position.
  * @param  Length: line length.
  * @param  Direction: line direction.
  *   This parameter can be one of the following values: Vertical or Horizontal.
  * @retval None
  */
void LCD_DrawLine(uint8_t Xpos, uint16_t Ypos, uint16_t Length, uint8_t Direction)
{
  uint32_t i = 0;

  LCD_SetCursor(Xpos, Ypos);

  if(Direction == LCD_DIR_HORIZONTAL)
  {
    LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */

    for(i = 0; i < Length; i++)
    {
      LCD_WriteRAM(TextColor);
    }
    LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);
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


/**
  * @brief  Displays a rectangle.
  * @param  Xpos: specifies the X position.
  * @param  Ypos: specifies the Y position.
  * @param  Height: display rectangle height.
  * @param  Width: display rectangle width.
  * @retval None
  */
void LCD_DrawRect(uint8_t Xpos, uint16_t Ypos, uint8_t Height, uint16_t Width)
{
  LCD_DrawLine(Xpos, Ypos, Width, LCD_DIR_HORIZONTAL);
  LCD_DrawLine((Xpos + Height), Ypos, Width, LCD_DIR_HORIZONTAL);

  LCD_DrawLine(Xpos, Ypos, Height, LCD_DIR_VERTICAL);
  LCD_DrawLine(Xpos, (Ypos - Width + 1), Height, LCD_DIR_VERTICAL);
}


/**
  * @brief  Displays a circle.
  * @param  Xpos: specifies the X position.
  * @param  Ypos: specifies the Y position.
  * @param  Radius
  * @retval None
  */
void LCD_DrawCircle(uint8_t Xpos, uint16_t Ypos, uint16_t Radius)
{
  int32_t  D;/* Decision Variable */
  uint32_t  CurX;/* Current X Value */
  uint32_t  CurY;/* Current Y Value */

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


/**
  * @brief  Displays a monocolor picture.
  * @param  Pict: pointer to the picture array.
  * @retval None
  */
void LCD_DrawMonoPict(const uint32_t *Pict)
{
  uint32_t index = 0, i = 0;
  LCD_SetCursor(0, (LCD_PIXEL_WIDTH - 1));

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

  LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);
}

#ifdef USE_LCD_DrawBMP
/**
  * @brief  Displays a bitmap picture loaded in the SPI Flash.
  * @param  BmpAddress: Bmp picture address in the SPI Flash.
  * @retval None
  */
void LCD_DrawBMP(uint32_t BmpAddress)
{
  uint32_t i = 0, size = 0;
  /* Read bitmap size */
  SPI_FLASH_BufferRead((uint8_t*)&size, BmpAddress + 2, 4);
  /* get bitmap data address offset */
  SPI_FLASH_BufferRead((uint8_t*)&i, BmpAddress + 10, 4);

  size = (size - i)/2;
  SPI_FLASH_StartReadSequence(BmpAddress + i);
  /* Disable SPI1  */
  SPI_Cmd(SPI1, DISABLE);
  /* SPI in 16-bit mode */
  SPI_DataSizeConfig(SPI1, SPI_DataSize_16b);
  /* Enable SPI1  */
  SPI_Cmd(SPI1, ENABLE);

  if((LCDType == LCD_ILI9320) || (LCDType == LCD_SPFD5408))
  {
    /* Set GRAM write direction and BGR = 1 */
    /* I/D=00 (Horizontal : decrement, Vertical : decrement) */
    /* AM=1 (address is updated in vertical writing direction) */
    LCD_WriteReg(LCD_REG_3, 0x1008);
    LCD_WriteRAM_Prepare(); /* Prepare to write GRAM */
  }

  /* Read bitmap data from SPI Flash and send them to LCD */
  for(i = 0; i < size; i++)
  {
    LCD_WriteRAM(__REV16(SPI_FLASH_SendHalfWord(0xA5A5)));
  }
  if((LCDType == LCD_ILI9320) || (LCDType == LCD_SPFD5408))
  {
    LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);
  }

  /* Deselect the FLASH: Chip Select high */
  SPI_FLASH_CS_HIGH();
  /* Disable SPI1  */
  SPI_Cmd(SPI1, DISABLE);
  /* SPI in 8-bit mode */
  SPI_DataSizeConfig(SPI1, SPI_DataSize_8b);
  /* Enable SPI1  */
  SPI_Cmd(SPI1, ENABLE);

  if((LCDType == LCD_ILI9320) || (LCDType == LCD_SPFD5408))
  {
    /* Set GRAM write direction and BGR = 1 */
    /* I/D = 01 (Horizontal : increment, Vertical : decrement) */
    /* AM = 1 (address is updated in vertical writing direction) */
    LCD_WriteReg(LCD_REG_3, 0x1018);
  }
}
#endif /* USE_LCD_DrawBMP */

/**
  * @brief  Displays a full rectangle.
  * @param  Xpos: specifies the X position.
  * @param  Ypos: specifies the Y position.
  * @param  Height: rectangle height.
  * @param  Width: rectangle width.
  * @retval None
  */
void LCD_DrawFullRect(uint16_t Xpos, uint16_t Ypos, uint16_t Width, uint16_t Height)
{
  LCD_SetTextColor(TextColor);

  LCD_DrawLine(Xpos, Ypos, Width, LCD_DIR_HORIZONTAL);
  LCD_DrawLine((Xpos + Height), Ypos, Width, LCD_DIR_HORIZONTAL);

  LCD_DrawLine(Xpos, Ypos, Height, LCD_DIR_VERTICAL);
  LCD_DrawLine(Xpos, (Ypos - Width + 1), Height, LCD_DIR_VERTICAL);

  Width -= 2;
  Height--;
  Ypos--;

  LCD_SetTextColor(BackColor);

  while(Height--)
  {
    LCD_DrawLine(++Xpos, Ypos, Width, LCD_DIR_HORIZONTAL);
  }

  LCD_SetTextColor(TextColor);
}

/**
  * @brief  Displays a full circle.
  * @param  Xpos: specifies the X position.
  * @param  Ypos: specifies the Y position.
  * @param  Radius
  * @retval None
  */
void LCD_DrawFullCircle(uint16_t Xpos, uint16_t Ypos, uint16_t Radius)
{
  int32_t  D;    /* Decision Variable */
  uint32_t  CurX;/* Current X Value */
  uint32_t  CurY;/* Current Y Value */

  D = 3 - (Radius << 1);

  CurX = 0;
  CurY = Radius;

  LCD_SetTextColor(BackColor);

  while (CurX <= CurY)
  {
    if(CurY > 0)
    {
      LCD_DrawLine(Xpos - CurX, Ypos + CurY, 2*CurY, LCD_DIR_HORIZONTAL);
      LCD_DrawLine(Xpos + CurX, Ypos + CurY, 2*CurY, LCD_DIR_HORIZONTAL);
    }

    if(CurX > 0)
    {
      LCD_DrawLine(Xpos - CurY, Ypos + CurX, 2*CurX, LCD_DIR_HORIZONTAL);
      LCD_DrawLine(Xpos + CurY, Ypos + CurX, 2*CurX, LCD_DIR_HORIZONTAL);
    }
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

  LCD_SetTextColor(TextColor);
  LCD_DrawCircle(Xpos, Ypos, Radius);
}

/**
  * @brief  Displays an uni line (between two points).
  * @param  x1: specifies the point 1 x position.
  * @param  y1: specifies the point 1 y position.
  * @param  x2: specifies the point 2 x position.
  * @param  y2: specifies the point 2 y position.
  * @retval None
  */
void LCD_DrawUniLine(uint16_t x1, uint16_t y1, uint16_t x2, uint16_t y2)
{
  int16_t deltax = 0, deltay = 0, x = 0, y = 0, xinc1 = 0, xinc2 = 0,
  yinc1 = 0, yinc2 = 0, den = 0, num = 0, numadd = 0, numpixels = 0,
  curpixel = 0;

  deltax = ABS(x2 - x1);        /* The difference between the x's */
  deltay = ABS(y2 - y1);        /* The difference between the y's */
  x = x1;                       /* Start x off at the first pixel */
  y = y1;                       /* Start y off at the first pixel */

  if (x2 >= x1)                 /* The x-values are increasing */
  {
    xinc1 = 1;
    xinc2 = 1;
  }
  else                          /* The x-values are decreasing */
  {
    xinc1 = -1;
    xinc2 = -1;
  }

  if (y2 >= y1)                 /* The y-values are increasing */
  {
    yinc1 = 1;
    yinc2 = 1;
  }
  else                          /* The y-values are decreasing */
  {
    yinc1 = -1;
    yinc2 = -1;
  }

  if (deltax >= deltay)         /* There is at least one x-value for every y-value */
  {
    xinc1 = 0;                  /* Don't change the x when numerator >= denominator */
    yinc2 = 0;                  /* Don't change the y for every iteration */
    den = deltax;
    num = deltax / 2;
    numadd = deltay;
    numpixels = deltax;         /* There are more x-values than y-values */
  }
  else                          /* There is at least one y-value for every x-value */
  {
    xinc2 = 0;                  /* Don't change the x for every iteration */
    yinc1 = 0;                  /* Don't change the y when numerator >= denominator */
    den = deltay;
    num = deltay / 2;
    numadd = deltax;
    numpixels = deltay;         /* There are more y-values than x-values */
  }

  for (curpixel = 0; curpixel <= numpixels; curpixel++)
  {
    PutPixel(x, y);             /* Draw the current pixel */
    num += numadd;              /* Increase the numerator by the top of the fraction */
    if (num >= den)             /* Check if numerator >= denominator */
    {
      num -= den;               /* Calculate the new numerator value */
      x += xinc1;               /* Change the x as appropriate */
      y += yinc1;               /* Change the y as appropriate */
    }
    x += xinc2;                 /* Change the x as appropriate */
    y += yinc2;                 /* Change the y as appropriate */
  }
}

/**
  * @brief  Displays an polyline (between many points).
  * @param  Points: pointer to the points array.
  * @param  PointCount: Number of points.
  * @retval None
  */
void LCD_PolyLine(pPoint Points, uint16_t PointCount)
{
  int16_t X = 0, Y = 0;

  if(PointCount < 2)
  {
    return;
  }

  while(--PointCount)
  {
    X = Points->X;
    Y = Points->Y;
    Points++;
    LCD_DrawUniLine(X, Y, Points->X, Points->Y);
  }
}

/**
  * @brief  Displays an relative polyline (between many points).
  * @param  Points: pointer to the points array.
  * @param  PointCount: Number of points.
  * @param  Closed: specifies if the draw is closed or not.
  *           1: closed, 0 : not closed.
  * @retval None
  */
static void LCD_PolyLineRelativeClosed(pPoint Points, uint16_t PointCount, uint16_t Closed)
{
  int16_t X = 0, Y = 0;
  pPoint First = Points;

  if(PointCount < 2)
  {
    return;
  }
  X = Points->X;
  Y = Points->Y;
  while(--PointCount)
  {
    Points++;
    LCD_DrawUniLine(X, Y, X + Points->X, Y + Points->Y);
    X = X + Points->X;
    Y = Y + Points->Y;
  }
  if(Closed)
  {
    LCD_DrawUniLine(First->X, First->Y, X, Y);
  }
}

/**
  * @brief  Displays a closed polyline (between many points).
  * @param  Points: pointer to the points array.
  * @param  PointCount: Number of points.
  * @retval None
  */
void LCD_ClosedPolyLine(pPoint Points, uint16_t PointCount)
{
  LCD_PolyLine(Points, PointCount);
  LCD_DrawUniLine(Points->X, Points->Y, (Points+PointCount-1)->X, (Points+PointCount-1)->Y);
}

/**
  * @brief  Displays a relative polyline (between many points).
  * @param  Points: pointer to the points array.
  * @param  PointCount: Number of points.
  * @retval None
  */
void LCD_PolyLineRelative(pPoint Points, uint16_t PointCount)
{
  LCD_PolyLineRelativeClosed(Points, PointCount, 0);
}

/**
  * @brief  Displays a closed relative polyline (between many points).
  * @param  Points: pointer to the points array.
  * @param  PointCount: Number of points.
  * @retval None
  */
void LCD_ClosedPolyLineRelative(pPoint Points, uint16_t PointCount)
{
  LCD_PolyLineRelativeClosed(Points, PointCount, 1);
}


/**
  * @brief  Displays a  full polyline (between many points).
  * @param  Points: pointer to the points array.
  * @param  PointCount: Number of points.
  * @retval None
  */
void LCD_FillPolyLine(pPoint Points, uint16_t PointCount)
{
  /*  public-domain code by Darel Rex Finley, 2007 */
  uint16_t  nodes = 0, nodeX[MAX_POLY_CORNERS], pixelX = 0, pixelY = 0, i = 0,
  j = 0, swap = 0;
  uint16_t  IMAGE_LEFT = 0, IMAGE_RIGHT = 0, IMAGE_TOP = 0, IMAGE_BOTTOM = 0;

  IMAGE_LEFT = IMAGE_RIGHT = Points->X;
  IMAGE_TOP= IMAGE_BOTTOM = Points->Y;

  for(i = 1; i < PointCount; i++)
  {
    pixelX = POLY_X(i);
    if(pixelX < IMAGE_LEFT)
    {
      IMAGE_LEFT = pixelX;
    }
    if(pixelX > IMAGE_RIGHT)
    {
      IMAGE_RIGHT = pixelX;
    }

    pixelY = POLY_Y(i);
    if(pixelY < IMAGE_TOP)
    {
      IMAGE_TOP = pixelY;
    }
    if(pixelY > IMAGE_BOTTOM)
    {
      IMAGE_BOTTOM = pixelY;
    }
  }

  LCD_SetTextColor(BackColor);

  /*  Loop through the rows of the image. */
  for (pixelY = IMAGE_TOP; pixelY < IMAGE_BOTTOM; pixelY++)
  {
    /* Build a list of nodes. */
    nodes = 0; j = PointCount-1;

    for (i = 0; i < PointCount; i++)
    {
      if (POLY_Y(i)<(double) pixelY && POLY_Y(j)>=(double) pixelY || POLY_Y(j)<(double) pixelY && POLY_Y(i)>=(double) pixelY)
      {
        nodeX[nodes++]=(int) (POLY_X(i)+((pixelY-POLY_Y(i))*(POLY_X(j)-POLY_X(i)))/(POLY_Y(j)-POLY_Y(i)));
      }
      j = i;
    }

    /* Sort the nodes, via a simple “Bubble” sort. */
    i = 0;
    while (i < nodes-1)
    {
      if (nodeX[i]>nodeX[i+1])
      {
        swap = nodeX[i];
        nodeX[i] = nodeX[i+1];
        nodeX[i+1] = swap;
        if(i)
        {
          i--;
        }
      }
      else
      {
        i++;
      }
    }

    /*  Fill the pixels between node pairs. */
    for (i = 0; i < nodes; i+=2)
    {
      if(nodeX[i] >= IMAGE_RIGHT)
      {
        break;
      }
      if(nodeX[i+1] > IMAGE_LEFT)
      {
        if (nodeX[i] < IMAGE_LEFT)
        {
          nodeX[i]=IMAGE_LEFT;
        }
        if(nodeX[i+1] > IMAGE_RIGHT)
        {
          nodeX[i+1] = IMAGE_RIGHT;
        }
        LCD_SetTextColor(BackColor);
        LCD_DrawLine(pixelY, nodeX[i+1], nodeX[i+1] - nodeX[i], LCD_DIR_HORIZONTAL);
        LCD_SetTextColor(TextColor);
        PutPixel(pixelY, nodeX[i+1]);
        PutPixel(pixelY, nodeX[i]);
        /* for (j=nodeX[i]; j<nodeX[i+1]; j++) PutPixel(j,pixelY); */
      }
    }
  }

  /* draw the edges */
  LCD_SetTextColor(TextColor);
}

/**
  * @brief  Reset LCD control line(/CS) and Send Start-Byte
  * @param  Start_Byte: the Start-Byte to be sent
  * @retval None
  */
void LCD_nCS_StartByte(uint8_t Start_Byte)
{
  LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_RESET);

  SPI_SendData(LCD_SPI, Start_Byte);

  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }
}


/**
  * @brief  Writes index to select the LCD register.
  * @param  LCD_Reg: address of the selected register.
  * @retval None
  */
void LCD_WriteRegIndex(uint8_t LCD_Reg)
{
  /* Reset LCD control line(/CS) and Send Start-Byte */
  LCD_nCS_StartByte(START_BYTE | SET_INDEX);

  /* Write 16-bit Reg Index (High Byte is 0) */
  SPI_SendData(LCD_SPI, 0x00);

  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }

  SPI_SendData(LCD_SPI, LCD_Reg);

  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }

  LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);
}


/**
  * @brief  Writes to the selected LCD ILI9320 register.
  * @param  LCD_Reg: address of the selected register.
  * @param  LCD_RegValue: value to write to the selected register.
  * @retval None
  */
void LCD_WriteReg(uint8_t LCD_Reg, uint16_t LCD_RegValue)
{
  /* Write 16-bit Index (then Write Reg) */
  LCD_WriteRegIndex(LCD_Reg);

  /* Write 16-bit Reg */
  /* Reset LCD control line(/CS) and Send Start-Byte */
  LCD_nCS_StartByte(START_BYTE | LCD_WRITE_REG);

  SPI_SendData(LCD_SPI, LCD_RegValue >> 8);

  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }

  SPI_SendData(LCD_SPI, (LCD_RegValue & 0xFF));

  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }

  LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);
}


/**
  * @brief  Reads the selected LCD Register.
  * @param  LCD_Reg: address of the selected register.
  * @retval LCD Register Value.
  */
uint16_t LCD_ReadReg(uint8_t LCD_Reg)
{
  uint16_t tmp = 0;
  uint8_t i = 0;

  /* LCD_SPI prescaler: 4 */
  LCD_SPI->CR1 &= 0xFFC7;
  LCD_SPI->CR1 |= 0x0008;
  /* Write 16-bit Index (then Read Reg) */
  LCD_WriteRegIndex(LCD_Reg);
  /* Read 16-bit Reg */
  /* Reset LCD control line(/CS) and Send Start-Byte */
  LCD_nCS_StartByte(START_BYTE | LCD_READ_REG);

  for(i = 0; i < 5; i++)
  {
    SPI_SendData(LCD_SPI, 0xFF);
    while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
    {
    }
    /* One byte of invalid dummy data read after the start byte */
    while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_RXNE) == RESET)
    {
    }
    SPI_ReceiveData(LCD_SPI);
  }

  SPI_SendData(LCD_SPI, 0xFF);

  /* Read upper byte */
  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }

  /* Read lower byte */
  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_RXNE) == RESET)
  {
  }
  tmp = SPI_ReceiveData(LCD_SPI);


  SPI_SendData(LCD_SPI, 0xFF);
  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }

  /* Read lower byte */
  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_RXNE) == RESET)
  {
  }

  tmp = ((tmp & 0xFF) << 8) | SPI_ReceiveData(LCD_SPI);
  LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);

  /* LCD_SPI prescaler: 2 */
  LCD_SPI->CR1 &= 0xFFC7;

  return tmp;
}


/**
  * @brief  Prepare to write to the LCD RAM.
  * @param  None
  * @retval None
  */
void LCD_WriteRAM_Prepare(void)
{
  LCD_WriteRegIndex(LCD_REG_34); /* Select GRAM Reg */

  /* Reset LCD control line(/CS) and Send Start-Byte */
  LCD_nCS_StartByte(START_BYTE | LCD_WRITE_REG);
}


/**
  * @brief  Writes 1 word to the LCD RAM.
  * @param  RGB_Code: the pixel color in RGB mode (5-6-5).
  * @retval None
  */
void LCD_WriteRAMWord(uint16_t RGB_Code)
{
  LCD_WriteRAM_Prepare();

  LCD_WriteRAM(RGB_Code);

  LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);
}

/**
  * @brief  Writes to the LCD RAM.
  * @param  RGB_Code: the pixel color in RGB mode (5-6-5).
  * @retval None
  */
void LCD_WriteRAM(uint16_t RGB_Code)
{
  SPI_SendData(LCD_SPI, RGB_Code >> 8);
  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }
  SPI_SendData(LCD_SPI, RGB_Code & 0xFF);
  while(SPI_GetFlagStatus(LCD_SPI, SPI_FLAG_BSY) != RESET)
  {
  }
}


/**
  * @brief  Power on the LCD.
  * @param  None
  * @retval None
  */
void LCD_PowerOn(void)
{
  /* Power On sequence ---------------------------------------------------------*/
  LCD_WriteReg(LCD_REG_16, 0x0000); /* SAP, BT[3:0], AP, DSTB, SLP, STB */
  LCD_WriteReg(LCD_REG_17, 0x0000); /* DC1[2:0], DC0[2:0], VC[2:0] */
  LCD_WriteReg(LCD_REG_18, 0x0000); /* VREG1OUT voltage */
  LCD_WriteReg(LCD_REG_19, 0x0000); /* VDV[4:0] for VCOM amplitude */
  _delay_(20);                 /* Dis-charge capacitor power voltage (200ms) */
  LCD_WriteReg(LCD_REG_16, 0x17B0); /* SAP, BT[3:0], AP, DSTB, SLP, STB */
  LCD_WriteReg(LCD_REG_17, 0x0137); /* DC1[2:0], DC0[2:0], VC[2:0] */
  _delay_(5);                /* Delay 50 ms */
  LCD_WriteReg(LCD_REG_18, 0x0139); /* VREG1OUT voltage */
  _delay_(5);                /* delay 50 ms */
  LCD_WriteReg(LCD_REG_19, 0x1d00); /* VDV[4:0] for VCOM amplitude */
  LCD_WriteReg(LCD_REG_41, 0x0013); /* VCM[4:0] for VCOMH */
  _delay_(5);                /* delay 50 ms */
  LCD_WriteReg(LCD_REG_7, 0x0173);  /* 262K color and display ON */
}


/**
  * @brief  Enables the Display.
  * @param  None
  * @retval None
  */
void LCD_DisplayOn(void)
{
  /* Display On */
  LCD_WriteReg(LCD_REG_7, 0x0173); /* 262K color and display ON */
}


/**
  * @brief  Disables the Display.
  * @param  None
  * @retval None
  */
void LCD_DisplayOff(void)
{
  /* Display Off */
  LCD_WriteReg(LCD_REG_7, 0x0);
}


/**
  * @brief  Configures LCD control lines in Output Push-Pull mode.
  * @param  None
  * @retval None
  */
void LCD_CtrlLinesConfig(void)
{
  GPIO_InitTypeDef GPIO_InitStructure;

  RCC_AHBPeriphClockCmd(LCD_NCS_GPIO_CLK, ENABLE);

  /* Configure NCS (PF.02) in Output Push-Pull mode */
  GPIO_InitStructure.GPIO_Pin = LCD_NCS_PIN;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_2MHz;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_OUT;
  GPIO_InitStructure.GPIO_OType = GPIO_OType_PP;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;
  GPIO_Init(LCD_NCS_GPIO_PORT, &GPIO_InitStructure);

  LCD_CtrlLinesWrite(LCD_NCS_GPIO_PORT, LCD_NCS_PIN, Bit_SET);
}


/**
  * @brief  Sets or reset LCD control lines.
  * @param  GPIOx: where x can be B or D to select the GPIO peripheral.
  * @param  CtrlPins: the Control line.
  *   This parameter can be:
  *     @arg LCD_NCS_PIN: Chip Select pin
  *     @arg LCD_NWR_PIN: Read/Write Selection pin
  *     @arg LCD_RS_PIN: Register/RAM Selection pin
  * @param  BitVal: specifies the value to be written to the selected bit.
  *   This parameter can be:
  *     @arg Bit_RESET: to clear the port pin
  *     @arg Bit_SET: to set the port pin
  * @retval None
  */
void LCD_CtrlLinesWrite(GPIO_TypeDef* GPIOx, uint16_t CtrlPins, BitAction BitVal)
{
  /* Set or Reset the control line */
  GPIO_WriteBit(GPIOx, CtrlPins, BitVal);
}


/**
  * @brief  Configures the LCD_SPI interface.
  * @param  None
  * @retval None
  */
void LCD_SPIConfig(void)
{
  SPI_InitTypeDef    SPI_InitStructure;
  GPIO_InitTypeDef   GPIO_InitStructure;

  /* Enable LCD_SPI_SCK_GPIO_CLK, LCD_SPI_MISO_GPIO_CLK and LCD_SPI_MOSI_GPIO_CLK clock */
  RCC_AHBPeriphClockCmd(LCD_SPI_SCK_GPIO_CLK | LCD_SPI_MISO_GPIO_CLK | LCD_SPI_MOSI_GPIO_CLK, ENABLE);

  /* Enable LCD_SPI and SYSCFG clock  */
  RCC_APB2PeriphClockCmd(LCD_SPI_CLK | RCC_APB2Periph_SYSCFG, ENABLE);

  /* Configure LCD_SPI SCK pin */
  GPIO_InitStructure.GPIO_Pin = LCD_SPI_SCK_PIN;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_40MHz;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
  GPIO_InitStructure.GPIO_OType = GPIO_OType_PP;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;
  GPIO_Init(LCD_SPI_SCK_GPIO_PORT, &GPIO_InitStructure);

  /* Configure LCD_SPI MISO pin */
  GPIO_InitStructure.GPIO_Pin = LCD_SPI_MISO_PIN;
  GPIO_Init(LCD_SPI_MISO_GPIO_PORT, &GPIO_InitStructure);

  /* Configure LCD_SPI MOSI pin */
  GPIO_InitStructure.GPIO_Pin = LCD_SPI_MOSI_PIN;
  GPIO_Init(LCD_SPI_MOSI_GPIO_PORT, &GPIO_InitStructure);

  /* Connect PE.13 to SPI SCK */
  GPIO_PinAFConfig(LCD_SPI_SCK_GPIO_PORT, LCD_SPI_SCK_SOURCE, LCD_SPI_SCK_AF);

  /* Connect PE.14 to SPI MISO */
  GPIO_PinAFConfig(LCD_SPI_MISO_GPIO_PORT, LCD_SPI_MISO_SOURCE, LCD_SPI_MISO_AF);

  /* Connect PE.15 to SPI MOSI */
  GPIO_PinAFConfig(LCD_SPI_MOSI_GPIO_PORT, LCD_SPI_MOSI_SOURCE, LCD_SPI_MOSI_AF);

  SPI_DeInit(LCD_SPI);

  /* SPI Config */
  SPI_InitStructure.SPI_Direction = SPI_Direction_2Lines_FullDuplex;
  SPI_InitStructure.SPI_Mode = SPI_Mode_Master;
  SPI_InitStructure.SPI_DataSize = SPI_DataSize_8b;
  SPI_InitStructure.SPI_CPOL = SPI_CPOL_High;
  SPI_InitStructure.SPI_CPHA = SPI_CPHA_2Edge;
  SPI_InitStructure.SPI_NSS = SPI_NSS_Soft;
  SPI_InitStructure.SPI_BaudRatePrescaler = SPI_BaudRatePrescaler_2;
  SPI_InitStructure.SPI_FirstBit = SPI_FirstBit_MSB;
  SPI_InitStructure.SPI_CRCPolynomial = 7;
  SPI_Init(LCD_SPI, &SPI_InitStructure);

  /* SPI enable */
  SPI_Cmd(LCD_SPI, ENABLE);
}

/**
  * @brief  Displays a pixel.
  * @param  x: pixel x.
  * @param  y: pixel y.
  * @retval None
  */
static void PutPixel(int16_t x, int16_t y)
{
  if(x < 0 || x > 239 || y < 0 || y > 319)
  {
    return;
  }
  LCD_DrawLine(x, y, 1, LCD_DIR_HORIZONTAL);
}

#ifndef USE_Delay
/**
  * @brief  Inserts a delay time.
  * @param  nCount: specifies the delay time length.
  * @retval None
  */
static void delay(__IO uint32_t nCount)
{
  __IO uint32_t index = 0;
  for(index = (34000 * nCount); index != 0; index--)
  {
  }
}
#endif /* USE_Delay*/
/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/******************* (C) COPYRIGHT 2010 STMicroelectronics *****END OF FILE****/
