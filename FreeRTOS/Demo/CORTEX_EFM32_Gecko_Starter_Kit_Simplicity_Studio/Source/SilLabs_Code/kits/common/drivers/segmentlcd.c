/**************************************************************************//**
 * @file
 * @brief EFM32 Segment LCD Display driver
 * @version 4.2.1
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/


#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include "em_device.h"
#include "em_cmu.h"
#include "em_gpio.h"

#include "segmentlcd.h"

/**************************************************************************//**
 * @brief
 * Defines each text symbol's segment in terms of COM and BIT numbers,
 * in a way that we can enumerate each bit for each text segment in the
 * following bit pattern:
 * @verbatim
 *  -------0------
 *
 * |   \7  |8  /9 |
 * |5   \  |  /   |1
 *
 *  --6---  ---10--
 *
 * |    /  |  \11 |
 * |4  /13 |12 \  |2
 *
 *  -------3------
 * @endverbatim
 * E.g.: First text character bit pattern #3 (above) is
 *  Segment 1D for Display
 *  Location COM 3, BIT 0
 *****************************************************************************/
typedef struct
{
  uint8_t com[14]; /**< LCD COM line (for multiplexing) */
  uint8_t bit[14]; /**< LCD bit number */
} CHAR_TypeDef;


/**************************************************************************//**
 * @brief Defines segment COM and BIT fields numeric display
 *****************************************************************************/
typedef struct
{
  uint8_t com[7]; /**< LCD COM line (for multiplexing) */
  uint8_t bit[7]; /**< LCD bit number */
} NUMBER_TypeDef;

/**************************************************************************//**
 * @brief Defines segment COM and BIT fields for Energy Modes on display
 *****************************************************************************/
typedef struct
{
  uint8_t com[5]; /**< LCD COM line (for multiplexing) */
  uint8_t bit[5]; /**< LCD bit number */
} EM_TypeDef;

/**************************************************************************//**
 * @brief Defines segment COM and BIT fields for A-wheel (suited for Anim)
 *****************************************************************************/
typedef struct
{
  uint8_t com[8]; /**< LCD COM line (for multiplexing) */
  uint8_t bit[8]; /**< LCD bit number */
} ARING_TypeDef;

/**************************************************************************//**
 * @brief Defines segment COM and BIT fields for A-wheel (suited for Anim)
 *****************************************************************************/
typedef struct
{
  uint8_t com[4]; /**< LCD COM line (for multiplexing) */
  uint8_t bit[4]; /**< LCD bit number */
} BATTERY_TypeDef;

/**************************************************************************//**
 * @brief Defines prototype for all segments in display
 *****************************************************************************/
typedef struct
{
  CHAR_TypeDef    Text[7];      /**< Text on display */
  NUMBER_TypeDef  Number[4];    /**< Numbers on display */
  EM_TypeDef      EMode;        /**< Display energy mode */
  ARING_TypeDef   ARing;        /**< Display ring */
  BATTERY_TypeDef Battery;      /**< Display battery */
} MCU_DISPLAY;

/**************************************************************************//**
 * @brief Working instance of LCD display
 *****************************************************************************/
static const MCU_DISPLAY EFM_Display = EFM_DISPLAY_DEF;


/**************************************************************************//**
 * @brief
 * Defines higlighted segments for the alphabet, starting from "blank" (SPACE)
 * Uses bit pattern as defined for text segments above.
 * E.g. a capital O, would have bits 0 1 2 3 4 5 => 0x003f defined
 *****************************************************************************/
static const uint16_t EFM_Alphabet[] = {
  0x0000, /* space */
  0x1100, /* ! */
  0x0280, /* " */
  0x0000, /* # */
  0x0000, /* $ */
  0x0602, /* % */
  0x0000, /* & */
  0x0020, /* ' */
  0x0039, /* ( */
  0x000f, /* ) */
  0x0000, /* * */
  0x1540, /* + */
  0x2000, /* , */
  0x0440, /* - */
  0x1000, /* . */
  0x2200, /* / */

  0x003f, /* 0 */
  0x0006, /* 1 */
  0x045b, /* 2 */
  0x044f, /* 3 */
  0x0466, /* 4 */
  0x046d, /* 5 */
  0x047d, /* 6 */
  0x0007, /* 7 */
  0x047f, /* 8 */
  0x046f, /* 9 */

  0x0000, /* : */
  0x0000, /* ; */
  0x0a00, /* < */
  0x0000, /* = */
  0x2080, /* > */
  0x0000, /* ? */
  0xffff, /* @ */

  0x0477, /* A */
  0x0a79, /* B */
  0x0039, /* C */
  0x20b0, /* D */
  0x0079, /* E */
  0x0071, /* F */
  0x047d, /* G */
  0x0476, /* H */
  0x0006, /* I */
  0x000e, /* J */
  0x0a70, /* K */
  0x0038, /* L */
  0x02b6, /* M */
  0x08b6, /* N */
  0x003f, /* O */
  0x0473, /* P */
  0x083f, /* Q */
  0x0c73, /* R */
  0x046d, /* S */
  0x1101, /* T */
  0x003e, /* U */
  0x2230, /* V */
  0x2836, /* W */
  0x2a80, /* X */
  0x046e, /* Y */
  0x2209, /* Z */

  0x0039, /* [ */
  0x0880, /* backslash */
  0x000f, /* ] */
  0x0001, /* ^ */
  0x0008, /* _ */
  0x0100, /* ` */

  0x1058, /* a */
  0x047c, /* b */
  0x0058, /* c */
  0x045e, /* d */
  0x2058, /* e */
  0x0471, /* f */
  0x0c0c, /* g */
  0x0474, /* h */
  0x0004, /* i */
  0x000e, /* j */
  0x0c70, /* k */
  0x0038, /* l */
  0x1454, /* m */
  0x0454, /* n */
  0x045c, /* o */
  0x0473, /* p */
  0x0467, /* q */
  0x0450, /* r */
  0x0c08, /* s */
  0x0078, /* t */
  0x001c, /* u */
  0x2010, /* v */
  0x2814, /* w */
  0x2a80, /* x */
  0x080c, /* y */
  0x2048, /* z */

  0x0000,
};

/**************************************************************************//**
 * @brief
 * Defines higlighted segments for the numeric display
 *****************************************************************************/

static const uint16_t EFM_Numbers[] = {
  0x003f, /* 0 */
  0x0006, /* 1 */
  0x005b, /* 2 */
  0x004f, /* 3 */
  0x0066, /* 4 */
  0x006d, /* 5 */
  0x007d, /* 6 */
  0x0007, /* 7 */
  0x007f, /* 8 */
  0x006f, /* 9 */
  0x0077, /* A */
  0x007c, /* b */
  0x0039, /* C */
  0x005e, /* d */
  0x0079, /* E */
  0x0071, /* F */
  0x0040  /* - */
};

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */
/* sign is last element of the table  */
static const uint16_t signIndex = sizeof(EFM_Numbers)/sizeof(uint16_t) - 1 ;

static const LCD_Init_TypeDef lcdInit = LCD_INIT_DEF;
/** @endcond */


/**************************************************************************//**
 * @brief Disable all segments
 *****************************************************************************/
void SegmentLCD_AllOff(void)
{
  /* Turn on low segments */
  LCD_ALL_SEGMENTS_OFF();
}


/**************************************************************************//**
 * @brief Enable all segments
 *****************************************************************************/
void SegmentLCD_AllOn(void)
{
  LCD_ALL_SEGMENTS_ON();
}


/**************************************************************************//**
 * @brief Turn all segments on alpha characters in display off
 *****************************************************************************/
void SegmentLCD_AlphaNumberOff(void)
{
  LCD_ALPHA_NUMBER_OFF();
  return;
}


/**************************************************************************//**
 * @brief Light up or shut off Ring of Indicators
 * @param anum "Segment number" on "Ring", range 0 - 7
 * @param on Zero is off, non-zero is on
 *****************************************************************************/
void SegmentLCD_ARing(int anum, int on)
{
  uint32_t com, bit;

  com = EFM_Display.ARing.com[anum];
  bit = EFM_Display.ARing.bit[anum];

  if (on)
  {
    LCD_SegmentSet(com, bit, true);
  }
  else
  {
    LCD_SegmentSet(com, bit, false);
  }
}


/**************************************************************************//**
 * @brief Light up or shut off Battery Indicator
 * @param batteryLevel Battery Level, 0 to 4 (0 turns all off)
 *****************************************************************************/
void SegmentLCD_Battery(int batteryLevel)
{
  uint32_t com, bit;
  int      i, on;

  for (i = 0; i < 4; i++)
  {
    if (i < batteryLevel)
    {
      on = 1;
    }
    else
    {
      on = 0;
    }
    com = EFM_Display.Battery.com[i];
    bit = EFM_Display.Battery.bit[i];

    if (on)
    {
      LCD_SegmentSet(com, bit, true);
    }
    else
    {
      LCD_SegmentSet(com, bit, false);
    }
  }
}


/**************************************************************************//**
 * @brief Disables LCD controller
 *****************************************************************************/
void SegmentLCD_Disable(void)
{
  /* Disable LCD */
  LCD_Enable(false);

  /* Make sure CTRL register has been updated */
  LCD_SyncBusyDelay(LCD_SYNCBUSY_CTRL);

  /* Turn off LCD clock */
  CMU_ClockEnable(cmuClock_LCD, false);

  /* Turn off voltage boost if enabled */
  CMU->LCDCTRL = 0;
}


/**************************************************************************//**
 * @brief Light up or shut off Energy Mode indicator
 * @param em Energy Mode numer 0 to 4
 * @param on Zero is off, non-zero is on
 *****************************************************************************/
void SegmentLCD_EnergyMode(int em, int on)
{
  uint32_t com, bit;

  com = EFM_Display.EMode.com[em];
  bit = EFM_Display.EMode.bit[em];

  if (on)
  {
    LCD_SegmentSet(com, bit, true);
  }
  else
  {
    LCD_SegmentSet(com, bit, false);
  }
}


/**************************************************************************//**
 * @brief Segment LCD Initialization routine for EFM32 STK display
 * @param useBoost Set to use voltage boost
 *****************************************************************************/
void SegmentLCD_Init(bool useBoost)
{

  /* Ensure LE modules are accessible */
  CMU_ClockEnable(cmuClock_CORELE, true);

  /* Enable LFRCO as LFACLK in CMU (will also enable oscillator if not enabled) */
  CMU_ClockSelectSet(cmuClock_LFA, cmuSelect_LFRCO);

  /* LCD Controller Prescaler  */
  CMU_ClockDivSet(cmuClock_LCDpre, LCD_CMU_CLK_PRE);

  /* Frame Rate */
  CMU_LCDClkFDIVSet(LCD_CMU_CLK_DIV);

  /* Enable clock to LCD module */
  CMU_ClockEnable(cmuClock_LCD, true);

  LCD_DISPLAY_ENABLE();

  /* Disable interrupts */
  LCD_IntDisable(0xFFFFFFFF);

  /* Initialize and enable LCD controller */
  LCD_Init(&lcdInit);

  /* Enable all display segments */
  LCD_SEGMENTS_ENABLE();

  /* Enable boost if necessary */
  if (useBoost)
  {
    LCD_VBoostSet(LCD_BOOST_LEVEL);
    LCD_VLCDSelect(lcdVLCDSelVExtBoost);
    CMU->LCDCTRL |= CMU_LCDCTRL_VBOOSTEN;
  }

  /* Turn all segments off */
  SegmentLCD_AllOff();

  LCD_SyncBusyDelay(0xFFFFFFFF);
}


/**************************************************************************//**
 * @brief Write a hexadecimal number on lower alphanumeric part of
 *        Segment LCD display
 * @param num Hexadecimal number value to put on display, in range 0
 *        to 0x0FFFFFFF
 *****************************************************************************/
void SegmentLCD_LowerHex( uint32_t num )
{
  int       i;
  char      str[7];
  uint32_t  nibble;

  SegmentLCD_Symbol(LCD_SYMBOL_MINUS, 0);

  for ( i=6; i>=0; i-- )
  {
    nibble = num & 0xF;

    if ( nibble < 10 )
      str[i] = nibble + '0';
    else if ( nibble == 11 )
      str[i] = 'b';
    else if ( nibble == 13 )
      str[i] = 'd';
    else
      str[i] = (nibble - 10) + 'A';

    num >>= 4;
  }

  SegmentLCD_Write(str);
}

/**************************************************************************//**
 * @brief Write number on lower alphanumeric part of Segment LCD display
 * @param num Numeric value to put on display, in range -9999999 to +9999999
 *****************************************************************************/
void SegmentLCD_LowerNumber( int num )
{
  int i;
  char str[7];

  SegmentLCD_Symbol(LCD_SYMBOL_MINUS, 0);

  if ( ( num > 9999999 ) || ( num < -9999999 ) )
  {
    SegmentLCD_Write("Ovrflow");
    return;
  }

  if ( num < 0 )
  {
    SegmentLCD_Symbol(LCD_SYMBOL_MINUS, 1);
    num = -num;
  }

  for ( i=6; i>=0; i-- )
  {
    if ( ( i < 6 ) && ( num == 0 ) )
    {
      str[i] = ' ';
    }
    else
    {
      str[i] = (num % 10) + '0';
      num /= 10;
    }
  }

  SegmentLCD_Write(str);
}


/**************************************************************************//**
 * @brief Write number on numeric part on Segment LCD display
 * @param value Numeric value to put on display, in range -999 to +9999
 *****************************************************************************/
void SegmentLCD_Number(int value)
{
  int      i, com, bit, digit, div, neg;
  uint16_t bitpattern;
  uint16_t num;

  /* Parameter consistancy check */
  if (value >= 9999)
  {
    value = 9999;
  }
  if (value <= -1000)
  {
    value = -999;
  }
  if (value < 0)
  {
    value = abs(value);
    neg   = 1;
  }
  else
  {
    neg = 0;
  }

  /* If an update is in progress we must block, or there might be tearing */
  LCD_SyncBusyDelay(0xFFFFFFFF);

  /* Freeze updates to avoid partial refresh of display */
  LCD_FreezeEnable(true);

  /* Turn off all number LCD segments */
  SegmentLCD_NumberOff();

  /* Extract useful digits */
  div = 1;
  for (digit = 0; digit < 4; digit++)
  {
    num = (value / div) % 10;
    if ((neg == 1) && (digit == 3)) num = signIndex;
    /* Get number layout of display */
    bitpattern = EFM_Numbers[num];
    for (i = 0; i < 7; i++)
    {
      bit = EFM_Display.Number[digit].bit[i];
      com = EFM_Display.Number[digit].com[i];
      if (bitpattern & (1 << i))
      {
        LCD_SegmentSet(com, bit, true);
      }
    }
    div = div * 10;
  }
  /* Sync LCD registers to LE domain */
  LCD_FreezeEnable(false);
}


/**************************************************************************//**
 * @brief Turn all segments on numeric digits in display off
 *****************************************************************************/
void SegmentLCD_NumberOff(void)
{
  /* Turn off all number segments */
  LCD_NUMBER_OFF();
  return;
}


/**************************************************************************//**
 * @brief Light up or shut off various symbols on Segment LCD
 * @param s Which symbol to turn on or off
 * @param on Zero is off, non-zero is on
 *****************************************************************************/
void SegmentLCD_Symbol(lcdSymbol s, int on)
{
  int com = 0;
  int bit = 0;

  switch (s)
  {
  case LCD_SYMBOL_GECKO:
    com = LCD_SYMBOL_GECKO_COM;
    bit = LCD_SYMBOL_GECKO_SEG;
    break;
  case LCD_SYMBOL_ANT:
    com = LCD_SYMBOL_ANT_COM;
    bit = LCD_SYMBOL_ANT_SEG;
    break;
  case LCD_SYMBOL_PAD0:
    com = LCD_SYMBOL_PAD0_COM;
    bit = LCD_SYMBOL_PAD0_SEG;
    break;
  case LCD_SYMBOL_PAD1:
    com = LCD_SYMBOL_PAD1_COM;
    bit = LCD_SYMBOL_PAD1_SEG;
    break;
  case LCD_SYMBOL_EFM32:
    com = LCD_SYMBOL_EFM32_COM;
    bit = LCD_SYMBOL_EFM32_SEG;
    break;
  case LCD_SYMBOL_MINUS:
    com = LCD_SYMBOL_MINUS_COM;
    bit = LCD_SYMBOL_MINUS_SEG;
    break;
  case LCD_SYMBOL_COL3:
    com = LCD_SYMBOL_COL3_COM;
    bit = LCD_SYMBOL_COL3_SEG;
    break;
  case LCD_SYMBOL_COL5:
    com = LCD_SYMBOL_COL5_COM;
    bit = LCD_SYMBOL_COL5_SEG;
    break;
  case LCD_SYMBOL_COL10:
    com = LCD_SYMBOL_COL10_COM;
    bit = LCD_SYMBOL_COL10_SEG;
    break;
#ifdef LCD_SYMBOL_DEGC_SEG
  case LCD_SYMBOL_DEGC:
    com = LCD_SYMBOL_DEGC_COM;
    bit = LCD_SYMBOL_DEGC_SEG;
    break;
#endif
#ifdef LCD_SYMBOL_DEGF_SEG
  case LCD_SYMBOL_DEGF:
    com = LCD_SYMBOL_DEGF_COM;
    bit = LCD_SYMBOL_DEGF_SEG;
    break;
#endif
#ifdef LCD_SYMBOL_DP2_SEG
  case LCD_SYMBOL_DP2:
    com = LCD_SYMBOL_DP2_COM;
    bit = LCD_SYMBOL_DP2_SEG;
    break;
#endif
#ifdef LCD_SYMBOL_DP3_SEG
  case LCD_SYMBOL_DP3:
    com = LCD_SYMBOL_DP3_COM;
    bit = LCD_SYMBOL_DP3_SEG;
    break;
#endif
#ifdef LCD_SYMBOL_DP4_SEG
  case LCD_SYMBOL_DP4:
    com = LCD_SYMBOL_DP4_COM;
    bit = LCD_SYMBOL_DP4_SEG;
    break;
#endif
#ifdef LCD_SYMBOL_DP5_SEG
  case LCD_SYMBOL_DP5:
    com = LCD_SYMBOL_DP5_COM;
    bit = LCD_SYMBOL_DP5_SEG;
    break;
#endif
  case LCD_SYMBOL_DP6:
    com = LCD_SYMBOL_DP6_COM;
    bit = LCD_SYMBOL_DP6_SEG;
    break;
  case LCD_SYMBOL_DP10:
    com = LCD_SYMBOL_DP10_COM;
    bit = LCD_SYMBOL_DP10_SEG;
    break;
#ifdef LCD_SYMBOL_AM_SEG
  case LCD_SYMBOL_AM:
    com = LCD_SYMBOL_AM_COM;
    bit = LCD_SYMBOL_AM_SEG;
    break;
#endif
#ifdef LCD_SYMBOL_PM_SEG
  case LCD_SYMBOL_PM:
    com = LCD_SYMBOL_PM_COM;
    bit = LCD_SYMBOL_PM_SEG;
    break;
#endif
#ifdef LCD_SYMBOL_MICROAMP_SEG
  case LCD_SYMBOL_MICROAMP:
    com = LCD_SYMBOL_MICROAMP_COM;
    bit = LCD_SYMBOL_MICROAMP_SEG;
    break;
#endif
#ifdef LCD_SYMBOL_MILLIAMP_SEG
  case LCD_SYMBOL_MILLIAMP:
    com = LCD_SYMBOL_MILLIAMP_COM;
    bit = LCD_SYMBOL_MILLIAMP_SEG;
    break;
#endif

  }
  if (on)
  {
    LCD_SegmentSet(com, bit, true);
  }
  else
  {
    LCD_SegmentSet(com, bit, false);
  }
}


/**************************************************************************//**
 * @brief Write hexadecimal number on numeric part on Segment LCD display
 * @param value Numeric value to put on display, in range 0x0000-0xFFFF
 *****************************************************************************/
void SegmentLCD_UnsignedHex(uint16_t value)
{
  int      num, i, com, bit, digit;
  uint16_t bitpattern;

  /* Parameter consistancy check */
  if (value >= 0xffff)
  {
    value = 0xffff;
  }

  /* If an update is in progress we must block, or there might be tearing */
  LCD_SyncBusyDelay(0xFFFFFFFF);

  /* Freeze updates to avoid partial refresh of display */
  LCD_FreezeEnable(true);

  /* Turn off all number LCD segments */
  SegmentLCD_NumberOff();

  for (digit = 0; digit < 4; digit++)
  {
    num        = (value >> (4 * digit)) & 0x0f;
    bitpattern = EFM_Numbers[num];
    for (i = 0; i < 7; i++)
    {
      bit = EFM_Display.Number[digit].bit[i];
      com = EFM_Display.Number[digit].com[i];
      if (bitpattern & (1 << i))
      {
        LCD_SegmentSet(com, bit, true);
      }
    }
  }

  /* Sync LCD registers to LE domain */
  LCD_FreezeEnable(false);
}


/**************************************************************************//**
 * @brief Write text on LCD display
 * @param string Text string to show on display
 *****************************************************************************/
void SegmentLCD_Write(char *string)
{
  int      data, length, index;
  uint16_t bitfield;
  uint32_t com, bit;
  int      i;

  length = strlen(string);
  index  = 0;

  /* If an update is in progress we must block, or there might be tearing */
  LCD_SyncBusyDelay(0xFFFFFFFF);

  /* Freeze LCD to avoid partial updates */
  LCD_FreezeEnable(true);

  /* Turn all segments off */
  SegmentLCD_AlphaNumberOff();

  /* Fill out all characters on display */
  for (index = 0; index < 7; index++)
  {
    if (index < length)
    {
      data = (int) *string;
    }
    else           /* Padding with space */
    {
      data = 0x20; /* SPACE */
    }
    /* Defined letters currently starts at "SPACE" - ASCII 0x20; */
    data = data - 0x20;
    /* Get font for this letter */
    bitfield = EFM_Alphabet[data];

    for (i = 0; i < 14; i++)
    {
      bit = EFM_Display.Text[index].bit[i];
      com = EFM_Display.Text[index].com[i];

      if (bitfield & (1 << i))
      {
        /* Turn on segment */
        LCD_SegmentSet(com, bit, true);
      }
    }
    string++;
  }
  /* Enable update */
  LCD_FreezeEnable(false);
}
