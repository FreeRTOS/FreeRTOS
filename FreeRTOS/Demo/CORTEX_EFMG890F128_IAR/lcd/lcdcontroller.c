/**************************************************************************//**
 * @file
 * @brief LCD Controller driver
 * @author Energy Micro AS
 * @version 1.0.1
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2009 Energy Micro AS, http://www.energymicro.com</b>
 ******************************************************************************
 *
 * This source code is the property of Energy Micro AS. The source and compiled
 * code may only be used on Energy Micro "EFM32" microcontrollers.
 *
 * This copyright notice may not be removed from the source code nor changed.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Energy Micro AS has no
 * obligation to support this Software. Energy Micro AS is providing the
 * Software "AS IS", with no express or implied warranties of any kind,
 * including, but not limited to, any implied warranties of merchantability
 * or fitness for any particular purpose or warranties against infringement
 * of any proprietary rights of a third party.
 *
 * Energy Micro AS will not be liable for any consequential, incidental, or
 * special damages, or any other relief, or for any claim by any third party,
 * arising from your use of this Software.
 *
 *****************************************************************************/
#include "FreeRTOS.h"
#include "task.h"

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "efm32.h"
#include "lcdcontroller.h"
#include "lcddisplay.h"

/** Counts every n'th frame */
int frameCounter = 0;

/**************************************************************************//**
 * @brief LCD Interrupt Handler, triggers on frame counter, every n'th frame
 *****************************************************************************/
void LCD_IRQHandler(void)
{
  LCD_TypeDef *lcd = LCD;

  /* clear interrupt */
  lcd->IFC = 0xFFFFFFFF;
  frameCounter++;
}

/**************************************************************************//**
 * @brief Enables a segment on the LCD display
 * @param lcd Pointer to LCD register block
 * @param com COM segment number
 * @param bitvalue Bit value for segment
 *****************************************************************************/
static void LCD_enableSegment(LCD_TypeDef * lcd, int com, int bitvalue)
{
  switch (com)
  {
  case 0:
    lcd->SEGD0L |= bitvalue;
    break;
  case 1:
    lcd->SEGD1L |= bitvalue;
    break;
  case 2:
    lcd->SEGD2L |= bitvalue;
    break;
  case 3:
    lcd->SEGD3L |= bitvalue;
    break;
  case 4:
    lcd->SEGD0H |= bitvalue;
    break;
  case 5:
    lcd->SEGD1H |= bitvalue;
    break;
  case 6:
    lcd->SEGD2H |= bitvalue;
    break;
  case 7:
    lcd->SEGD3H |= bitvalue;
    break;
  }
}

/**************************************************************************//**
 * @brief Disables a segment on the LCD Display
 * @param lcd Pointer to LCD register structure
 * @param com COM segment number
 * @param bitvalue Bit value for segment
 *****************************************************************************/
static void LCD_disableSegment(LCD_TypeDef * lcd, int com, int bitvalue)
{
  switch (com)
  {
  case 0:
    lcd->SEGD0L &= ~bitvalue;
    break;
  case 1:
    lcd->SEGD1L &= ~bitvalue;
    break;
  case 2:
    lcd->SEGD2L &= ~bitvalue;
    break;
  case 3:
    lcd->SEGD3L &= ~bitvalue;
    break;
  case 4:
    lcd->SEGD0H &= ~bitvalue;
    break;
  case 5:
    lcd->SEGD1H &= ~bitvalue;
    break;
  case 6:
    lcd->SEGD2H &= ~bitvalue;
    break;
  case 7:
    lcd->SEGD3H &= ~bitvalue;
    break;
  }
}

/**************************************************************************//**
 * @brief Write number on numeric part on LCD display
 * @param lcd Pointer to LCD control block
 * @param value Numeric value to put on display, in range -999 to +9999
 *****************************************************************************/
void LCD_Number(LCD_TypeDef *lcd, int value)
{
  int      num, i, com, bit, digit, div, neg;
  uint16_t bitpattern;

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
  /* Extract useful digits */
  div = 1;
  for (digit = 0; digit < 4; digit++)
  {
    num = (value / div) % 10;
    if ((neg == 1) && (digit == 3)) num = 10;
    bitpattern = EM_Numbers[num];
    for (i = 0; i < 7; i++)
    {
      bit = EFMDisplay.Number[digit].bit[i];
      com = EFMDisplay.Number[digit].com[i];
      if (bitpattern & (1 << i))
      {
        LCD_enableSegment(lcd, com, 1 << bit);
      }
      else
      {
        LCD_disableSegment(lcd, com, 1 << bit);
      }
    }
    div = div * 10;
  }
}

/**************************************************************************//**
 * @brief Turn all segments on numeric display off
 * @param lcd Pointer to LCD register structure
 *****************************************************************************/
void LCD_NumberOff(LCD_TypeDef *lcd)
{
  int digit, i, bit, com;

  /* Turn off all segments */
  for (digit = 0; digit < 4; digit++)
  {
    for (i = 0; i < 7; i++)
    {
      bit = EFMDisplay.Number[digit].bit[i];
      com = EFMDisplay.Number[digit].com[i];
      LCD_disableSegment(lcd, com, 1 << bit);
    }
  }
  return;
}


/**************************************************************************//**
 * @brief Write text on LCD display
 * @param lcd Pointer to LCD register structure
 * @param string Text string to show on display
 *****************************************************************************/
void LCD_Write(LCD_TypeDef *lcd, char *string)
{
  int      data, length, index;
  uint16_t bitfield;
  uint32_t value;
  uint32_t com, bit;
  int      i;

  length = strlen(string);
  index  = 0;
  /* fill out all characters on display */
  for (index = 0; index < 7; index++)
  {
    if (index < length)
    {
      data = (int) *string;
    }
    else           /* padding with space */
    {
      data = 0x20; /* SPACE */
    }
    /* defined letters currently starts at "SPACE" - 0x20; */
    data     = data - 0x20;
    bitfield = EM_alphabet[data];


    for (i = 0; i < 14; i++)
    {
      bit   = EFMDisplay.Text[index].bit[i];
      com   = EFMDisplay.Text[index].com[i];
      value = (1 << bit);

      if (bitfield & (1 << i))
      {
        /* Turn on segment */
        LCD_enableSegment(lcd, com, value);
      }
      else
      {
        /* Turn off segment */
        LCD_disableSegment(lcd, com, value);
      }
    }
    string++;
  }
  while (lcd->SYNCBUSY) ;
}

/**************************************************************************//**
 * @brief LCD Disable all segments
 * @param lcd Pointer to LCD register block
 *****************************************************************************/
void LCD_AllOff(LCD_TypeDef *lcd)
{
  lcd->SEGD0L = 0x00000000;
  lcd->SEGD0H = 0x00000000;
  lcd->SEGD1L = 0x00000000;
  lcd->SEGD1H = 0x00000000;
  lcd->SEGD2L = 0x00000000;
  lcd->SEGD2H = 0x00000000;
  lcd->SEGD3L = 0x00000000;
  lcd->SEGD3H = 0x00000000;
  while (lcd->SYNCBUSY) ;
}

/**************************************************************************//**
 * @brief LCD Enable all segments
 * @param lcd Pointer to LCD register block
 *****************************************************************************/
void LCD_AllOn(LCD_TypeDef *lcd)
{
  lcd->SEGD0L = 0xffffffff;
  lcd->SEGD0H = 0xffffffff;
  lcd->SEGD1L = 0xffffffff;
  lcd->SEGD1H = 0xffffffff;
  lcd->SEGD2L = 0xffffffff;
  lcd->SEGD2H = 0xffffffff;
  lcd->SEGD3L = 0xffffffff;
  lcd->SEGD3H = 0xffffffff;
  while (lcd->SYNCBUSY) ;
}

/**************************************************************************//**
 * @brief LCD Light up or shut off Energy Mode indicator
 * @param lcd Pointer to LCD register block
 * @pararm em Energy Mode numer 0 to 4
 * @param on Zero is off, non-zero is on
 *****************************************************************************/
void LCD_EnergyMode(LCD_TypeDef *lcd, int em, int on)
{
  uint32_t com, bitvalue;

  com      = EFMDisplay.EMode.com[em];
  bitvalue = 1 << EFMDisplay.EMode.bit[em];

  if (on)
  {
    LCD_enableSegment(lcd, com, bitvalue);
  }
  else
  {
    LCD_disableSegment(lcd, com, bitvalue);
  }
}

/**************************************************************************//**
 * @brief LCD Light up or shut off Ring of Indicators
 * @param lcd Pointer to LCD register block
 * @param anum "Segment number" on "Ring", range 0 - 7
 * @param on Zero is off, non-zero is on
 *****************************************************************************/
void LCD_ARing(LCD_TypeDef *lcd, int anum, int on)
{
  uint32_t com, bitvalue;

  com      = EFMDisplay.ARing.com[anum];
  bitvalue = 1 << EFMDisplay.ARing.bit[anum];

  if (on)
  {
    LCD_enableSegment(lcd, com, bitvalue);
  }
  else
  {
    LCD_disableSegment(lcd, com, bitvalue);
  }
}

/**************************************************************************//**
 * @brief LCD Light up or shut off various symbols on LCD Display
 * @param lcd Pointer to LCD register block
 * @param s Which symbol to turn on or off
 * @param on Zero is off, non-zero is on
 *****************************************************************************/
void LCD_Symbol(LCD_TypeDef *lcd, lcdSymbol s, int on)
{
  int com, bit;

  switch (s)
  {
  case LCD_SYMBOL_GECKO:
    com = 3; bit = 8;
    break;
  case LCD_SYMBOL_ANT:
    com = 3; bit = 1;
    break;
  case LCD_SYMBOL_PAD0:
    com = 1; bit = 8;
    break;
  case LCD_SYMBOL_PAD1:
    com = 2; bit = 8;
    break;
  case LCD_SYMBOL_AM:
    com = 4; bit = 0;
    break;
  case LCD_SYMBOL_PM:
    com = 4; bit = 3;
    break;
  case LCD_SYMBOL_EFM32:
    com = 0; bit = 8;
    break;
  case LCD_SYMBOL_MINUS:
    com = 0; bit = 9;
    break;
  case LCD_SYMBOL_COL3:
    com = 0; bit = 16;
    break;
  case LCD_SYMBOL_COL5:
    com = 0; bit = 24;
    break;
  case LCD_SYMBOL_COL10:
    com = 4; bit = 7;
    break;
  case LCD_SYMBOL_DP2:
    com = 4; bit = 2;
    break;
  case LCD_SYMBOL_DP3:
    com = 5; bit = 2;
    break;
  case LCD_SYMBOL_DP4:
    com = 6; bit = 2;
    break;
  case LCD_SYMBOL_DP5:
    com = 7; bit = 2;
    break;
  case LCD_SYMBOL_DP6:
    com = 0; bit = 21;
    break;
  case LCD_SYMBOL_DP10:
    com = 4; bit = 5;
    break;
  }
  if (on)
  {
    LCD_enableSegment(lcd, com, 1 << bit);
  }
  else
  {
    LCD_disableSegment(lcd, com, 1 << bit);
  }
}

/**************************************************************************//**
 * @brief LCD Light up or shut off Battery Indicator
 * @param lcd Pointer to LCD register block
 * @param batteryLevel Battery Level, 0 to 4 (0 turns all off)
 *****************************************************************************/
void LCD_Battery(LCD_TypeDef *lcd, int batteryLevel)
{
  uint32_t com, bitvalue;
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
    com      = EFMDisplay.Battery.com[i];
    bitvalue = 1 << EFMDisplay.Battery.bit[i];

    if (on)
    {
      LCD_enableSegment(lcd, com, bitvalue);
    }
    else
    {
      LCD_disableSegment(lcd, com, bitvalue);
    }
  }
}

/**************************************************************************//**
 * @brief LCD Initialization routine for EFM32 DVK display
 * @param lcd Pointer to LCD register block
 *****************************************************************************/
void LCD_Init(LCD_TypeDef *lcd)
{
  CMU_TypeDef *cmu = CMU;

  /* Enable LFXO oscillator */
  cmu->OSCENCMD |= CMU_OSCENCMD_LFXOEN;
  while (!(cmu->STATUS & CMU_STATUS_LFXORDY)) ;

  /* Enable LCD clock in CMU */
  cmu->LFACLKEN0 |= CMU_LFACLKEN0_LCD;

  /* Select LFXO for LCD */
  cmu->LFCLKSEL = CMU_LFCLKSEL_LFA_LFXO | CMU_LFCLKSEL_LFB_LFXO;

  /* LCD Controller Prescaler (divide by 1) */
  /* CLKlcd = 0.25 kHz */
  cmu->LFAPRESC0 &= ~_CMU_LFAPRESC0_LCD_MASK;
  cmu->LFAPRESC0 |= _CMU_LFAPRESC0_LCD_DIV128 << _CMU_LFAPRESC0_LCD_SHIFT;

  /* Set up interrupt handler */
  lcd->IEN = 0;
  while (lcd->SYNCBUSY) ;

  /* Clear pending interrupts */
  lcd->IFC = ~0;
  /* Enable interrupt */
  NVIC_EnableIRQ(LCD_IRQn);
  lcd->IEN = LCD_IEN_FC;

  /* Frame rate is 32Hz, 0.25Khz LFCLK128, QUADRUPLEX mode, FDIV=0 */
  lcd->DISPCTRL = LCD_DISPCTRL_MUX_QUADRUPLEX |
                  LCD_DISPCTRL_BIAS_ONETHIRD |
                  LCD_DISPCTRL_WAVE_LOWPOWER |
                  LCD_DISPCTRL_CONLEV_MAX |
                  LCD_DISPCTRL_VLCDSEL_VDD |
                  LCD_DISPCTRL_VBLEV_3V00;

  /* No voltage boost, framerate 32Hz */
  cmu->LCDCTRL = 0;

  /* Turn all segments off */
  LCD_AllOff(lcd);

  /* Enable all segment registers */
  lcd->SEGEN = 0x000003FF;
  lcd->CTRL  = LCD_CTRL_EN | LCD_CTRL_UDCTRL_FRAMESTART;
  while (lcd->SYNCBUSY) ;

  /* Configure LCD to give a frame counter interrupt every 8th frame. */
  lcd->BACTRL = LCD_BACTRL_FCEN | (7 << _LCD_BACTRL_FCTOP_SHIFT) | (0 << _LCD_BACTRL_FCPRESC_SHIFT);
  while (lcd->SYNCBUSY) ;
  lcd->IFC = LCD_IFC_FC;
  lcd->IEN = LCD_IEN_FC;
}


/**************************************************************************//**
 * @brief Disables LCD controller
 * @param lcd Pointer to LCD register block
 *****************************************************************************/
void LCD_Disable(LCD_TypeDef *lcd)
{
  CMU_TypeDef *cmu = CMU;

  /* Turn off interrupts */
  lcd->IEN = 0x00000000;
  lcd->IFC = LCD_IFC_FC;
  NVIC_DisableIRQ(LCD_IRQn);
  /* Disable LCD */
  lcd->CTRL = 0;
  /* Turn off LCD clock */
  cmu->LFACLKEN0 &= ~(CMU_LFACLKEN0_LCD);
  /* Turn off voltage boost if enabled */
  cmu->LCDCTRL = 0;
}

/**************************************************************************//**
 * @brief LCD scrolls a text over the display, sort of "polled printf"
 * @param lcd Pointer to LCD register block
 *****************************************************************************/
void LCD_ScrollText(LCD_TypeDef *lcd, char *scrolltext)
{
  int  i, len;
  char buffer[8];

  buffer[7] = 0x00;
  len       = strlen(scrolltext);
  if (len < 7) return;
  for (i = 0; i < (len - 7); i++)
  {
    memcpy(buffer, scrolltext + i, 7);
    LCD_Write(lcd, buffer);
    vTaskDelay(100/portTICK_RATE_MS);
  }
}


