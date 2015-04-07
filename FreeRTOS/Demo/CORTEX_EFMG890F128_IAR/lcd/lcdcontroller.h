/**************************************************************************//**
 * @file
 * @brief LCD Controller header file
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

#ifndef _LCDCONTROLLER_H
#define _LCDCONTROLLER_H

#include "efm32.h"

/* Range of symbols available on display */
typedef enum
{
  LCD_SYMBOL_GECKO,
  LCD_SYMBOL_ANT,
  LCD_SYMBOL_PAD0,
  LCD_SYMBOL_PAD1,
  LCD_SYMBOL_AM,
  LCD_SYMBOL_PM,
  LCD_SYMBOL_EFM32,
  LCD_SYMBOL_MINUS,
  LCD_SYMBOL_COL3,
  LCD_SYMBOL_COL5,
  LCD_SYMBOL_COL10,
  LCD_SYMBOL_DP2,
  LCD_SYMBOL_DP3,
  LCD_SYMBOL_DP4,
  LCD_SYMBOL_DP5,
  LCD_SYMBOL_DP6,
  LCD_SYMBOL_DP10,
} lcdSymbol;

/* Regular functions */
void LCD_Init(LCD_TypeDef *lcd);
void LCD_IRQHandler(void);
void LCD_Disable(LCD_TypeDef *lcd);

void LCD_AllOff(LCD_TypeDef *lcd);
void LCD_AllOn(LCD_TypeDef *lcd);

void LCD_ARing(LCD_TypeDef *lcd, int anum, int on);
void LCD_Battery(LCD_TypeDef *lcd, int batteryLevel);
void LCD_EnergyMode(LCD_TypeDef *lcd, int em, int on);
void LCD_Number(LCD_TypeDef *lcd, int value);
void LCD_NumberOff(LCD_TypeDef *lcd);
void LCD_Symbol(LCD_TypeDef *lcd, lcdSymbol s, int on);
void LCD_Write(LCD_TypeDef *lcd, char *string);
void LCD_ScrollText(LCD_TypeDef *lcd, char *scrolltext);

#endif
