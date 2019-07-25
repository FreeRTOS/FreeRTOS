/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name     : lcd_pmod.h
* Device(s)     : RZ/T1 (R7S910017)
* Tool-Chain    : GNUARM-NONEv14.02-EABI
* H/W Platform  : RSK+RZT1 CPU Board
*
* Description   : This Header file contains the Macro Definitions & prototypes
*                 for the functions used in lcd.c
*
*                 This function is created to drive the Okaya LCD display with
*                 either ST7735 or ST7715 driver device. The commands for both
*                 the devices are the same.
*
*                 The display is controlled using the SPI bus. In this example,
*                 the SCI5 is used. This can be modified to the SCI connected to
*                 the PMOD interface. The SCI driver file will also be required.
*
*                 The display memory has an offset with respect to the actual
*                 pixel. This is not documented but realised from driving the
*                 display. The offset is set as LEFT MARGIN and TOP MARGIN.
*                 This offset is catered for internally, so as far as the user
*                 is concerned, cursor position 0,0 is the top left pixel.
* 
*                 The simplest procedure to run the display is as follows:
*                 Init_LCD(); Initialise the serial port and set up the display.
*
*                 Clear the display.
*                 The font colour is set to white and background colour to black.
*
*                 DisplaySetFontColour(COL_YELLOW);
*                                    set the font colour to desired colour
*                 DisplaySetBackColour(COL_BLUE);
*                                    set the background colour to desired value
*                 DisplayCenter(1,"Renesas");
*                                    write a title on line 1 of the display.
*
*                Note: Line 0 is the top line.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History       : DD.MM.YYYY Version Description
*               : 21.04.2015 1.00
***********************************************************************************************************************/

/***********************************************************************************************************************
User Includes (Project Level Includes)
***********************************************************************************************************************/
/* Defines standard variable types used in this file */
#include <stdint.h>
#include "iodefine.h"

/***********************************************************************************************************************
Macro Definitions
***********************************************************************************************************************/
/* Multiple inclusion prevention macro */
#ifndef LCD_PMOD_H
#define LCD_PMOD_H


/***********************************************************************************************************************
Macro Definitions for Okaya display on PMOD connector
***********************************************************************************************************************/


/***********************************************************************************************************************
*  SCREEN
*
*  The screen size is 128 x 128 pixels, with coordinate 0,0 at the top left.
*  The display controller is ST7735 or ST7715.
*
***********************************************************************************************************************/
/* 16 lines @ 8 bits = 128. */
#define SCREEN_HEIGHT             (128)            
#define SCREEN_WIDTH              (128)

#ifndef USE_PMOD2
/* DATA/COMMAND select pin */
#define DATA_CMD_PIN              (PORT7.PODR.BIT.B6)
/* Backlight enable pin */
#define BL_ENABLE_PIN             (PORT7.PODR.BIT.B4)  
/* Reset pin */
#define RESET_PIN                 (PORT6.PODR.BIT.B7)
#else
/* DATA/COMMAND select pin */
#define DATA_CMD_PIN              (PORTM.PODR.BIT.B2)
/* Backlight enable pin */
#define BL_ENABLE_PIN             (PORTM.PODR.BIT.B3) 
/* Reset pin */
#define RESET_PIN                 (PORT5.PODR.BIT.B1)
#endif

/* Automatic calculation of parameters */

 /* including a space */
#define FONT_WIDTH                (6u)
/* including 1 pixel space */
#define FONT_HEIGHT               (8u)
#define MAX_LINES                 (SCREEN_HEIGHT / FONT_HEIGHT)
#define CHAR_PER_LINE             (SCREEN_WIDTH / FONT_WIDTH)

/* Allow 2 pixel margin on the left and the top */
#define LEFT_MARGIN               (2u)
#define TOP_MARGIN                (3u)
#define CR                        (0x0d)
#define LF                        (0x0a)
#define BS                        (0x08)


/***********************************************************************************************************************
*  DISPLAY COLOUR DEFINITIONS (16 bits) R5G6B5 format
*
*  Only Primary & secondary colours are defined here. Other colours can be
*  created using RGB values.
***********************************************************************************************************************/
#define COL_BLACK       (0x0000)
#define COL_RED         (0xF800)
#define COL_GREEN       (0x07E0)
#define COL_BLUE        (0x001F)
#define COL_YELLOW      (0xFFE0)
#define COL_CYAN        (0x07FF)
#define COL_MAGENTA     (0xF81F)
#define COL_WHITE       (0xFFFF)

/***********************************************************************************************************************

  DISPLAY COMMAND SET ST7735

***********************************************************************************************************************/
#define ST7735_NOP      (0x0)
#define ST7735_SWRESET  (0x01)
#define ST7735_SLPIN    (0x10)
#define ST7735_SLPOUT   (0x11)
#define ST7735_PTLON    (0x12)
#define ST7735_NORON    (0x13)
#define ST7735_INVOFF   (0x20)
#define ST7735_INVON    (0x21)
#define ST7735_DISPOFF  (0x28)
#define ST7735_DISPON   (0x29)
#define ST7735_CASET    (0x2A)
#define ST7735_RASET    (0x2B)
#define ST7735_RAMWR    (0x2C)
#define ST7735_COLMOD   (0x3A)
#define ST7735_MADCTL   (0x36)
#define ST7735_FRMCTR1  (0xB1)
#define ST7735_INVCTR   (0xB4)
#define ST7735_DISSET5  (0xB6)
#define ST7735_PWCTR1   (0xC0)
#define ST7735_PWCTR2   (0xC1)
#define ST7735_PWCTR3   (0xC2)
#define ST7735_VMCTR1   (0xC5)
#define ST7735_PWCTR6   (0xFC)
#define ST7735_GMCTRP1  (0xE0)
#define ST7735_GMCTRN1  (0xE1)

/* delay for delay counter */
#define DELAY_TIMING    (0x08)

/***********************************************************************************************************************
* Function Prototypes
***********************************************************************************************************************/
/* Initialises the debug LCD */
void lcd_init (void);

/* Display string at specific line of display */
void display_lcd (uint8_t const line, uint8_t const column, uint8_t const * string);

/* Display the string at current cursor position */
void display_str (uint8_t const * str);

/* Display the sting at the centre of the specified line */
void display_center (uint8_t const line_num, uint8_t * const str);

/* Clears the display */
void clear_display (uint16_t colour);

/* Clear a specified line */
void display_clear_line(uint8_t line_num);

/* Set the current cursor position */
void display_set_cursor (uint8_t const x, uint8_t const y);

/* Delay function */
void display_delay_us (uint32_t time_us);
void display_delay_ms (uint32_t time_ms);

/* Set Font colour */
void display_set_font_colour (uint16_t const col);

/* Set Background colour */
void display_set_back_colour (uint16_t const col);

/* Simple image blit */
void display_image (uint8_t *image, uint8_t image_width,
		                 uint8_t image_height, uint8_t loc_x, uint8_t loc_y);

/* Enable display */
void display_on (void);

/* Disable display */
void display_off (void);


/* LCD_PMOD_H */
#endif

