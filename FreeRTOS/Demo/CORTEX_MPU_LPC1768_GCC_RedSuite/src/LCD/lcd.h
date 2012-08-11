//*****************************************************************************
//   +--+       
//   | ++----+   
//   +-++    |  
//     |     |  
//   +-+--+  |   
//   | +--+--+  
//   +----+    Copyright (c) 2009 Code Red Technologies Ltd. 
//
// lcd.h - Routines containing primitives for writing to the LCD
//
//
// Software License Agreement
// 
// The software is owned by Code Red Technologies and/or its suppliers, and is 
// protected under applicable copyright laws.  All rights are reserved.  Any 
// use in violation of the foregoing restrictions may subject the user to criminal 
// sanctions under applicable laws, as well as to civil liability for the breach 
// of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// USE OF THIS SOFTWARE FOR COMMERCIAL DEVELOPMENT AND/OR EDUCATION IS SUBJECT
// TO A CURRENT END USER LICENSE AGREEMENT (COMMERCIAL OR EDUCATIONAL) WITH
// CODE RED TECHNOLOGIES LTD. 


#ifndef LCD_H_
#define LCD_H_

// Define size of LCD screen.

#define LCD_MAX_X 128
#define LCD_MAX_Y 128

// Translates a 24-bit RGB color to RGB565
#define TRANSLATE24BIT_TO_RGB565(c)    ((((c) & 0x00ff0000) >> 19) |               \
                                 ((((c) & 0x0000ff00) >> 5) & 0x000007e0) | \
                                 ((((c) & 0x000000ff) << 8) & 0x0000f800))

// Define a basic set of 24bit colors, based on the standard "websafe" set
#define COLOR24_AQUA	0x00FFFF
#define COLOR24_GREY	0x808080
#define COLOR24_NAVY 	0x000080 	
#define COLOR24_SILVER 	0xC0C0C0
#define COLOR24_BLACK 	0x000000 	
#define COLOR24_GREEN 	0x008000 	
#define COLOR24_OLIVE 	0x808000 	
#define COLOR24_TEAL 	0x008080
#define COLOR24_BLUE 	0x0000FF 	
#define COLOR24_LIME 	0x00FF00 	
#define COLOR24_PURPLE 	0x800080 	
#define COLOR24_WHITE 	0xFFFFFF
#define COLOR24_FUCHSIA	0xFF00FF 	
#define COLOR24_MAROON	0x800000 	
#define COLOR24_RED 	0xFF0000
#define COLOR24_YELLOW 	0xFFFF00

// Create a set of RGB565 colors that can be used directly within code
#define COLOR_AQUA TRANSLATE24BIT_TO_RGB565(COLOR24_AQUA)
#define COLOR_GREY	TRANSLATE24BIT_TO_RGB565(COLOR24_GREY)
#define COLOR_NAVY	TRANSLATE24BIT_TO_RGB565(COLOR24_NAVY) 	
#define COLOR_SILVER 	TRANSLATE24BIT_TO_RGB565(COLOR24_SILVER)
#define COLOR_BLACK 	TRANSLATE24BIT_TO_RGB565(COLOR24_BLACK) 	
#define COLOR_GREEN 	TRANSLATE24BIT_TO_RGB565(COLOR24_GREEN) 	
#define COLOR_OLIVE 	TRANSLATE24BIT_TO_RGB565(COLOR24_OLIVE) 	
#define COLOR_TEAL 		TRANSLATE24BIT_TO_RGB565(COLOR24_TEAL)
#define COLOR_BLUE 		TRANSLATE24BIT_TO_RGB565(COLOR24_BLUE) 	
#define COLOR_LIME 		TRANSLATE24BIT_TO_RGB565(COLOR24_LIME) 	
#define COLOR_PURPLE 	TRANSLATE24BIT_TO_RGB565(COLOR24_PURPLE) 	
#define COLOR_WHITE 	TRANSLATE24BIT_TO_RGB565(COLOR24_WHITE)
#define COLOR_FUCHSIA	TRANSLATE24BIT_TO_RGB565(COLOR24_FUCHSIA) 	
#define COLOR_MAROON	TRANSLATE24BIT_TO_RGB565(COLOR24_MAROON)	
#define COLOR_RED 		TRANSLATE24BIT_TO_RGB565(COLOR24_RED)
#define COLOR_YELLOW 	TRANSLATE24BIT_TO_RGB565(COLOR24_YELLOW)


void LCD_Line (int xmin,int xmax,int ymin,int ymax,int color);
void LCD_FilledRect(int xmin,int xmax,int ymin,int ymax,int color);
void LCD_Rect(int xmin,int xmax,int ymin,int ymax,int color);
void LCD_WriteBitMap8x15(int x, int y, int height, int width, unsigned char *pBitMap, int color);
void LCD_PlotPoint(int x,int y,int color);
void LCD_Circle (int x0, int y0, int radius, int color);
void LCD_FilledCircle (int x0, int y0, int radius, int color);
void LCD_ClearScreen(void);
void LCD_WriteBitMap8x15(int x, int y, int height, int width, unsigned char *pBitMap, int color);
void LCD_PrintChar(int x, int y, unsigned char c, int color );
void LCD_PrintString(int x, int y, char *pcString, int iStrLen, int color);


#endif /*LCD_H_*/