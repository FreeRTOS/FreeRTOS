/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Interface of ILI9325 driver.
 *
 */

#ifndef _ILI9488_H_
#define _ILI9488_H_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include <stdint.h>
typedef uint32_t LcdColor_t ;

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/
//#define LCD_SPI_3

/* ILI9325 ID code */
#define ILI9488_DEVICE_CODE    0x9488

#define ILI9488_LCD_WIDTH       320
#define ILI9488_LCD_HEIGHT      480
#define ILI9488_SELF_TEST_OK    0xC0
   
/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

typedef volatile uint8_t REG8;

/*----------------------------------------------------------------------------
 *        Marcos
 *----------------------------------------------------------------------------*/

/** LCD index register address */
#define ILI9488_CMD(x) (uint16_t)(x & 0x00FF)
/** ILI9488 status register address */
#define ILI9488_PARAM(x) (uint16_t)(x | 0x100)
   

#define ILI9488_cs          1

/* Pixel cache used to speed up communication */
#define LCD_DATA_CACHE_SIZE BOARD_LCD_WIDTH
//extern  LcdColor_t gLcdPixelCache[LCD_DATA_CACHE_SIZE];
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
extern void ILI9488_WriteSingle( LcdColor_t data );
extern void ILI9488_WriteRAM_Prepare( void );
extern void ILI9488_WriteRAM( LcdColor_t dwColor );
extern void ILI9488_ReadRAM_Prepare( void );
extern void ILI9488_WriteRAMBuffer( const LcdColor_t *pBuf, uint32_t size);
extern void ILI9488_SetCursor(uint16_t x, uint16_t y);
extern uint32_t ILI9488_ReadRAM( void );
extern uint32_t ILI9488_Initialize( void );
extern void ILI9488_On( void );
extern void ILI9488_Off( void );
extern void ILI9488_PowerDown( void );
extern void ILI9488_SetWindow( uint16_t dwX, uint16_t dwY, uint16_t dwWidth, uint16_t dwHeight );
extern void ILI9488_SetDisplayLandscape( uint8_t dwRGB, uint8_t LandscaprMode );
extern void ILI9488_SetDisplayPortrait( uint8_t dwRGB );
extern void ILI9488_SetVerticalScrollWindow( uint16_t dwStartAdd, uint16_t dwHeight );
extern void ILI9488_VerticalScroll( uint16_t wY );
extern void ILI9488_SetPartialImage1( uint32_t dwDisplayPos, uint32_t dwStart, uint32_t dwEnd );
extern void ILI9488_SetPartialImage2( uint32_t dwDisplayPos, uint32_t dwStart, uint32_t dwEnd );
extern void ILI9488_TestPattern( void );
extern uint32_t ILI9488_SetColor( uint32_t dwRgb24Bits );
extern void ILI9488_ExitScrollMode(void );
extern void ILI9488_SetPartialWindow( uint16_t Start, uint16_t End);
#endif /* #ifndef ILI9488 */
