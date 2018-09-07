/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
 * Interface of ILI9488 driver.
 *
 */

#ifndef _ILI9488_SPI_H_
#define _ILI9488_SPI_H_

/*------------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

/*------------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
extern uint32_t ILI9488_SpiReadChipId (void);
extern uint32_t ILI9488_SpiInitialize( sXdmad * dmad );
extern void ILI9488_SpiSetPixelFormat(uint8_t format);
extern void ILI9488_SpiNop(void);
extern void ILI9488_SpiWriteMemory(const uint8_t *pBuf, uint32_t size);
extern void ILI9488_SpiReadMemory( const uint8_t *pBuf, uint32_t size);
extern void ILI9488_SpiSetCursor(uint16_t x, uint16_t y);
extern void ILI9488_SpiSetWindow(
				uint16_t dwX,
				uint16_t dwY,
				uint16_t dwWidth,
				uint16_t dwHeight );

extern void ILI9488_SpiSetFullWindow(void);
extern void ILI9488_SpiOn(void );
extern void ILI9488_SpiOff(void );
extern void ILI9488_SpiSetDisplayLandscape( 
				uint8_t dwRGB, uint8_t LandscaprMode );

#endif /* #ifndef ILI9488_SPI */
