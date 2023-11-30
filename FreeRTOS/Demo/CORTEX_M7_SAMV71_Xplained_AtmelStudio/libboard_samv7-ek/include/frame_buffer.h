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
 * Interface of frame buffer driver.
 *
 */

#ifndef _FRAME_BUFFER_
#define _FRAME_BUFFER_

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern void FB_SetFrameBuffer(
				LcdColor_t *pBuffer,
				uint8_t ucWidth,
				uint8_t ucHeight);

extern void FB_SetColor(uint32_t color);

extern uint32_t FB_DrawLine (
				uint32_t dwX1,
				uint32_t dwY1,
				uint32_t dwX2,
				uint32_t dwY2 );

extern uint32_t FB_DrawPixel( uint32_t x, uint32_t y );
extern uint32_t FB_DrawCircle( uint32_t x, uint32_t y, uint32_t r );
extern uint32_t FB_DrawFilledCircle(
				uint32_t dwX,
				uint32_t dwY, 
				uint32_t dwRadius);

extern uint32_t FB_DrawRectangle(
				uint32_t dwX1,
				uint32_t dwY1,
				uint32_t dwX2,
				uint32_t dwY2 );

extern uint32_t FB_DrawFilledRectangle(
				uint32_t dwX1,
				uint32_t dwY1,
				uint32_t dwX2,
				uint32_t dwY2 );

extern uint32_t FB_DrawPicture(
				uint32_t dwX1,
				uint32_t dwY1,
				uint32_t dwX2,
				uint32_t dwY2,
				const void *pBuffer );

#endif /* #ifndef _FRAME_BUFFER_ */
