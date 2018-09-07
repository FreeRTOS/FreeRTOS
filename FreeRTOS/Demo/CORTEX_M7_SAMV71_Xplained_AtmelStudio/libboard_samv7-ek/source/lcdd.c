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
 * Implementation of LCD driver, Include LCD initialization,
 * LCD on/off and LCD back-light control.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"
#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/
 uint8_t ili9488_lcdMode;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Turn on the LCD.
 */
void LCDD_On( void)
{
	if (ili9488_lcdMode == ILI9488_SPIMODE ) {
		ILI9488_SpiOn();
	} else {
		ILI9488_EbiOn();
	} 
}

/**
 * \brief Turn off the LCD.
 */
void LCDD_Off( void)
{
	if (ili9488_lcdMode == ILI9488_SPIMODE ) {
		ILI9488_SpiOff();
	} else {
		ILI9488_EbiOff();
	}
}

/**
 * \brief Set the back-light of the LCD.
 *
 * \param level   Back-light brightness level [1..16], 1 means maximum brightness.
 */
#if defined (BOARD_LCD_SPI_EXT1)
void LCDD_SpiSetBacklight (uint32_t level)
{
	/* Ensure valid level */
	level = (level < 1) ? 1 : level;
	level = (level > 16) ? 16 : level;
	PWMC_SetDutyCycle(PWM0, CHANNEL_PWM_LCD, level);
}
#endif

/**
 * \brief Initializes the LCD controller.
 * Configure SMC to access LCD controller at 64MHz MCK.
 * \param lcdMode LCD_SPI or LCD_EBI mode
 * \param cRotate rotate direction 0: H 1:V
 */
void LCDD_Initialize( uint8_t lcdMode, sXdmad * dmad, uint8_t cRotate)
{
	ili9488_lcdMode = lcdMode;
	/* Initialize LCD controller */
	if (lcdMode == ILI9488_SPIMODE ) {
		ILI9488_SpiInitialize(dmad) ;
		ILI9488_SpiSetDisplayLandscape(1, cRotate);
	} else {
		ILI9488_EbiInitialize(dmad) ;
		ILI9488_EbiSetDisplayLandscape(1, cRotate);
	}

#if defined (BOARD_LCD_SPI_EXT1)
	/* Set LCD back-light */
	LCDD_SpiSetBacklight( 16 );
#endif

}

