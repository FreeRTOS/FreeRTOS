/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "lcdd.h"

#include <board.h>
#include <pmc/pmc.h>
#include <hx8347/hx8347.h>
#include <pio/pio.h>

#include "FreeRTOS.h"
#include "task.h"

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Initializes the LCD controller.
/// \param pLcdBase   LCD base address.
//------------------------------------------------------------------------------
void LCDD_Initialize(void)
{
    const Pin pPins[] = {BOARD_LCD_PINS};
    AT91PS_HSMC4_CS pSMC = AT91C_BASE_HSMC4_CS2;
    unsigned int rMode;

    // Enable pins
    PIO_Configure(pPins, PIO_LISTSIZE(pPins));

    // Enable peripheral clock
    PMC_EnablePeripheral(AT91C_ID_HSMC4);

    // EBI SMC Configuration
    pSMC->HSMC4_SETUP = 0
                    | ((4 <<  0) & AT91C_HSMC4_NWE_SETUP)
                    | ((2 <<  8) & AT91C_HSMC4_NCS_WR_SETUP)
                    | ((4 << 16) & AT91C_HSMC4_NRD_SETUP)
                    | ((2 << 24) & AT91C_HSMC4_NCS_RD_SETUP)
                    ;

    pSMC->HSMC4_PULSE = 0
                    | (( 5 <<  0) & AT91C_HSMC4_NWE_PULSE)
                    | (( 18 <<  8) & AT91C_HSMC4_NCS_WR_PULSE)
                    | (( 5 << 16) & AT91C_HSMC4_NRD_PULSE)
                    | (( 18 << 24) & AT91C_HSMC4_NCS_RD_PULSE)
                    ;

    pSMC->HSMC4_CYCLE = 0
                  | ((22 <<  0) & AT91C_HSMC4_NWE_CYCLE)
                  | ((22 << 16) & AT91C_HSMC4_NRD_CYCLE)
                  ;

    rMode = pSMC->HSMC4_MODE;
    pSMC->HSMC4_MODE = (rMode & ~(AT91C_HSMC4_DBW | AT91C_HSMC4_READ_MODE
                 | AT91C_HSMC4_WRITE_MODE | AT91C_HSMC4_PMEN))
                 | (AT91C_HSMC4_READ_MODE)
                 | (AT91C_HSMC4_WRITE_MODE)
                 | (AT91C_HSMC4_DBW_WIDTH_SIXTEEN_BITS)
                 ;

    // Initialize LCD controller (HX8347)
    LCD_Initialize((void *)BOARD_LCD_BASE);

    // Set LCD backlight
    LCDD_SetBacklight(25);
}

//------------------------------------------------------------------------------
/// Turn on the LCD
//------------------------------------------------------------------------------
void LCDD_Start(void)
{
    LCD_On((void *)BOARD_LCD_BASE);
}

//------------------------------------------------------------------------------
/// Turn off the LCD
//------------------------------------------------------------------------------
void LCDD_Stop(void)
{
    LCD_Off((void *)BOARD_LCD_BASE);
}

//------------------------------------------------------------------------------
/// Set the backlight of the LCD.
/// \param level   Backlight brightness level [1..32], 32 is maximum level.
//------------------------------------------------------------------------------
void LCDD_SetBacklight (unsigned int level)
{
    unsigned int i;
    const Pin pPins[] = {BOARD_BACKLIGHT_PIN};

    // Enable pins
    PIO_Configure(pPins, PIO_LISTSIZE(pPins));

    // Switch off backlight
    PIO_Clear(pPins);
	vTaskDelay( 2 );

    // Set new backlight level
    for (i = 0; i < level; i++) {

        PIO_Set(pPins);
        PIO_Set(pPins);
        PIO_Set(pPins);

        PIO_Clear(pPins);
        PIO_Clear(pPins);
        PIO_Clear(pPins);
    }
    PIO_Set(pPins);
}
