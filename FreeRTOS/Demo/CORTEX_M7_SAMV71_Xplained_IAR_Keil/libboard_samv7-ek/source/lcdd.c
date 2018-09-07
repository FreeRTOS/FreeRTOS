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
 * LCD on/off and LCD backlight control.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initializes the LCD controller.
 * Configure SMC to access LCD controller at 64MHz MCK.
 */
extern void LCDD_Initialize( void )
{
    
    /* Initialize LCD controller */
    ILI9488_Initialize() ;

    /* Initialize LCD controller */
    ILI9488_SetDisplayPortrait( 0 ) ;

    /* Set LCD backlight */
    LCDD_SetBacklight( 16 ) ;
}

/**
 * \brief Turn on the LCD.
 */
void LCDD_On(void)
{
    ILI9488_On();
}

/**
 * \brief Turn off the LCD.
 */
void LCDD_Off(void)
{
    ILI9488_Off();
}

/**
 * \brief Set the backlight of the LCD.
 *
 * \param level   Backlight brightness level [1..16], 1 means maximum brightness.
 */
void LCDD_SetBacklight (uint32_t level)
{
    
    /* Ensure valid level */
    level = (level < 1) ? 1 : level;
    level = (level > 16) ? 16 : level;

   PWMC_SetDutyCycle(PWM0, CHANNEL_PWM_LCD, level);
}
