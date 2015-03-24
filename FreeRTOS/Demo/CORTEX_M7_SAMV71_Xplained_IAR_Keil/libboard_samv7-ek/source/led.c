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
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "board.h"

/*------------------------------------------------------------------------------
 *         Local Variables
 *------------------------------------------------------------------------------*/

#ifdef PINS_LEDS
static const Pin pinsLeds[] = {PIN_LED_0, PIN_LED_1} ;
static const uint32_t numLeds = PIO_LISTSIZE( pinsLeds ) ;
#endif

/*------------------------------------------------------------------------------
 *         Global Functions
 *------------------------------------------------------------------------------*/

/**
 *  Configures the pin associated with the given LED number. If the LED does
 *  not exist on the board, the function does nothing.
 *  \param led  Number of the LED to configure.
 *  \return 1 if the LED exists and has been configured; otherwise 0.
 */
extern uint32_t LED_Configure( uint32_t dwLed )
{
#ifdef PINS_LEDS
    // Check that LED exists
    if ( dwLed >= numLeds)
    {

        return 0;
    }

    // Configure LED
    return ( PIO_Configure( &pinsLeds[dwLed], 1 ) ) ;
#else
    return 0 ;
#endif
}

/**
 *  Turns the given LED on if it exists; otherwise does nothing.
 *  \param led  Number of the LED to turn on.
 *  \return 1 if the LED has been turned on; 0 otherwise.
 */
extern uint32_t LED_Set( uint32_t dwLed )
{
#ifdef PINS_LEDS
    /* Check if LED exists */
    if ( dwLed >= numLeds )
    {
        return 0 ;
    }

    /* Turn LED on */
    if ( pinsLeds[dwLed].type == PIO_OUTPUT_0 )
    {

        PIO_Set( &pinsLeds[dwLed] ) ;
    }
    else
    {
        PIO_Clear( &pinsLeds[dwLed] ) ;
    }

    return 1 ;
#else
    return 0 ;
#endif
}

/**
 *  Turns a LED off.
 *
 *  \param led  Number of the LED to turn off.
 *  \return 1 if the LED has been turned off; 0 otherwise.
 */
extern uint32_t LED_Clear( uint32_t dwLed )
{
#ifdef PINS_LEDS
    /* Check if LED exists */
    if ( dwLed >= numLeds )
    {
        return 0 ;
    }

    /* Turn LED off */
    if ( pinsLeds[dwLed].type == PIO_OUTPUT_0 )
    {
        PIO_Clear( &pinsLeds[dwLed] ) ;
    }
    else
    {
        PIO_Set( &pinsLeds[dwLed] ) ;
    }

    return 1 ;
#else
    return 0 ;
#endif
}

/**
 *  Toggles the current state of a LED.
 *
 *  \param led  Number of the LED to toggle.
 *  \return 1 if the LED has been toggled; otherwise 0.
 */
extern uint32_t LED_Toggle( uint32_t dwLed )
{
#ifdef PINS_LEDS
    /* Check if LED exists */
    if ( dwLed >= numLeds )
    {
        return 0 ;
    }

    /* Toggle LED */
    if ( PIO_GetOutputDataStatus( &pinsLeds[dwLed] ) )
    {
        PIO_Clear( &pinsLeds[dwLed] ) ;
    }
    else
    {
        PIO_Set( &pinsLeds[dwLed] ) ;
    }

    return 1 ;
#else
    return 0 ;
#endif
}

