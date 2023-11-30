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

/*
    Title: LED implementation

    About: Purpose
        Implementation of LED-related functionalities.
*/

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "led.h"
#include <board.h>
#include <pio/pio.h>

//------------------------------------------------------------------------------
//         Internal variables
//------------------------------------------------------------------------------

#ifdef PINS_LEDS
static const Pin pinsLeds[] = {PINS_LEDS};
static const unsigned int numLeds = PIO_LISTSIZE(pinsLeds);
#endif

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
/*
    Function: LED_Configure
        Configures the pin associated with the given LED number.

    Parameters:
        led - Number of the LED to configure.

    Returns:
        1 if the LED exists and has been configured; otherwise 0.
*/
unsigned char LED_Configure(unsigned int led)
{
#ifdef PINS_LEDS
    // Check that LED exists
    if (led >= numLeds) {

        return 0;
    }

    // Configure LED
    return (PIO_Configure(&pinsLeds[led], 1));
#else
    return 0;
#endif
}

/*
    Function: LED_Set
        Turns a LED on.

    Parameters:
        led - Number of the LED to turn on.

    Returns:
        1 if the LED has been turned on; 0 otherwise.
*/
unsigned char LED_Set(unsigned int led)
{
#ifdef PINS_LEDS
    // Check if LED exists
    if (led >= numLeds) {

        return 0;
    }

    // Turn LED on
    if (pinsLeds[led].type == PIO_OUTPUT_0) {

        PIO_Set(&pinsLeds[led]);
    }
    else {

        PIO_Clear(&pinsLeds[led]);
    }

    return 1;
#else
    return 0;
#endif
}

/*
    Function: LED_Clear
        Turns a LED off.

    Parameters:
        led - Number of the LED to turn off.

    Returns:
        1 if the LED has been turned off; 0 otherwise.
*/
unsigned char LED_Clear(unsigned int led)
{
#ifdef PINS_LEDS
    // Check if LED exists
    if (led >= numLeds) {

        return 0;
    }

    // Turn LED off
    if (pinsLeds[led].type == PIO_OUTPUT_0) {

        PIO_Clear(&pinsLeds[led]);
    }
    else {

        PIO_Set(&pinsLeds[led]);
    }

    return 1;
#else
    return 0;
#endif
}

/*
    Function: LED_Toggle
        Toggles the current state of a LED.

    Parameters:
        led - Number of the LED to toggle.

    Returns:
        1 if the LED has been toggled; otherwise 0.
*/
unsigned char LED_Toggle(unsigned int led)
{
#ifdef PINS_LEDS
    // Check if LED exists
    if (led >= numLeds) {

        return 0;
    }

    // Toggle LED
    if (PIO_GetOutputDataStatus(&pinsLeds[led])) {

        PIO_Clear(&pinsLeds[led]);
    }
    else {

        PIO_Set(&pinsLeds[led]);
    }

    return 1;
#else
    return 0;
#endif
}

