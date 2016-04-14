/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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
#include "misc/led.h"
#include "peripherals/pio.h"

/*------------------------------------------------------------------------------
 *         Local Variables
 *------------------------------------------------------------------------------*/

#ifdef PINS_LEDS
static const struct _pin pinsLeds[] = PINS_LEDS;

static const uint32_t numLeds = ARRAY_SIZE(pinsLeds);
#endif

/*------------------------------------------------------------------------------
 *         Global Functions
 *------------------------------------------------------------------------------*/

/**
 *  Configures the pin associated with the given LED number. If the LED does
 *  not exist on the board, the function does nothing.
 *  \param dwLed  Number of the LED to configure.
 *  \return 1 if the LED exists and has been configured; otherwise 0.
 */
extern uint32_t led_configure (uint32_t led)
{
#ifdef PINS_LEDS
	// Check that LED exists
	if (led >= numLeds) {
		return 0;
	}
	// Configure LED
	return pio_configure(&pinsLeds[led], 1);
#else
	return 0;
#endif
}

/**
 *  Turns the given LED on if it exists; otherwise does nothing.
 *  \param dwLed  Number of the LED to turn on.
 *  \return 1 if the LED has been turned on; 0 otherwise.
 */
extern uint32_t led_set(uint32_t led)
{
#ifdef PINS_LEDS
	/* Check if LED exists */
	if (led >= numLeds) {
		return 0;
	}

	/* Turn LED on */
	if (pinsLeds[led].type == PIO_OUTPUT_0) {
		pio_set(&pinsLeds[led]);
	} else {
		pio_clear(&pinsLeds[led]);
	}
	return 1;
#else
	return 0;
#endif
}

/**
 *  Turns a LED off.
 *
 *  \param dwLed  Number of the LED to turn off.
 *  \return 1 if the LED has been turned off; 0 otherwise.
 */
extern uint32_t led_clear (uint32_t led)
{
#ifdef PINS_LEDS
	/* Check if LED exists */
	if (led >= numLeds) {
		return 0;
	}
	/* Turn LED off */
	if (pinsLeds[led].type == PIO_OUTPUT_0) {
		pio_clear(&pinsLeds[led]);
	} else {
		pio_set(&pinsLeds[led]);
	}
	return 1;
#else
	return 0;
#endif
}

/**
 *  Toggles the current state of a LED.
 *
 *  \param dwLed  Number of the LED to toggle.
 *  \return 1 if the LED has been toggled; otherwise 0.
 */
extern uint32_t led_toggle(uint32_t led)
{
#ifdef PINS_LEDS
	/* Check if LED exists */
	if (led >= numLeds) {
		return 0;
	}
	/* Toggle LED */
	if (pio_get_output_data_status(&pinsLeds[led])) {
		pio_clear(&pinsLeds[led]);
	} else {
		pio_set(&pinsLeds[led]);
	}
	return 1;
#else
	return 0;
#endif
}
