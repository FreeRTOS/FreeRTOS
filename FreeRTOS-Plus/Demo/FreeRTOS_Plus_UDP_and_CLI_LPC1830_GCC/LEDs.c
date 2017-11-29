/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Simple LED IO functions.  LED 0 is toggled by a timer every half second. */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "timers.h"

/* Library includes. */
#include "lpc18xx_gpio.h"
#include "lpc18xx_scu.h"
#include "lpc18xx_cgu.h"

#define ledTOGGLE_RATE	( 500 / portTICK_RATE_MS )

#define ledLED0_PORT	1
#define ledLED0_BIT		( 1UL << 11UL )

#define ledLED1_PORT	2
#define ledLED1_BIT		( 1UL << 12UL )

/*
 * Toggles an LED just to show the application is running.
 */
static void prvLEDToggleTimerCallback( xTimerHandle xTimer );

/*-----------------------------------------------------------*/

void vLEDsInitialise( void )
{
static xTimerHandle xLEDToggleTimer = NULL;

	/* Set the LED pin-muxing and configure as output. */
	scu_pinmux( 0x2 , 11, MD_PUP, FUNC0 );
	scu_pinmux( 0x2 , 12, MD_PUP, FUNC0 );
	GPIO_SetDir( ledLED0_PORT, ledLED0_BIT, 1 );
	GPIO_SetDir( ledLED1_PORT, ledLED1_BIT, 1 );

    /* Create the timer used to toggle LED0. */
	xLEDToggleTimer = xTimerCreate(	"LEDTmr", 		/* Just a text name to associate with the timer, useful for debugging, but not used by the kernel. */
									ledTOGGLE_RATE,	/* The period of the timer. */
									pdTRUE,			/* This timer will autoreload, so uxAutoReload is set to pdTRUE. */
									NULL,			/* The timer ID is not used, so can be set to NULL. */
									prvLEDToggleTimerCallback );		/* The callback function executed each time the timer expires. */

    /* Sanity check that the timer was actually created. */
    configASSERT( xLEDToggleTimer );

    /* Start the timer.  If this is called before the scheduler is started then
    the block time will automatically get changed to 0 (from portMAX_DELAY). */
    xTimerStart( xLEDToggleTimer, portMAX_DELAY );
}
/*-----------------------------------------------------------*/

static void prvLEDToggleTimerCallback( xTimerHandle xTimer )
{
static uint8_t ucState = 0;

	/* Remove compiler warnings. */
	( void ) xTimer;

	/* Just toggle an LED to show the program is running. */
	if( ucState == 0 )
	{
		GPIO_SetValue( ledLED0_PORT, ledLED0_BIT );
	}
	else
	{
		GPIO_ClearValue( ledLED0_PORT, ledLED0_BIT );
	}

	ucState = !ucState;
}

