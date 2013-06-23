/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems, who sell the code with commercial support,
    indemnification and middleware, under the OpenRTOS brand.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.
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
	xLEDToggleTimer = xTimerCreate(	( const int8_t * ) "LEDTmr", 	/* Just a text name to associate with the timer, useful for debugging, but not used by the kernel. */
								ledTOGGLE_RATE,						/* The period of the timer. */
								pdTRUE,								/* This timer will autoreload, so uxAutoReload is set to pdTRUE. */
								NULL,								/* The timer ID is not used, so can be set to NULL. */
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

