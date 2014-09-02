/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

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
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

/* Library includes. */
#include <board.h>
#include <gpio.h>

/* The number of LEDs available to the user on the evaluation kit. */
#define partestNUM_LEDS			( 3UL )

/* One of the LEDs is wired in the inverse to the others as it is also used as
the power LED. */
#define partstsINVERTED_LED		( 0UL )

/* The index of the pins to which the LEDs are connected.  The ordering of the
LEDs in this array is intentional and matches the order they appear on the
hardware. */
static const uint32_t ulLED[] = { LED2_GPIO, LED0_GPIO, LED1_GPIO };

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned long ul;

	for( ul = 0; ul < partestNUM_LEDS; ul++ )
	{
		/* Configure the LED, before ensuring it starts in the off state. */
		gpio_configure_pin( ulLED[ ul ],  ( PIO_OUTPUT_1 | PIO_DEFAULT ) );
		vParTestSetLED( ul, pdFALSE );
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partestNUM_LEDS )
	{
		if( uxLED == partstsINVERTED_LED )
		{
			xValue = !xValue;
		}

		if( xValue != pdFALSE )
		{
			/* Turn the LED on. */
			taskENTER_CRITICAL();
			{
				gpio_set_pin_low( ulLED[ uxLED ]);
			}
			taskEXIT_CRITICAL();
		}
		else
		{
			/* Turn the LED off. */
			taskENTER_CRITICAL();
			{
				gpio_set_pin_high( ulLED[ uxLED ]);
			}
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partestNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			gpio_toggle_pin( ulLED[ uxLED ] );
		}
		taskEXIT_CRITICAL();
	}
}



