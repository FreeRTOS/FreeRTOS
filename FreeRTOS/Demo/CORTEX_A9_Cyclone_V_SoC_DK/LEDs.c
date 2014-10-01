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

/* Altera library includes. */
#include "socal/socal.h"
#include "socal/alt_gpio.h"
#include "alt_generalpurpose_io.h"
#include "alt_address_space.h"


#define partstNUM_LEDS	4

/*-----------------------------------------------------------*/

const uint32_t ulLEDs[ partstNUM_LEDS ] = { ALT_GPIO_BIT12, ALT_GPIO_BIT13, ALT_GPIO_BIT14, ALT_GPIO_BIT15 };
const uint32_t ulAllLEDs = ALT_GPIO_BIT12 | ALT_GPIO_BIT13 | ALT_GPIO_BIT14 | ALT_GPIO_BIT15;
const uint32_t *pulPortBData = ALT_GPIO1_SWPORTA_DR_ADDR;
static uint32_t ulPortValue;

void vParTestInitialise( void )
{
	/* Set GPIO direction. */
	alt_gpio_port_datadir_set( ALT_GPIO_PORTB, ulAllLEDs, ulAllLEDs );

	/* Start with all LEDs off. */
	alt_gpio_port_data_write( ALT_GPIO_PORTB, ulAllLEDs, ulAllLEDs );
	ulPortValue = ulAllLEDs;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( UBaseType_t uxLED, BaseType_t xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if( xValue == pdFALSE )
			{
				ulPortValue |= ulLEDs[ uxLED ];
			}
			else
			{
				ulPortValue &= ~ulLEDs[ uxLED ];
			}

			alt_replbits_word( pulPortBData, ulAllLEDs, ulPortValue );
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			ulPortValue ^= ulLEDs[ uxLED ];
			alt_replbits_word( pulPortBData, ulAllLEDs, ulPortValue );
		}
		taskEXIT_CRITICAL();
	}
}



