/*
    FreeRTOS V8.2.0 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

	***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
	***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
	the FAQ page "My application does not run, what could be wrong?".  Have you
	defined configASSERT()?

	http://www.FreeRTOS.org/support - In return for receiving this top quality
	embedded software for free we request you assist our global community by
	participating in the support forum.

	http://www.FreeRTOS.org/training - Investing in training allows your team to
	be as productive as possible as early as possible.  Now you can receive
	FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
	Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "7seg.h"
#include "demoGpio.h"

#define x7segSTACK_SIZE			configMINIMAL_STACK_SIZE

static void prvRefreshTask( void *pvParameters );
static void prvCountTask( void *pvParameters );

/* Value to output to 7 segment display
led_digits[0] is the right most digit */
static signed char seg7_digits[4];

void vStart7SegTasks( unsigned portBASE_TYPE uxPriority )
{
	xTaskCreate( prvRefreshTask, "7SegRefresh", x7segSTACK_SIZE, NULL, uxPriority, ( TaskHandle_t *) NULL );
	xTaskCreate( prvCountTask, "7SegCount",	x7segSTACK_SIZE, NULL, uxPriority, ( TaskHandle_t *) NULL );
}
/*-----------------------------------------------------------*/

static void prvRefreshTask( void *pvParameters )
{
/* This is table 3.3 from the Spartan-3 Starter Kit board user guide */
const unsigned char bits[ 16 ] =
{
	0x01,
	0x4f,
	0x12,
	0x06,
	0x4c,
	0x24,
	0x20,
	0x0f,
	0x00,
	0x04,
	0x08,
	0x60,
	0x31,
	0x42,
	0x30,
	0x38
};

const unsigned char apsx[4] =
{
	0x06, /* 3 */
	0x24, /* S */
	0x18, /* P */
	0x08  /* A */
};

TickType_t xRefreshRate, xLastRefreshTime;

/* Digit to scan */
static int d = 0;

	xRefreshRate = 2;

	/* We need to initialise xLastRefreshTime prior to the first call to
	vTaskDelayUntil(). */
	xLastRefreshTime = xTaskGetTickCount();

	for (;;)
	{
		for( d = 0; d < 4; d++ )
		{
			vTaskDelayUntil ( &xLastRefreshTime, xRefreshRate );

			/* Display digit */
			gpio->out.an  = -1;
			if( ( seg7_digits[ 1 ] == 4 ) || ( seg7_digits[ 1 ] == 5 ) )
			{
				gpio->out.digit = apsx[ d ];
			}
			else
			{
				gpio->out.digit = bits[ seg7_digits[ d ] ];
			}

			gpio->out.dp = 1;
			gpio->out.an  = ~(1 << d);
		}
	}
}
/*-----------------------------------------------------------*/

static void prvCountTask( void *pvParameters )
{
TickType_t xCountRate, xLastCountTime;

	/* Approximately 20HZ */
	xCountRate = configTICK_RATE_HZ / 20;

	/* We need to initialise xLastCountTime prior to the first call to
	vTaskDelayUntil(). */
	xLastCountTime = xTaskGetTickCount();

	for (;;)
	{
		vTaskDelayUntil( &xLastCountTime, xCountRate );

		/* Really ugly way to do BCD arithmetic.... */
		seg7_digits[ 0 ] -= 1;
		if( seg7_digits[ 0 ] < 0 )
		{
			seg7_digits[ 0 ] = 9;
			seg7_digits[ 1 ] -= 1;
			if( seg7_digits[ 1 ] < 0 )
			{
				seg7_digits[ 1 ] = 9;
				seg7_digits[ 2 ] -= 1;
				if( seg7_digits[ 2 ] < 0 )
				{
					seg7_digits[ 2 ] = 9;
					seg7_digits[ 3 ] -= 1;
					if( seg7_digits[ 3 ] < 0 )
					{
						seg7_digits[ 3 ] = 9;
					}
				}
			}
		}
	}
}


