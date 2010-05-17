/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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
	xTaskCreate( prvRefreshTask, ( signed char * ) "7SegRefresh", x7segSTACK_SIZE, NULL, uxPriority, ( xTaskHandle *) NULL );
	xTaskCreate( prvCountTask,   ( signed char * ) "7SegCount",	x7segSTACK_SIZE, NULL, uxPriority, ( xTaskHandle *) NULL );
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

portTickType xRefreshRate, xLastRefreshTime;

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
portTickType xCountRate, xLastCountTime;

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


