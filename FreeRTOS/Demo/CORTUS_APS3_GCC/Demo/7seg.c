/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
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


