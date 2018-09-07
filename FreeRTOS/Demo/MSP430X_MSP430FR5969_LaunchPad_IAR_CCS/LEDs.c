/*
 * FreeRTOS Kernel V10.1.1
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


/*-----------------------------------------------------------
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

/* TI includes. */
#include "driverlib.h"

/* Port/pin definitions. */
#define partstNUM_LEDS	2
const uint8_t ucPorts[ partstNUM_LEDS ] = { GPIO_PORT_P1, GPIO_PORT_P4 };
const uint16_t usPins[ partstNUM_LEDS ] = { GPIO_PIN0, GPIO_PIN6 };

/*-----------------------------------------------------------*/

void vParTestSetLED( UBaseType_t uxLED, BaseType_t xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		if( xValue == pdFALSE )
		{
			GPIO_setOutputLowOnPin( ucPorts[ uxLED ], usPins[ uxLED ] );
		}
		else
		{
			GPIO_setOutputHighOnPin( ucPorts[ uxLED ], usPins[ uxLED ] );
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( UBaseType_t uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		GPIO_toggleOutputOnPin( ucPorts[ uxLED ], usPins[ uxLED ] );
	}
}

