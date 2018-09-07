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
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

#define partstNUM_LEDs	4

#define LED0_MASK		( ( unsigned short ) 0x08 )
#define LED1_MASK		( ( unsigned short ) 0x10 )
#define LED2_MASK		( ( unsigned short ) 0x40 )
#define LED3_MASK		( ( unsigned short ) 0x80 )

static const unsigned short xLEDs[ partstNUM_LEDs ] = { LED0_MASK, LED1_MASK, LED2_MASK, LED3_MASK };



void vParTestInitialise( void )
{
	/* Set GPIO to output. */
	PM3 &= ~( LED0_MASK | LED1_MASK | LED2_MASK | LED3_MASK );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxLEDMask;

	if( uxLED < partstNUM_LEDs )
	{
		uxLEDMask = xLEDs[ uxLED ];
		
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				P3 |= uxLEDMask;
			}
			else
			{
				P3 &= ~uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxLEDMask;

	if( uxLED < partstNUM_LEDs )
	{
		uxLEDMask = xLEDs[ uxLED ];
		
		taskENTER_CRITICAL();
		{
			if( P3 & uxLEDMask )
			{
				P3 &= ~uxLEDMask;
			}
			else
			{
				P3 |= uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
}

