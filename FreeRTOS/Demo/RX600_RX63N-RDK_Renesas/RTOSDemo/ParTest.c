/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#define partestNUM_LEDS ( 4 )

long lParTestGetLEDState( unsigned long ulLED );

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Port pin configuration is done by the low level set up prior to this 
	function being called. */
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed long xValue )
{
	if( ulLED < partestNUM_LEDS )
	{
		if( xValue != 0 )
		{
			/* Turn the LED on. */
			taskENTER_CRITICAL();
			{
				switch( ulLED )
				{
					case 0:	LED4 = LED_ON;
							break;
					case 1:	LED5 = LED_ON;
							break;
					case 2:	LED6 = LED_ON;
							break;
					case 3:	LED7 = LED_ON;
							break;
				}
			}
			taskEXIT_CRITICAL();
		}
		else
		{
			/* Turn the LED off. */
			taskENTER_CRITICAL();
			{
				switch( ulLED )
				{
					case 0:	LED4 = LED_OFF;
							break;
					case 1:	LED5 = LED_OFF;
							break;
					case 2:	LED6 = LED_OFF;
							break;
					case 3:	LED7 = LED_OFF;
							break;
				}

			}
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
	if( ulLED < partestNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if( lParTestGetLEDState( ulLED ) != 0x00 )
			{
				vParTestSetLED( ulLED, 0 );
			}
			else
			{
				vParTestSetLED( ulLED, 1 );
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/
							
long lParTestGetLEDState( unsigned long ulLED )
{
long lReturn = pdTRUE;

	if( ulLED < partestNUM_LEDS )
	{
		switch( ulLED )
		{
			case 0	:	if( LED4 != 0 )
						{
							lReturn =  pdFALSE;
						}
						break;					
			case 1	:	if( LED5 != 0 )
						{
							lReturn =  pdFALSE;
						}
						break;					
			case 2	:	if( LED6 != 0 )
						{
							lReturn =  pdFALSE;
						}
						break;					
			case 3	:	if( LED7 != 0 )
						{
							lReturn =  pdFALSE;
						}
						break;					
		}
	}
	
	return lReturn;
}
/*-----------------------------------------------------------*/

							