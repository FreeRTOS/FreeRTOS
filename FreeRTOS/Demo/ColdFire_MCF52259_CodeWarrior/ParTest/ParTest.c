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

/*
	Changes from V2.5.2

	+ All LED's are turned off to start.
*/


#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#define partstNUM_LEDs	4

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
    /* Enable signals as GPIO */
    MCF_GPIO_PTCPAR = 0
        | MCF_GPIO_PTCPAR_DTIN3_GPIO
        | MCF_GPIO_PTCPAR_DTIN2_GPIO
        | MCF_GPIO_PTCPAR_DTIN1_GPIO
        | MCF_GPIO_PTCPAR_DTIN0_GPIO;
    
    /* Enable signals as digital outputs */
    MCF_GPIO_DDRTC = 0
        | MCF_GPIO_DDRTC_DDRTC3
        | MCF_GPIO_DDRTC_DDRTC2
        | MCF_GPIO_DDRTC_DDRTC1
        | MCF_GPIO_DDRTC_DDRTC0;

	MCF_GPIO_PORTTC = 0x00; // TURN LEDS OFF
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxLEDMask;

	if( uxLED < partstNUM_LEDs )
	{
		uxLEDMask = 1UL << uxLED;
		
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				MCF_GPIO_PORTTC |= uxLEDMask;
			}
			else
			{
				MCF_GPIO_PORTTC &= ~uxLEDMask;
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
		uxLEDMask = 1UL << uxLED;
		
		taskENTER_CRITICAL();
		{
			if( MCF_GPIO_PORTTC & uxLEDMask )
			{
				MCF_GPIO_PORTTC &= ~uxLEDMask;
			}
			else
			{
				MCF_GPIO_PORTTC |= uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
}

