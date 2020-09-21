/*
 * FreeRTOS Kernel V10.0.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#define partstNUM_LEDs	4

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
    /* Ensure LED outputs are set to GPIO */
    MCF_GPIO_PTCPAR = MCF_GPIO_PTCPAR_DTIN3_GPIO | MCF_GPIO_PTCPAR_DTIN2_GPIO | MCF_GPIO_PTCPAR_DTIN1_GPIO | MCF_GPIO_PTCPAR_DTIN0_GPIO;

    /* Set GPIO to outputs. */
    MCF_GPIO_DDRTC = MCF_GPIO_DDRTC_DDRTC3 | MCF_GPIO_DDRTC_DDRTC2 | MCF_GPIO_DDRTC_DDRTC1 | MCF_GPIO_DDRTC_DDRTC0;

    /* Start with all LEDs off. */
	MCF_GPIO_PORTTC = 0x00;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstNUM_LEDs )
	{
		if( xValue != 0 )
		{
			taskENTER_CRITICAL();
				MCF_GPIO_PORTTC |= ( 1 << uxLED );
			taskEXIT_CRITICAL();
		}
		else
		{
			taskENTER_CRITICAL();
				MCF_GPIO_PORTTC &= ~( 1 << uxLED );
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDs )
	{
		taskENTER_CRITICAL();
		{
			if( ( MCF_GPIO_PORTTC & ( 1 << uxLED ) ) == ( unsigned char ) 0 )
			{
				MCF_GPIO_PORTTC |= ( 1 << uxLED );
			}
			else
			{
				MCF_GPIO_PORTTC &= ~( 1 << uxLED );
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxParTestGetLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxReturn = pdFALSE;

	if( uxLED < partstNUM_LEDs )
	{
		if( ( MCF_GPIO_PORTTC & ( 1 << uxLED ) ) != 0 )
		{
			uxReturn = pdTRUE;
		}
	}

	return uxReturn;
}



