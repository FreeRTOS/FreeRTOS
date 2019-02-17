/*
 * FreeRTOS Kernel V10.2.0
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
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

#define partstTOTAL_NUM_LEDs		16
#define partstNUM_LEDs_PER_DISPLAY	8

volatile unsigned char *pucDisplayOutput[ 2 ] = { ( unsigned char * ) 3, ( unsigned char * ) 5 };

void vParTestInitialise( void )
{
	/* In this case all the initialisation is performed in prvSetupHardware()
	in main.c. */	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxLEDMask = 0x01;

	if( uxLED < partstNUM_LEDs_PER_DISPLAY )
	{
		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				*pucDisplayOutput[ 0 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 0 ] |= uxLEDMask;				
			}
		}
		taskEXIT_CRITICAL();
	}
	else if( uxLED < partstTOTAL_NUM_LEDs )
	{
		uxLED -= partstNUM_LEDs_PER_DISPLAY;

		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				*pucDisplayOutput[ 1 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 1 ] |= uxLEDMask;				
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxLEDMask = 0x01;

	if( uxLED < partstNUM_LEDs_PER_DISPLAY )
	{
		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( *pucDisplayOutput[ 0 ] & uxLEDMask )
			{
				*pucDisplayOutput[ 0 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 0 ] |= uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
	else if( uxLED < partstTOTAL_NUM_LEDs )
	{
		uxLED -= partstNUM_LEDs_PER_DISPLAY;

		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( *pucDisplayOutput[ 1 ] & uxLEDMask )
			{
				*pucDisplayOutput[ 1 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 1 ] |= uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
}




