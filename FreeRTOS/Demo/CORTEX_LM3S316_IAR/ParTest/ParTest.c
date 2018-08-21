/*
 * FreeRTOS Kernel V10.1.0
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

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/*
*/


#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#include "pdc.h"

#define partstPINS	(GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_2 | GPIO_PIN_3 Z | GPIO_PIN_4 | GPIO_PIN_5 | GPIO_PIN_6 | GPIO_PIN_7)

#define partstALL_OUTPUTS_OFF	( ( unsigned char ) 0x00 )
#define partstMAX_OUTPUT_LED	( ( unsigned char ) 8 )

static volatile unsigned char ucOutputValue = partstALL_OUTPUTS_OFF;

void vParTestInitialise( void )
{
	PDCInit();
	PDCWrite( PDC_LED, ucOutputValue );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned char ucBit = ( unsigned char ) 1;

	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			ucBit = ( ( unsigned char ) 1 ) << uxLED;

			if( xValue == pdFALSE )
			{
				ucBit ^= ( unsigned char ) 0xff;
				ucOutputValue &= ucBit;
			}
			else
			{
				ucOutputValue |= ucBit;
			}

			PDCWrite( PDC_LED, ucOutputValue );
		}	
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned char ucBit;

	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			ucBit = ( ( unsigned char ) 1 ) << uxLED;

			if( ucOutputValue & ucBit )
			{
				ucOutputValue &= ~ucBit;
			}
			else
			{
				ucOutputValue |= ucBit;
			}

			PDCWrite( PDC_LED, ucOutputValue );
		}
	}
	xTaskResumeAll();
}

