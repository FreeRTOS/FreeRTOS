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

#include <device.h>

#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"
/*---------------------------------------------------------------------------*/

#define partstMAX_LED			( 4 )
/*---------------------------------------------------------------------------*/

static volatile char cLedOutput[ partstMAX_LED ];
/*---------------------------------------------------------------------------*/

void vParTestInitialise( void )
{
long lIndex;

	for( lIndex = 0; lIndex < partstMAX_LED; lIndex++ )
	{
		cLedOutput[ lIndex ] = 0;
	}
}
/*---------------------------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	taskENTER_CRITICAL();
	{
		switch( uxLED )
		{
			case 0:
				Pin_LED_0_Write( xValue & 0x1 );
				break;
			case 1:
				Pin_LED_1_Write( xValue & 0x1 );
				break;
			case 2:
				Pin_LED_2_Write( xValue & 0x1 );
				break;
			case 3:
				Pin_LED_3_Write( xValue & 0x1 );
				break;
			default:
				/* Do nothing. */
				break;
		}
	}
	taskEXIT_CRITICAL();
	
	/* Record the output for the sake of toggling. */
	if( uxLED < partstMAX_LED )
	{
		cLedOutput[ uxLED ] = ( xValue & 0x1 );
	}
}
/*---------------------------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstMAX_LED )
	{
		vParTestSetLED( uxLED, !cLedOutput[ uxLED ] );
	}
}
/*---------------------------------------------------------------------------*/
