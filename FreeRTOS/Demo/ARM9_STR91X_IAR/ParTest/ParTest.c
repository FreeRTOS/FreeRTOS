/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Library includes. */
#include  "91x_lib.h"

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

#define partstMAX_LEDs		4
#define partstLED_PORT		*( ( unsigned short * ) 0x5800f3fc )

/*-----------------------------------------------------------*/

static GPIO_InitTypeDef GPIO9_InitStruct;

void vParTestInitialise( void )
{	
	/* Configure the bits used to flash LED's on port 9 as output. */
	GPIO_StructInit( &GPIO9_InitStruct );
	GPIO9_InitStruct.GPIO_Pin = GPIO_Pin_0 | GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3;
	GPIO9_InitStruct.GPIO_Direction = GPIO_PinOutput;
	GPIO_Init( GPIO9, &GPIO9_InitStruct );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned short usLED = 0x0001;

	if( uxLED < partstMAX_LEDs )
	{
		usLED <<= uxLED;

		portENTER_CRITICAL();
		{
			if( xValue )
			{
				partstLED_PORT &= ~usLED;
			}
			else
			{
				partstLED_PORT |= usLED;				
			}		
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned short usLED = 0x0001;

	if( uxLED < partstMAX_LEDs )
	{
		usLED <<= uxLED;

		portENTER_CRITICAL();
		{
			if( partstLED_PORT & usLED )
			{
				partstLED_PORT &= ~usLED;
			}
			else
			{
				partstLED_PORT |= usLED;			
			}	
		}
		portEXIT_CRITICAL();
	}
}




