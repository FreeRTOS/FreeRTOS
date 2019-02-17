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

/* Library includes. */
#include "75x_GPIO.h"
#include "75x_map.h"

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines for the LED's 
 *-----------------------------------------------------------*/

#define partstNUM_LEDS	4

typedef struct GPIOMAP
{
	GPIO_TypeDef	*pxPort;
	unsigned long ulPin;
	unsigned long ulValue;
} GPIO_MAP;

static GPIO_MAP xLEDMap[ partstNUM_LEDS ] =
{
	{ ( GPIO_TypeDef	* )GPIO1_BASE, GPIO_Pin_1, 0UL },
	{ ( GPIO_TypeDef	* )GPIO0_BASE, GPIO_Pin_16, 0UL },
	{ ( GPIO_TypeDef	* )GPIO2_BASE, GPIO_Pin_18, 0UL },	
	{ ( GPIO_TypeDef	* )GPIO2_BASE, GPIO_Pin_19, 0UL }	
};

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{	
GPIO_InitTypeDef GPIO_InitStructure ;

    /* Configure the bits used to flash LED's on port 1 as output. */

	/* Configure LED3 */
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
	GPIO_InitStructure.GPIO_Pin = GPIO_Pin_16;
	GPIO_Init(GPIO0,&GPIO_InitStructure);

	/* Configure LED2 */
	GPIO_InitStructure.GPIO_Pin = GPIO_Pin_1;
	GPIO_Init(GPIO1, &GPIO_InitStructure);

	/* Configure LED4 and LED5 */
	GPIO_InitStructure.GPIO_Pin = GPIO_Pin_18 | GPIO_Pin_19;
	GPIO_Init(GPIO2, &GPIO_InitStructure);

	vParTestSetLED( 0, 0 );
	vParTestSetLED( 1, 0 );
	vParTestSetLED( 2, 0 );
	vParTestSetLED( 3, 0 );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		portENTER_CRITICAL();
		{
			if( xValue )
			{
				GPIO_WriteBit( xLEDMap[ uxLED ].pxPort, xLEDMap[ uxLED ].ulPin, Bit_RESET );
				xLEDMap[ uxLED ].ulValue = 0;
			}
			else
			{
				GPIO_WriteBit( xLEDMap[ uxLED ].pxPort, xLEDMap[ uxLED ].ulPin, Bit_SET );
				xLEDMap[ uxLED ].ulValue = 1;			
			}
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		portENTER_CRITICAL();
		{
			if( xLEDMap[ uxLED ].ulValue == 1 )
			{
				GPIO_WriteBit( xLEDMap[ uxLED ].pxPort, xLEDMap[ uxLED ].ulPin, Bit_RESET );
				xLEDMap[ uxLED ].ulValue = 0;
			}
			else
			{
				GPIO_WriteBit( xLEDMap[ uxLED ].pxPort, xLEDMap[ uxLED ].ulPin, Bit_SET );
				xLEDMap[ uxLED ].ulValue = 1;			
			}
		}
		portEXIT_CRITICAL();
	}
}




