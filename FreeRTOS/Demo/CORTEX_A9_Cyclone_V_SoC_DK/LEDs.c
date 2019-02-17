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
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

/* Altera library includes. */
#include "socal/socal.h"
#include "socal/alt_gpio.h"
#include "alt_generalpurpose_io.h"
#include "alt_address_space.h"


#define partstNUM_LEDS	4

/*-----------------------------------------------------------*/

const uint32_t ulLEDs[ partstNUM_LEDS ] = { ALT_GPIO_BIT12, ALT_GPIO_BIT13, ALT_GPIO_BIT14, ALT_GPIO_BIT15 };
const uint32_t ulAllLEDs = ALT_GPIO_BIT12 | ALT_GPIO_BIT13 | ALT_GPIO_BIT14 | ALT_GPIO_BIT15;
const uint32_t *pulPortBData = ALT_GPIO1_SWPORTA_DR_ADDR;
static uint32_t ulPortValue;

void vParTestInitialise( void )
{
	/* Set GPIO direction. */
	alt_gpio_port_datadir_set( ALT_GPIO_PORTB, ulAllLEDs, ulAllLEDs );

	/* Start with all LEDs off. */
	alt_gpio_port_data_write( ALT_GPIO_PORTB, ulAllLEDs, ulAllLEDs );
	ulPortValue = ulAllLEDs;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( UBaseType_t uxLED, BaseType_t xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if( xValue == pdFALSE )
			{
				ulPortValue |= ulLEDs[ uxLED ];
			}
			else
			{
				ulPortValue &= ~ulLEDs[ uxLED ];
			}

			alt_replbits_word( pulPortBData, ulAllLEDs, ulPortValue );
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			ulPortValue ^= ulLEDs[ uxLED ];
			alt_replbits_word( pulPortBData, ulAllLEDs, ulPortValue );
		}
		taskEXIT_CRITICAL();
	}
}



