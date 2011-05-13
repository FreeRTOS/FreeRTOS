/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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




