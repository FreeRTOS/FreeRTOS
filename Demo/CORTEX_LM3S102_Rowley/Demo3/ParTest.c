/*
    FreeRTOS V7.0.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/*
*/

/* Kernel include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

/* Hardware specific include files. */
#include "DriverLib.h"

static const unsigned long ulLEDs[] =
{
	GPIO_PIN_6, GPIO_PIN_1, GPIO_PIN_0
};

#define partstLED_PINS ( GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_6 )

#define partstMAX_OUTPUT_LED	( ( unsigned char ) 3 )

/*-----------------------------------------------------------*/
void vParTestInitialise( void )
{
portBASE_TYPE xLED;

	/* The LED's are on port B. */
    GPIODirModeSet( GPIO_PORTB_BASE, partstLED_PINS, GPIO_DIR_MODE_OUT );

	for( xLED = 0; xLED < partstMAX_OUTPUT_LED; xLED++ )
	{
		vParTestSetLED( xLED, pdFALSE );
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			if( xValue == pdFALSE )
			{
				GPIOPinWrite( GPIO_PORTB_BASE, ulLEDs[ uxLED ], ulLEDs[ uxLED ] );
			}
			else
			{
				GPIOPinWrite( GPIO_PORTB_BASE, ulLEDs[ uxLED ], ~ulLEDs[ uxLED ] );
			}
		}	
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
portBASE_TYPE xCurrentValue;

	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			xCurrentValue = GPIOPinRead( GPIO_PORTB_BASE, ulLEDs[ uxLED ] );
			if( xCurrentValue )
			{
				GPIOPinWrite( GPIO_PORTB_BASE, ulLEDs[ uxLED ], ~ulLEDs[ uxLED ] );
			}
			else
			{
				GPIOPinWrite( GPIO_PORTB_BASE, ulLEDs[ uxLED ], ulLEDs[ uxLED ] );
			}
		}
	}
	xTaskResumeAll();
}
