/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
 * Simple parallel port IO routines to flash LEDs.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Hardware includes. */
#include "msp430.h"
#include "hal_MSP-EXP430F5438.h"

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* The port used by the two LEDs is configured from halBoardInit() so
	nothing needs to be done here. */
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* Only two LEDs are provided on the hardware. */
	taskENTER_CRITICAL();
	{
		if( xValue != pdFALSE )
		{
			switch( uxLED )
			{
				case 0: LED_PORT_OUT |= LED_1;
						break;
	
				case 1: LED_PORT_OUT |= LED_2;
						break;
						
				default: /* Nothing to do here, there are only two LEDs. */
						break;
			}
		}
		else
		{
			switch( uxLED )
			{
				case 0: LED_PORT_OUT &= ~LED_1;
						break;
	
				case 1: LED_PORT_OUT &= ~LED_2;
						break;
				default: /* Nothing to do here, there are only two LEDs. */
						break;
			}
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	taskENTER_CRITICAL();
	{
		switch( uxLED )
		{
			case 0: if( ( LED_PORT_OUT & LED_1 ) == 0 )
					{
						LED_PORT_OUT |= LED_1;
					}
					else
					{
						LED_PORT_OUT &= ~LED_1;
					}
					break;

			case 1: if( ( LED_PORT_OUT & LED_2 ) == 0 )
					{
						LED_PORT_OUT |= LED_2;
					}
					else
					{
						LED_PORT_OUT &= ~LED_2;
					}
					break;
			default: /* Nothing to do here, there are only two LEDs. */
					break;
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

