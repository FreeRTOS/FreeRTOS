/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

#define partestNUM_LEDS ( 4 )

long lParTestGetLEDState( unsigned long ulLED );

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Port pin configuration is done by the low level set up prior to this
	function being called. */
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed long xValue )
{
	if( ulLED < partestNUM_LEDS )
	{
		if( xValue != 0 )
		{
			/* Turn the LED on. */
			taskENTER_CRITICAL();
			{
				switch( ulLED )
				{
					case 0:	LED0 = LED_ON;
							break;
					case 1:	LED1 = LED_ON;
							break;
					case 2:	LED2 = LED_ON;
							break;
					case 3:	LED3 = LED_ON;
							break;
				}
			}
			taskEXIT_CRITICAL();
		}
		else
		{
			/* Turn the LED off. */
			taskENTER_CRITICAL();
			{
				switch( ulLED )
				{
					case 0:	LED0 = LED_OFF;
							break;
					case 1:	LED1 = LED_OFF;
							break;
					case 2:	LED2 = LED_OFF;
							break;
					case 3:	LED3 = LED_OFF;
							break;
				}

			}
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
	if( ulLED < partestNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if( lParTestGetLEDState( ulLED ) != 0x00 )
			{
				vParTestSetLED( ulLED, 0 );
			}
			else
			{
				vParTestSetLED( ulLED, 1 );
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

long lParTestGetLEDState( unsigned long ulLED )
{
long lReturn = pdTRUE;

	if( ulLED < partestNUM_LEDS )
	{
		switch( ulLED )
		{
			case 0	:	if( LED0 != 0 )
						{
							lReturn =  pdFALSE;
						}
						break;
			case 1	:	if( LED1 != 0 )
						{
							lReturn =  pdFALSE;
						}
						break;
			case 2	:	if( LED2 != 0 )
						{
							lReturn =  pdFALSE;
						}
						break;
			case 3	:	if( LED3 != 0 )
						{
							lReturn =  pdFALSE;
						}
						break;
		}
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

