/*
    FreeRTOS V7.5.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

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

/* Hardware specifics. */
#include <iodefine.h>

#define partestNUM_LEDS ( 12 )

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
					case 0:	LED4 = LED_ON;
							break;
					case 1:	LED5 = LED_ON;
							break;
					case 2:	LED6 = LED_ON;
							break;
					case 3:	LED7 = LED_ON;
							break;
					case 4:	LED8 = LED_ON;
							break;
					case 5:	LED9 = LED_ON;
							break;
					case 6:	LED10 = LED_ON;
							break;
					case 7:	LED11 = LED_ON;
							break;
					case 8:	LED12 = LED_ON;
							break;
					case 9:	LED13 = LED_ON;
							break;
					case 10:LED14 = LED_ON;
							break;
					case 11:LED15 = LED_ON;
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
					case 0:	LED4 = LED_OFF;
							break;
					case 1:	LED5 = LED_OFF;
							break;
					case 2:	LED6 = LED_OFF;
							break;
					case 3:	LED7 = LED_OFF;
							break;
					case 4:	LED8 = LED_OFF;
							break;
					case 5:	LED9 = LED_OFF;
							break;
					case 6:	LED10 = LED_OFF;
							break;
					case 7:	LED11 = LED_OFF;
							break;
					case 8:	LED12 = LED_OFF;
							break;
					case 9:	LED13 = LED_OFF;
							break;
					case 10:LED14 = LED_OFF;
							break;
					case 11:LED15 = LED_OFF;
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
long lReturn = pdFALSE;

	if( ulLED < partestNUM_LEDS )
	{
		switch( ulLED )
		{
			case 0	:	if( LED4 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 1	:	if( LED5 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 2	:	if( LED6 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 3	:	if( LED7 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 4	:	if( LED8 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 5	:	if( LED9 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 6	:	if( LED10 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 7	:	if( LED11 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 8	:	if( LED12 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 9	:	if( LED13 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 10	:	if( LED14 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
			case 11	:	if( LED15 != LED_OFF )
						{
							lReturn =  pdTRUE;
						}
						break;
		}
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

