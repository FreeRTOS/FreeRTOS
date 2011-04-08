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
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

/* Hardware specifics. */
#include "iodefine.h"

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

