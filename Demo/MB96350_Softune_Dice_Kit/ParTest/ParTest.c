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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

#define partstTOTAL_NUM_LEDs		16
#define partstNUM_LEDs_PER_DISPLAY	8

volatile unsigned char *pucDisplayOutput[ 2 ] = { ( unsigned portCHAR * ) 3, ( unsigned portCHAR * ) 5 };

void vParTestInitialise( void )
{
	/* In this case all the initialisation is performed in prvSetupHardware()
	in main.c. */	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxLEDMask = 0x01;

	if( uxLED < partstNUM_LEDs_PER_DISPLAY )
	{
		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				*pucDisplayOutput[ 0 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 0 ] |= uxLEDMask;				
			}
		}
		taskEXIT_CRITICAL();
	}
	else if( uxLED < partstTOTAL_NUM_LEDs )
	{
		uxLED -= partstNUM_LEDs_PER_DISPLAY;

		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				*pucDisplayOutput[ 1 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 1 ] |= uxLEDMask;				
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxLEDMask = 0x01;

	if( uxLED < partstNUM_LEDs_PER_DISPLAY )
	{
		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( *pucDisplayOutput[ 0 ] & uxLEDMask )
			{
				*pucDisplayOutput[ 0 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 0 ] |= uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
	else if( uxLED < partstTOTAL_NUM_LEDs )
	{
		uxLED -= partstNUM_LEDs_PER_DISPLAY;

		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( *pucDisplayOutput[ 1 ] & uxLEDMask )
			{
				*pucDisplayOutput[ 1 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 1 ] |= uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
}




