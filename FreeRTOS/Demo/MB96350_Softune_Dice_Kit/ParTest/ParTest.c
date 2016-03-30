/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
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
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

#define partstTOTAL_NUM_LEDs		16
#define partstNUM_LEDs_PER_DISPLAY	8

volatile unsigned char *pucDisplayOutput[ 2 ] = { ( unsigned char * ) 3, ( unsigned char * ) 5 };

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




