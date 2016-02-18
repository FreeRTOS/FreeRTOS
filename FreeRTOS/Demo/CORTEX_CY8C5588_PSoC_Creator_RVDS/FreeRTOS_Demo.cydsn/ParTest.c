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

#include <device.h>

#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"
/*---------------------------------------------------------------------------*/

#define partstMAX_LED			( 4 )
/*---------------------------------------------------------------------------*/

static volatile char cLedOutput[ partstMAX_LED ];
/*---------------------------------------------------------------------------*/

void vParTestInitialise( void )
{
long lIndex;

	for( lIndex = 0; lIndex < partstMAX_LED; lIndex++ )
	{
		cLedOutput[ lIndex ] = 0;
	}
}
/*---------------------------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	taskENTER_CRITICAL();
	{
		switch( uxLED )
		{
			case 0:
				Pin_LED_0_Write( xValue & 0x1 );
				break;
			case 1:
				Pin_LED_1_Write( xValue & 0x1 );
				break;
			case 2:
				Pin_LED_2_Write( xValue & 0x1 );
				break;
			case 3:
				Pin_LED_3_Write( xValue & 0x1 );
				break;
			default:
				/* Do nothing. */
				break;
		}
	}
	taskEXIT_CRITICAL();
	
	/* Record the output for the sake of toggling. */
	if( uxLED < partstMAX_LED )
	{
		cLedOutput[ uxLED ] = ( xValue & 0x1 );
	}
}
/*---------------------------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstMAX_LED )
	{
		vParTestSetLED( uxLED, !cLedOutput[ uxLED ] );
	}
}
/*---------------------------------------------------------------------------*/
