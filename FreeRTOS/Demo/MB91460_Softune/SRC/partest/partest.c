/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
*/


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

#define partstNUM_LEDs	8

static unsigned portCHAR sState[ partstNUM_LEDs ] = { pdFALSE };
static unsigned portCHAR sState1[ partstNUM_LEDs ] = { pdFALSE };


/*-----------------------------------------------------------*/
void vParTestInitialise( void )
{
	/* Set port for LED outputs. */
	DDR16 = 0xFF;
	DDR25 = 0xFF;

	/* Start with LEDs off. */
	PDR25 = 0x00;
	PDR16 = 0x00;
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDs )
	{
		taskENTER_CRITICAL();
		{		
			/* Toggle the state of the single genuine on board LED. */
			if( sState[ uxLED ] )
			{
				PDR25 |= ( 1 << uxLED );
			}
			else
			{
				PDR25 &= ~( 1 << uxLED );
			}
		
			sState[uxLED] = !( sState[ uxLED ] );
		}		
		taskEXIT_CRITICAL();
	}
	else
	{
		uxLED -= partstNUM_LEDs;

		if( uxLED < partstNUM_LEDs )
		{		
			taskENTER_CRITICAL();
			{		
				/* Toggle the state of the single genuine on board LED. */
				if( sState1[uxLED])	
				{
					PDR16 |= ( 1 << uxLED );
				}
				else
				{
					PDR16 &= ~( 1 << uxLED );
				}
			
				sState1[ uxLED ] = !( sState1[ uxLED ] );
			}
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* Set or clear the output [in this case show or hide the '*' character. */
	if( uxLED < partstNUM_LEDs )
	{
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				PDR25 |= ( 1 << uxLED );
				sState[ uxLED ] = 1;
			}
			else
			{
				PDR25 &= ~( 1 << uxLED );
				sState[ uxLED ] = 0;
			}
		}
		taskEXIT_CRITICAL();
	}
	else 
	{
		uxLED -= partstNUM_LEDs;

		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				PDR16 |= ( 1 << uxLED );
				sState1[ uxLED ] = 1;
			}
			else
			{
				PDR16 &= ~( 1 << uxLED );
				sState1[ uxLED ] = 0;
			}
		}
		taskEXIT_CRITICAL();
	}
}

