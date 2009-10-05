/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it    under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation and modified by the FreeRTOS exception.
    **NOTE** The exception to the GPL is included to allow you to distribute a
    combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    Alternative commercial license and support terms are also available upon
    request.  See the licensing section of http://www.FreeRTOS.org for full
    license details.

    FreeRTOS is distributed in the hope that it will be useful,    but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details.

    You should have received a copy of the GNU General Public License along
    with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
    Temple Place, Suite 330, Boston, MA  02111-1307  USA.


    ***************************************************************************
    *                                                                         *
    * The FreeRTOS eBook and reference manual are available to purchase for a *
    * small fee. Help yourself get started quickly while also helping the     *
    * FreeRTOS project! See http://www.FreeRTOS.org/Documentation for details *
    *                                                                         *
    ***************************************************************************

    1 tab == 4 spaces!

    Please ensure to read the configuration and relevant port sections of the
    online documentation.

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


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo app includes. */
#include "system.h"
#include "altera_avalon_pio_regs.h"
#include "partest.h"

/*---------------------------------------------------------------------------*/

#define partstNUM_LEDS			( 8 )

/*---------------------------------------------------------------------------*/

static unsigned long ulLedStates;

/*---------------------------------------------------------------------------*/

void vParTestInitialise( void )
{
	IOWR_ALTERA_AVALON_PIO_DIRECTION( LED_PIO_BASE, ALTERA_AVALON_PIO_DIRECTION_OUTPUT );
	ulLedStates = 0;    
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if ( xValue > 0 )
			{
				ulLedStates |= 1 << uxLED;
			}
			else
			{
				ulLedStates &= ~( 1 << uxLED );
			}
			IOWR_ALTERA_AVALON_PIO_DATA( LED_PIO_BASE, ulLedStates );
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			vParTestSetLED( uxLED, !( ulLedStates & ( 1 << uxLED ) ) );
		}	
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/
