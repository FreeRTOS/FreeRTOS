/*
	FreeRTOS.org V5.0.2 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
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
portBASE_TYPE x;

	/* Set port for LED outputs. */
	DDR00 = 0xFF;
	DDR09 = 0xFF;

	/* Start with LEDs off. */
	PDR09 = 0xff;
	PDR00 = 0xff;

	for( x = 0; x < partstNUM_LEDs; x++ )
	{
		sState[ x ] = pdTRUE;
		sState1[ x ] = pdTRUE;
	}
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
				PDR09 |= ( 1 << uxLED );
			}
			else
			{
				PDR09 &= ~( 1 << uxLED );
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
					PDR00 |= ( 1 << uxLED );
				}
				else
				{
					PDR00 &= ~( 1 << uxLED );
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
				PDR09 |= ( 1 << uxLED );
				sState[ uxLED ] = 1;
			}
			else
			{
				PDR09 &= ~( 1 << uxLED );
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
				PDR00 |= ( 1 << uxLED );
				sState1[ uxLED ] = 1;
			}
			else
			{
				PDR00 &= ~( 1 << uxLED );
				sState1[ uxLED ] = 0;
			}
		}
		taskEXIT_CRITICAL();
	}
}

