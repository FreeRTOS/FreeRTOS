/*
	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
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

