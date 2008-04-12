/*
	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

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

/*-----------------------------------------------------------
 * Components that can be compiled to either ARM or THUMB mode are
 * contained in serial.c  The ISR routines, which can only be compiled
 * to ARM mode, are contained in this file.
 *----------------------------------------------------------*/



/* Library includes. */
#include "75x_uart.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"

static xQueueHandle xRxedChars;
static xQueueHandle xCharsForTx;
static portBASE_TYPE volatile *pxQueueEmpty;

void vConfigureQueues( xQueueHandle xQForRx, xQueueHandle xQForTx, portBASE_TYPE volatile *pxEmptyFlag )
{
	xRxedChars = xQForRx;
	xCharsForTx = xQForTx;
	pxQueueEmpty = pxEmptyFlag;
}
/*-----------------------------------------------------------*/

void vSerialISR( void )
{
signed portCHAR cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	do
	{
		if( UART0->MIS & UART_IT_Transmit )
		{
			/* The interrupt was caused by the THR becoming empty.  Are there any
			more characters to transmit? */
			if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
			{
				/* A character was retrieved from the queue so can be sent to the
				THR now. */
				UART0->DR = cChar;
			}
			else
			{
				*pxQueueEmpty = pdTRUE;		
			}		

			UART_ClearITPendingBit( UART0, UART_IT_Transmit );
		}
	
		if( UART0->MIS & UART_IT_Receive )
		{
			/* The interrupt was caused by a character being received.  Grab the
			character from the RHR and place it in the queue of received
			characters. */
			cChar = UART0->DR;
			xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
			UART_ClearITPendingBit( UART0, UART_IT_Receive );
		}
	} while( UART0->MIS );

	/* If a task was woken by either a character being received or a character
	being transmitted then we may need to switch to another task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}


