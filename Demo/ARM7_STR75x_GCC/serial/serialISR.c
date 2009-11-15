/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
signed char cChar;
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


