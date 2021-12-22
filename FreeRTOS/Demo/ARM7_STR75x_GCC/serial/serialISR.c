/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
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

static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;
static portBASE_TYPE volatile *pxQueueEmpty;

void vConfigureQueues( QueueHandle_t xQForRx, QueueHandle_t xQForTx, portBASE_TYPE volatile *pxEmptyFlag )
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


