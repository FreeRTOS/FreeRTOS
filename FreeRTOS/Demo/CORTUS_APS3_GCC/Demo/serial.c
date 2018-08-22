/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*  Basic interrupt driven serial port driver for uart1.
*/

/* Standard includes. */
#include <stdlib.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include <machine/uart.h>
#include <machine/ic.h>
#include "serial.h"
/*-----------------------------------------------------------*/

#define comBLOCK_RETRY_TIME				10
/*-----------------------------------------------------------*/

/* The interrupt handlers are naked functions that call C handlers.  The C
handlers are marked as noinline to ensure they work correctly when the
optimiser is on. */
void interrupt5_handler( void ) __attribute__((naked));
static void prvTxHandler( void ) __attribute__((noinline));
void interrupt6_handler( void ) __attribute__((naked));
static void prvRxHandler( void ) __attribute__((noinline));

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;
/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	if( ( xRxedChars ) && ( xCharsForTx ) )
	{
		/* Set up interrupts */
		/* tx interrupt will be enabled when we need to send something */
		uart1->tx_mask = 0;
		uart1->rx_mask = 1;
		irq[IRQ_UART1_TX].ien = 1;
		irq[IRQ_UART1_RX].ien = 1;
	}

	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* The port handle is not required as this driver only supports uart1. */
	(void) pxPort;

	/* Get the next character from the buffer.	Return false if no characters
	   are available, or arrive before xBlockTime expires. */
	if( xQueueReceive( xRxedChars, pcRxedChar, xBlockTime ) )
	{
		return pdTRUE;
	}
	else
	{
		return pdFALSE;
	}
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
	int i;
	signed char *pChNext;

	/* Send each character in the string, one at a time. */
	pChNext = ( signed char * )pcString;
	for( i = 0; i < usStringLength; i++ )
	{
		/* Block until character has been transmitted. */
		while( xSerialPutChar( pxPort, *pChNext, comBLOCK_RETRY_TIME ) != pdTRUE ); pChNext++;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
	( void ) pxPort;

	/* Place the character in the queue of characters to be transmitted. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* Turn on the Tx interrupt so the ISR will remove the character from the
	   queue and send it. This does not need to be in a critical section as
	   if the interrupt has already removed the character the next interrupt
	   will simply turn off the Tx interrupt again. */
	uart1->tx_mask = 1;

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/

/* UART Tx interrupt handler. */
void interrupt5_handler( void )
{
	/* This is a naked function. */
	portSAVE_CONTEXT();
	prvTxHandler();
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

static void prvTxHandler( void )
{
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* The interrupt was caused by the transmit fifo having space for at least one
	character. Are there any more characters to transmit? */
	if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
	{
		/* A character was retrieved from the queue so can be sent to the uart now. */
		uart1->tx_data = cChar;
	}
	else
	{
		/* Queue empty, nothing to send so turn off the Tx interrupt. */
		uart1->tx_mask = 0;
	}

	/* If an event caused a task to unblock then we call "Yield from ISR" to
	ensure that the unblocked task is the task that executes when the interrupt
	completes if the unblocked task has a priority higher than the interrupted
	task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

/* UART Rx interrupt. */
void interrupt6_handler( void )
{
	portSAVE_CONTEXT();
	prvRxHandler();
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

static void prvRxHandler( void )
{
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* The interrupt was caused by the receiver getting data. */
	cChar = uart1->rx_data;

	xQueueSendFromISR(xRxedChars, &cChar, &xHigherPriorityTaskWoken );

	/* If an event caused a task to unblock then we call "Yield from ISR" to
	ensure that the unblocked task is the task that executes when the interrupt
	completes if the unblocked task has a priority higher than the interrupted
	task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/


