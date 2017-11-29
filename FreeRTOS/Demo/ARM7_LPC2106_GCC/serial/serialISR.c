/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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


/* 
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART0. 

	This file contains all the serial port components that must be compiled
	to ARM mode.  The components that can be compiled to either ARM or THUMB
	mode are contained in serial.c.

*/

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

/*-----------------------------------------------------------*/

/* Constant to access the VIC. */
#define serCLEAR_VIC_INTERRUPT			( ( unsigned long ) 0 )

/* Constants to determine the ISR source. */
#define serSOURCE_THRE					( ( unsigned char ) 0x02 )
#define serSOURCE_RX_TIMEOUT			( ( unsigned char ) 0x0c )
#define serSOURCE_ERROR					( ( unsigned char ) 0x06 )
#define serSOURCE_RX					( ( unsigned char ) 0x04 )
#define serINTERRUPT_SOURCE_MASK		( ( unsigned char ) 0x0f )

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx; 
static volatile long lTHREEmpty;

/*-----------------------------------------------------------*/

/* 
 * The queues are created in serialISR.c as they are used from the ISR.
 * Obtain references to the queues and THRE Empty flag. 
 */
void vSerialISRCreateQueues( unsigned portBASE_TYPE uxQueueLength, QueueHandle_t *pxRxedChars, QueueHandle_t *pxCharsForTx, long volatile **pplTHREEmptyFlag );

/* UART0 interrupt service routine entry point. */
void vUART_ISR_Wrapper( void ) __attribute__ ((naked));

/* UART0 interrupt service routine handler. */
void vUART_ISR_Handler( void ) __attribute__ ((noinline));

/*-----------------------------------------------------------*/
void vSerialISRCreateQueues(	unsigned portBASE_TYPE uxQueueLength, QueueHandle_t *pxRxedChars, 
								QueueHandle_t *pxCharsForTx, long volatile **pplTHREEmptyFlag )
{
	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* Pass back a reference to the queues so the serial API file can 
	post/receive characters. */
	*pxRxedChars = xRxedChars;
	*pxCharsForTx = xCharsForTx;

	/* Initialise the THRE empty flag - and pass back a reference. */
	lTHREEmpty = ( long ) pdTRUE;
	*pplTHREEmptyFlag = &lTHREEmpty;
}
/*-----------------------------------------------------------*/

void vUART_ISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();

	/* Call the handler.  This must be a separate function from the wrapper
	to ensure the correct stack frame is set up. */
	__asm volatile ("bl vUART_ISR_Handler");

	/* Restore the context of whichever task is going to run next. */
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

void vUART_ISR_Handler( void )
{
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* What caused the interrupt? */
	switch( UART0_IIR & serINTERRUPT_SOURCE_MASK )
	{
		case serSOURCE_ERROR :	/* Not handling this, but clear the interrupt. */
								cChar = UART0_LSR;
								break;

		case serSOURCE_THRE	:	/* The THRE is empty.  If there is another
								character in the Tx queue, send it now. */
								if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
								{
									UART0_THR = cChar;
								}
								else
								{
									/* There are no further characters 
									queued to send so we can indicate 
									that the THRE is available. */
									lTHREEmpty = pdTRUE;
								}
								break;

		case serSOURCE_RX_TIMEOUT :
		case serSOURCE_RX	:	/* A character was received.  Place it in 
								the queue of received characters. */
								cChar = UART0_RBR;
								xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
								break;

		default				:	/* There is nothing to do, leave the ISR. */
								break;
	}

	if( xHigherPriorityTaskWoken )
	{
		portYIELD_FROM_ISR();
	}

	/* Clear the ISR in the VIC. */
	VICVectAddr = serCLEAR_VIC_INTERRUPT;
}






	
