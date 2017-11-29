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
  BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR USART0. 

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
#include "AT91R40008.h"
#include "usart.h"

/*-----------------------------------------------------------*/

/* Constant to access the AIC. */
#define serCLEAR_AIC_INTERRUPT      ( ( unsigned long ) 0 )

/* Constants to determine the ISR source. */
#define serSOURCE_THRE				( ( unsigned char ) 0x02 )
#define serSOURCE_RX_TIMEOUT		( ( unsigned char ) 0x0c )
#define serSOURCE_ERROR				( ( unsigned char ) 0x06 )
#define serSOURCE_RX				( ( unsigned char ) 0x04 )
#define serINTERRUPT_SOURCE_MASK    ( ( unsigned long ) (US_RXRDY | US_TXRDY | US_RXBRK | US_OVRE | US_FRAME | US_PARE) )

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx; 

/*-----------------------------------------------------------*/

/* UART0 interrupt service routine.  This can cause a context switch so MUST
be declared "naked". */
void vUART_ISR_Wrapper( void ) __attribute__ ((naked));

/* The ISR function that actually performs the work.  This must be separate 
from the wrapper to ensure the correct stack frame is set up. */
void vUART_ISR_Handler( void ) __attribute__ ((noinline));

/*-----------------------------------------------------------*/
void vSerialISRCreateQueues( unsigned portBASE_TYPE uxQueueLength, QueueHandle_t *pxRxedChars, QueueHandle_t *pxCharsForTx )
{
	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* Pass back a reference to the queues so the serial API file can 
	post/receive characters. */
	*pxRxedChars = xRxedChars;
	*pxCharsForTx = xCharsForTx;
}
/*-----------------------------------------------------------*/

void vUART_ISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();

	/* Call the handler.  This must be a separate function to ensure the 
	stack frame is correctly set up. */
	__asm volatile( "bl vUART_ISR_Handler" );

	/* Restore the context of whichever task will run next. */
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

void vUART_ISR_Handler( void )
{
/* Now we can declare the local variables.   These must be static. */
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
unsigned long ulStatus;

	/* What caused the interrupt? */
	ulStatus = AT91C_BASE_US0->US_CSR & AT91C_BASE_US0->US_IMR;

	if (ulStatus & US_TXRDY)
	{
		/* The interrupt was caused by the THR becoming empty.  Are there any
		more characters to transmit? */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* A character was retrieved from the queue so can be sent to the
			THR now. */
			AT91C_BASE_US0->US_THR = cChar;
		}
		else
		{
			/* Queue empty, nothing to send so turn off the Tx interrupt. */
			AT91C_BASE_US0->US_IDR = US_TXRDY;
		}    
	}

	if (ulStatus & US_RXRDY)
	{
		/* The interrupt was caused by the receiver getting data. */
		cChar = AT91C_BASE_US0->US_RHR;

		xQueueSendFromISR(xRxedChars, &cChar, &xHigherPriorityTaskWoken);
	}

	/* Acknowledge the interrupt at AIC level... */
	AT91C_BASE_AIC->AIC_EOICR = serCLEAR_AIC_INTERRUPT;

	/* If an event caused a task to unblock then we call "Yield from ISR" to
	ensure that the unblocked task is the task that executes when the interrupt
	completes if the unblocked task has a priority higher than the interrupted
	task. */
	if( xHigherPriorityTaskWoken )
	{
		portYIELD_FROM_ISR();
	}
}
/*-----------------------------------------------------------*/

