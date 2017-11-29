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


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.
 *
 * This is not a proper UART driver.  It only supports one port, and is not
 * intended to show an efficient implementation as queues are used to pass
 * individual characters one at a time!  This is ok for a slow interface, such
 * as a command line interface (which this driver is used for), but is too
 * inefficient for higher bandwidth applications.
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

/* TI includes. */
#include "driverlib.h"

/* Misc. constants. */
#define serNO_BLOCK				( ( TickType_t ) 0 )

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars;

/* The queue used to hold characters waiting transmission. */
static QueueHandle_t xCharsForTx;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulBaudRateCount;

	/* Initialise the hardware. */

	/* Generate the baud rate constants for the wanted baud rate. */
	ulBaudRateCount = configCPU_CLOCK_HZ / ulWantedBaud;

	portENTER_CRITICAL();
	{
		/* Create the queues used by the com test task. */
		xRxedChars = xQueueCreate( uxQueueLength, ( UBaseType_t ) sizeof( signed char ) );
		xCharsForTx = xQueueCreate( uxQueueLength, ( UBaseType_t ) sizeof( signed char ) );

		/* Reset UART. */
		UCA0CTL1 |= UCSWRST;

		/* Use SMCLK. */
		UCA0CTL1 = UCSSEL0 | UCSSEL1;

		/* Setup baud rate low byte. */
		UCA0BR0 = ( unsigned char ) ( ulBaudRateCount & ( unsigned long ) 0xff );

		/* Setup baud rate high byte. */
		ulBaudRateCount >>= 8UL;
		UCA0BR1 = ( unsigned char ) ( ulBaudRateCount & ( unsigned long ) 0xff );

		/* Enable interrupts. */
		UCA0IE |= UCRXIE;

		/* Take out of reset. */
		UCA0CTL1 &= ~UCSWRST;
	}
	portEXIT_CRITICAL();

	/* Note the comments at the top of this file about this not being a generic
	UART driver. */
	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* Get the next character from the buffer.  Return false if no characters
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
BaseType_t xReturn;

	/* Send the next character to the queue of characters waiting transmission,
	then enable the UART Tx interrupt, just in case UART transmission has already
	completed and switched itself off. */
	xReturn = xQueueSend( xCharsForTx, &cOutChar, xBlockTime );
	UCA0IE |= UCTXIE;

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
UBaseType_t uxChar;
const TickType_t xMaxBlockTime = pdMS_TO_TICKS( 100 );

	/* The driver only supports one port so the pxPort parameter is not used. */
	( void ) pxPort;

	for( uxChar = 0; uxChar < usStringLength; uxChar++ )
	{
		if( xQueueSend( xCharsForTx, &( pcString[ uxChar ] ), xMaxBlockTime ) == pdFALSE )
		{
			break;
		}
		else
		{
			UCA0IE |= UCTXIE;
		}
	}
}
/*-----------------------------------------------------------*/

/* The implementation of this interrupt is provided to demonstrate the use
of queues from inside an interrupt service routine.  It is *not* intended to
be an efficient interrupt implementation.  A real application should make use
of the DMA.  Or, as a minimum, transmission and reception could use a simple
RAM ring buffer, and synchronise with a task using a semaphore when a complete
message has been received or transmitted. */
#pragma vector=USCI_A0_VECTOR
__interrupt void prvUSCI_A0_ISR( void )
{
signed char cChar;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	while( ( UCA0IFG & UCRXIFG ) != 0 )
	{
		/* Get the character from the UART and post it on the queue of Rxed
		characters. */
		cChar = UCA0RXBUF;
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}

	/* If there is a Tx interrupt pending and the tx interrupts are enabled. */
	if( ( UCA0IFG & UCTXIFG ) != 0 )
	{
		/* The previous character has been transmitted.  See if there are any
		further characters waiting transmission. */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* There was another character queued - transmit it now. */
			UCA0TXBUF = cChar;
		}
		else
		{
			/* There were no other characters to transmit - disable the Tx
			interrupt. */
			UCA0IE &= ~UCTXIE;
		}
	}

	__bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );

	/* If writing to a queue caused a task to unblock, and the unblocked task
	has a priority equal to or above the task that this interrupt interrupted,
	then lHigherPriorityTaskWoken will have been set to pdTRUE internally within
	xQueuesendFromISR(), and portEND_SWITCHING_ISR() will ensure that this
	interrupt returns directly to the higher priority unblocked task.

	THIS MUST BE THE LAST THING DONE IN THE ISR. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}


