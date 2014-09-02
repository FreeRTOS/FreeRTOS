/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.
 *
 * This is not a proper UART driver.  It only supports one port, uses loopback
 * mode, and is used to test interrupts that use the FreeRTOS API as part of
 * a wider test suite.  Nor is it intended to show an efficient implementation
 * of a UART interrupt service routine as queues are used to pass individual
 * characters one at a time!
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

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
		xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
		xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

		/* Reset UART. */
		UCA1CTL1 |= UCSWRST;

		/* Use SMCLK. */
		UCA1CTL1 = UCSSEL0 | UCSSEL1;
		
		/* Setup baud rate low byte. */
		UCA1BR0 = ( unsigned char ) ( ulBaudRateCount & ( unsigned long ) 0xff );

		/* Setup baud rate high byte. */
		ulBaudRateCount >>= 8UL;
		UCA1BR1 = ( unsigned char ) ( ulBaudRateCount & ( unsigned long ) 0xff );

		/* UCLISTEN sets loopback mode! */
		UCA1STAT = UCLISTEN;

		/* Enable interrupts. */
		UCA1IE |= UCRXIE;
		
		/* Take out of reset. */
		UCA1CTL1 &= ~UCSWRST;
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
signed portBASE_TYPE xReturn;

	/* Send the next character to the queue of characters waiting transmission,
	then enable the UART Tx interrupt, just in case UART transmission has already
	completed and switched itself off. */
	xReturn = xQueueSend( xCharsForTx, &cOutChar, xBlockTime );
	UCA1IE |= UCTXIE;

	return xReturn;
}
/*-----------------------------------------------------------*/

/* The implementation of this interrupt is provided to demonstrate the use
of queues from inside an interrupt service routine.  It is *not* intended to
be an efficient interrupt implementation.  A real application should make use
of the DMA.  Or, as a minimum, transmission and reception could use a simple
RAM ring buffer, and synchronise with a task using a semaphore when a complete
message has been received or transmitted. */
#pragma vector=USCI_A1_VECTOR
static __interrupt void prvUSCI_A1_ISR( void )
{
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	while( ( UCA1IFG & UCRXIFG ) != 0 )
	{
		/* Get the character from the UART and post it on the queue of Rxed
		characters. */
		cChar = UCA1RXBUF;
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}
	
	/* If there is a Tx interrupt pending and the tx interrupts are enabled. */
	if( ( UCA1IFG & UCTXIFG ) != 0 )
	{
		/* The previous character has been transmitted.  See if there are any
		further characters waiting transmission. */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* There was another character queued - transmit it now. */
			UCA1TXBUF = cChar;
		}
		else
		{
			/* There were no other characters to transmit - disable the Tx
			interrupt. */
			UCA1IE &= ~UCTXIE;
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


