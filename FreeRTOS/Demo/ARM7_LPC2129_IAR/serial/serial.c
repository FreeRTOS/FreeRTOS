/*
 * FreeRTOS Kernel V10.3.1
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


/*
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART0.
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

/* Constants to setup and access the UART. */
#define serDLAB							( ( unsigned char ) 0x80 )
#define serENABLE_INTERRUPTS			( ( unsigned char ) 0x03 )
#define serNO_PARITY					( ( unsigned char ) 0x00 )
#define ser1_STOP_BIT					( ( unsigned char ) 0x00 )
#define ser8_BIT_CHARS					( ( unsigned char ) 0x03 )
#define serFIFO_ON						( ( unsigned char ) 0x01 )
#define serCLEAR_FIFO					( ( unsigned char ) 0x06 )
#define serWANTED_CLOCK_SCALING			( ( unsigned long ) 16 )

/* Constants to setup and access the VIC. */
#define serU0VIC_CHANNEL				( ( unsigned long ) 0x0006 )
#define serU0VIC_CHANNEL_BIT			( ( unsigned long ) 0x0040 )
#define serU0VIC_ENABLE					( ( unsigned long ) 0x0020 )
#define serCLEAR_VIC_INTERRUPT			( ( unsigned long ) 0 )

/* Constants to determine the ISR source. */
#define serSOURCE_THRE					( ( unsigned char ) 0x02 )
#define serSOURCE_RX_TIMEOUT			( ( unsigned char ) 0x0c )
#define serSOURCE_ERROR					( ( unsigned char ) 0x06 )
#define serSOURCE_RX					( ( unsigned char ) 0x04 )
#define serINTERRUPT_SOURCE_MASK		( ( unsigned char ) 0x0f )

/* Misc. */
#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serHANDLE						( ( xComPortHandle ) 1 )
#define serNO_BLOCK						( ( TickType_t ) 0 )

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;
static volatile long lTHREEmpty = pdFALSE;

/*-----------------------------------------------------------*/

/* The ISR.  Note that this is called by a wrapper written in the file
SerialISR.s79.  See the WEB documentation for this port for further
information. */
__arm void vSerialISR( void );

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulDivisor, ulWantedClock;
xComPortHandle xReturn = serHANDLE;
extern void ( vSerialISREntry) ( void );

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* Initialise the THRE empty flag. */
	lTHREEmpty = pdTRUE;

	if(
		( xRxedChars != serINVALID_QUEUE ) &&
		( xCharsForTx != serINVALID_QUEUE ) &&
		( ulWantedBaud != ( unsigned long ) 0 )
	  )
	{
		portENTER_CRITICAL();
		{
			/* Setup the baud rate:  Calculate the divisor value. */
			ulWantedClock = ulWantedBaud * serWANTED_CLOCK_SCALING;
			ulDivisor = configCPU_CLOCK_HZ / ulWantedClock;

			/* Set the DLAB bit so we can access the divisor. */
			U0LCR |= serDLAB;

			/* Setup the divisor. */
			U0DLL = ( unsigned char ) ( ulDivisor & ( unsigned long ) 0xff );
			ulDivisor >>= 8;
			U0DLM = ( unsigned char ) ( ulDivisor & ( unsigned long ) 0xff );

			/* Turn on the FIFO's and clear the buffers. */
			U0FCR = ( serFIFO_ON | serCLEAR_FIFO );

			/* Setup transmission format. */
			U0LCR = serNO_PARITY | ser1_STOP_BIT | ser8_BIT_CHARS;

			/* Setup the VIC for the UART. */
			VICIntSelect &= ~( serU0VIC_CHANNEL_BIT );
			VICIntEnable |= serU0VIC_CHANNEL_BIT;
			VICVectAddr1 = ( unsigned long ) vSerialISREntry;
			VICVectCntl1 = serU0VIC_CHANNEL | serU0VIC_ENABLE;

			/* Enable UART0 interrupts. */
			U0IER |= serENABLE_INTERRUPTS;
		}
		portEXIT_CRITICAL();

		xReturn = ( xComPortHandle ) 1;
	}
	else
	{
		xReturn = ( xComPortHandle ) 0;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;

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

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
signed char *pxNext;

	/* NOTE: This implementation does not handle the queue being full as no
	block time is used! */

	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;
	( void ) usStringLength;

	/* Send each character in the string, one at a time. */
	pxNext = ( signed char * ) pcString;
	while( *pxNext )
	{
		xSerialPutChar( pxPort, *pxNext, serNO_BLOCK );
		pxNext++;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
signed portBASE_TYPE xReturn;

	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;

	portENTER_CRITICAL();
	{
		/* Is there space to write directly to the UART? */
		if( lTHREEmpty == ( long ) pdTRUE )
		{
			/* We wrote the character directly to the UART, so was
			successful. */
			lTHREEmpty = pdFALSE;
			U0THR = cOutChar;
			xReturn = pdPASS;
		}
		else
		{
			/* We cannot write directly to the UART, so queue the character.
			Block for a maximum of xBlockTime if there is no space in the
			queue.  It is ok to block within a critical section as each
			task has it's own critical section management. */
			xReturn = xQueueSend( xCharsForTx, &cOutChar, xBlockTime );

			/* Depending on queue sizing and task prioritisation:  While we
			were blocked waiting to post interrupts were not disabled.  It is
			possible that the serial ISR has emptied the Tx queue, in which
			case we need to start the Tx off again. */
			if( lTHREEmpty == ( long ) pdTRUE )
			{
				xQueueReceive( xCharsForTx, &cOutChar, serNO_BLOCK );
				lTHREEmpty = pdFALSE;
				U0THR = cOutChar;
			}
		}
	}
	portEXIT_CRITICAL();

	return xReturn;
}
/*-----------------------------------------------------------*/

__arm void vSerialISR( void )
{
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* What caused the interrupt? */
	switch( U0IIR & serINTERRUPT_SOURCE_MASK )
	{
		case serSOURCE_ERROR :	/* Not handling this, but clear the interrupt. */
								cChar = U0LSR;
								break;

		case serSOURCE_THRE	:	/* The THRE is empty.  If there is another
								character in the Tx queue, send it now. */
								if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
								{
									U0THR = cChar;
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
								cChar = U0RBR;
								xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
								break;

		default				:	/* There is nothing to do, leave the ISR. */
								break;
	}

	/* Exit the ISR.  If a task was woken by either a character being received
	or transmitted then a context switch will occur. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );

	/* Clear the ISR in the VIC. */
	VICVectAddr = serCLEAR_VIC_INTERRUPT;
}
/*-----------------------------------------------------------*/
