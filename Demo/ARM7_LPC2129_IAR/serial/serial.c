/*
	FreeRTOS.org V5.2.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it 
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for 
	more details.

	You should have received a copy of the GNU General Public License along 
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59 
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.

	A special exception to the GPL is included to allow you to distribute a 
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details.


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
#define serDLAB							( ( unsigned portCHAR ) 0x80 )
#define serENABLE_INTERRUPTS			( ( unsigned portCHAR ) 0x03 )
#define serNO_PARITY					( ( unsigned portCHAR ) 0x00 )
#define ser1_STOP_BIT					( ( unsigned portCHAR ) 0x00 )
#define ser8_BIT_CHARS					( ( unsigned portCHAR ) 0x03 )
#define serFIFO_ON						( ( unsigned portCHAR ) 0x01 )
#define serCLEAR_FIFO					( ( unsigned portCHAR ) 0x06 )
#define serWANTED_CLOCK_SCALING			( ( unsigned portLONG ) 16 )

/* Constants to setup and access the VIC. */
#define serU0VIC_CHANNEL				( ( unsigned portLONG ) 0x0006 )
#define serU0VIC_CHANNEL_BIT			( ( unsigned portLONG ) 0x0040 )
#define serU0VIC_ENABLE					( ( unsigned portLONG ) 0x0020 )
#define serCLEAR_VIC_INTERRUPT			( ( unsigned portLONG ) 0 )

/* Constants to determine the ISR source. */
#define serSOURCE_THRE					( ( unsigned portCHAR ) 0x02 )
#define serSOURCE_RX_TIMEOUT			( ( unsigned portCHAR ) 0x0c )
#define serSOURCE_ERROR					( ( unsigned portCHAR ) 0x06 )
#define serSOURCE_RX					( ( unsigned portCHAR ) 0x04 )
#define serINTERRUPT_SOURCE_MASK		( ( unsigned portCHAR ) 0x0f )

/* Misc. */
#define serINVALID_QUEUE				( ( xQueueHandle ) 0 )
#define serHANDLE						( ( xComPortHandle ) 1 )
#define serNO_BLOCK						( ( portTickType ) 0 )

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static xQueueHandle xRxedChars;
static xQueueHandle xCharsForTx;
static volatile portLONG lTHREEmpty = pdFALSE;

/*-----------------------------------------------------------*/

/* The ISR.  Note that this is called by a wrapper written in the file
SerialISR.s79.  See the WEB documentation for this port for further
information. */
__arm void vSerialISR( void );

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned portLONG ulDivisor, ulWantedClock;
xComPortHandle xReturn = serHANDLE;
extern void ( vSerialISREntry) ( void );

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	/* Initialise the THRE empty flag. */
	lTHREEmpty = pdTRUE;

	if(
		( xRxedChars != serINVALID_QUEUE ) &&
		( xCharsForTx != serINVALID_QUEUE ) &&
		( ulWantedBaud != ( unsigned portLONG ) 0 )
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
			U0DLL = ( unsigned portCHAR ) ( ulDivisor & ( unsigned portLONG ) 0xff );
			ulDivisor >>= 8;
			U0DLM = ( unsigned portCHAR ) ( ulDivisor & ( unsigned portLONG ) 0xff );

			/* Turn on the FIFO's and clear the buffers. */
			U0FCR = ( serFIFO_ON | serCLEAR_FIFO );

			/* Setup transmission format. */
			U0LCR = serNO_PARITY | ser1_STOP_BIT | ser8_BIT_CHARS;

			/* Setup the VIC for the UART. */
			VICIntSelect &= ~( serU0VIC_CHANNEL_BIT );
			VICIntEnable |= serU0VIC_CHANNEL_BIT;
			VICVectAddr1 = ( unsigned portLONG ) vSerialISREntry;
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

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
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

void vSerialPutString( xComPortHandle pxPort, const signed portCHAR * const pcString, unsigned portSHORT usStringLength )
{
signed portCHAR *pxNext;

	/* NOTE: This implementation does not handle the queue being full as no
	block time is used! */

	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;
	( void ) usStringLength;

	/* Send each character in the string, one at a time. */
	pxNext = ( signed portCHAR * ) pcString;
	while( *pxNext )
	{
		xSerialPutChar( pxPort, *pxNext, serNO_BLOCK );
		pxNext++;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed portCHAR cOutChar, portTickType xBlockTime )
{
signed portBASE_TYPE xReturn;

	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;

	portENTER_CRITICAL();
	{
		/* Is there space to write directly to the UART? */
		if( lTHREEmpty == ( portLONG ) pdTRUE )
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
			if( lTHREEmpty == ( portLONG ) pdTRUE )
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
signed portCHAR cChar;
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
