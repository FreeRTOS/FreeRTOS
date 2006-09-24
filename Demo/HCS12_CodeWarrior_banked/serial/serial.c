/*
	FreeRTOS.org V4.1.1 - Copyright (C) 2003-2006 Richard Barry.

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
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
*/


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER for port 1.

Note that this driver is written to test the RTOS port and is not intended
to represent an optimised solution. */

/* Processor Expert generated includes. */
#include "com0.h"

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application include files. */
#include "serial.h"

/* The queues used to communicate between the task code and the interrupt
service routines. */
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

/* Interrupt identification bits. */
#define serOVERRUN_INTERRUPT		( 0x08 )
#define serRX_INTERRUPT				( 0x20 )
#define serTX_INTERRUPT				( 0x80 )

/*-----------------------------------------------------------*/


/*
 * Initialise port for interrupt driven communications.
 */
xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Hardware setup is performed by the Processor Expert generated code.  
	This function just creates the queues used to communicate between the 
	interrupt code and the task code - then sets the required baud rate. */

	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	COM0_SetBaudRateMode( ( portCHAR ) ulWantedBaud );

	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
{
	/* Get the next character from the buffer queue.  Return false if no characters
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed portCHAR cOutChar, portTickType xBlockTime )
{
	/* Place the character in the queue of characters to be transmitted. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* Turn on the Tx interrupt so the ISR will remove the character from the
	queue and send it.   This does not need to be in a critical section as
	if the interrupt has already removed the character the next interrupt
	will simply turn off the Tx interrupt again. */
	SCI0CR2_SCTIE = 1;;

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{	
	/* Not supported. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/


/* 
 * Interrupt service routine for the serial port.  Must be in non-banked
 * memory. 
 */

#pragma CODE_SEG __NEAR_SEG NON_BANKED

__interrupt void vCOM0_ISR( void )
{
volatile unsigned portCHAR ucByte, ucStatus;
portBASE_TYPE xTaskWokenByPost = pdFALSE, xTaskWokenByTx = pdFALSE;

	/* What caused the interrupt? */
	ucStatus = SCI0SR1;
	
	if( ucStatus & serOVERRUN_INTERRUPT )
	{
		/* The interrupt was caused by an overrun.  Clear the error by reading
		the data register. */
		ucByte = SCI0DRL;
	}

	if( ucStatus & serRX_INTERRUPT )
	{	
		/* The interrupt was caused by a character being received.
		Read the received byte. */
		ucByte = SCI0DRL;                      

		/* Post the character onto the queue of received characters - noting
		whether or not this wakes a task. */
		xTaskWokenByPost = xQueueSendFromISR( xRxedChars, ( void * ) &ucByte, pdFALSE );		
	}
	
	if( ( ucStatus & serTX_INTERRUPT ) && ( SCI0CR2_SCTIE ) )
	{	
		/* The interrupt was caused by a character being transmitted. */
		if( xQueueReceiveFromISR( xCharsForTx, ( void * ) &ucByte, &xTaskWokenByTx ) == pdTRUE )
		{
			/* Clear the SCRF bit. */
			SCI0DRL = ucByte;
		}
		else
		{
			/* Disable transmit interrupt */
			SCI0CR2_SCTIE = 0;                 
		}
	}

	if( ( xTaskWokenByPost ) || ( xTaskWokenByTx ) )
	{
		portYIELD();
	}
}

#pragma CODE_SEG DEFAULT

