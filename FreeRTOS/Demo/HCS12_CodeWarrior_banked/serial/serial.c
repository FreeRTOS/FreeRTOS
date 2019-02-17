/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx; 

/* Interrupt identification bits. */
#define serOVERRUN_INTERRUPT		( 0x08 )
#define serRX_INTERRUPT				( 0x20 )
#define serTX_INTERRUPT				( 0x80 )

/*-----------------------------------------------------------*/


/*
 * Initialise port for interrupt driven communications.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Hardware setup is performed by the Processor Expert generated code.  
	This function just creates the queues used to communicate between the 
	interrupt code and the task code - then sets the required baud rate. */

	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	COM0_SetBaudRateMode( ( char ) ulWantedBaud );

	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
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
volatile unsigned char ucByte, ucStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

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
		xQueueSendFromISR( xRxedChars, ( void * ) &ucByte, &xHigherPriorityTaskWoken );
	}
	
	if( ( ucStatus & serTX_INTERRUPT ) && ( SCI0CR2_SCTIE ) )
	{	
		/* The interrupt was caused by a character being transmitted. */
		if( xQueueReceiveFromISR( xCharsForTx, ( void * ) &ucByte, &xHigherPriorityTaskWoken ) == pdTRUE )
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

	if( xHigherPriorityTaskWoken )
	{
		portYIELD();
	}
}

#pragma CODE_SEG DEFAULT

