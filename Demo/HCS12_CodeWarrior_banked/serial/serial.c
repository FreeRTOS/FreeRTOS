/*
    FreeRTOS V6.0.4 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
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

