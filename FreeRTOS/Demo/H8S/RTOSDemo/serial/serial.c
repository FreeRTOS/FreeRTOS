/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER for port 1.

Note that this driver is written to test the RTOS port and is not intended
to represent an optimised solution.  In particular no use is made of the DMA
peripheral. */

/* Standard include files. */
#include <stdlib.h>

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

/* Hardware specific constants. */
#define serTX_INTERRUPT				( ( unsigned char ) 0x80 )
#define serRX_INTERRUPT				( ( unsigned char ) 0x40 )
#define serTX_ENABLE				( ( unsigned char ) 0x20 )
#define serRX_ENABLE				( ( unsigned char ) 0x10 )

/* Macros to turn on and off the serial port THRE interrupt while leaving the
other register bits in their correct state.   The Rx interrupt is always 
enabled. */
#define serTX_INTERRUPT_ON()		SCR1 = serTX_INTERRUPT | serRX_INTERRUPT | serTX_ENABLE | serRX_ENABLE;									
#define serTX_INTERRUPT_OFF()		SCR1 = 					 serRX_INTERRUPT | serTX_ENABLE | serRX_ENABLE;

/* Bit used to switch on the channel 1 serial port in the module stop 
register. */
#define serMSTP6					( ( unsigned short ) 0x0040 )

/* Interrupt service routines.  Note that the Rx and Tx service routines can 
cause a context switch and are therefore defined with the saveall attribute in
addition to the interrupt_handler attribute.  See the FreeRTOS.org WEB site 
documentation for a full explanation.*/
void vCOM_1_Rx_ISR( void ) __attribute__ ( ( saveall, interrupt_handler ) );
void vCOM_1_Tx_ISR( void ) __attribute__ ( ( saveall, interrupt_handler ) );
void vCOM_1_Error_ISR( void ) __attribute__ ( ( interrupt_handler ) );

/*-----------------------------------------------------------*/

/*
 * Initialise port 1 for interrupt driven communications.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Create the queues used to communicate between the tasks and the
	interrupt service routines. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* No parity, 8 data bits and 1 stop bit is the default so does not require 
	configuration - setup the remains of the hardware. */
	portENTER_CRITICAL();
	{
		/* Turn channel 1 on. */
		MSTPCR &= ~serMSTP6;

		/* Enable the channels and the Rx interrupt.  The Tx interrupt is only 
		enabled when data is being transmitted. */
		SCR1 = serRX_INTERRUPT | serTX_ENABLE | serRX_ENABLE;

		/* Bit rate settings for 22.1184MHz clock only!. */
		switch( ulWantedBaud )
		{
			case 4800	:	BRR1 = 143;
							break;
			case 9600	:	BRR1 = 71;
							break;
			case 19200	:	BRR1 = 35;
							break;
			case 38400	:	BRR1 = 17;
							break;
			case 57600	:	BRR1 = 11;
							break;
			case 115200	:	BRR1 = 5;
							break;
			default		:	BRR1 = 5;
							break;
		}
	}
	portEXIT_CRITICAL();	

	/* Unlike some ports, this driver code does not allow for more than one
	com port.  We therefore don't return a pointer to a port structure and can
	instead just return NULL. */
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
signed portBASE_TYPE xReturn = pdPASS;

	/* Return false if after the block time there is no room on the Tx queue. */
	portENTER_CRITICAL();
	{
		/* Send a character to the queue of characters waiting transmission.
		The queue is serviced by the Tx ISR. */
		if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
		{
			/* Could not post onto the queue. */
			xReturn = pdFAIL;
		}
		else
		{
			/* The message was posted onto the queue so we turn on the Tx
			interrupt to allow the Tx ISR to remove the character from the
			queue. */
			serTX_INTERRUPT_ON();
		}
	}
	portEXIT_CRITICAL();

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{	
	/* Not supported. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/

void vCOM_1_Rx_ISR( void )
{
	/* This can cause a context switch so this macro must be the first line
	in the function. */
	portENTER_SWITCHING_ISR();

	/* As this is a switching ISR the local variables must be declared as 
	static. */
	static char cRxByte;
	static portBASE_TYPE xHigherPriorityTaskWoken;

		xHigherPriorityTaskWoken = pdFALSE;

		/* Get the character. */
		cRxByte = RDR1;

		/* Post the character onto the queue of received characters - noting
		whether or not this wakes a task. */
		xQueueSendFromISR( xRxedChars, &cRxByte, &xHigherPriorityTaskWoken );

		/* Clear the interrupt. */
		SSR1 &= ~serRX_INTERRUPT;

	/* This must be the last line in the function.  We pass cTaskWokenByPost so 
	a context switch will occur if the received character woke a task that has
	a priority higher than the task we interrupted. */
	portEXIT_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vCOM_1_Tx_ISR( void )
{
	/* This can cause a context switch so this macro must be the first line
	in the function. */
	portENTER_SWITCHING_ISR();

	/* As this is a switching ISR the local variables must be declared as 
	static. */
	static char cTxByte;
	static signed portBASE_TYPE xTaskWokenByTx;

		/* This variable is static so must be explicitly reinitialised each
		time the function executes. */
		xTaskWokenByTx = pdFALSE;

		/* The interrupt was caused by the THR becoming empty.  Are there any
		more characters to transmit?  Note whether or not the Tx interrupt has
		woken a task. */
		if( xQueueReceiveFromISR( xCharsForTx, &cTxByte, &xTaskWokenByTx ) == pdTRUE )
		{
			/* A character was retrieved from the queue so can be sent to the
			THR now. */							
			TDR1 = cTxByte;

			/* Clear the interrupt. */
			SSR1 &= ~serTX_INTERRUPT;
		}
		else
		{
			/* Queue empty, nothing to send so turn off the Tx interrupt. */
			serTX_INTERRUPT_OFF();
		}		

	/* This must be the last line in the function.  We pass cTaskWokenByTx so 
	a context switch will occur if the Tx'ed character woke a task that has
	a priority higher than the task we interrupted. */
	portEXIT_SWITCHING_ISR( xTaskWokenByTx );
}
/*-----------------------------------------------------------*/

/*
 * This ISR cannot cause a context switch so requires no special 
 * considerations. 
 */
void vCOM_1_Error_ISR( void )
{
volatile unsigned char ucIn;

	ucIn = SSR1;
	SSR1 = 0;
}

