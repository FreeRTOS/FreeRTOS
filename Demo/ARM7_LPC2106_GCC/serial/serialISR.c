/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

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
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 
static volatile long lTHREEmpty;

/*-----------------------------------------------------------*/

/* 
 * The queues are created in serialISR.c as they are used from the ISR.
 * Obtain references to the queues and THRE Empty flag. 
 */
void vSerialISRCreateQueues( unsigned portBASE_TYPE uxQueueLength, xQueueHandle *pxRxedChars, xQueueHandle *pxCharsForTx, long volatile **pplTHREEmptyFlag );

/* UART0 interrupt service routine entry point. */
void vUART_ISR_Wrapper( void ) __attribute__ ((naked));

/* UART0 interrupt service routine handler. */
void vUART_ISR_Handler( void ) __attribute__ ((noinline));

/*-----------------------------------------------------------*/
void vSerialISRCreateQueues(	unsigned portBASE_TYPE uxQueueLength, xQueueHandle *pxRxedChars, 
								xQueueHandle *pxCharsForTx, long volatile **pplTHREEmptyFlag )
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






	
