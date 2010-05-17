/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

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
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

/*-----------------------------------------------------------*/

/* UART0 interrupt service routine.  This can cause a context switch so MUST
be declared "naked". */
void vUART_ISR_Wrapper( void ) __attribute__ ((naked));

/* The ISR function that actually performs the work.  This must be separate 
from the wrapper to ensure the correct stack frame is set up. */
void vUART_ISR_Handler( void ) __attribute__ ((noinline));

/*-----------------------------------------------------------*/
void vSerialISRCreateQueues( unsigned portBASE_TYPE uxQueueLength, xQueueHandle *pxRxedChars, xQueueHandle *pxCharsForTx )
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

