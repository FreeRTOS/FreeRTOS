/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.   
 * 
 * This file only supports UART 2
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars; 

/* The queue used to hold characters waiting transmission. */
static QueueHandle_t xCharsForTx; 

static volatile short sTHREEmpty;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	portENTER_CRITICAL();
	{
		/* Create the queues used by the com test task. */
		xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
		xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

		 /* Initialize UART asynchronous mode */
		BGR02 = configPER_CLOCK_HZ / ulWantedBaud;
		  
		SCR02 = 0x17;	/* 8N1 */
		SMR02 = 0x0d;	/* enable SOT3, Reset, normal mode */
		SSR02 = 0x02;	/* LSB first, enable receive interrupts */

		PFR20_D0 = 1;	/* enable UART */
		PFR20_D1 = 1;	/* enable UART */

		EPFR20_D1 = 0;  /* enable UART */
	}
	portEXIT_CRITICAL();
	
	/* Unlike other ports, this serial code does not allow for more than one
	com port.  We therefore don't return a pointer to a port structure and can
	instead just return NULL. */
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

	/* Transmit a character. */
	portENTER_CRITICAL();
	{
		if( sTHREEmpty == pdTRUE )
		{
			/* If sTHREEmpty is true then the UART Tx ISR has indicated that 
			there are no characters queued to be transmitted - so we can
			write the character directly to the shift Tx register. */
			sTHREEmpty = pdFALSE;
			TDR02 = cOutChar;
			xReturn = pdPASS;
		}
		else
		{
			/* sTHREEmpty is false, so there are still characters waiting to be
			transmitted.  We have to queue this character so it gets 
			transmitted	in turn. */

			/* Return false if after the block time there is no room on the Tx 
			queue.  It is ok to block inside a critical section as each task
			maintains it's own critical section status. */
			if (xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) == pdTRUE)
			{
				xReturn = pdPASS;
			}
			else
			{
				xReturn = pdFAIL;
			}
		}
		
		if (pdPASS == xReturn)
		{
			/* Turn on the Tx interrupt so the ISR will remove the character from the
			queue and send it.   This does not need to be in a critical section as
			if the interrupt has already removed the character the next interrupt
			will simply turn off the Tx interrupt again. */
			SSR02_TIE = 1;
		}
		
	}
	portEXIT_CRITICAL();

	return pdPASS;
}
/*-----------------------------------------------------------*/

/*
 * UART RX interrupt service routine.
 */
 __interrupt void UART2_RxISR (void)
{
	signed char cChar;
	portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Get the character from the UART and post it on the queue of Rxed 
	characters. */
	cChar = RDR02;

	xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );

	if( xHigherPriorityTaskWoken )
	{
		/*If the post causes a task to wake force a context switch 
		as the woken task may have a higher priority than the task we have 
		interrupted. */
		portYIELD_FROM_ISR();
	}
}

/*-----------------------------------------------------------*/

/*
 * UART Tx interrupt service routine.
 */
__interrupt void UART2_TxISR (void)
{
	signed char cChar;
	signed portBASE_TYPE xTaskWoken = pdFALSE;

	/* The previous character has been transmitted.  See if there are any
	further characters waiting transmission. */
	if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWoken ) == pdTRUE )
	{
		/* There was another character queued - transmit it now. */
		TDR02 = cChar;
	}
	else
	{
		/* There were no other characters to transmit. */
		sTHREEmpty = pdTRUE;
		
		/* Disable transmit interrupts */
		SSR02_TIE = 0;
	}
}

