/*
	FreeRTOS.org V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


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

/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.   
 * 
 * This file only supports UART 0
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
static xQueueHandle			xRxedChars;

/* The queue used to hold characters waiting transmission. */
static xQueueHandle			xCharsForTx;

static volatile portSHORT	sTHREEmpty;

static volatile portSHORT	queueFail = pdFALSE;

/*-----------------------------------------------------------*/
xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Initialise the hardware. */
	portENTER_CRITICAL();
	{
		/* Create the queues used by the com test task. */
		xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof(signed portCHAR) );
		xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof(signed portCHAR) );

		if( xRxedChars == 0 )
		{
			queueFail = pdTRUE;
		}

		if( xCharsForTx == 0 )
		{
			queueFail = pdTRUE;
		}

		/* Initialize UART asynchronous mode */
		BGR0 = configCLKP1_CLOCK_HZ / ulWantedBaud;

		SCR0 = 0x17;	/* 8N1 */
		SMR0 = 0x0d;	/* enable SOT3, Reset, normal mode */
		SSR0 = 0x02;	/* LSB first, enable receive interrupts */

		PIER08_IE2 = 1; /* enable input */
		DDR08_D2 = 0;	/* switch P08_2 to input */
		DDR08_D3 = 1;	/* switch P08_3 to output */
	}
	portEXIT_CRITICAL();

	/* Unlike other ports, this serial code does not allow for more than one
	com port.  We therefore don't return a pointer to a port structure and can
	instead just return NULL. */
	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
{
	/* Get the next character from the buffer.  Return false if no characters
	are available, or arrive before xBlockTime expires. */
	if( xQueueReceive(xRxedChars, pcRxedChar, xBlockTime) )
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
signed portBASE_TYPE	xReturn;

	/* Transmit a character. */
	portENTER_CRITICAL();
	{
		if( sTHREEmpty == pdTRUE )
		{
			/* If sTHREEmpty is true then the UART Tx ISR has indicated that 
			there are no characters queued to be transmitted - so we can
			write the character directly to the shift Tx register. */
			sTHREEmpty = pdFALSE;
			TDR0 = cOutChar;
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
			if( xQueueSend(xCharsForTx, &cOutChar, xBlockTime) == pdTRUE )
			{
				xReturn = pdPASS;
			}
			else
			{
				xReturn = pdFAIL;
			}
		}

		if( pdPASS == xReturn )
		{
			/* Turn on the Tx interrupt so the ISR will remove the character from the
			queue and send it.   This does not need to be in a critical section as
			if the interrupt has already removed the character the next interrupt
			will simply turn off the Tx interrupt again. */
			SSR0_TIE = 1;
		}
	}
	portEXIT_CRITICAL();

	return pdPASS;
}
/*-----------------------------------------------------------*/

/*
 * UART RX interrupt service routine.
 */
__interrupt void UART0_RxISR( void )
{
volatile signed portCHAR	cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Get the character from the UART and post it on the queue of Rxed 
	characters. */
	cChar = RDR0;

	xQueueSendFromISR( xRxedChars, ( const void *const ) &cChar, &xHigherPriorityTaskWoken );

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
__interrupt void UART0_TxISR( void )
{
signed portCHAR			cChar;
signed portBASE_TYPE	xTaskWoken = pdFALSE;

	/* The previous character has been transmitted.  See if there are any
	further characters waiting transmission. */
	if( xQueueReceiveFromISR(xCharsForTx, &cChar, &xTaskWoken) == pdTRUE )
	{
		/* There was another character queued - transmit it now. */
		TDR0 = cChar;
	}
	else
	{
		/* There were no other characters to transmit. */
		sTHREEmpty = pdTRUE;

		/* Disable transmit interrupts */
		SSR0_TIE = 0;
	}
}
