/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.
 *
 * This file only supports UART 1
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

/* Constants required to setup the hardware. */
#define serTX_AND_RX			( ( unsigned char ) 0x03 )

/* Misc. constants. */
#define serNO_BLOCK				( ( TickType_t ) 0 )

/* Enable the UART Tx interrupt. */
#define vInterruptOn() IFG2 |= UTXIFG1

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars;

/* The queue used to hold characters waiting transmission. */
static QueueHandle_t xCharsForTx;

static volatile short sTHREEmpty;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulBaudRateCount;

	/* Initialise the hardware. */

	/* Generate the baud rate constants for the wanted baud rate. */
	ulBaudRateCount = configCPU_CLOCK_HZ / ulWantedBaud;

	portENTER_CRITICAL();
	{
		/* Create the queues used by the com test task. */
		xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
		xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

		/* Reset UART. */
		UCTL1 |= SWRST;

		/* Set pin function. */
		P4SEL |= serTX_AND_RX;

		/* All other bits remain at zero for n, 8, 1 interrupt driven operation.
		LOOPBACK MODE!*/
		U1CTL |= CHAR + LISTEN;
		U1TCTL |= SSEL1;

		/* Setup baud rate low byte. */
		U1BR0 = ( unsigned char ) ( ulBaudRateCount & ( unsigned long ) 0xff );

		/* Setup baud rate high byte. */
		ulBaudRateCount >>= 8UL;
		U1BR1 = ( unsigned char ) ( ulBaudRateCount & ( unsigned long ) 0xff );

		/* Enable ports. */
		ME2 |= UTXE1 + URXE1;

		/* Set. */
		UCTL1 &= ~SWRST;

		/* Nothing in the buffer yet. */
		sTHREEmpty = pdTRUE;

		/* Enable interrupts. */
		IE2 |= URXIE1 + UTXIE1;
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
			U1TXBUF = cOutChar;
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
			xReturn = xQueueSend( xCharsForTx, &cOutChar, xBlockTime );

			/* Depending on queue sizing and task prioritisation:  While we
			were blocked waiting to post on the queue interrupts were not
			disabled.  It is possible that the serial ISR has emptied the
			Tx queue, in which case we need to start the Tx off again
			writing directly to the Tx register. */
			if( ( sTHREEmpty == pdTRUE ) && ( xReturn == pdPASS ) )
			{
				/* Get back the character we just posted. */
				xQueueReceive( xCharsForTx, &cOutChar, serNO_BLOCK );
				sTHREEmpty = pdFALSE;
				U1TXBUF = cOutChar;
			}
		}
	}
	portEXIT_CRITICAL();

	return pdPASS;
}
/*-----------------------------------------------------------*/

#if configINTERRUPT_EXAMPLE_METHOD == 1

	/*
	 * UART RX interrupt service routine.
	 */
	#pragma vector=UART1RX_VECTOR
	__interrupt void vRxISR( void )
	{
	signed char cChar;
	portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
	
		/* Get the character from the UART and post it on the queue of Rxed
		characters. */
		cChar = U1RXBUF;
	
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );

		if( xHigherPriorityTaskWoken )
		{
			/*If the post causes a task to wake force a context switch
			as the woken task may have a higher priority than the task we have
			interrupted. */
			taskYIELD();
		}

        /* Make sure any low power mode bits are clear before leaving the ISR. */
        __bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );
	}
	/*-----------------------------------------------------------*/
	
	/*
	 * UART Tx interrupt service routine.
	 */
	#pragma vector=UART1TX_VECTOR
	__interrupt void vTxISR( void )
	{
	signed char cChar;
	portBASE_TYPE xTaskWoken = pdFALSE;
	
		/* The previous character has been transmitted.  See if there are any
		further characters waiting transmission. */
	
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWoken ) == pdTRUE )
		{
			/* There was another character queued - transmit it now. */
			U1TXBUF = cChar;
		}
		else
		{
			/* There were no other characters to transmit. */
			sTHREEmpty = pdTRUE;
		}

        /* Make sure any low power mode bits are clear before leaving the ISR. */
        __bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );
	}
    /*-----------------------------------------------------------*/

#elif configINTERRUPT_EXAMPLE_METHOD == 2

    /* This is a standard C function as an assembly file wrapper is used as an
    interrupt entry point. */
	void vRxISR( void )
	{
	signed char cChar;
	portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
	
		/* Get the character from the UART and post it on the queue of Rxed
		characters. */
		cChar = U1RXBUF;
	
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );

        /*If the post causes a task to wake force a context switch
        as the woken task may have a higher priority than the task we have
        interrupted. */
        portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
	/*-----------------------------------------------------------*/
	
    /* This is a standard C function as an assembly file wrapper is used as an
    interrupt entry point. */
	void vTxISR( void )
	{
	signed char cChar;
	portBASE_TYPE xTaskWoken = pdFALSE;
	
		/* The previous character has been transmitted.  See if there are any
		further characters waiting transmission. */
	
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWoken ) == pdTRUE )
		{
			/* There was another character queued - transmit it now. */
			U1TXBUF = cChar;
		}
		else
		{
			/* There were no other characters to transmit. */
			sTHREEmpty = pdTRUE;
		}
	}

#endif /* configINTERRUPT_EXAMPLE_METHOD */
/*-----------------------------------------------------------*/
