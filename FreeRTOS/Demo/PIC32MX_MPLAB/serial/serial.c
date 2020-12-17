/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER. 

NOTE:  This driver is primarily to test the scheduler functionality.  It does
not effectively use the buffers or DMA and is therefore not intended to be
an example of an efficient driver. */

/* Standard include file. */
#include <stdlib.h>
#include <plib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo app include files. */
#include "serial.h"

/* Hardware setup. */
#define serSET_FLAG						( 1 )

/* The queues used to communicate between tasks and ISR's. */
static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx; 

/* Flag used to indicate the tx status. */
static volatile portBASE_TYPE xTxHasEnded;

/*-----------------------------------------------------------*/

/* The UART interrupt handler.  As this uses the FreeRTOS assembly interrupt
entry point the IPL setting in the following prototype has no effect.  The
interrupt priority is set by the call to  ConfigIntUART2() in 
xSerialPortInitMinimal(). */
void __attribute__( (interrupt(IPL0AUTO), vector(_UART2_VECTOR))) vU2InterruptWrapper( void );

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned short usBRG;

	/* Create the queues used by the com test task. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* Configure the UART and interrupts. */
	usBRG = (unsigned short)(( (float)configPERIPHERAL_CLOCK_HZ / ( (float)16 * (float)ulWantedBaud ) ) - (float)0.5);
	OpenUART2( UART_EN, UART_RX_ENABLE | UART_TX_ENABLE | UART_INT_TX | UART_INT_RX_CHAR, usBRG );
	ConfigIntUART2( ( configKERNEL_INTERRUPT_PRIORITY + 1 ) | UART_INT_SUB_PR0 | UART_TX_INT_EN | UART_RX_INT_EN );

	xTxHasEnded = pdTRUE;

	/* Only a single port is implemented so we don't need to return anything. */
	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* Only one port is supported. */
	( void ) pxPort;

	/* Get the next character from the buffer.  Return false if no characters
	are available or arrive before xBlockTime expires. */
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

	/* Only one port is supported. */
	( void ) pxPort;

	/* Return false if after the block time there is no room on the Tx queue. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		xReturn = pdFAIL;
	}
	else
	{
		xReturn = pdPASS;
	}

	if( xReturn != pdFAIL )
	{
		/* A critical section should not be required as xTxHasEnded will not be
		written to by the ISR if it is already 0. */
		if(  xTxHasEnded == pdTRUE )
		{
			xTxHasEnded = pdFALSE;
			IFS1SET = _IFS1_U2TXIF_MASK;
		}
	}

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
}
/*-----------------------------------------------------------*/

void vU2InterruptHandler( void )
{
/* Declared static to minimise stack use. */
static char cChar;
static portBASE_TYPE xHigherPriorityTaskWoken;

	xHigherPriorityTaskWoken = pdFALSE;

	/* Are any Rx interrupts pending? */
	if( IFS1bits.U2RXIF == 1)
	{
		while( U2STAbits.URXDA )
		{
			/* Retrieve the received character and place it in the queue of
			received characters. */
			cChar = U2RXREG;
			xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
		}
		IFS1CLR = _IFS1_U2RXIF_MASK;
	}

	/* Are any Tx interrupts pending? */
	if( IFS1bits.U2TXIF == 1 )
	{
		while( ( U2STAbits.UTXBF ) == 0 )
		{
			if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
			{
				/* Send the next character queued for Tx. */
				U2TXREG = cChar;
			}
			else
			{
				/* Queue empty, nothing to send. */
				xTxHasEnded = pdTRUE;
				break;
			}
		}

		IFS1CLR = _IFS1_U2TXIF_MASK;
	}

	/* If sending or receiving necessitates a context switch, then switch now. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}







