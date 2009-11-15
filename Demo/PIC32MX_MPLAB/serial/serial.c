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
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

/* Flag used to indicate the tx status. */
static portBASE_TYPE xTxHasEnded;

/*-----------------------------------------------------------*/

/* The UART interrupt handler. */
void __attribute__( (interrupt(ipl1), vector(_UART2_VECTOR))) vU2InterruptWrapper( void );

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned portSHORT usBRG;

	/* Create the queues used by the com test task. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	/* Configure the UART and interrupts. */
	usBRG = (unsigned portSHORT)(( (float)configPERIPHERAL_CLOCK_HZ / ( (float)16 * (float)ulWantedBaud ) ) - (float)0.5);
	OpenUART2( UART_EN, UART_RX_ENABLE | UART_TX_ENABLE | UART_INT_TX | UART_INT_RX_CHAR, usBRG );
	ConfigIntUART2( ( configKERNEL_INTERRUPT_PRIORITY + 1 ) | UART_INT_SUB_PR0 | UART_TX_INT_EN | UART_RX_INT_EN );

	xTxHasEnded = pdTRUE;

	/* Only a single port is implemented so we don't need to return anything. */
	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed portCHAR cOutChar, portTickType xBlockTime )
{
	/* Only one port is supported. */
	( void ) pxPort;

	/* Return false if after the block time there is no room on the Tx queue. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* A critical section should not be required as xTxHasEnded will not be
	written to by the ISR if it is already 0 (is this correct?). */
	if( xTxHasEnded )
	{
		xTxHasEnded = pdFALSE;
		IFS1bits.U2TXIF = serSET_FLAG;
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
static portCHAR cChar;
static portBASE_TYPE xHigherPriorityTaskWoken;

	xHigherPriorityTaskWoken = pdFALSE;

	/* Are any Rx interrupts pending? */
	if( mU2RXGetIntFlag() )
	{
		while( U2STAbits.URXDA )
		{
			/* Retrieve the received character and place it in the queue of
			received characters. */
			cChar = U2RXREG;
			xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
		}
		mU2RXClearIntFlag();
	}

	/* Are any Tx interrupts pending? */
	if( mU2TXGetIntFlag() )
	{
		while( !( U2STAbits.UTXBF ) )
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

		mU2TXClearIntFlag();
	}

	/* If sending or receiving necessitates a context switch, then switch now. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}







