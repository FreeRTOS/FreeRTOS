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

/* Hardware specific includes. */
#include <tc1782.h>
#include <machine/intrinsics.h>
#include <machine/cint.h>
#include <machine/wdtcon.h>

/* Scheduler Includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo Includes. */
#include "serial.h"

/*****************************************************************************
 * Please note!
 *
 * This file is here to provide a means of generating interrupts to test the
 * FreeRTOS tricore port.  First - it configures the UART into loopback mode,
 * and has only been used in loopback mode.  Therefore, the baud rate
 * calculation used has never been verified for correctness.  Second -
 * characters are passed into and out of the interrupt service routines using
 * character queues.  This provides a good test of the interrupt interaction,
 * context switching mechanism, and kernel loading, it is however highly
 * inefficient if the UART is being used to handle even moderate amounts of
 * data throughput.
 */


/*---------------------------------------------------------------------------*/

/*
 * See if the Serial Transmit Interrupt is currently activated, meaning that
 * the interrupt is working through the back log of bytes that it needs to
 * send. If the ISR is not enabled, then it will be triggered to send the first
 * byte, and it will be automatically re-triggered when that byte has been
 * sent. When the queue is exhausted, the ISR disables itself.
 */
static void prvCheckTransmit( void );

/*
 * The transmit and receive interrupt handlers.
 */
static void prvTxBufferInterruptHandler( int iArg ) __attribute__( ( longcall ) );
static void prvRxInterruptHandler( int iArg )__attribute__( ( longcall ) );

/*-----------------------------------------------------------*/

/* Queues used to pass bytes into and out of the interrupt handlers.
NOTE:  This is not intended to be an example of an efficient interrupt handler,
but instead to load the kernel and interrupt mechanisms in order to test the
FreeRTOS port.  Using a FIFO, DMA, circular buffer, etc. architecture will
to improve efficiency. */
static QueueHandle_t xSerialTransmitQueue = NULL;
static QueueHandle_t xSerialReceiveQueue = NULL;
static volatile portBASE_TYPE xTransmitStatus = 0UL;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulReloadValue = 0UL;

	ulReloadValue = ( configPERIPHERAL_CLOCK_HZ / ( 48UL * ulWantedBaud ) ) - 1UL;

	if( NULL == xSerialTransmitQueue )
	{
		xSerialTransmitQueue = xQueueCreate( uxQueueLength, sizeof( char ) );
		xSerialReceiveQueue = xQueueCreate( uxQueueLength, sizeof( char ) );
	}

	/* Enable ASC0 Module. */
	unlock_wdtcon();
	{
		while ( 0 != ( WDT_CON0.reg & 0x1UL ) );
		ASC0_CLC.reg = 0x0200UL;
	}
	lock_wdtcon();

	/* Disable the Operation. */
	ASC0_CON.reg &= 0xFFFF7FFF;

	/* Set-up the GPIO Ports. */
	P3_IOCR0.reg = 0x00009000;	/* 3.0 ASC In, 3.1 Alt ASC Out */

	/* Write the baud rate. */
	ASC0_BG.reg = ulReloadValue;

	/* Reconfigure and re-initialise the Operation. */
	ASC0_PISEL.reg = 0UL;
	ASC0_CON.reg = 0UL;
	ASC0_CON.bits.M = 0x01; /* 8bit async. */
	ASC0_CON.bits.REN = 0x01; /* Receiver enabled. */
	ASC0_CON.bits.FDE = 0x01; /* Fractional divider enabled. */
	ASC0_CON.bits.BRS = 0x01; /* Divide by three. */
	ASC0_CON.bits.LB = 0x01; /* Loopback enabled. */
	ASC0_CON.bits.R = 0x01; /* Enable the baud rate generator. */

	/* Install the Tx interrupt. */
	if( 0 != _install_int_handler( configINTERRUPT_PRIORITY_TX, prvTxBufferInterruptHandler, 0 ) )
	{
		ASC0_TBSRC.reg = configINTERRUPT_PRIORITY_TX | 0x5000UL;
		xTransmitStatus = 0UL;
	}

	/* Install the Rx interrupt. */
	if( 0 != _install_int_handler( configINTERRUPT_PRIORITY_RX, prvRxInterruptHandler, 0 ) )
	{
		ASC0_RSRC.reg = configINTERRUPT_PRIORITY_RX | 0x5000UL;
	}

	/* COM Handle is never used by demo code. */
	return (xComPortHandle) pdPASS;
}
/*---------------------------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
unsigned short usChar;

	for( usChar = 0; usChar < usStringLength; usChar++ )
	{
		xSerialPutChar( pxPort, pcString[ usChar ], portMAX_DELAY );
	}
}
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* Just to remove compiler warnings about unused parameters. */
	( void )pxPort;

	return xQueueReceive( xSerialReceiveQueue, pcRxedChar, xBlockTime );
}
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
portBASE_TYPE xReturn = pdPASS;

	/* Just to remove compiler warnings about unused parameters. */
	( void )pxPort;

	/* Send the character to the interrupt handler. */
	xReturn = xQueueSend( xSerialTransmitQueue, &cOutChar, xBlockTime );

	/* Start the transmission of bytes if necessary. */
	prvCheckTransmit();

	return xReturn;
}
/*---------------------------------------------------------------------------*/

static void prvTxBufferInterruptHandler( int iArg )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
unsigned char ucTx;

	/* Just to remove compiler warnings about unused parameters. */
	( void ) iArg;

	/* ACK. */
	ASC0_TBSRC.reg |= 0x4000UL;
	xTransmitStatus = 1UL;

	/* TBUF Can be refilled. */
	if( pdPASS == xQueueReceiveFromISR( xSerialTransmitQueue, &ucTx, &xHigherPriorityTaskWoken ) )
	{
		ASC0_TBUF.reg = ucTx;
	}
	else
	{
		/* Failed to get a character out of the Queue. No longer busy. */
		xTransmitStatus = 0UL;
	}

	/* Finally end ISR and switch Task if necessary. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*---------------------------------------------------------------------------*/

static void prvRxInterruptHandler( int iArg )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
unsigned char ucRx;

	/* Just to remove compiler warnings about unused parameters. */
	( void ) iArg;

	/* Grab the character as early as possible. */
	ucRx = ( unsigned char ) ASC0_RBUF.reg;

	/* ACK. */
	ASC0_RSRC.reg |= 0x4000UL;

	/* Frame available in RBUF. */
	if( pdPASS != xQueueSendFromISR( xSerialReceiveQueue, &ucRx, &xHigherPriorityTaskWoken ) )
	{
		/* Error handling code can go here. */
	}

	/* Finally end ISR and switch Task if necessary. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*---------------------------------------------------------------------------*/

void prvCheckTransmit( void )
{
	/* Check to see if the interrupt handler is working its way through the
	buffer. */
	if( 0 == xTransmitStatus )
	{
		/* Not currently operational so kick off the first byte. */
		ASC0_TBSRC.reg |= 0x8000UL;
	}
}
/*---------------------------------------------------------------------------*/
