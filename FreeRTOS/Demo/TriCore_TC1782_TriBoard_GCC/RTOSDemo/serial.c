/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
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
static xQueueHandle xSerialTransmitQueue = NULL;
static xQueueHandle xSerialReceiveQueue = NULL;
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

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
{
	/* Just to remove compiler warnings about unused parameters. */
	( void )pxPort;

	return xQueueReceive( xSerialReceiveQueue, pcRxedChar, xBlockTime );
}
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
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
