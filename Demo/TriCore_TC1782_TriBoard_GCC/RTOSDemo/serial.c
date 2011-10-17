/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.


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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
/*---------------------------------------------------------------------------*/

#define serialINTERRUPT_PRIORITY_TX			16
#define serialINTERRUPT_PRIORITY_RX			18
/*---------------------------------------------------------------------------*/

/*
 * This reference is required by the Save/Restore Context Macros.
 */
extern volatile unsigned portBASE_TYPE * pxCurrentTCB;
/*-----------------------------------------------------------*/

/**
 * This function will check to see whether the Serial Transmit Interrupt is currently
 * activated, meaning that the interrupt is working through the back log of bytes
 * that it needs to send. If the ISR is not enabled, then it will be triggered to send
 * the first byte and it will be automatically re-triggered when that byte has been
 * sent. When the queue is exhausted, the ISR disables itself.
 * This function is privileged because it will trigger an interrupt.
 */
static void prvCheckTransmit( void ) PRIVILEGED_FUNCTION;
/*-----------------------------------------------------------*/

void vSerialTransmitBufferInterrupt( int iArg ) __attribute__((longcall));
void vSerialReceiveInterrupt( int iArg )__attribute__((longcall));
/*-----------------------------------------------------------*/

static xQueueHandle xSerialTransmitQueue = NULL;
static xQueueHandle xSerialReceiveQueue = NULL;
static volatile portBASE_TYPE xTransmitStatus = 0UL;
/*---------------------------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulReloadValue = 0UL;
	ulReloadValue = ( configPERIPHERAL_CLOCK_HZ / ( 32 * ulWantedBaud ) ) - 1;

	if ( NULL == xSerialTransmitQueue )
	{
		xSerialTransmitQueue = xQueueCreate( uxQueueLength, sizeof( char ) );
		xSerialReceiveQueue = xQueueCreate( uxQueueLength, sizeof( char ) );
	}

	/* Enable ASC0 Module. */
	unlock_wdtcon();
		while ( 0 != ( WDT_CON0.reg & 0x1UL ) );
		ASC0_CLC.reg = 0x0200UL;
	lock_wdtcon();

	/* Disable the Operation. */
	ASC0_CON.reg &= 0xFFFF7FFF;

	/* Set-up the GPIO Ports. */
	P3_IOCR0.reg = 0x00009000;	/* 3.0 ASC In, 3.1 Alt ASC Out */
	/* Do we need to set 3.1 high? OMR.PS1 = 1??? */

	/* Write the Baudrate. */
	ASC0_BG.reg = ulReloadValue;

	/* Reconfigure and re-initialise the Operation. */
	ASC0_PISEL.reg = 0UL;
	ASC0_CON.reg = 0x00008011;	/* 1 Start, 1 Stop, 8 Data, No Parity, No Error Checking, Receive On, Module On. */

	/* Install the Tx interrupt. */
	if ( 0 != _install_int_handler( serialINTERRUPT_PRIORITY_TX, vSerialTransmitBufferInterrupt, 0 ) )
	{
		ASC0_TBSRC.reg = serialINTERRUPT_PRIORITY_TX | 0x5000UL;
		xTransmitStatus = 0UL;
	}

	/* Install the Rx interrupt. */
	if ( 0 != _install_int_handler( serialINTERRUPT_PRIORITY_RX, vSerialReceiveInterrupt, 0 ) )
	{
		ASC0_RSRC.reg = serialINTERRUPT_PRIORITY_RX | 0x5000UL;
	}

	/* COM Handle is never used by demo code. */
	return (xComPortHandle) pdPASS;
}
/*---------------------------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
unsigned short usChar;
	for ( usChar = 0; usChar < usStringLength; usChar++ )
	{
		(void)xSerialPutChar( pxPort, pcString[ usChar ], portMAX_DELAY );
	}
}
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
{
	return xQueueReceive( xSerialReceiveQueue, pcRxedChar, xBlockTime );
	(void)pxPort;
}
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
{
portBASE_TYPE xReturn = pdPASS;

	/* Send the character to the interrupt handler. */
	xReturn = xQueueSend( xSerialTransmitQueue, &cOutChar, xBlockTime );

	/* Start the transmission of bytes if necessary. */
	prvCheckTransmit();

	return xReturn;

	(void)pxPort;
}
/*---------------------------------------------------------------------------*/

void vSerialTransmitBufferInterrupt( int iArg )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
unsigned char ucTx;

	/* ACK. */
	ASC0_TBSRC.reg |= 0x4000UL;
	xTransmitStatus = 1UL;

	/* Enter the Critical Section. */
	portINTERRUPT_ENTER_CRITICAL();
	{
		/* TBUF Can be refilled. */
		if ( pdPASS == xQueueReceiveFromISR( xSerialTransmitQueue, &ucTx, &xHigherPriorityTaskWoken ) )
		{
			ASC0_TBUF.reg = ucTx;
		}
		else
		{
			/* Failed to get a character out of the Queue. No longer busy. */
			xTransmitStatus = 0UL;
		}
	}
	portINTERRUPT_EXIT_CRITICAL();

	/* Finally end ISR and switch Task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );

	(void)iArg;
}
/*---------------------------------------------------------------------------*/

void vSerialReceiveInterrupt( int iArg )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
unsigned char ucRx;

	/* Grab the character as early as possible. */
	ucRx = (unsigned char)ASC0_RBUF.reg;

	/* ACK. */
	ASC0_RSRC.reg |= 0x4000UL;

	/* Enter the Critical Section. */
	portINTERRUPT_ENTER_CRITICAL();
	{
		/* Frame available in RBUF. */
		if ( pdPASS != xQueueSendFromISR( xSerialReceiveQueue, &ucRx, &xHigherPriorityTaskWoken ) )
		{
			/* Need some error handling code. */
		}
	}
	portINTERRUPT_EXIT_CRITICAL();

	/* Finally end ISR and switch Task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );

	(void)iArg;
}
/*---------------------------------------------------------------------------*/

void prvCheckTransmit( void )
{
	/* Check to see if the interrupt handler is working its way through the buffer. */
	if ( 0 == xTransmitStatus )
	{
		/* Not currently operational so kick off the first byte. */
		ASC0_TBSRC.reg |= 0x8000UL;
	}
}
/*---------------------------------------------------------------------------*/
