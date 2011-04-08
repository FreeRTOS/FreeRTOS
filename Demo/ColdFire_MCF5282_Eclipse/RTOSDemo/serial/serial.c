/*
    FreeRTOS V7.0.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.

NOTE:  This driver is primarily to test the scheduler functionality.  It does
not effectively use the buffers or DMA and is therefore not intended to be
an example of an efficient driver. */

/* Standard include file. */
#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo app include files. */
#include "serial.h"

/* Hardware definitions. */
#define serNO_PARITY		( ( unsigned portCHAR ) 0x02 << 3 )
#define ser8DATA_BITS		( ( unsigned portCHAR ) 0x03 )
#define ser1STOP_BIT		( ( unsigned portCHAR ) 0x07 )
#define serSYSTEM_CLOCK		( ( unsigned portCHAR ) 0xdd )
#define serTX_OUTPUT		( ( unsigned portCHAR ) 0x04 )
#define serRX_INPUT			( ( unsigned portCHAR ) 0x08 )
#define serTX_ENABLE		( ( unsigned portCHAR ) 0x04 )
#define serRX_ENABLE		( ( unsigned portCHAR ) 0x01 )
#define serTX_INT			( ( unsigned portCHAR ) 0x01 )
#define serRX_INT			( ( unsigned portCHAR ) 0x02 )


/* The queues used to communicate between tasks and ISR's. */
static xQueueHandle xRxedChars;
static xQueueHandle xCharsForTx;

/* Flag used to indicate the tx status. */
static portBASE_TYPE xTxHasEnded = pdTRUE;

/*-----------------------------------------------------------*/

/* The UART interrupt handler. */
void __attribute__( ( interrupt ) ) __cs3_isr_interrupt_78( void );

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
const unsigned portLONG ulBaudRateDivisor = ( configCPU_CLOCK_HZ / ( 32UL * ulWantedBaud ) );

	/* Create the queues used by the com test task. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	xTxHasEnded = pdTRUE;

	/* Set the pins to UART mode. */
	MCF_PAD_PUAPAR |= ( serTX_OUTPUT | serRX_INPUT );

	/* Reset the peripheral. */
	MCF_UART1_UCR = MCF_UART_UCR_RESET_RX;
	MCF_UART1_UCR = MCF_UART_UCR_RESET_TX;
	MCF_UART1_UCR = MCF_UART_UCR_RESET_ERROR;
	MCF_UART1_UCR = MCF_UART_UCR_RESET_BKCHGINT;
	MCF_UART1_UCR = MCF_UART_UCR_RESET_MR | MCF_UART_UCR_RX_DISABLED | MCF_UART_UCR_TX_DISABLED;

	/* Configure the UART. */
	MCF_UART1_UMR1 = serNO_PARITY | ser8DATA_BITS;
	MCF_UART1_UMR2 = ser1STOP_BIT;
	MCF_UART1_UCSR = serSYSTEM_CLOCK;

	MCF_UART1_UBG1 = ( unsigned portCHAR ) ( ( ulBaudRateDivisor >> 8UL ) & 0xffUL );
	MCF_UART1_UBG2 = ( unsigned portCHAR ) ( ulBaudRateDivisor & 0xffUL );

	/* Turn it on. */
	MCF_UART1_UCR = serTX_ENABLE | serRX_ENABLE;

	/* Configure the interrupt controller.  Run the UARTs above the kernel
	interrupt priority for demo purposes. */
    MCF_INTC0_ICR14 = ( ( configMAX_SYSCALL_INTERRUPT_PRIORITY - 2  ) << 3 );
    MCF_INTC0_IMRL &= ~( MCF_INTC_IMRL_INT_MASK14 | 0x01 );

	/* The Tx interrupt is not enabled until there is data to send. */
	MCF_UART1_UIMR = serRX_INT;

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
	if( xTxHasEnded != pdFALSE )
	{
		xTxHasEnded = pdFALSE;
		MCF_UART1_UIMR = serRX_INT | serTX_INT;
	}

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	( void ) xPort;
}
/*-----------------------------------------------------------*/

void __cs3_isr_interrupt_78( void )
{
unsigned portCHAR ucChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE, xDoneSomething = pdTRUE;

	while( xDoneSomething != pdFALSE )
	{
		xDoneSomething = pdFALSE;

		/* Does the tx buffer contain space? */
		if( ( MCF_UART1_USR & MCF_UART_USR_TXRDY ) != 0x00 )
		{
			/* Are there any characters queued to be sent? */
			if( xQueueReceiveFromISR( xCharsForTx, &ucChar, &xHigherPriorityTaskWoken ) == pdTRUE )
			{
				/* Send the next char. */
				MCF_UART1_UTB = ucChar;
				xDoneSomething = pdTRUE;
			}
			else
			{
				/* Turn off the Tx interrupt until such time as another character
				is being transmitted. */
				MCF_UART1_UIMR = serRX_INT;
				xTxHasEnded = pdTRUE;
			}
		}

		if( MCF_UART1_USR & MCF_UART_USR_RXRDY )
		{
			ucChar = MCF_UART1_URB;
			xQueueSendFromISR( xRxedChars, &ucChar, &xHigherPriorityTaskWoken );
			xDoneSomething = pdTRUE;
		}
	}

    portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}







