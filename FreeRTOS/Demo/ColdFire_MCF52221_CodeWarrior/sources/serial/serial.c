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
#define serNO_PARITY		( ( unsigned char ) 0x02 << 3 )
#define ser8DATA_BITS		( ( unsigned char ) 0x03 )
#define ser1STOP_BIT		( ( unsigned char ) 0x07 )
#define serSYSTEM_CLOCK		( ( unsigned char ) 0xdd )
#define serTX_ENABLE		( ( unsigned char ) 0x04 )
#define serRX_ENABLE		( ( unsigned char ) 0x01 )
#define serTX_INT			( ( unsigned char ) 0x01 )
#define serRX_INT			( ( unsigned char ) 0x02 )


/* The queues used to communicate between tasks and ISR's. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

/* Flag used to indicate the tx status. */
static portBASE_TYPE xTxHasEnded = pdTRUE;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
const unsigned long ulBaudRateDivisor = ( configCPU_CLOCK_HZ / ( 32UL * ulWantedBaud ) );

	/* Create the queues used by the com test task. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	xTxHasEnded = pdTRUE;

	/* Set the pins to UART mode. */
	MCF_GPIO_PUAPAR |= MCF_GPIO_PUAPAR_UTXD0_UTXD0;
	MCF_GPIO_PUAPAR |= MCF_GPIO_PUAPAR_URXD0_URXD0;

	/* Reset the peripheral. */
	MCF_UART0_UCR = MCF_UART_UCR_RESET_RX;
	MCF_UART0_UCR = MCF_UART_UCR_RESET_TX;
	MCF_UART0_UCR = MCF_UART_UCR_RESET_ERROR;
	MCF_UART0_UCR = MCF_UART_UCR_RESET_BKCHGINT;
	MCF_UART0_UCR = MCF_UART_UCR_RESET_MR | MCF_UART_UCR_RX_DISABLED | MCF_UART_UCR_TX_DISABLED;

	/* Configure the UART. */
	MCF_UART0_UMR1 = serNO_PARITY | ser8DATA_BITS;
	MCF_UART0_UMR2 = ser1STOP_BIT;
	MCF_UART0_UCSR = serSYSTEM_CLOCK;

	MCF_UART0_UBG1 = ( unsigned char ) ( ( ulBaudRateDivisor >> 8UL ) & 0xffUL );
	MCF_UART0_UBG2 = ( unsigned char ) ( ulBaudRateDivisor & 0xffUL );

	/* Turn it on. */
	MCF_UART0_UCR = serTX_ENABLE | serRX_ENABLE;

	/* Configure the interrupt controller.  Run the UARTs above the kernel
	interrupt priority for demo purposes. */
    MCF_INTC0_ICR13 = ( ( configMAX_SYSCALL_INTERRUPT_PRIORITY - 1  ) << 3 );
    MCF_INTC0_IMRL &= ~( MCF_INTC_IMRL_INT_MASK13 | 0x01 );

	/* The Tx interrupt is not enabled until there is data to send. */
	MCF_UART0_UIMR = serRX_INT;

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
		MCF_UART0_UIMR = serRX_INT | serTX_INT;
	}

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	( void ) xPort;
}
/*-----------------------------------------------------------*/

__declspec(interrupt:0) void vUART0InterruptHandler( void )
{
unsigned char ucChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE, xDoneSomething = pdTRUE;

	while( xDoneSomething != pdFALSE )
	{
		xDoneSomething = pdFALSE;

		/* Does the tx buffer contain space? */
		if( ( MCF_UART0_USR & MCF_UART_USR_TXRDY ) != 0x00 )
		{
			/* Are there any characters queued to be sent? */
			if( xQueueReceiveFromISR( xCharsForTx, &ucChar, &xHigherPriorityTaskWoken ) == pdTRUE )
			{
				/* Send the next char. */
				MCF_UART0_UTB = ucChar;
				xDoneSomething = pdTRUE;
			}
			else
			{
				/* Turn off the Tx interrupt until such time as another character
				is being transmitted. */
				MCF_UART0_UIMR = serRX_INT;
				xTxHasEnded = pdTRUE;
			}
		}

		if( MCF_UART0_USR & MCF_UART_USR_RXRDY )
		{
			ucChar = MCF_UART0_URB;
			xQueueSendFromISR( xRxedChars, &ucChar, &xHigherPriorityTaskWoken );
			xDoneSomething = pdTRUE;
		}
	}

    portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}







