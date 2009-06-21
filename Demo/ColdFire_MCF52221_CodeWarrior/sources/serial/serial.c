/*
	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.

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

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
const unsigned portLONG ulBaudRateDivisor = ( configCPU_CLOCK_HZ / ( 32UL * ulWantedBaud ) );

	/* Create the queues used by the com test task. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

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

	MCF_UART0_UBG1 = ( unsigned portCHAR ) ( ( ulBaudRateDivisor >> 8UL ) & 0xffUL );
	MCF_UART0_UBG2 = ( unsigned portCHAR ) ( ulBaudRateDivisor & 0xffUL );

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
unsigned portCHAR ucChar;
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







