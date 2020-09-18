/*
 * FreeRTOS Kernel V10.4.1
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

/*
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART0.
	
	***Note*** This example uses queues to send each character into an interrupt
	service routine and out of an interrupt service routine individually.  This
	is done to demonstrate queues being used in an interrupt, and to deliberately
	load the system to test the FreeRTOS port.  It is *NOT* meant to be an
	example of an efficient implementation.  An efficient implementation should
	use FIFOs or DMA if available, and only use FreeRTOS API functions when
	enough has been received to warrant a task being unblocked to process the
	data.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
#include "comtest2.h"

/* Library includes. */
#include "mcu.h"

/* Demo application includes. */
#include "serial.h"
/*-----------------------------------------------------------*/

/* Register bit definitions. */
#define serRX_INT_ENABLE		0x10
#define serTX_INT_ENABLE		0x08
#define serRX_ENABLE			0x02
#define serTX_ENABLE			0x01
#define serORE_ERROR_BIT		0x08
#define serFRE_ERROR_BIT		0x10
#define serPE_ERROR_BIT			0x20
#define serRX_INT				0x04
#define serTX_INT				0x02

/* Misc defines. */
#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serNO_BLOCK						( ( TickType_t ) 0 )

/*-----------------------------------------------------------*/

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Create the queues used to hold Rx/Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	
	/* If the queues were created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
		/* Ensure interrupts don't fire during the init process.  Interrupts
		will be enabled automatically when the first task start running. */
		portDISABLE_INTERRUPTS();
		
		/* Configure P21 and P22 for use by the UART. */
		FM3_GPIO->PFR2 |= ( 1 << 0x01 ) | ( 1 << 0x02 );
		
		/* SIN0_0 and SOT0_0. */
		FM3_GPIO->EPFR07 |= ( 1 << 6 );
		
		/* Reset. */
		FM3_MFS0_UART->SCR = 0x80;
		
		/* Enable output in mode 0. */
		FM3_MFS0_UART->SMR = 0x01;
		
		/* Clear all errors that may already be present. */
		FM3_MFS0_UART->SSR = 0x00;
		FM3_MFS0_UART->ESCR = 0x00;
		
		FM3_MFS0_UART->BGR = ( configCPU_CLOCK_HZ / 2UL ) / ( ulWantedBaud - 1UL );

		/* Enable Rx, Tx, and the Rx interrupt. */		
		FM3_MFS0_UART->SCR |= ( serRX_ENABLE | serTX_ENABLE | serRX_INT_ENABLE );
		
		/* Configure the NVIC for UART interrupts. */
		NVIC_ClearPendingIRQ( MFS0RX_IRQn );
		NVIC_EnableIRQ( MFS0RX_IRQn );
		
		/* The priority *MUST* be at or below
		configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY as FreeRTOS API functions
		are called in the interrupt handler. */
		NVIC_SetPriority( MFS0RX_IRQn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
		
		/* Do the same for the Tx interrupts. */
		NVIC_ClearPendingIRQ( MFS0TX_IRQn );
		NVIC_EnableIRQ( MFS0TX_IRQn );
		
		/* The priority *MUST* be at or below
		configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY as FreeRTOS API functions
		are called in the interrupt handler. */
		NVIC_SetPriority( MFS0TX_IRQn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
	}

	/* This demo file only supports a single port but we have to return
	something to comply with the standard demo header file. */
	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* The port handle is not required as this driver only supports one port. */
	( void ) pxPort;

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

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
signed char *pxNext;

	/* A couple of parameters that this port does not use. */
	( void ) usStringLength;
	( void ) pxPort;

	/* NOTE: This implementation does not handle the queue being full as no
	block time is used! */

	/* The port handle is not required as this driver only supports one UART. */
	( void ) pxPort;

	/* Send each character in the string, one at a time. */
	pxNext = ( signed char * ) pcString;
	while( *pxNext )
	{
		xSerialPutChar( pxPort, *pxNext, serNO_BLOCK );
		pxNext++;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
signed portBASE_TYPE xReturn;

	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) == pdPASS )
	{
		xReturn = pdPASS;
		
		/* Enable the UART Tx interrupt. */
		FM3_MFS0_UART->SCR |= serTX_INT_ENABLE;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

void MFS0RX_IRQHandler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
char cChar;

	if( ( FM3_MFS0_UART->SSR & ( serORE_ERROR_BIT | serFRE_ERROR_BIT | serPE_ERROR_BIT ) ) != 0 )
	{
		/* A PE, ORE or FRE error occurred.  Clear it. */
		FM3_MFS0_UART->SSR |= ( 1 << 7 );
		cChar = FM3_MFS0_UART->RDR;
	}
	else if( FM3_MFS0_UART->SSR & serRX_INT )
	{
		/* A character has been received on the USART, send it to the Rx
		handler task. */
		cChar = FM3_MFS0_UART->RDR;
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}	

	/* If sending or receiving from a queue has caused a task to unblock, and
	the unblocked task has a priority equal to or higher than the currently
	running task (the task this ISR interrupted), then xHigherPriorityTaskWoken
	will have automatically been set to pdTRUE within the queue send or receive
	function.  portEND_SWITCHING_ISR() will then ensure that this ISR returns
	directly to the higher priority unblocked task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void MFS0TX_IRQHandler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
char cChar;

	if( FM3_MFS0_UART->SSR & serTX_INT )
	{
		/* The interrupt was caused by the TX register becoming empty.  Are
		there any more characters to transmit? */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* A character was retrieved from the queue so can be sent to the
			USART now. */
			FM3_MFS0_UART->TDR = cChar;
		}
		else
		{
			/* Disable the Tx interrupt. */
			FM3_MFS0_UART->SCR &= ~serTX_INT_ENABLE;
		}		
	}	

	/* If sending or receiving from a queue has caused a task to unblock, and
	the unblocked task has a priority equal to or higher than the currently
	running task (the task this ISR interrupted), then xHigherPriorityTaskWoken
	will have automatically been set to pdTRUE within the queue send or receive
	function.  portEND_SWITCHING_ISR() will then ensure that this ISR returns
	directly to the higher priority unblocked task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}





	
