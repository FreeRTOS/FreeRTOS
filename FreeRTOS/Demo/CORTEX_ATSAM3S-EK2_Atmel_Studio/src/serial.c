/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR USART1.

	***Note*** This example uses queues to send each character into an interrupt
	service routine and out of an interrupt service routine individually.  This
	is done to demonstrate queues being used in an interrupt, and to deliberately
	load the system to test the FreeRTOS port.  It is *NOT* meant to be an
	example of an efficient implementation.  An efficient implementation should
	use FIFO's or DMA if available, and only use FreeRTOS API functions when
	enough has been received to warrant a task being unblocked to process the
	data.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
#include "comtest2.h"

/* Library includes. */
#include "asf.h"

/* Demo application includes. */
#include "demo_serial.h"
/*-----------------------------------------------------------*/

/* Misc defines. */
#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serNO_BLOCK						( ( TickType_t ) 0 )
#define serPMC_USART_ID					( BOARD_ID_USART )

/* The USART supported by this file. */
#define serUSART_PORT					( USART1 )
#define serUSART_IRQ					( USART1_IRQn )

/* Every bit in the interrupt mask. */
#define serMASK_ALL_INTERRUPTS			( 0xffffffffUL )

/*-----------------------------------------------------------*/

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

/*-----------------------------------------------------------*/


/*
 * See the serial.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
uint32_t ulChar;
xComPortHandle xReturn;
const sam_usart_opt_t xUSARTSettings =
{
	ulWantedBaud,
	US_MR_CHRL_8_BIT,
	US_MR_PAR_NO,
	US_MR_NBSTOP_1_BIT,
	US_MR_CHMODE_NORMAL,
	0 /* Only used in IrDA mode. */
};

	/* Create the queues used to hold Rx/Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* If the queues were created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
		/* Enable the peripheral clock in the PMC. */
		pmc_enable_periph_clk( serPMC_USART_ID );

		/* Configure USART in serial mode. */
		usart_init_rs232( serUSART_PORT, &xUSARTSettings, sysclk_get_cpu_hz() );

		/* Disable all the interrupts. */
		usart_disable_interrupt( serUSART_PORT, serMASK_ALL_INTERRUPTS );

		/* Enable the receiver and transmitter. */
		usart_enable_tx( serUSART_PORT );
		usart_enable_rx( serUSART_PORT );

		/* Clear any characters before enabling interrupt. */
		usart_getchar( serUSART_PORT, &ulChar );

		/* Enable Rx end interrupt. */
		usart_enable_interrupt( serUSART_PORT, US_IER_RXRDY );

		/* Configure and enable interrupt of USART. */
		NVIC_SetPriority( serUSART_IRQ, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
		NVIC_EnableIRQ( serUSART_IRQ );
	}
	else
	{
		xReturn = ( xComPortHandle ) 0;
	}

	/* This demo file only supports a single port but we have to return
	something to comply with the standard demo header file. */
	return xReturn;
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

	/* The port handle is not required as this driver only supports USART1. */
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

	/* This simple example only supports one port. */
	( void ) pxPort;

	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) == pdPASS )
	{
		xReturn = pdPASS;
		usart_enable_interrupt( serUSART_PORT, US_IER_TXRDY );
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
	( void ) xPort;
}
/*-----------------------------------------------------------*/

/*
 * It should be noted that the com test tasks (which use make use of this file)
 * are included to demonstrate queues being used to communicate between tasks
 * and interrupts, and to demonstrate a context switch being performed from
 * inside an interrupt service routine.  The serial driver used here is *not*
 * intended to represent an efficient implementation.  Real applications should
 * make use of the USARTS peripheral DMA channel (PDC).
 */
void USART1_Handler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
uint8_t ucChar;
uint32_t ulChar;
uint32_t ulUSARTStatus, ulUSARTMask;

	ulUSARTStatus = usart_get_status( serUSART_PORT );
	ulUSARTMask = usart_get_interrupt_mask( serUSART_PORT );
	ulUSARTStatus &= ulUSARTMask;

	if( ( ulUSARTStatus & US_CSR_TXRDY ) != 0UL )
	{
		/* The interrupt was caused by the TX register becoming empty.  Are
		there any more characters to transmit? */
		if( xQueueReceiveFromISR( xCharsForTx, &ucChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* A character was retrieved from the queue so can be sent to the
			USART now. */
			usart_putchar( serUSART_PORT, ( uint32_t ) ucChar );
		}
		else
		{
			usart_disable_interrupt( serUSART_PORT, US_IER_TXRDY );
		}
	}

	if( ( ulUSARTStatus & US_CSR_RXRDY ) != 0UL )
	{
		/* A character has been received on the USART, send it to the Rx
		handler task. */
		usart_getchar( serUSART_PORT, &ulChar );
		ucChar = ( uint8_t ) ( ulChar & 0xffUL );
		xQueueSendFromISR( xRxedChars, &ucChar, &xHigherPriorityTaskWoken );
	}

	/* If sending or receiving from a queue has caused a task to unblock, and
	the unblocked task has a priority equal to or higher than the currently
	running task (the task this ISR interrupted), then xHigherPriorityTaskWoken
	will have automatically been set to pdTRUE within the queue send or receive
	function.  portEND_SWITCHING_ISR() will then ensure that this ISR returns
	directly to the higher priority unblocked task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}






