/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
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

#include <device.h>
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"
#include "serial.h"
/*---------------------------------------------------------------------------*/

#define serialSTRING_DELAY_TICKS		( portMAX_DELAY )
/*---------------------------------------------------------------------------*/

CY_ISR_PROTO( vUartRxISR );
CY_ISR_PROTO( vUartTxISR );
/*---------------------------------------------------------------------------*/

static QueueHandle_t xSerialTxQueue = NULL;
static QueueHandle_t xSerialRxQueue = NULL;
/*---------------------------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Configure Rx. */
	xSerialRxQueue = xQueueCreate( uxQueueLength, sizeof( signed char ) );	
	isr_UART1_RX_BYTE_RECEIVED_ClearPending();
	isr_UART1_RX_BYTE_RECEIVED_StartEx(vUartRxISR);

	/* Configure Tx */
	xSerialTxQueue = xQueueCreate( uxQueueLength, sizeof( signed char ) );
	isr_UART1_TX_BYTE_COMPLETE_ClearPending() ;
	isr_UART1_TX_BYTE_COMPLETE_StartEx(vUartTxISR);

	/* Clear the interrupt modes for the Tx for the time being. */
	UART_1_SetTxInterruptMode( 0 );

	/* Both configured successfully. */
	return ( xComPortHandle )( xSerialTxQueue && xSerialRxQueue );
}
/*---------------------------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
unsigned short usIndex = 0;

	for( usIndex = 0; usIndex < usStringLength; usIndex++ )
	{
		/* Check for pre-mature end of line. */
		if( '\0' == pcString[ usIndex ] )
		{
			break;
		}
		
		/* Send out, one character at a time. */
		if( pdTRUE != xSerialPutChar( NULL, pcString[ usIndex ], serialSTRING_DELAY_TICKS ) )
		{
			/* Failed to send, this will be picked up in the receive comtest task. */
		}
	}
}
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
portBASE_TYPE xReturn = pdFALSE;

	if( pdTRUE == xQueueReceive( xSerialRxQueue, pcRxedChar, xBlockTime ) )
	{
		/* Picked up a character. */
		xReturn = pdTRUE;
	}
	return xReturn;
}
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
portBASE_TYPE xReturn = pdFALSE;

	/* The ISR is processing characters is so just add to the end of the queue. */
	if( pdTRUE == xQueueSend( xSerialTxQueue, &cOutChar, xBlockTime ) )
	{	
		xReturn = pdTRUE;
	}
	else
	{
		/* The queue is probably full. */
		xReturn = pdFALSE;
	}

	/* Make sure that the interrupt will fire in the case where:
	    Currently sending so the Tx Complete will fire.
	    Not sending so the Empty will fire.	*/
	taskENTER_CRITICAL();
		UART_1_SetTxInterruptMode( UART_1_TX_STS_COMPLETE | UART_1_TX_STS_FIFO_EMPTY );
	taskEXIT_CRITICAL();
	
	return xReturn;
}
/*---------------------------------------------------------------------------*/

CY_ISR(vUartRxISR)
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
volatile unsigned char ucStatus = 0;
signed char cInChar = 0;
unsigned long ulMask = 0;

	/* Read the status to acknowledge. */
	ucStatus = UART_1_ReadRxStatus();

	/* Only interested in a character being received. */
	if( 0 != ( ucStatus & UART_1_RX_STS_FIFO_NOTEMPTY ) )
	{
		/* Get the character. */
		cInChar = UART_1_GetChar();
		
		/* Mask off the other RTOS interrupts to interact with the queue. */
		ulMask = portSET_INTERRUPT_MASK_FROM_ISR();
		{
			/* Try to deliver the character. */
			if( pdTRUE != xQueueSendFromISR( xSerialRxQueue, &cInChar, &xHigherPriorityTaskWoken ) )
			{
				/* Run out of space. */
			}
		}
		portCLEAR_INTERRUPT_MASK_FROM_ISR( ulMask );
	}

	/* If we delivered the character then a context switch might be required.
	xHigherPriorityTaskWoken was set to pdFALSE on interrupt entry.  If calling 
	xQueueSendFromISR() caused a task to unblock, and the unblocked task has
	a priority equal to or higher than the currently running task (the task this
	ISR interrupted), then xHigherPriorityTaskWoken will have been set to pdTRUE and
	portEND_SWITCHING_ISR() will request a context switch to the newly unblocked
	task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*---------------------------------------------------------------------------*/

CY_ISR(vUartTxISR)
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
volatile unsigned char ucStatus = 0;
signed char cOutChar = 0;
unsigned long ulMask = 0;

	/* Read the status to acknowledge. */
	ucStatus = UART_1_ReadTxStatus();
	
	/* Check to see whether this is a genuine interrupt. */
	if( ( 0 != ( ucStatus & UART_1_TX_STS_COMPLETE ) ) || ( 0 != ( ucStatus & UART_1_TX_STS_FIFO_EMPTY ) ) )
	{	
		/* Mask off the other RTOS interrupts to interact with the queue. */
		ulMask = portSET_INTERRUPT_MASK_FROM_ISR();
		{
			if( pdTRUE == xQueueReceiveFromISR( xSerialTxQueue, &cOutChar, &xHigherPriorityTaskWoken ) )
			{
				/* Send the next character. */
				UART_1_PutChar( cOutChar );			

				/* If we are firing, then the only interrupt we are interested in
				is the Complete. The application code will add the Empty interrupt
				when there is something else to be done. */
				UART_1_SetTxInterruptMode( UART_1_TX_STS_COMPLETE );
			}
			else
			{
				/* There is no work left so disable the interrupt until the application 
				puts more into the queue. */
				UART_1_SetTxInterruptMode( 0 );
			}
		}
		portCLEAR_INTERRUPT_MASK_FROM_ISR( ulMask );
	}

	/* If we delivered the character then a context switch might be required.
	xHigherPriorityTaskWoken was set to pdFALSE on interrupt entry.  If calling 
	xQueueSendFromISR() caused a task to unblock, and the unblocked task has
	a priority equal to or higher than the currently running task (the task this
	ISR interrupted), then xHigherPriorityTaskWoken will have been set to pdTRUE and
	portEND_SWITCHING_ISR() will request a context switch to the newly unblocked
	task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*---------------------------------------------------------------------------*/
