/*
    FreeRTOS V7.1.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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

static xQueueHandle xSerialTxQueue = NULL;
static xQueueHandle xSerialRxQueue = NULL;
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

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
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
