/*
    FreeRTOS V6.0.2 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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


/* 
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

/* Microblaze driver includes. */
#include "xuartlite_l.h"
#include "xintc_l.h"

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulControlReg, ulMask;

	/* NOTE: The baud rate used by this driver is determined by the hardware
	parameterization of the UART Lite peripheral, and the baud value passed to
	this function has no effect. */

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	if( ( xRxedChars ) && ( xCharsForTx ) )
	{
		/* Disable the interrupt. */
		XUartLite_mDisableIntr( XPAR_RS232_UART_BASEADDR );
		
		/* Flush the fifos. */
		ulControlReg = XIo_In32( XPAR_RS232_UART_BASEADDR + XUL_STATUS_REG_OFFSET );
		XIo_Out32( XPAR_RS232_UART_BASEADDR + XUL_CONTROL_REG_OFFSET, ulControlReg | XUL_CR_FIFO_TX_RESET | XUL_CR_FIFO_RX_RESET );

		/* Enable the interrupt again.  The interrupt controller has not yet been 
		initialised so there is no chance of receiving an interrupt until the 
		scheduler has been started. */
		XUartLite_mEnableIntr( XPAR_RS232_UART_BASEADDR );

		/* Enable the interrupt in the interrupt controller while maintaining 
		all the other bit settings. */
		ulMask = XIntc_In32( ( XPAR_OPB_INTC_0_BASEADDR + XIN_IER_OFFSET ) );
		ulMask |= XPAR_RS232_UART_INTERRUPT_MASK;
		XIntc_Out32( ( XPAR_OPB_INTC_0_BASEADDR + XIN_IER_OFFSET ), ( ulMask ) );
		XIntc_mAckIntr( XPAR_INTC_SINGLE_BASEADDR, 2 );
	}
	
	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
{
	/* The port handle is not required as this driver only supports one UART. */
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
{
portBASE_TYPE xReturn = pdTRUE;

	portENTER_CRITICAL();
	{
		/* If the UART FIFO is full we can block posting the new data on the
		Tx queue. */
		if( XUartLite_mIsTransmitFull( XPAR_RS232_UART_BASEADDR ) )
		{
			if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
			{
				xReturn = pdFAIL;
			}
		}
		/* Otherwise, if there is data already in the queue we should add the
		new data to the back of the queue to ensure the sequencing is 
		maintained. */
		else if( uxQueueMessagesWaiting( xCharsForTx ) )
		{
			if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
			{
				xReturn = pdFAIL;
			}			
		}
		/* If the UART FIFO is not full and there is no data already in the
		queue we can write directly to the FIFO without disrupting the 
		sequence. */
		else
		{
			XIo_Out32( XPAR_RS232_UART_BASEADDR + XUL_TX_FIFO_OFFSET, cOutChar );
		}
	}
	portEXIT_CRITICAL();

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/

void vSerialISR( void *pvBaseAddress )
{
unsigned long ulISRStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
char cChar;

	/* Determine the cause of the interrupt. */
    ulISRStatus = XIo_In32( XPAR_RS232_UART_BASEADDR + XUL_STATUS_REG_OFFSET );

    if( ( ulISRStatus & ( XUL_SR_RX_FIFO_FULL | XUL_SR_RX_FIFO_VALID_DATA ) ) != 0 )
	{
		/* A character is available - place it in the queue of received
		characters.  This might wake a task that was blocked waiting for 
		data. */
		cChar = ( char )XIo_In32( XPAR_RS232_UART_BASEADDR + XUL_RX_FIFO_OFFSET );
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
    }

    if( ( ulISRStatus & XUL_SR_TX_FIFO_EMPTY ) != 0 )
    {
		/* There is space in the FIFO - if there are any characters queue for
		transmission they can be send to the UART now.  This might unblock a
		task that was waiting for space to become available on the Tx queue. */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			XIo_Out32( XPAR_RS232_UART_BASEADDR + XUL_TX_FIFO_OFFSET, cChar );
		}
    }

	/* If we woke any tasks we may require a context switch. */
	if( xHigherPriorityTaskWoken )
	{
		portYIELD_FROM_ISR();
	}
}
