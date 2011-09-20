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


/* 
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

/* Library includes. */
#include "xparameters.h"
#include "xuartlite.h"
#include "xuartlite_l.h"

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

/* Structure that maintains information on the UART being used. */
static XUartLite xUART;

/*
 * Sample UART interrupt handler.  Note this is used to demonstrate the kernel
 * features and test the port - it is not intended to represent an efficient
 * implementation.
 */
static void vSerialISR( XUartLite *pxUART );

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* NOTE: The baud rate used by this driver is determined by the hardware
	parameterization of the UART Lite peripheral, and the baud value passed to
	this function has no effect. */
	( void ) ulWantedBaud;

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	/* Only initialise the UART if the queues were created correctly. */
	if( ( xRxedChars != NULL ) && ( xCharsForTx != NULL ) )
	{

		XUartLite_Initialize( &xUART, XPAR_RS232_UART_DEVICE_ID );
		XUartLite_ResetFifos( &xUART );
		XUartLite_DisableInterrupt( &xUART );

		if( xPortInstallInterruptHandler( XPAR_XPS_INTC_0_RS232_UART_INTERRUPT_INTR, ( XInterruptHandler )vSerialISR, (void *)&xUART ) == pdPASS )
		{
			/* xPortInstallInterruptHandler() could fail if 
			vPortSetupInterruptController() has not been called prior to this 
			function. */
			XUartLite_EnableInterrupt( &xUART );
		}
	}
	
	/* There is only one port so the handle is not used. */
	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed portCHAR cOutChar, portTickType xBlockTime )
{
portBASE_TYPE xReturn = pdTRUE;

	/* Just to remove compiler warning. */
	( void ) pxPort;

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

static void vSerialISR( XUartLite *pxUART )
{
unsigned portLONG ulISRStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE, lDidSomething;
portCHAR cChar;

	/* Just to remove compiler warning. */
	( void ) pxUART;

	do
	{
		lDidSomething = pdFALSE;

		ulISRStatus = XIo_In32( XPAR_RS232_UART_BASEADDR + XUL_STATUS_REG_OFFSET );

		if( ( ulISRStatus & XUL_SR_RX_FIFO_VALID_DATA ) != 0 )
		{
			/* A character is available - place it in the queue of received
			characters.  This might wake a task that was blocked waiting for 
			data. */
			cChar = ( portCHAR ) XIo_In32( XPAR_RS232_UART_BASEADDR + XUL_RX_FIFO_OFFSET );
			xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
			lDidSomething = pdTRUE;
		}
		
		if( ( ulISRStatus & XUL_SR_TX_FIFO_EMPTY ) != 0 )
		{
			/* There is space in the FIFO - if there are any characters queue for
			transmission they can be sent to the UART now.  This might unblock a
			task that was waiting for space to become available on the Tx queue. */
			if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
			{
				XIo_Out32( XPAR_RS232_UART_BASEADDR + XUL_TX_FIFO_OFFSET, cChar );
				lDidSomething = pdTRUE;
			}			
		}
	} while( lDidSomething == pdTRUE );

	/* If we woke any tasks we may require a context switch. */
	if( xHigherPriorityTaskWoken )
	{
		portYIELD_FROM_ISR();
	}
}



