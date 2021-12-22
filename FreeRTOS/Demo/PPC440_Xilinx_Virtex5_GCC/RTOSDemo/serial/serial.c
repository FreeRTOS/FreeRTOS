/*
 * FreeRTOS V202112.00
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
static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx; 

/* Structure that maintains information on the UART being used. */
static XUartLite xUART;

/*
 * Sample UART interrupt handler.  Note this is used to demonstrate the kernel
 * features and test the port - it is not intended to represent an efficient
 * implementation.
 */
static void vSerialISR( XUartLite *pxUART );

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* NOTE: The baud rate used by this driver is determined by the hardware
	parameterization of the UART Lite peripheral, and the baud value passed to
	this function has no effect. */
	( void ) ulWantedBaud;

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* Only initialise the UART if the queues were created correctly. */
	if( ( xRxedChars != NULL ) && ( xCharsForTx != NULL ) )
	{

		XUartLite_Initialize( &xUART, XPAR_RS232_UART_1_DEVICE_ID );
		XUartLite_ResetFifos( &xUART );
		XUartLite_DisableInterrupt( &xUART );

		if( xPortInstallInterruptHandler( XPAR_XPS_INTC_0_RS232_UART_1_INTERRUPT_INTR, ( XInterruptHandler )vSerialISR, (void *)&xUART ) == pdPASS )
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

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
portBASE_TYPE xReturn = pdTRUE;

	/* Just to remove compiler warning. */
	( void ) pxPort;

	portENTER_CRITICAL();
	{
		/* If the UART FIFO is full we can block posting the new data on the
		Tx queue. */
		if( XUartLite_mIsTransmitFull( XPAR_RS232_UART_1_BASEADDR ) )
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
			XIo_Out32( XPAR_RS232_UART_1_BASEADDR + XUL_TX_FIFO_OFFSET, cOutChar );
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
unsigned long ulISRStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE, lDidSomething;
char cChar;

	/* Just to remove compiler warning. */
	( void ) pxUART;

	do
	{
		lDidSomething = pdFALSE;

		ulISRStatus = XIo_In32( XPAR_RS232_UART_1_BASEADDR + XUL_STATUS_REG_OFFSET );

		if( ( ulISRStatus & XUL_SR_RX_FIFO_VALID_DATA ) != 0 )
		{
			/* A character is available - place it in the queue of received
			characters.  This might wake a task that was blocked waiting for 
			data. */
			cChar = ( char ) XIo_In32( XPAR_RS232_UART_1_BASEADDR + XUL_RX_FIFO_OFFSET );
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
				XIo_Out32( XPAR_RS232_UART_1_BASEADDR + XUL_TX_FIFO_OFFSET, cChar );
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



