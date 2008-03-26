/*
	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

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

		if( xPortInstallInterruptHandler( XPAR_OPB_INTC_0_RS232_UART_INTERRUPT_INTR, ( XInterruptHandler )vSerialISR, (void *)&xUART ) == pdPASS )
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
portBASE_TYPE xTaskWokenByTx = pdFALSE, xTaskWokenByRx = pdFALSE, lDidSomething;
portCHAR cChar;

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
			xTaskWokenByRx = xQueueSendFromISR( xRxedChars, &cChar, xTaskWokenByRx );
			lDidSomething = pdTRUE;
		}
		
		if( ( ulISRStatus & XUL_SR_TX_FIFO_EMPTY ) != 0 )
		{
			/* There is space in the FIFO - if there are any characters queue for
			transmission they can be sent to the UART now.  This might unblock a
			task that was waiting for space to become available on the Tx queue. */
			if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWokenByTx ) == pdTRUE )
			{
				XIo_Out32( XPAR_RS232_UART_BASEADDR + XUL_TX_FIFO_OFFSET, cChar );
				lDidSomething = pdTRUE;
			}			
		}
	} while( lDidSomething == pdTRUE );

	/* If we woke any tasks we may require a context switch. */
	if( xTaskWokenByTx || xTaskWokenByRx )
	{
		portYIELD_FROM_ISR();
	}
}



