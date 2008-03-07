/*
	FreeRTOS.org V4.7.2 - Copyright (C) 2003-2008 Richard Barry.

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

	Please ensure to read the configuration and relevant port sections of the 
	online documentation.

	+++ http://www.FreeRTOS.org +++
	Documentation, latest information, license and contact details.  

	+++ http://www.SafeRTOS.com +++
	A version that is certified for use in safety critical systems.

	+++ http://www.OpenRTOS.com +++
	Commercial support, development, porting, licensing and training services.

	***************************************************************************
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

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned portLONG ulControlReg, ulMask;

	/* NOTE: The baud rate used by this driver is determined by the hardware
	parameterization of the UART Lite peripheral, and the baud value passed to
	this function has no effect. */

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

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

void vSerialISR( void *pvBaseAddress )
{
unsigned portLONG ulISRStatus;
portBASE_TYPE xTaskWokenByTx = pdFALSE, xTaskWokenByRx = pdFALSE;
portCHAR cChar;

	/* Determine the cause of the interrupt. */
    ulISRStatus = XIo_In32( XPAR_RS232_UART_BASEADDR + XUL_STATUS_REG_OFFSET );

    if( ( ulISRStatus & ( XUL_SR_RX_FIFO_FULL | XUL_SR_RX_FIFO_VALID_DATA ) ) != 0 )
	{
		/* A character is available - place it in the queue of received
		characters.  This might wake a task that was blocked waiting for 
		data. */
		cChar = ( portCHAR )XIo_In32( XPAR_RS232_UART_BASEADDR + XUL_RX_FIFO_OFFSET );
		xTaskWokenByRx = xQueueSendFromISR( xRxedChars, &cChar, xTaskWokenByRx );
    }

    if( ( ulISRStatus & XUL_SR_TX_FIFO_EMPTY ) != 0 )
    {
		/* There is space in the FIFO - if there are any characters queue for
		transmission they can be send to the UART now.  This might unblock a
		task that was waiting for space to become available on the Tx queue. */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWokenByTx ) == pdTRUE )
		{
			XIo_Out32( XPAR_RS232_UART_BASEADDR + XUL_TX_FIFO_OFFSET, cChar );
		}
    }

	/* If we woke any tasks we may require a context switch. */
	if( xTaskWokenByTx || xTaskWokenByRx )
	{
		portYIELD_FROM_ISR();
	}
}
