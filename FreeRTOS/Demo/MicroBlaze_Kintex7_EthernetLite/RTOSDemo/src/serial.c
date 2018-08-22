/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR a UARTLite peripheral.

	NOTE:  This is not intended to represent an efficient driver.  It is
	designed to test the FreeRTOS port.  Normally a UART driver would use a DMA,
	or at least a circular RAM buffer rather than a queue.  A task notification
	can then be used to unblock any task that is waiting for a complete message
	once a complete message has been buffered.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "comtest_strings.h"

/* Library includes. */
#include "xuartlite.h"
#include "xuartlite_l.h"

/* Demo application includes. */
#include "serial.h"

/*-----------------------------------------------------------*/

/* Functions that are installed as the handler for interrupts that are caused by
Rx and Tx events respectively. */
static void prvRxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount );
static void prvTxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount );

/* Structure that hold the state of the UARTLite peripheral used by this demo.
This is used by the Xilinx peripheral driver API functions. */
static XUartLite xUartLiteInstance;

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars;

/* Holds the handle of a task performing a Tx so it can be notified of when
the Tx has completed. */
static TaskHandle_t xUARTSendingTask = NULL;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
BaseType_t xStatus;

	/* The standard demo header file requires a baud rate to be passed into this
	function.  However, in this case the baud rate is configured when the
	hardware is generated, leaving the ulWantedBaud parameter redundant. */
	( void ) ulWantedBaud;

	/* Create the queue used to hold Rx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* If the queue was created correctly, then setup the serial port
	hardware. */
	if( xRxedChars != NULL )
	{
		xStatus = XUartLite_Initialize( &xUartLiteInstance, XPAR_UARTLITE_0_DEVICE_ID );

		if( xStatus == XST_SUCCESS )
		{
			/* Complete initialisation of the UART and its associated
			interrupts. */
			XUartLite_ResetFifos( &xUartLiteInstance );

			/* Install the handlers that the standard Xilinx library interrupt
			service routine will call when Rx and Tx events occur
			respectively. */
			XUartLite_SetRecvHandler( &xUartLiteInstance, ( XUartLite_Handler ) prvRxHandler, NULL );
			XUartLite_SetSendHandler( &xUartLiteInstance, ( XUartLite_Handler ) prvTxHandler, NULL );

			/* Install the standard Xilinx library interrupt handler itself.
			*NOTE* The xPortInstallInterruptHandler() API function must be used
			for	this purpose. */
			xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_UARTLITE_0_VEC_ID, ( XInterruptHandler ) XUartLite_InterruptHandler, &xUartLiteInstance );

			/* Enable the interrupt in the peripheral. */
			XUartLite_EnableIntr( xUartLiteInstance.RegBaseAddress );

			/* Enable the interrupt in the interrupt controller.
			*NOTE* The vPortEnableInterrupt() API function must be used for this
			purpose. */
			vPortEnableInterrupt( XPAR_INTC_0_UARTLITE_0_VEC_ID );
		}

		configASSERT( xStatus == pdPASS );
	}

	/* This demo file only supports a single port but something must be
	returned to comply with the standard demo header file. */
	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
portBASE_TYPE xReturn;

	/* The port handle is not required as this driver only supports one port. */
	( void ) pxPort;

	/* Get the next character from the receive queue.  Return false if no
	characters are available, or arrive before xBlockTime expires. */
	if( xQueueReceive( xRxedChars, pcRxedChar, xBlockTime ) )
	{
		xReturn = pdTRUE;
	}
	else
	{
		xReturn = pdFALSE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
const TickType_t xMaxBlockTime = pdMS_TO_TICKS( 150UL );
portBASE_TYPE xReturn;

	( void ) pxPort;
	( void ) xBlockTime;

	/* Note this is the currently sending task. */
	xUARTSendingTask = xTaskGetCurrentTaskHandle();

	XUartLite_Send( &xUartLiteInstance, ( unsigned char * ) &cOutChar, sizeof( cOutChar ) );

	/* Wait in the Blocked state (so not using any CPU time) for the Tx to
	complete. */
	xReturn = ulTaskNotifyTake( pdTRUE, xMaxBlockTime );

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
const TickType_t xMaxBlockTime = pdMS_TO_TICKS( 150UL );

	( void ) pxPort;

	/* Note this is the currently sending task. */
	xUARTSendingTask = xTaskGetCurrentTaskHandle();

	/* Output uxStringLength bytes starting from pcString. */
	XUartLite_Send( &xUartLiteInstance, ( unsigned char * ) pcString, usStringLength );

	/* Wait in the Blocked state (so not using any CPU time) for the Tx to
	complete. */
	ulTaskNotifyTake( pdTRUE, xMaxBlockTime );
}
/*-----------------------------------------------------------*/

static void prvRxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount )
{
signed char cRxedChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	( void ) pvUnused;
	( void ) uxByteCount;

	/* Place any received characters into the receive queue. */
	while( XUartLite_IsReceiveEmpty( xUartLiteInstance.RegBaseAddress ) == pdFALSE )
	{
		cRxedChar = XUartLite_ReadReg( xUartLiteInstance.RegBaseAddress, XUL_RX_FIFO_OFFSET);
		xQueueSendFromISR( xRxedChars, &cRxedChar, &xHigherPriorityTaskWoken );
	}

	/* If calling xQueueSendFromISR() caused a task to unblock, and the task
	that unblocked has a priority equal to or greater than the task currently
	in the Running state (the task that was interrupted), then
	xHigherPriorityTaskWoken will have been set to pdTRUE internally within the
	xQueueSendFromISR() API function.  If xHigherPriorityTaskWoken is equal to
	pdTRUE then a context switch should be requested to ensure that the
	interrupt returns to the highest priority task that is able	to run. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvTxHandler( void *pvUnused, unsigned portBASE_TYPE uxUnused )
{
BaseType_t xHigherPriorityTaskWoken = ( BaseType_t ) NULL;

	( void ) pvUnused;
	( void ) uxUnused;

	/* Notify the sending that that the Tx has completed. */
	if( xUARTSendingTask != NULL )
	{
		vTaskNotifyGiveFromISR( xUARTSendingTask, &xHigherPriorityTaskWoken );
		xUARTSendingTask = NULL;
	}

	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}









