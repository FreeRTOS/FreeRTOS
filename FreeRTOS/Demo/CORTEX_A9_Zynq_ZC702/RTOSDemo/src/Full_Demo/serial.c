/*
 FreeRTOS V8.1.0 - Copyright (C) 2014 Real Time Engineers Ltd.
 All rights reserved

 VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

 ***************************************************************************
 *                                                                       *
 *    FreeRTOS provides completely free yet professionally developed,    *
 *    robust, strictly quality controlled, supported, and cross          *
 *    platform software that has become a de facto standard.             *
 *                                                                       *
 *    Help yourself get started quickly and support the FreeRTOS         *
 *    project by purchasing a FreeRTOS tutorial book, reference          *
 *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
 *                                                                       *
 *    Thank you!                                                         *
 *                                                                       *
 ***************************************************************************

 This file is part of the FreeRTOS distribution.

 FreeRTOS is free software; you can redistribute it and/or modify it under
 the terms of the GNU General Public License (version 2) as published by the
 Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

 FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
 WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 FOR A PARTICULAR PURPOSE.  Full license text is available from the following
 link: http://www.freertos.org/a00114.html

 1 tab == 4 spaces!

 ***************************************************************************
 *                                                                       *
 *    Having a problem?  Start by reading the FAQ "My application does   *
 *    not run, what could be wrong?"                                     *
 *                                                                       *
 *    http://www.FreeRTOS.org/FAQHelp.html                               *
 *                                                                       *
 ***************************************************************************

 http://www.FreeRTOS.org - Documentation, books, training, latest versions,
 license and Real Time Engineers Ltd. contact details.

 http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
 including FreeRTOS+Trace - an indispensable productivity tool, a DOS
 compatible FAT file system, and our tiny thread aware UDP/IP stack.

 http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
 Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
 licenses offer ticketed support, indemnification and middleware.

 http://www.SafeRTOS.com - High Integrity Systems also provide a safety
 engineered and independently SIL3 certified version for use in safety and
 mission critical applications that require provable dependability.

 1 tab == 4 spaces!
 */

/*
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.

	Note1:  This driver is used specifically to provide an interface to the
	FreeRTOS+CLI command interpreter.  It is *not* intended to be a generic
	serial port driver.  Nor is it intended to be used as an example of an
	efficient implementation.  In particular, a queue is used to buffer
	received characters, which is fine in this case as key presses arrive
	slowly, but a DMA and/or RAM buffer should be used in place of the queue in
	applications that expect higher throughput.

	Note2:  This driver does not attempt to handle UART errors.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo application includes. */
#include "serial.h"

/* Xilinx includes. */
#include "xuartps.h"
#include "xscugic.h"
#include "xil_exception.h"

/* The UART interrupts of interest when receiving. */
#define serRECEIVE_INTERRUPT_MASK	( XUARTPS_IXR_RXOVR | XUARTPS_IXR_RXFULL | XUARTPS_IXR_TOUT )

/* The UART interrupts of interest when transmitting. */
#define serTRANSMIT_IINTERRUPT_MASK ( XUARTPS_IXR_TXEMPTY )

/*-----------------------------------------------------------*/

/* The UART being used. */
static XUartPs xUARTInstance;

/* The interrupt controller, which is configred by the hardware setup routines
defined in main(). */
extern XScuGic xInterruptController;

/* The queue into which received key presses are placed.  NOTE THE COMMENTS AT
THE TOP OF THIS FILE REGARDING THE USE OF QUEUES FOR THIS PURPOSE. */
static QueueHandle_t xRxQueue = NULL;

/* The semaphore used to indicate the end of a transmission. */
static SemaphoreHandle_t xTxCompleteSemaphore = NULL;

/*-----------------------------------------------------------*/

/*
 * The UART interrupt handler is defined in this file to provide more control,
 * but still uses parts of the Xilinx provided driver.
 */
void prvUART_Handler( void *pvNotUsed );

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( uint32_t ulWantedBaud, UBaseType_t uxQueueLength )
{
BaseType_t xStatus;
XUartPs_Config *pxConfig;

	/* Create the queue used to hold received characters.  NOTE THE COMMENTS AT
	THE TOP OF THIS FILE REGARDING THE QUEUE OF QUEUES FOR THIS PURPSOE. */
	xRxQueue = xQueueCreate( uxQueueLength, sizeof( char ) );
	configASSERT( xRxQueue );

	/* Create the semaphore used to signal the end of a transmission, then take
	the semaphore so it is in the correct state the first time
	xSerialSendString() is called.  A block time of zero is used when taking
	the semaphore as it is guaranteed to be available (it was just created). */
	xTxCompleteSemaphore = xSemaphoreCreateBinary();
	configASSERT( xTxCompleteSemaphore );
	xSemaphoreTake( xTxCompleteSemaphore, 0 );

	/* Look up the UART configuration then initialise the dirver. */
	pxConfig = XUartPs_LookupConfig( XPAR_XUARTPS_0_DEVICE_ID );

	/* Initialise the driver. */
	xStatus = XUartPs_CfgInitialize( &xUARTInstance, pxConfig, XPAR_PS7_UART_1_BASEADDR );
	configASSERT( xStatus == XST_SUCCESS );
	( void ) xStatus; /* Remove compiler warning if configASSERT() is not defined. */

	/* Misc. parameter configuration. */
	XUartPs_SetBaudRate( &xUARTInstance, ulWantedBaud );
	XUartPs_SetOperMode( &xUARTInstance, XUARTPS_OPER_MODE_NORMAL );

	/* Install the interrupt service routine that is defined within this
	file. */
	xStatus = XScuGic_Connect( &xInterruptController, XPAR_XUARTPS_1_INTR,  (Xil_ExceptionHandler) prvUART_Handler, (void *) &xUARTInstance );
	configASSERT( xStatus == XST_SUCCESS );
	( void ) xStatus; /* Remove compiler warning if configASSERT() is not defined. */

	/* Ensure interrupts start clear. */
	XUartPs_WriteReg( XPAR_PS7_UART_1_BASEADDR, XUARTPS_ISR_OFFSET, XUARTPS_IXR_MASK );

	/* Enable the UART interrupt within the GIC. */
	XScuGic_Enable( &xInterruptController, XPAR_XUARTPS_1_INTR );

	/* Enable the interrupts of interest in the UART. */
	XUartPs_SetInterruptMask( &xUARTInstance, XUARTPS_IXR_RXFULL | XUARTPS_IXR_RXOVR | XUARTPS_IXR_TOUT | XUARTPS_IXR_TXEMPTY );

	/* Set the receive timeout. */
	XUartPs_SetRecvTimeout( &xUARTInstance, 8 );

	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

BaseType_t xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
BaseType_t xReturn;

	/* Only a single port is supported. */
	( void ) pxPort;

	/* Obtain a received character from the queue - entering the Blocked state
	(so not consuming any processing time) to wait for a character if one is not
	already available. */
	xReturn = xQueueReceive( xRxQueue, pcRxedChar, xBlockTime );
	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
const TickType_t xMaxWait = 200UL / portTICK_PERIOD_MS;

	/* Only a single port is supported. */
	( void ) pxPort;

	/* Start the transmission.  The interrupt service routine will complete the
	transmission if necessary. */
	XUartPs_Send( &xUARTInstance, ( void * ) pcString, usStringLength );

	/* Wait until the string has been transmitted before exiting this function,
	otherwise there is a risk the calling function will overwrite the string
	pointed to by the pcString parameter while it is still being transmitted.
	The calling task will wait in the Blocked state (so not consuming any
	processing time) until the semaphore is available. */
	xSemaphoreTake( xTxCompleteSemaphore, xMaxWait );
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
	/* Only a single port is supported. */
	( void ) pxPort;

	/* Send the character. */
	XUartPs_Send( &xUARTInstance, ( void * ) &cOutChar, sizeof( cOutChar ) );

	/* Wait for the transmission to be complete so the semaphore is left in the
	correct state for the next time vSerialPutString() is called. */
	xSemaphoreTake( xTxCompleteSemaphore, xBlockTime );

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose(xComPortHandle xPort)
{
	/* Not supported as not required by the demo application. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/

void prvUART_Handler( void *pvNotUsed )
{
extern unsigned int XUartPs_SendBuffer( XUartPs *InstancePtr );
uint32_t ulActiveInterrupts, ulChannelStatusRegister;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;
char cChar;

	configASSERT( pvNotUsed == &xUARTInstance );

	/* Remove compile warnings if configASSERT() is not defined. */
	( void ) pvNotUsed;

	/* Read the interrupt ID register to see which interrupt is active. */
	ulActiveInterrupts = XUartPs_ReadReg(XPAR_PS7_UART_1_BASEADDR,  XUARTPS_IMR_OFFSET);
	ulActiveInterrupts &= XUartPs_ReadReg(XPAR_PS7_UART_1_BASEADDR,  XUARTPS_ISR_OFFSET);

	/* Are any receive events of interest active? */
	if( ( ulActiveInterrupts & serRECEIVE_INTERRUPT_MASK ) != 0 )
	{
		/* Read the Channel Status Register to determine if there is any data in
		the RX FIFO. */
		ulChannelStatusRegister = XUartPs_ReadReg( XPAR_PS7_UART_1_BASEADDR, XUARTPS_SR_OFFSET );

		/* Move data from the Rx FIFO to the Rx queue.  NOTE THE COMMENTS AT THE
		TOP OF THIS FILE ABOUT USING QUEUES FOR THIS PURPSOE. */
		while( ( ulChannelStatusRegister & XUARTPS_SR_RXEMPTY ) == 0 )
		{
			cChar =	XUartPs_ReadReg( XPAR_PS7_UART_1_BASEADDR, XUARTPS_FIFO_OFFSET );

			/* If writing to the queue unblocks a task, and the unblocked task
			has a priority above the currently running task (the task that this
			interrupt interrupted), then xHigherPriorityTaskWoken will be set
			to pdTRUE inside the xQueueSendFromISR() function.
			xHigherPriorityTaskWoken is then passed to portYIELD_FROM_ISR() at
			the end of this interrupt handler to request a context switch so the
			interrupt returns directly to the (higher priority) unblocked
			task. */
			xQueueSendFromISR( xRxQueue, &cChar, &xHigherPriorityTaskWoken );
			ulChannelStatusRegister = XUartPs_ReadReg( XPAR_PS7_UART_1_BASEADDR, XUARTPS_SR_OFFSET );
		}
	}

	/* Are any transmit events of interest active? */
	if( ( ulActiveInterrupts & serTRANSMIT_IINTERRUPT_MASK ) != 0 )
	{
		if( xUARTInstance.SendBuffer.RemainingBytes == 0 )
		{
			/* Give back the semaphore to indicate that the tranmission is
			complete.  If giving the semaphore unblocks a task, and the
			unblocked task has a priority above the currently running task (the
			task that this interrupt interrupted), then xHigherPriorityTaskWoken
			will be set	to pdTRUE inside the xSemaphoreGiveFromISR() function.
			xHigherPriorityTaskWoken is then passed to portYIELD_FROM_ISR() at
			the end of this interrupt handler to request a context switch so the
			interrupt returns directly to the (higher priority) unblocked
			task. */
			xSemaphoreGiveFromISR( xTxCompleteSemaphore, &xHigherPriorityTaskWoken );

			/* No more data to transmit. */
			XUartPs_WriteReg( XPAR_PS7_UART_1_BASEADDR, XUARTPS_IDR_OFFSET, XUARTPS_IXR_TXEMPTY );
		}
		else
		{
			/* More data to send. */
			XUartPs_SendBuffer( &xUARTInstance );
		}
	}

	/* portYIELD_FROM_ISR() will request a context switch if executing this
	interrupt handler caused a task to leave the blocked state, and the task
	that left the blocked state has a higher priority than the currently running
	task (the task this interrupt interrupted).  See the comment above the calls
	to xSemaphoreGiveFromISR() and xQueueSendFromISR() within this function. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );

	/* Clear the interrupt status. */
	XUartPs_WriteReg( XPAR_PS7_UART_1_BASEADDR, XUARTPS_ISR_OFFSET, ulActiveInterrupts );
}





