/*
 FreeRTOS V8.0.0:rc2 - Copyright (C) 2014 Real Time Engineers Ltd.
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

 >>! NOTE: The modification to the GPL is included to allow you to distribute
 >>! a combined work that includes FreeRTOS without being obliged to provide
 >>! the source code for proprietary components outside of the FreeRTOS
 >>! kernel.

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
 BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART2.

 ***Note*** This example uses queues to send each character into an interrupt
 service routine and out of an interrupt service routine individually.  This
 is done to demonstrate queues being used in an interrupt, and to deliberately
 load the system to test the FreeRTOS port.  It is *NOT* meant to be an
 example of an efficient implementation.  An efficient implementation should
 use the DMA, and only use FreeRTOS API functions when enough has been
 received to warrant a task being unblocked to process the data.
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "comtest2.h"

/* Demo application includes. */
#include "serial.h"

/* Xilinx includes. */
#include "xuartps.h"
#include "xscugic.h"
#include "xil_exception.h"

/*-----------------------------------------------------------*/

static XUartPs xUARTInstance;
extern XScuGic xInterruptController;

/*-----------------------------------------------------------*/

static void prvISRHandler( void *pvUnused, uint32_t ulEvent, uint32_t ulUnused2 );

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( uint32_t ulWantedBaud, UBaseType_t uxQueueLength )
{
BaseType_t xStatus;
XUartPs_Config *pxConfig;

	/* Look up the UART configuration then initialise the dirver. */
	pxConfig = XUartPs_LookupConfig( XPAR_XUARTPS_0_DEVICE_ID );
	configASSERT( pxConfig );

	xStatus = XUartPs_CfgInitialize( &xUARTInstance, pxConfig, pxConfig->BaseAddress );
	configASSERT( xStatus == XST_SUCCESS );

	XUartPs_SetBaudRate( &xUARTInstance, ulWantedBaud );

	XUartPs_SetOperMode( &xUARTInstance, XUARTPS_OPER_MODE_NORMAL );

	return 0;
}
/*-----------------------------------------------------------*/

BaseType_t xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
{
TickType_t xTimeOnEntering;
const TickType_t xDelay = 10UL / portTICK_PERIOD_MS;
BaseType_t xReturn = 0;

	xTimeOnEntering = xTaskGetTickCount();

	do
	{
		/* Only wanting to receive one key press at a time. */
		if( XUartPs_Recv( &xUARTInstance, pcRxedChar, sizeof( pcRxedChar ) ) != 0 )
		{
			xReturn = 1;
			break;
		}
		else
		{
			vTaskDelay( xDelay );
		}
	} while( ( xTaskGetTickCount() - xTimeOnEntering ) <= xBlockTime );

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
static const xTxDelay = 10UL / portTICK_PERIOD_MS;
uint32_t ulBytesSent = 0UL;

	( void ) pxPort;

	while( ulBytesSent < usStringLength )
	{
		ulBytesSent += XUartPs_Send( &xUARTInstance, pcString + ulBytesSent, usStringLength - ulBytesSent );

		while( XUartPs_IsSending( &xUARTInstance ) )
		{
			vTaskDelay( xTxDelay );
		}
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
{
static const xTxDelay = 10UL / portTICK_PERIOD_MS;

	XUartPs_Send( &xUARTInstance, &cOutChar, sizeof( cOutChar ) );

	while( XUartPs_IsSending( &xUARTInstance ) )
	{
		vTaskDelay( xTxDelay );
	}

	return 0;
}
/*-----------------------------------------------------------*/

void vSerialClose(xComPortHandle xPort)
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

