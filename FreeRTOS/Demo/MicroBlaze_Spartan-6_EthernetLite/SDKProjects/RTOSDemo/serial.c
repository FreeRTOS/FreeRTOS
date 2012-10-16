/*
    FreeRTOS V7.3.0 - Copyright (C) 2012 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT 
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest versions, license 
    and contact details.  
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR a UARTLite peripheral.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
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
static xQueueHandle xRxedChars;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
portBASE_TYPE xStatus;

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
		xStatus = XUartLite_Initialize( &xUartLiteInstance, XPAR_UARTLITE_1_DEVICE_ID );

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
			xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_UARTLITE_1_VEC_ID, ( XInterruptHandler ) XUartLite_InterruptHandler, &xUartLiteInstance );
			
			/* Enable the interrupt in the peripheral. */
			XUartLite_EnableIntr( xUartLiteInstance.RegBaseAddress );
			
			/* Enable the interrupt in the interrupt controller.
			*NOTE* The vPortEnableInterrupt() API function must be used for this
			purpose. */
			vPortEnableInterrupt( XPAR_INTC_0_UARTLITE_1_VEC_ID );
		}

		configASSERT( xStatus == pdPASS );
	}

	/* This demo file only supports a single port but something must be
	returned to comply with the standard demo header file. */
	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
{
	/* The port handle is not required as this driver only supports one port. */
	( void ) pxPort;

	/* Get the next character from the receive queue.  Return false if no 
	characters are available, or arrive before xBlockTime expires. */
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

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
	( void ) pxPort;

	/* Output uxStringLength bytes starting from pcString. */
	XUartLite_Send( &xUartLiteInstance, ( unsigned char * ) pcString, usStringLength );
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

static void prvTxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount )
{
	( void ) pvUnused;
	( void ) uxByteCount;

	/* Nothing to do here.  The Xilinx library function takes care of the
	transmission. */
	portNOP();
}








	
