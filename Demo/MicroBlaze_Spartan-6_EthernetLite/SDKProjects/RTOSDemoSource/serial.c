/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART0.
	
	***Note*** This example uses queues to send each character into an interrupt
	service routine and out of an interrupt service routine individually.  This
	is done to demonstrate queues being used in an interrupt, and to deliberately
	load the system to test the FreeRTOS port.  It is *NOT* meant to be an
	example of an efficient implementation.  An efficient implementation should
	use FIFOs or DMA if available, and only use FreeRTOS API functions when
	enough has been received to warrant a task being unblocked to process the
	data.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h" /*_RB_ remove this when the file is working. */
#include "comtest_strings.h"

/* Library includes. */
#include "xuartlite.h"
#include "xuartlite_l.h"

/* Demo application includes. */
#include "serial.h"
/*-----------------------------------------------------------*/

static void prvRxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount );
static void prvTxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount );

static XUartLite xUartLiteInstance;

/* The queue used to hold received characters. */
static xQueueHandle xRxedChars;


/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
portBASE_TYPE xStatus;

	/* Create the queue used to hold Rx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* If the queue was created correctly then setup the serial port
	hardware. */
	if( xRxedChars != NULL )
	{
		xStatus = XUartLite_Initialize( &xUartLiteInstance, XPAR_UARTLITE_1_DEVICE_ID );

		if( xStatus == XST_SUCCESS )
		{
			/* Complete initialisation of the UART and its associated
			interrupts. */
			XUartLite_ResetFifos( &xUartLiteInstance );
			XUartLite_SetRecvHandler( &xUartLiteInstance, ( XUartLite_Handler ) prvRxHandler, NULL );
			XUartLite_SetSendHandler( &xUartLiteInstance, ( XUartLite_Handler ) prvTxHandler, NULL );
			xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_UARTLITE_1_VEC_ID, ( XInterruptHandler ) XUartLite_InterruptHandler, &xUartLiteInstance );
			XUartLite_EnableIntr( xUartLiteInstance.RegBaseAddress );
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

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned portBASE_TYPE uxStringLength )
{
	XUartLite_Send( &xUartLiteInstance, ( unsigned char * ) pcString, uxStringLength );
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
{
	/* Only vSerialPutString() is used in this demo. */
	( void ) pxPort;
	( void ) cOutChar;
	( void ) xBlockTime;

	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

static void prvRxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount )
{
signed char cRxedChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	while( XUartLite_IsReceiveEmpty( xUartLiteInstance.RegBaseAddress ) == pdFALSE )
	{
		cRxedChar = XUartLite_ReadReg( xUartLiteInstance.RegBaseAddress, XUL_RX_FIFO_OFFSET);
		xQueueSendFromISR( xRxedChars, &cRxedChar, &xHigherPriorityTaskWoken );
	}

	portYIELD_FROM_ISR( xHigherPriorityTaskWoken ); //_RB_ This needs re-implementing so it does not get called multiple times as multiple peripherals are servied in a single ISR. */
}
/*-----------------------------------------------------------*/

static void prvTxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount )
{
	portNOP();
}








	
