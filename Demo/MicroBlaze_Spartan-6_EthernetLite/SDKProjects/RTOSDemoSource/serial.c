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
#include "semphr.h"
#include "task.h" /*_RB_ remove this when the file is working. */
#include "comtest_strings.h"

/* Library includes. */
#include "xuartlite.h"
#include "xuartlite_l.h"

/* Demo application includes. */
#include "serial.h"
/*-----------------------------------------------------------*/

/* Misc defines. */
#define serINVALID_QUEUE				( ( xQueueHandle ) 0 )
#define serNO_BLOCK						( ( portTickType ) 0 )

/*-----------------------------------------------------------*/

/* The queue used to hold received characters. */
static xQueueHandle xRxedChars;
static xQueueHandle xCharsForTx;

static XUartLite xUartLiteInstance;

static void prvRxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount );
static void prvTxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount );

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
portBASE_TYPE xStatus;

	/* Create the queues used to hold Rx/Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	
	/* If the queues were created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
		xStatus = XUartLite_Initialize( &xUartLiteInstance, XPAR_UARTLITE_1_DEVICE_ID );

		if( xStatus == XST_SUCCESS )
		{
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
extern u8 XUartLite_RecvByte(u32 BaseAddress);

//	*pcRxedChar = XUartLite_RecvByte( xUartLiteInstance.RegBaseAddress );

	vTaskDelay( 1000 );
	return pdTRUE;
#if 0
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
#endif
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
	XUartLite_Send( &xUartLiteInstance, ( unsigned char * ) pcString, ( unsigned portBASE_TYPE ) usStringLength );

#if 0
unsigned portBASE_TYPE uxReturn = 0U;

char *pc = pc;
extern void XUartLite_SendByte(u32 BaseAddress, u8 Data);

	/* Just to avoid compiler warnings. */
	( void ) pxPort;

	while( uxReturn != usStringLength )
	{
		XUartLite_SendByte( xUartLiteInstance.RegBaseAddress, *pc );
		pc++;
		uxReturn++;
//		uxReturn += XUartLite_Send( &xUartLiteInstance, ( unsigned char * ) pcString, ( ( unsigned portBASE_TYPE ) usStringLength ) - uxReturn );
		while( XUartLite_IsSending( &xUartLiteInstance ) != pdFALSE )
		{
			/*_RB_ This function is not yet written to make use of the RTOS. */
		}
	}
#endif
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
{
#if 1
	extern void XUartLite_SendByte(u32 BaseAddress, u8 Data);

//	for( ;; )
//	{
		XUartLite_SendByte( xUartLiteInstance.RegBaseAddress, cOutChar );
//	}
//	vTaskDelay( 2 );
	return 1;
#else
signed portBASE_TYPE xReturn;

	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) == pdPASS )
	{
		xReturn = pdPASS;
		
		/* Enable the UART Tx interrupt. */
		XUartLite_EnableIntr( xUartLiteInstance.RegBaseAddress );
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
#endif
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

static void prvRxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount )
{
	portNOP();
}
/*-----------------------------------------------------------*/

static void prvTxHandler( void *pvUnused, unsigned portBASE_TYPE uxByteCount )
{
	portNOP();
}





	
