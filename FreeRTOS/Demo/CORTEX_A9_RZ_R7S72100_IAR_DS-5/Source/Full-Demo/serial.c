/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

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
#include "queue.h"
#include "semphr.h"
#include "comtest2.h"

/* Driver includes. */
#include "r_typedefs.h"
#include "dev_drv.h"
#include "devdrv_scif_uart.h"
#include "sio_char.h"
#include "iodefine.h"
#include "devdrv_intc.h"

/* Demo application includes. */
#include "serial.h"

/*-----------------------------------------------------------*/

/* Misc defines. */
#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serNO_BLOCK						( ( TickType_t ) 0 )

/*-----------------------------------------------------------*/

/* Handlers for the Rx and Tx interrupts respectively. */
static void prvRXI_Handler( uint32_t ulUnusedParameter );
static void prvTXI_Handler( uint32_t ulUnusedParameter );

/*-----------------------------------------------------------*/

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Baud is set in IoInitScif2(), called in prvSetupHardware() in main.c. */
	( void ) ulWantedBaud;

	/* Create the queues used to hold Rx/Tx characters.  Note the comments at
	the top of this file regarding the use of queues in this manner. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( char ) );

	/* If the queues were created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
	    /* Register RXI and TXI handlers. */
	    R_INTC_RegistIntFunc( INTC_ID_RXI2, prvRXI_Handler );
	    R_INTC_RegistIntFunc( INTC_ID_TXI2, prvTXI_Handler );

	    /* Set both interrupts such that they can interrupt the tick.  Also
	    set the Rx interrupt above the Tx interrupt in the hope that (for test
	    purposes) the Tx interrupt will interrupt the Rx interrupt. */
	    R_INTC_SetPriority( INTC_ID_RXI2, configMAX_API_CALL_INTERRUPT_PRIORITY );
	    R_INTC_SetPriority( INTC_ID_TXI2, ( configMAX_API_CALL_INTERRUPT_PRIORITY + 1 ) );

	    /* This driver is intended to test interrupt interactions, and not
	    intended to be efficient.  Therefore set the RX trigger level to 1. */
	    SCIF2.SCFCR.BIT.RTRG = 0;
	    SCIF2.SCFCR.BIT.TTRG = 3;

		/* Enable Rx interrupt.  Tx interrupt will be enabled when a Tx is
		performed. */
		SCIF2.SCSCR.BIT.RIE = 1;
		R_INTC_Enable( INTC_ID_RXI2 );
		R_INTC_Enable( INTC_ID_TXI2 );
	}

	/* This demo file only supports a single port but we have to return
	something to comply with the standard demo header file. */
	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
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

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
char *pxNext;

	/* A couple of parameters that this port does not use. */
	( void ) usStringLength;
	( void ) pxPort;

	/* Send each character in the string, one at a time. */
	pxNext = ( char * ) pcString;
	while( *pxNext )
	{
		xSerialPutChar( pxPort, *pxNext, portMAX_DELAY );
		pxNext++;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
signed portBASE_TYPE xReturn;

	/* Note the comments at the top of this file regarding the use of queues in
	this manner. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) == pdPASS )
	{
		xReturn = pdPASS;

		/* Enable the interrupt which will remove the character from the
		queue. */
		SCIF2.SCSCR.BIT.TIE = 1;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

static void prvRXI_Handler( uint32_t ulUnusedParameter )
{
unsigned char ucRxedByte;
long lHigherPriorityTaskWoken = pdFALSE;

	/* The parameter is not used.  It is only present because Renesas drivers
	are used to install the interrupt handlers, and the drivers expect the
	parameter to be present. */
	( void ) ulUnusedParameter;

	/* Note the comments at the top of this file regarding the use of queues in
	this manner. */
	while( ( SCIF2.SCFDR.WORD & 0x1F ) != 0 )
	{
		ucRxedByte = SCIF2.SCFRDR.BYTE;
		xQueueSendFromISR( xRxedChars, &ucRxedByte, &lHigherPriorityTaskWoken );
	}

	SCIF2.SCFSR.BIT.RDF = 0;

	/* If sending to the queue has caused a task to unblock, and the unblocked
	task has a priority equal to or higher than the currently running task (the
	task this ISR interrupted), then lHigherPriorityTaskWoken will have
	automatically been set to pdTRUE within the queue send function.
	portYIELD_FROM_ISR() will then ensure that this ISR returns	directly to the
	higher priority unblocked task. */
	portYIELD_FROM_ISR( lHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvTXI_Handler( uint32_t ulUnusedParameter )
{
unsigned char ucByte;
long lHigherPriorityTaskWoken = pdFALSE;

	/* The parameter is not used.  It is only present because Renesas drivers
	are used to install the interrupt handlers, and the drivers expect the
	parameter to be present. */
	( void ) ulUnusedParameter;

	/* Note the comments at the top of this file regarding the use of queues in
	this manner. */
	if( xQueueReceiveFromISR( xCharsForTx, &ucByte, &lHigherPriorityTaskWoken ) == pdPASS )
	{
		SCIF2.SCFTDR.BYTE = ucByte;

		/* Clear TDRE and TEND flag */
	    SCIF2.SCFSR.WORD &= ~0x0060;
	}
	else
	{
		/* No more characters.  Disable the interrupt. */
		SCIF2.SCSCR.BIT.TIE = 0;
	}

	/* If receiving from the queue has caused a task to unblock, and the
	unblocked task has a priority equal to or higher than the currently running
	task (the task this ISR interrupted), then lHigherPriorityTaskWoken will
	have automatically been set to pdTRUE within the queue receive function.
	portYIELD_FROM_ISR() will then ensure that this ISR returns	directly to the
	higher priority unblocked task. */
	portYIELD_FROM_ISR( lHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/




