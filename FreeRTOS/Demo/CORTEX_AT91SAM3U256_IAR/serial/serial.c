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
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART0.
*/

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* Demo application includes. */
#include "serial.h"

/* Library includes. */
#include "usart/usart.h"
#include "pmc/pmc.h"
#include "irq/irq.h"
#include "pio/pio.h"

/*-----------------------------------------------------------*/

/* Interrupt control macros. */
#define serINTERRUPT_LEVEL				( 5 )
#define vInterruptOn()					BOARD_USART_BASE->US_IER = ( AT91C_US_TXRDY | AT91C_US_RXRDY )
#define vInterruptOff()					BOARD_USART_BASE->US_IDR = AT91C_US_TXRDY

/* Misc constants. */
#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serHANDLE						( ( xComPortHandle ) 1 )
#define serNO_BLOCK						( ( TickType_t ) 0 )
#define serNO_TIMEGUARD					( ( unsigned long ) 0 )
#define serNO_PERIPHERAL_B_SETUP		( ( unsigned long ) 0 )


/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

/*-----------------------------------------------------------*/

/* The interrupt service routine - called from the assembly entry point. */
void vSerialISR( void );

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
xComPortHandle xReturn = serHANDLE;
extern void ( vUART_ISR )( void );
const Pin xUSART_Pins[] = { BOARD_PIN_USART_RXD, BOARD_PIN_USART_TXD };


	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* If the queues were created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
		portENTER_CRITICAL();
		{
			/* Enable the peripheral clock in the PMC. */
			PMC_EnablePeripheral( BOARD_ID_USART );
		
			/* Configure the USART. */
			USART_Configure( BOARD_USART_BASE, AT91C_US_CHRL_8_BITS | AT91C_US_PAR_NONE | AT91C_US_NBSTOP_1_BIT, ulWantedBaud, configCPU_CLOCK_HZ );
		
			/* Configure the interrupt.  Note the pre-emption priority is set
			in bits [8:15] of the priority value passed as the parameter. */
			IRQ_ConfigureIT( BOARD_ID_USART, ( configMAX_SYSCALL_INTERRUPT_PRIORITY << 8 ), vSerialISR );
			IRQ_EnableIT( BOARD_ID_USART );
		
			/* Enable receiver & transmitter. */
			USART_SetTransmitterEnabled( BOARD_USART_BASE, pdTRUE );
			USART_SetReceiverEnabled( BOARD_USART_BASE, pdTRUE );
			
			/* Configure IO for USART use. */
			PIO_Configure( xUSART_Pins, PIO_LISTSIZE( xUSART_Pins ) );
		}
		portEXIT_CRITICAL();
	}
	else
	{
		xReturn = ( xComPortHandle ) 0;
	}

	/* This demo file only supports a single port but we have to return
	something to comply with the standard demo header file. */
	return xReturn;
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
signed char *pxNext;

	/* A couple of parameters that this port does not use. */
	( void ) usStringLength;
	( void ) pxPort;

	/* NOTE: This implementation does not handle the queue being full as no
	block time is used! */

	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;

	/* Send each character in the string, one at a time. */
	pxNext = ( signed char * ) pcString;
	while( *pxNext )
	{
		xSerialPutChar( pxPort, *pxNext, serNO_BLOCK );
		pxNext++;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
	/* Place the character in the queue of characters to be transmitted. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* Turn on the Tx interrupt so the ISR will remove the character from the
	queue and send it.   This does not need to be in a critical section as
	if the interrupt has already removed the character the next interrupt
	will simply turn off the Tx interrupt again. */
	vInterruptOn();

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

void vSerialISR( void )
{
unsigned long ulStatus;
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* What caused the interrupt? */
	ulStatus = BOARD_USART_BASE->US_CSR &= BOARD_USART_BASE->US_IMR;

	if( ulStatus & AT91C_US_TXRDY )
	{
		/* The interrupt was caused by the THR becoming empty.  Are there any
		more characters to transmit? */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* A character was retrieved from the queue so can be sent to the
			THR now. */
			BOARD_USART_BASE->US_THR = cChar;
		}
		else
		{
			/* Queue empty, nothing to send so turn off the Tx interrupt. */
			vInterruptOff();
		}		
	}

	if( ulStatus & AT91C_US_RXRDY )
	{
		/* The interrupt was caused by a character being received.  Grab the
		character from the RHR and place it in the queue or received
		characters. */
		cChar = BOARD_USART_BASE->US_RHR;
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}

	/* If a task was woken by either a character being received or a character
	being transmitted then we may need to switch to another task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}




	
