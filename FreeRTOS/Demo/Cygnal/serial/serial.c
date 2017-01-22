/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
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


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR DEMO PURPOSES */
#include <stdlib.h>
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"
#include "serial.h"

/* Constants required to setup the serial control register. */
#define ser8_BIT_MODE			( ( unsigned char ) 0x40 )
#define serRX_ENABLE			( ( unsigned char ) 0x10 )

/* Constants to setup the timer used to generate the baud rate. */
#define serCLOCK_DIV_48			( ( unsigned char ) 0x03 )
#define serUSE_PRESCALED_CLOCK	( ( unsigned char ) 0x10 )
#define ser8BIT_WITH_RELOAD		( ( unsigned char ) 0x20 )
#define serSMOD					( ( unsigned char ) 0x10 )

static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx; 

data static unsigned portBASE_TYPE uxTxEmpty;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulReloadValue;
const portFLOAT fBaudConst = ( portFLOAT ) configCPU_CLOCK_HZ * ( portFLOAT ) 2.0;
unsigned char ucOriginalSFRPage;

	portENTER_CRITICAL();
	{
		ucOriginalSFRPage = SFRPAGE;
		SFRPAGE = 0;

		uxTxEmpty = pdTRUE;

		/* Create the queues used by the com test task. */
		xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( char ) );
		xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( char ) );
	
		/* Calculate the baud rate to use timer 1. */
		ulReloadValue = ( unsigned long ) ( ( ( portFLOAT ) 256 - ( fBaudConst / ( portFLOAT ) ( 32 * ulWantedBaud ) ) ) + ( portFLOAT ) 0.5 );

		/* Set timer one for desired mode of operation. */
		TMOD &= 0x08;
		TMOD |= ser8BIT_WITH_RELOAD;
		SSTA0 |= serSMOD;

		/* Set the reload and start values for the time. */
		TL1 = ( unsigned char ) ulReloadValue;
		TH1 = ( unsigned char ) ulReloadValue;

		/* Setup the control register for standard n, 8, 1 - variable baud rate. */
		SCON = ser8_BIT_MODE | serRX_ENABLE;

		/* Enable the serial port interrupts */
		ES = 1;

		/* Start the timer. */
		TR1 = 1;

		SFRPAGE = ucOriginalSFRPage;
	}
	portEXIT_CRITICAL();
	
	/* Unlike some ports, this serial code does not allow for more than one
	com port.  We therefore don't return a pointer to a port structure and can
	instead just return NULL. */
	return NULL;
}
/*-----------------------------------------------------------*/

void vSerialISR( void ) interrupt 4
{
char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* 8051 port interrupt routines MUST be placed within a critical section
	if taskYIELD() is used within the ISR! */

	portENTER_CRITICAL();
	{
		if( RI ) 
		{
			/* Get the character and post it on the queue of Rxed characters.
			If the post causes a task to wake force a context switch if the woken task
			has a higher priority than the task we have interrupted. */
			cChar = SBUF;
			RI = 0;

			xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
		}

		if( TI ) 
		{
			if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == ( portBASE_TYPE ) pdTRUE )
			{
				/* Send the next character queued for Tx. */
				SBUF = cChar;
			}
			else
			{
				/* Queue empty, nothing to send. */
				uxTxEmpty = pdTRUE;
			}

			TI = 0;
		}
	
		if( xHigherPriorityTaskWoken )
		{
			portYIELD();
		}
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* There is only one port supported. */
	( void ) pxPort;

	/* Get the next character from the buffer.  Return false if no characters
	are available, or arrive before xBlockTime expires. */
	if( xQueueReceive( xRxedChars, pcRxedChar, xBlockTime ) )
	{
		return ( portBASE_TYPE ) pdTRUE;
	}
	else
	{
		return ( portBASE_TYPE ) pdFALSE;
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
portBASE_TYPE xReturn;

	/* There is only one port supported. */
	( void ) pxPort;

	portENTER_CRITICAL();
	{
		if( uxTxEmpty == pdTRUE )
		{
			SBUF = cOutChar;
			uxTxEmpty = pdFALSE;
			xReturn = ( portBASE_TYPE ) pdTRUE;
		}
		else
		{
			xReturn = xQueueSend( xCharsForTx, &cOutChar, xBlockTime );

			if( xReturn == ( portBASE_TYPE ) pdFALSE )
			{
				xReturn = ( portBASE_TYPE ) pdTRUE;
			}
		}
	}
	portEXIT_CRITICAL();

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not implemented in this port. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/





