/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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





