/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * Creates a task and a timer that operate on an interrupt driven serial port.
 * This demo assumes that the characters transmitted on a port will also be
 * received on the same port.  Therefore, the UART must either be connected to
 * an echo server, or the uart connector must have a loopback connector fitted.
 * See http://www.serialporttool.com/CommEcho.htm for a suitable echo server
 * for Windows hosts.
 *
 * The timer sends a string to the UART, toggles an LED, then resets itself by
 * changing its own period.  The period is calculated as a pseudo random number
 * between comTX_MAX_BLOCK_TIME and comTX_MIN_BLOCK_TIME.
 *
 * The task blocks on an Rx queue waiting for a character to become available.
 * Received characters are checked to ensure they match those transmitted by the
 * Tx timer.  An error is latched if characters are missing, incorrect, or
 * arrive too slowly.
 *
 * How characters are actually transmitted and received is port specific.  Demos
 * that include this test/demo file will provide example drivers.  The Tx timer
 * executes in the context of the timer service (daemon) task, and must
 * therefore never attempt to block.
 *
 */

/* Scheduler include files. */
#include <stdlib.h>
#include <string.h>
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

#ifndef configUSE_TIMERS
	#error This demo uses timers.  configUSE_TIMERS must be set to 1 in FreeRTOSConfig.h.
#endif

#if configUSE_TIMERS != 1
	#error This demo uses timers.  configUSE_TIMERS must be set to 1 in FreeRTOSConfig.h.
#endif


/* Demo program include files. */
#include "serial.h"
#include "comtest_strings.h"
#include "partest.h"

/* The size of the stack given to the Rx task. */
#define comSTACK_SIZE				configMINIMAL_STACK_SIZE

/* See the comment above the declaraction of the uxBaseLED variable. */
#define comTX_LED_OFFSET			( 0 )
#define comRX_LED_OFFSET			( 1 )

/* The Tx timer transmits the sequence of characters at a pseudo random
interval that is capped between comTX_MAX_BLOCK_TIME and
comTX_MIN_BLOCK_TIME. */
#define comTX_MAX_BLOCK_TIME		( ( TickType_t ) 0x96 )
#define comTX_MIN_BLOCK_TIME		( ( TickType_t ) 0x32 )
#define comOFFSET_TIME				( ( TickType_t ) 3 )

/* States for the simple state machine implemented in the Rx task. */
#define comtstWAITING_START_OF_STRING 	0
#define comtstWAITING_END_OF_STRING		1

/* A short delay in ticks - this delay is used to allow the Rx queue to fill up
a bit so more than one character can be processed at a time.  This is relative
to comTX_MIN_BLOCK_TIME to ensure it is never longer than the shortest gap
between transmissions.  It could be worked out more scientifically from the
baud rate being used. */
#define comSHORT_DELAY				( comTX_MIN_BLOCK_TIME >> ( TickType_t ) 2 )

/* The string that is transmitted and received. */
#define comTRANSACTED_STRING		"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"

/* A block time of 0 simply means "don't block". */
#define comtstDONT_BLOCK			( TickType_t ) 0

/* Handle to the com port used by both tasks. */
static xComPortHandle xPort = NULL;

/* The callback function allocated to the transmit timer, as described in the
comments at the top of this file. */
static void prvComTxTimerCallback( TimerHandle_t xTimer );

/* The receive task as described in the comments at the top of this file. */
static void vComRxTask( void *pvParameters );

/* The Rx task will toggle LED ( uxBaseLED + comRX_LED_OFFSET).  The Tx task
will toggle LED ( uxBaseLED + comTX_LED_OFFSET ). */
static UBaseType_t uxBaseLED = 0;

/* The Rx task toggles uxRxLoops on each successful iteration of its defined
function - provided no errors have ever been latched.  If this variable stops
incrementing, then an error has occurred. */
static volatile UBaseType_t uxRxLoops = 0UL;

/* The timer used to periodically transmit the string.  This is the timer that
has prvComTxTimerCallback allocated to it as its callback function. */
static TimerHandle_t xTxTimer = NULL;

/* The string length is held at file scope so the Tx timer does not need to
calculate it each time it executes. */
static size_t xStringLength = 0U;

/*-----------------------------------------------------------*/

void vStartComTestStringsTasks( UBaseType_t uxPriority, uint32_t ulBaudRate, UBaseType_t uxLED )
{
	/* Store values that are used at run time. */
	uxBaseLED = uxLED;

	/* Calculate the string length here, rather than each time the Tx timer
	executes. */
	xStringLength = strlen( comTRANSACTED_STRING );

	/* Include the null terminator in the string length as this is used to
	detect the end of the string in the Rx task. */
	xStringLength++;

	/* Initialise the com port, then spawn the Rx task and create the Tx
	timer. */
	xSerialPortInitMinimal( ulBaudRate, ( xStringLength * 2U ) );

	/* Create the Rx task and the Tx timer.  The timer is started from the
	Rx task. */
	xTaskCreate( vComRxTask, "COMRx", comSTACK_SIZE, NULL, uxPriority, ( TaskHandle_t * ) NULL );
	xTxTimer = xTimerCreate( "TxTimer", comTX_MIN_BLOCK_TIME, pdFALSE, NULL, prvComTxTimerCallback );
	configASSERT( xTxTimer );
}
/*-----------------------------------------------------------*/

static void prvComTxTimerCallback( TimerHandle_t xTimer )
{
TickType_t xTimeToWait;

	/* The parameter is not used in this case. */
	( void ) xTimer;

	/* Send the string.  How this is actually performed depends on the
	sample driver provided with this demo.  However - as this is a timer,
	it executes in the context of the timer task and therefore must not
	block. */
	vSerialPutString( xPort, comTRANSACTED_STRING, xStringLength );

	/* Toggle an LED to give a visible indication that another transmission
	has been performed. */
	vParTestToggleLED( uxBaseLED + comTX_LED_OFFSET );

	/* Wait a pseudo random time before sending the string again. */
	xTimeToWait = xTaskGetTickCount() + comOFFSET_TIME;

	/* Ensure the time to wait is not greater than comTX_MAX_BLOCK_TIME. */
	xTimeToWait %= comTX_MAX_BLOCK_TIME;

	/* Ensure the time to wait is not less than comTX_MIN_BLOCK_TIME. */
	if( xTimeToWait < comTX_MIN_BLOCK_TIME )
	{
		xTimeToWait = comTX_MIN_BLOCK_TIME;
	}

	/* Reset the timer to run again xTimeToWait ticks from now.  This function
	is called from the context of the timer task, so the block time must not
	be anything other than zero. */
	xTimerChangePeriod( xTxTimer, xTimeToWait, comtstDONT_BLOCK );
}
/*-----------------------------------------------------------*/

static void vComRxTask( void *pvParameters )
{
BaseType_t xState = comtstWAITING_START_OF_STRING, xErrorOccurred = pdFALSE;
char *pcExpectedByte, cRxedChar;
const xComPortHandle xPort = NULL;

	/* The parameter is not used in this example. */
	( void ) pvParameters;

	/* Start the Tx timer.  This only needs to be started once, as it will
	reset itself thereafter. */
	xTimerStart( xTxTimer, portMAX_DELAY );

	/* The first expected Rx character is the first in the string that is
	transmitted. */
	pcExpectedByte = comTRANSACTED_STRING;

	for( ;; )
	{
		/* Wait for the next character. */
		if( xSerialGetChar( xPort, &cRxedChar, ( comTX_MAX_BLOCK_TIME * 2 ) ) == pdFALSE )
		{
			/* A character definitely should have been received by now.  As a
			character was not received an error must have occurred (which might
			just be that the loopback connector is not fitted). */
			xErrorOccurred = pdTRUE;
		}

		switch( xState )
		{
			case comtstWAITING_START_OF_STRING:
				if( cRxedChar == *pcExpectedByte )
				{
					/* The received character was the first character of the
					string.  Move to the next state to check each character
					as it comes in until the entire string has been received. */
					xState = comtstWAITING_END_OF_STRING;
					pcExpectedByte++;

					/* Block for a short period.  This just allows the Rx queue
					to contain more than one character, and therefore prevent
					thrashing reads to the queue, and repetitive context
					switches as	each character is received. */
					vTaskDelay( comSHORT_DELAY );
				}
				break;

			case comtstWAITING_END_OF_STRING:
				if( cRxedChar == *pcExpectedByte )
				{
					/* The received character was the expected character.  Was
					it the last character in the string - i.e. the null
					terminator? */
					if( cRxedChar == 0x00 )
					{
						/* The entire string has been received.  If no errors
						have been latched, then increment the loop counter to
						show this task is still healthy. */
						if( xErrorOccurred == pdFALSE )
						{
							uxRxLoops++;

							/* Toggle an LED to give a visible sign that a
							complete string has been received. */
							vParTestToggleLED( uxBaseLED + comRX_LED_OFFSET );
						}

						/* Go back to wait for the start of the next string. */
						pcExpectedByte = comTRANSACTED_STRING;
						xState = comtstWAITING_START_OF_STRING;
					}
					else
					{
						/* Wait for the next character in the string. */
						pcExpectedByte++;
					}
				}
				else
				{
					/* The character received was not that expected. */
					xErrorOccurred = pdTRUE;
				}
				break;

			default:
				/* Should not get here.  Stop the Rx loop counter from
				incrementing to latch the error. */
				xErrorOccurred = pdTRUE;
				break;
		}
	}
}
/*-----------------------------------------------------------*/

BaseType_t xAreComTestTasksStillRunning( void )
{
BaseType_t xReturn;

	/* If the count of successful reception loops has not changed than at
	some time an error occurred (i.e. a character was received out of sequence)
	and false is returned. */
	if( uxRxLoops == 0UL )
	{
		xReturn = pdFALSE;
	}
	else
	{
		xReturn = pdTRUE;
	}

	/* Reset the count of successful Rx loops.  When this function is called
	again it should have been incremented again. */
	uxRxLoops = 0UL;

	return xReturn;
}

