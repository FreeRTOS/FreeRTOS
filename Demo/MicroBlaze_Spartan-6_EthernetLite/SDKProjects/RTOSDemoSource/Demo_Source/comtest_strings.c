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
 * Creates a task and a timer that operate on an interrupt driven serial port.
 * This demo assumes that the characters transmitted on a port will also be
 * received on the same port.  Therefore, the UART must either be connected to
 * an echo server, or the uart connector must have a loopback connector fitted.
 * See http://www.serialporttool.com/CommEcho.htm for a suitable echo server
 * for Windows hosts.
 *
 * The timer sends a string to the UART, toggles an LED, then waits resets
 * itself by changing its own period.  The period is calculated as a pseudo
 * random number between comTX_MAX_BLOCK_TIME and comTX_MIN_BLOCK_TIME.
 *
 * The task blocks on an Rx queue waiting for a character to become
 * available.  Received characters are checked to ensure they match those
 * transmitted by the Tx timer.  An error is latched if characters are missing,
 * incorrect, or arrive too slowly.
 *
 * How characters are actually transmitted and received is port specific.  Demos
 * that include this test/demo file will provide example drivers.  The Tx timer
 * executes in the context of the timer service (daemon) task, and must therefore
 * never attempt to block.
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

/* See the comment above the declaraction of uxBaseLED. */
#define comTX_LED_OFFSET			( 0 )
#define comRX_LED_OFFSET			( 1 )

/* The Tx timer transmits the sequence of characters at a pseudo random
interval that is capped between comTX_MAX_BLOCK_TIME and
comTX_MIN_BLOCK_TIME. */
#define comTX_MAX_BLOCK_TIME		( ( portTickType ) 0x96 )
#define comTX_MIN_BLOCK_TIME		( ( portTickType ) 0x32 )
#define comOFFSET_TIME				( ( portTickType ) 3 )

/* States for the simple state machine implemented in the Rx task. */
#define comtstWAITING_START_OF_STRING 	0
#define comtstWAITING_END_OF_STRING		1

/* A short delay in ticks - this delay is used to allow the Rx queue to fill up
a bit so more than one character can be processed at a time.  This is relative
to comTX_MIN_BLOCK_TIME to ensure it is never longer than the shortest gap
between transmissions.  It could be worked out more scientifically from the
baud rate being used. */
#define comSHORT_DELAY				( comTX_MIN_BLOCK_TIME >> ( portTickType ) 2 )

/* The string that is transmitted and received. */
#define comTRANSACTED_STRING		"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"

/* Handle to the com port used by both tasks. */
static xComPortHandle xPort = NULL;

/* The transmit timer as described at the top of the file. */
static void vComTxTimerCallback( xTimerHandle xTimer );

/* The receive task as described at the top of the file. */
static void vComRxTask( void *pvParameters );

/* The Rx task will toggle LED ( uxBaseLED + comRX_LED_OFFSET).  The Tx task
will toggle LED ( uxBaseLED + comTX_LED_OFFSET ). */
static unsigned portBASE_TYPE uxBaseLED = 0;

/* The Rx task toggles uxRxLoops on each successful iteration of its defined
function - provided no errors have ever been latched.  If this variable stops
incrementing, then an error has occurred. */
static volatile unsigned portBASE_TYPE uxRxLoops = 0UL;

/* The timer used to periodically transmit the string. */
static xTimerHandle xTxTimer = NULL;

/* The string length is held at file scope so the Tx timer does not need to
calculate it each time it executes. */
static size_t xStringLength = 0U;

/*-----------------------------------------------------------*/

void vStartComTestStringsTasks( unsigned portBASE_TYPE uxPriority, unsigned long ulBaudRate, unsigned portBASE_TYPE uxLED )
{
	/* Store values that are used at run time. */
	uxBaseLED = uxLED;

	/* Calculate the string length here, rather than each time the timer
	executes. */
	xStringLength = strlen( comTRANSACTED_STRING );

	/* Include the null terminator in the string length as this is used to
	detect the end of the string in the Rx task. */
	xStringLength++;

	/* Initialise the com port then spawn the Rx task and create the Tx
	timer. */
	xSerialPortInitMinimal( ulBaudRate, ( xStringLength * 2U ) );

	/* Create the Rx task and the Tx timer.  The timer is started from the
	Rx task. */
	xTaskCreate( vComRxTask, ( signed char * ) "COMRx", comSTACK_SIZE, NULL, uxPriority, ( xTaskHandle * ) NULL );
	xTxTimer = xTimerCreate( ( const signed char * ) "TxTimer", comTX_MIN_BLOCK_TIME, pdFALSE, NULL, vComTxTimerCallback );
	configASSERT( xTxTimer );
}
/*-----------------------------------------------------------*/

static void vComTxTimerCallback( xTimerHandle xTimer )
{
portTickType xTimeToWait;

	/* Just to stop compiler warnings. */
	( void ) xTimer;

	/* Send the string.  How this is actually performed depends on the
	sample driver provided with this demo.  However - as this is a timer,
	it executes in the context of the timer task and therefore must not
	block. */
	vSerialPutString( xPort, ( const signed char * const ) comTRANSACTED_STRING, xStringLength );

	/* Toggle an LED to give a visible indication that another transmission
	has been performed. */
	vParTestToggleLED( uxBaseLED + comTX_LED_OFFSET );

	/* Wait a pseudo random time before sending the string again. */
	xTimeToWait = xTaskGetTickCount() + comOFFSET_TIME;

	/* Ensure the time to wait does not greater than comTX_MAX_BLOCK_TIME. */
	xTimeToWait %= comTX_MAX_BLOCK_TIME;

	/* Ensure the time to wait is not less than comTX_MIN_BLOCK_TIME. */
	if( xTimeToWait < comTX_MIN_BLOCK_TIME )
	{
		xTimeToWait = comTX_MIN_BLOCK_TIME;
	}

	/* Reset the timer to run again xTimeToWait ticks from now.  This function
	is called from the context of the timer task, so the block time must not
	be anything other than zero. */
	xTimerChangePeriod( xTxTimer, xTimeToWait, 0 );
}
/*-----------------------------------------------------------*/

static void vComRxTask( void *pvParameters )
{
portBASE_TYPE xState = comtstWAITING_START_OF_STRING, xErrorOccurred = pdFALSE;
signed char *pcExpectedByte, cRxedChar;
const xComPortHandle xPort = NULL;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	/* Start the Tx timer.  This only needs to be started once, as it will
	reset itself thereafter. */
	xTimerStart( xTxTimer, portMAX_DELAY );

	/* The first expected Rx character is the first in the string that is
	transmitted. */
	pcExpectedByte = ( signed char * ) comTRANSACTED_STRING;

	for( ;; )
	{
		/* Wait for the next character. */
		if( xSerialGetChar( xPort, &cRxedChar, ( comTX_MAX_BLOCK_TIME * 2 ) ) == pdFALSE )
		{
			/* A character definitely should have been received by now.  As a
			character was not received an error must have occurred (which might
			just be that the loopback connector is not fitted. */
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

					/* Block for a short period.  This just allows the Rx queue to
					contain more than one character, and therefore prevent
					thrashing reads to the queue and repetitive context switches as
					each character is received. */
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
						show that this task is still healthy. */
						if( xErrorOccurred == pdFALSE )
						{
							uxRxLoops++;

							/* Toggle an LED to give a visible sign that a
							complete string has been received. */
							vParTestToggleLED( uxBaseLED + comRX_LED_OFFSET );
						}

						/* Go back to wait for the start of the next string. */
						pcExpectedByte = ( signed char * ) comTRANSACTED_STRING;
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

portBASE_TYPE xAreComTestTasksStillRunning( void )
{
portBASE_TYPE xReturn;

	/* If the count of successful reception loops has not changed than at
	some time an error occurred (i.e. a character was received out of sequence)
	and we will return false. */
	if( uxRxLoops == 0UL )
	{
		xReturn = pdFALSE;
	}
	else
	{
		xReturn = pdTRUE;
	}

	/* Reset the count of successful Rx loops.  When this function is called
	again it should have been incremented. */
	uxRxLoops = 0UL;

	return xReturn;
}

