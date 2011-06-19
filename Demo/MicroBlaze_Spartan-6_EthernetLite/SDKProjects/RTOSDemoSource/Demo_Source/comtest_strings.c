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
 * This version of comtest. c is for use on systems that have limited stack
 * space and no display facilities.  The complete version can be found in
 * the Demo/Common/Full directory.
 *
 * Creates two tasks that operate on an interrupt driven serial port.  A
 * loopback connector should be used so that everything that is transmitted is
 * also received.  The serial port does not use any flow control.  On a
 * standard 9way 'D' connector pins two and three should be connected together.
 *
 * The first task posts a sequence of characters to the Tx queue, toggling an
 * LED on each successful post.  At the end of the sequence it sleeps for a
 * pseudo-random period before resending the same sequence.
 *
 * The UART Tx end interrupt is enabled whenever data is available in the Tx
 * queue.  The Tx end ISR removes a single character from the Tx queue and
 * passes it to the UART for transmission.
 *
 * The second task blocks on the Rx queue waiting for a character to become
 * available.  When the UART Rx end interrupt receives a character it places
 * it in the Rx queue, waking the second task.  The second task checks that the
 * characters removed from the Rx queue form the same sequence as those posted
 * to the Tx queue, and toggles an LED for each correct character.
 *
 * The receiving task is spawned with a higher priority than the transmitting
 * task.  The receiver will therefore wake every time a character is
 * transmitted so neither the Tx or Rx queue should ever hold more than a few
 * characters.
 *
 */

/* Scheduler include files. */
#include <stdlib.h>
#include <string.h>
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "serial.h"
#include "comtest_strings.h"
#include "partest.h"

#define comSTACK_SIZE				configMINIMAL_STACK_SIZE
#define comTX_LED_OFFSET			( 0 )
#define comRX_LED_OFFSET			( 1 )
#define comTOTAL_PERMISSIBLE_ERRORS ( 2 )

/* The Tx task will transmit the sequence of characters at a pseudo random
interval.  This is the maximum and minimum block time between sends. */
#define comTX_MAX_BLOCK_TIME		( ( portTickType ) 0x96 )
#define comTX_MIN_BLOCK_TIME		( ( portTickType ) 0x32 )
#define comOFFSET_TIME				( ( portTickType ) 3 )

/* We should find that each character can be queued for Tx immediately and we
don't have to block to send. */
#define comNO_BLOCK					( ( portTickType ) 0 )

/* The Rx task will block on the Rx queue for a long period. */
#define comRX_BLOCK_TIME			( ( portTickType ) 0xffff )

/* The string that is transmitted and received. */
#define comTRANSACTED_STRING		"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

#define comBUFFER_LEN				( ( unsigned portBASE_TYPE ) ( comLAST_BYTE - comFIRST_BYTE ) + ( unsigned portBASE_TYPE ) 1 )
#define comINITIAL_RX_COUNT_VALUE	( 0 )

/* Handle to the com port used by both tasks. */
static xComPortHandle xPort = NULL;

/* The transmit task as described at the top of the file. */
static void vComTxTask( void *pvParameters );

/* The receive task as described at the top of the file. */
static portTASK_FUNCTION_PROTO( vComRxTask, pvParameters );

/* The LED that should be toggled by the Rx and Tx tasks.  The Rx task will
toggle LED ( uxBaseLED + comRX_LED_OFFSET).  The Tx task will toggle LED
( uxBaseLED + comTX_LED_OFFSET ). */
static unsigned portBASE_TYPE uxBaseLED = 0;

/* Check variable used to ensure no error have occurred.  The Rx task will
increment this variable after every successfully received sequence.  If at any
time the sequence is incorrect the the variable will stop being incremented. */
static volatile unsigned portBASE_TYPE uxRxLoops = comINITIAL_RX_COUNT_VALUE;

/*-----------------------------------------------------------*/

void vStartComTestStringsTasks( unsigned portBASE_TYPE uxPriority, unsigned long ulBaudRate, unsigned portBASE_TYPE uxLED )
{
	/* Initialise the com port then spawn the Rx and Tx tasks. */
	uxBaseLED = uxLED;
	xSerialPortInitMinimal( ulBaudRate, strlen( comTRANSACTED_STRING ) );

	/* The Tx task is spawned with a lower priority than the Rx task. */
	xTaskCreate( vComTxTask, ( signed char * ) "COMTx", comSTACK_SIZE, NULL, uxPriority - 1, ( xTaskHandle * ) NULL );
	xTaskCreate( vComRxTask, ( signed char * ) "COMRx", comSTACK_SIZE, NULL, uxPriority, ( xTaskHandle * ) NULL );
}
/*-----------------------------------------------------------*/

static void vComTxTask( void * pvParameters )
{
portTickType xTimeToWait;
size_t xStringLength;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	xStringLength = strlen( comTRANSACTED_STRING );

	/* Include the null terminator in the string length. */
	xStringLength++;

	for( ;; )
	{
		/* Send the string.  Setting the last parameter to pdTRUE ensures
		that vSerialPutString() will not return until the entire string has
		been sent to the UART.  The UART interrupt is used to send more data
		to the UART as the UART FIFO empties, until the entire string has been
		sent.  No CPU time is consumed by this task while it waits for the
		string to be sent to the UART. */
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

		vTaskDelay( xTimeToWait );
	}
}
/*-----------------------------------------------------------*/

#define comtstWAITING_START_OF_STRING 	0
#define comtstWAITING_END_OF_STRING		1


static void vComRxTask( void *pvParameters )
{
portBASE_TYPE xState = comtstWAITING_START_OF_STRING, xErrorOccurred = pdFALSE;
char *pcExpectedByte, cRxedChar;
const xComPortHandle xPort = NULL;


	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	pcExpectedByte = comTRANSACTED_STRING;

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

portBASE_TYPE xAreComTestTasksStillRunning( void )
{
portBASE_TYPE xReturn;

	/* If the count of successful reception loops has not changed than at
	some time an error occurred (i.e. a character was received out of sequence)
	and we will return false. */
	if( uxRxLoops == comINITIAL_RX_COUNT_VALUE )
	{
		xReturn = pdFALSE;
	}
	else
	{
		xReturn = pdTRUE;
	}

	/* Reset the count of successful Rx loops.  When this function is called
	again it should have been incremented. */
	uxRxLoops = comINITIAL_RX_COUNT_VALUE;

	return xReturn;
}

