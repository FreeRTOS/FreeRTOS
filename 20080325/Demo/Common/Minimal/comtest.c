/*
	FreeRTOS.org V4.7.2 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************

	Please ensure to read the configuration and relevant port sections of the 
	online documentation.

	+++ http://www.FreeRTOS.org +++
	Documentation, latest information, license and contact details.  

	+++ http://www.SafeRTOS.com +++
	A version that is certified for use in safety critical systems.

	+++ http://www.OpenRTOS.com +++
	Commercial support, development, porting, licensing and training services.

	***************************************************************************
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

/*
Changes from V1.2.0:

	+ Reduced the maximum time between successive transmissions.  This provides
	  for a more rigorous test.

Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  portTickType rather than unsigned portLONG.

Changes from V2.5.1

	+ The constant comOFFSET_TIME added to the delay period to ensure a more
	  random delay period is used.
*/

/* Scheduler include files. */
#include <stdlib.h>
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "serial.h"
#include "comtest.h"
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

/* The sequence transmitted is from comFIRST_BYTE to and including comLAST_BYTE. */
#define comFIRST_BYTE				( 'A' )
#define comLAST_BYTE				( 'X' )

#define comBUFFER_LEN				( ( unsigned portBASE_TYPE ) ( comLAST_BYTE - comFIRST_BYTE ) + ( unsigned portBASE_TYPE ) 1 )
#define comINITIAL_RX_COUNT_VALUE	( 0 )

/* Handle to the com port used by both tasks. */
static xComPortHandle xPort = NULL;

/* The transmit task as described at the top of the file. */
static portTASK_FUNCTION_PROTO( vComTxTask, pvParameters );

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

void vAltStartComTestTasks( unsigned portBASE_TYPE uxPriority, unsigned portLONG ulBaudRate, unsigned portBASE_TYPE uxLED )
{
	/* Initialise the com port then spawn the Rx and Tx tasks. */
	uxBaseLED = uxLED;
	xSerialPortInitMinimal( ulBaudRate, comBUFFER_LEN );

	/* The Tx task is spawned with a lower priority than the Rx task. */
	xTaskCreate( vComTxTask, ( signed portCHAR * ) "COMTx", comSTACK_SIZE, NULL, uxPriority - 1, ( xTaskHandle * ) NULL );
	xTaskCreate( vComRxTask, ( signed portCHAR * ) "COMRx", comSTACK_SIZE, NULL, uxPriority, ( xTaskHandle * ) NULL );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vComTxTask, pvParameters )
{
signed portCHAR cByteToSend;
portTickType xTimeToWait;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Simply transmit a sequence of characters from comFIRST_BYTE to
		comLAST_BYTE. */
		for( cByteToSend = comFIRST_BYTE; cByteToSend <= comLAST_BYTE; cByteToSend++ )
		{
			if( xSerialPutChar( xPort, cByteToSend, comNO_BLOCK ) == pdPASS )
			{
				vParTestToggleLED( uxBaseLED + comTX_LED_OFFSET );
			}
		}

		/* Turn the LED off while we are not doing anything. */
		vParTestSetLED( uxBaseLED + comTX_LED_OFFSET, pdFALSE );

		/* We have posted all the characters in the string - wait before
		re-sending.  Wait a pseudo-random time as this will provide a better
		test. */
		xTimeToWait = xTaskGetTickCount() + comOFFSET_TIME;

		/* Make sure we don't wait too long... */
		xTimeToWait %= comTX_MAX_BLOCK_TIME;

		/* ...but we do want to wait. */
		if( xTimeToWait < comTX_MIN_BLOCK_TIME )
		{
			xTimeToWait = comTX_MIN_BLOCK_TIME;
		}

		vTaskDelay( xTimeToWait );
	}
} /*lint !e715 !e818 pvParameters is required for a task function even if it is not referenced. */
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vComRxTask, pvParameters )
{
signed portCHAR cExpectedByte, cByteRxed;
portBASE_TYPE xResyncRequired = pdFALSE, xErrorOccurred = pdFALSE;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* We expect to receive the characters from comFIRST_BYTE to
		comLAST_BYTE in an incrementing order.  Loop to receive each byte. */
		for( cExpectedByte = comFIRST_BYTE; cExpectedByte <= comLAST_BYTE; cExpectedByte++ )
		{
			/* Block on the queue that contains received bytes until a byte is
			available. */
			if( xSerialGetChar( xPort, &cByteRxed, comRX_BLOCK_TIME ) )
			{
				/* Was this the byte we were expecting?  If so, toggle the LED,
				otherwise we are out on sync and should break out of the loop
				until the expected character sequence is about to restart. */
				if( cByteRxed == cExpectedByte )
				{
					vParTestToggleLED( uxBaseLED + comRX_LED_OFFSET );
				}
				else
				{
					xResyncRequired = pdTRUE;
					break; /*lint !e960 Non-switch break allowed. */
				}
			}
		}

		/* Turn the LED off while we are not doing anything. */
		vParTestSetLED( uxBaseLED + comRX_LED_OFFSET, pdFALSE );

		/* Did we break out of the loop because the characters were received in
		an unexpected order?  If so wait here until the character sequence is
		about to restart. */
		if( xResyncRequired == pdTRUE )
		{
			while( cByteRxed != comLAST_BYTE )
			{
				/* Block until the next char is available. */
				xSerialGetChar( xPort, &cByteRxed, comRX_BLOCK_TIME );
			}

			/* Note that an error occurred which caused us to have to resync.
			We use this to stop incrementing the loop counter so
			sAreComTestTasksStillRunning() will return false - indicating an
			error. */
			xErrorOccurred++;

			/* We have now resynced with the Tx task and can continue. */
			xResyncRequired = pdFALSE;
		}
		else
		{
			if( xErrorOccurred < comTOTAL_PERMISSIBLE_ERRORS )
			{
				/* Increment the count of successful loops.  As error
				occurring (i.e. an unexpected character being received) will
				prevent this counter being incremented for the rest of the
				execution.   Don't worry about mutual exclusion on this
				variable - it doesn't really matter as we just want it
				to change. */
				uxRxLoops++;
			}
		}
	}
} /*lint !e715 !e818 pvParameters is required for a task function even if it is not referenced. */
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
	again we expect this to have been incremented. */
	uxRxLoops = comINITIAL_RX_COUNT_VALUE;

	return xReturn;
}

