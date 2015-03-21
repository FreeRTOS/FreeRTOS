/*
    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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
#define comTX_MAX_BLOCK_TIME		( ( TickType_t ) 0x96 )
#define comTX_MIN_BLOCK_TIME		( ( TickType_t ) 0x32 )
#define comOFFSET_TIME				( ( TickType_t ) 3 )

/* We should find that each character can be queued for Tx immediately and we
don't have to block to send. */
#define comNO_BLOCK					( ( TickType_t ) 0 )

/* The Rx task will block on the Rx queue for a long period. */
#define comRX_BLOCK_TIME			( ( TickType_t ) 0xffff )

/* The sequence transmitted is from comFIRST_BYTE to and including comLAST_BYTE. */
#define comFIRST_BYTE				( 'A' )
#define comLAST_BYTE				( 'X' )

#define comBUFFER_LEN				( ( UBaseType_t ) ( comLAST_BYTE - comFIRST_BYTE ) + ( UBaseType_t ) 1 )
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
static UBaseType_t uxBaseLED = 0;

/* Check variable used to ensure no error have occurred.  The Rx task will
increment this variable after every successfully received sequence.  If at any
time the sequence is incorrect the the variable will stop being incremented. */
static volatile UBaseType_t uxRxLoops = comINITIAL_RX_COUNT_VALUE;

/*-----------------------------------------------------------*/

void vAltStartComTestTasks( UBaseType_t uxPriority, uint32_t ulBaudRate, UBaseType_t uxLED )
{
	/* Initialise the com port then spawn the Rx and Tx tasks. */
	uxBaseLED = uxLED;
	xSerialPortInitMinimal( ulBaudRate, comBUFFER_LEN );

	/* The Tx task is spawned with a lower priority than the Rx task. */
	xTaskCreate( vComTxTask, "COMTx", comSTACK_SIZE, NULL, uxPriority - 1, ( TaskHandle_t * ) NULL );
	xTaskCreate( vComRxTask, "COMRx", comSTACK_SIZE, NULL, uxPriority, ( TaskHandle_t * ) NULL );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vComTxTask, pvParameters )
{
char cByteToSend;
TickType_t xTimeToWait;

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
signed char cExpectedByte, cByteRxed;
BaseType_t xResyncRequired = pdFALSE, xErrorOccurred = pdFALSE;

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

BaseType_t xAreComTestTasksStillRunning( void )
{
BaseType_t xReturn;

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

