/*
 * FreeRTOS Kernel V10.0.0
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
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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
 * This demo file demonstrates how to send data between an ISR and a
 * co-routine.  A tick hook function is used to periodically pass data between
 * the RTOS tick and a set of 'hook' co-routines.
 *
 * hookNUM_HOOK_CO_ROUTINES co-routines are created.  Each co-routine blocks
 * to wait for a character to be received on a queue from the tick ISR, checks
 * to ensure the character received was that expected, then sends the number
 * back to the tick ISR on a different queue.
 *
 * The tick ISR checks the numbers received back from the 'hook' co-routines
 * matches the number previously sent.
 *
 * If at any time a queue function returns unexpectedly, or an incorrect value
 * is received either by the tick hook or a co-routine then an error is
 * latched.
 *
 * This demo relies on each 'hook' co-routine to execute between each
 * hookTICK_CALLS_BEFORE_POST tick interrupts.  This and the heavy use of
 * queues from within an interrupt may result in an error being detected on
 * slower targets simply due to timing.
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "croutine.h"
#include "queue.h"

/* Demo application includes. */
#include "crhook.h"

/* The number of 'hook' co-routines that are to be created. */
#define hookNUM_HOOK_CO_ROUTINES        ( 4 )

/* The number of times the tick hook should be called before a character is
posted to the 'hook' co-routines. */
#define hookTICK_CALLS_BEFORE_POST      ( 500 )

/* There should never be more than one item in any queue at any time. */
#define hookHOOK_QUEUE_LENGTH           ( 1 )

/* Don't block when initially posting to the queue. */
#define hookNO_BLOCK_TIME               ( 0 )

/* The priority relative to other co-routines (rather than tasks) that the
'hook' co-routines should take. */
#define mainHOOK_CR_PRIORITY			( 1 )
/*-----------------------------------------------------------*/

/*
 * The co-routine function itself.
 */
static void prvHookCoRoutine( CoRoutineHandle_t xHandle, UBaseType_t uxIndex );


/*
 * The tick hook function.  This receives a number from each 'hook' co-routine
 * then sends a number to each co-routine.  An error is flagged if a send or
 * receive fails, or an unexpected number is received.
 */
void vApplicationTickHook( void );

/*-----------------------------------------------------------*/

/* Queues used to send data FROM a co-routine TO the tick hook function.
The hook functions received (Rx's) on these queues.  One queue per
'hook' co-routine. */
static QueueHandle_t xHookRxQueues[ hookNUM_HOOK_CO_ROUTINES ];

/* Queues used to send data FROM the tick hook TO a co-routine function.
The hood function transmits (Tx's) on these queues.  One queue per
'hook' co-routine. */
static QueueHandle_t xHookTxQueues[ hookNUM_HOOK_CO_ROUTINES ];

/* Set to true if an error is detected at any time. */
static BaseType_t xCoRoutineErrorDetected = pdFALSE;

/*-----------------------------------------------------------*/

void vStartHookCoRoutines( void )
{
UBaseType_t uxIndex, uxValueToPost = 0;

	for( uxIndex = 0; uxIndex < hookNUM_HOOK_CO_ROUTINES; uxIndex++ )
	{
		/* Create a queue to transmit to and receive from each 'hook'
		co-routine. */
		xHookRxQueues[ uxIndex ] = xQueueCreate( hookHOOK_QUEUE_LENGTH, sizeof( UBaseType_t ) );
		xHookTxQueues[ uxIndex ] = xQueueCreate( hookHOOK_QUEUE_LENGTH, sizeof( UBaseType_t ) );

		/* To start things off the tick hook function expects the queue it
		uses to receive data to contain a value.  */
		xQueueSend( xHookRxQueues[ uxIndex ], &uxValueToPost, hookNO_BLOCK_TIME );

		/* Create the 'hook' co-routine itself. */
		xCoRoutineCreate( prvHookCoRoutine, mainHOOK_CR_PRIORITY, uxIndex );
	}
}
/*-----------------------------------------------------------*/

static UBaseType_t uxCallCounter = 0, uxNumberToPost = 0;
void vApplicationTickHook( void )
{
UBaseType_t uxReceivedNumber;
BaseType_t xIndex, xCoRoutineWoken;

	/* Is it time to talk to the 'hook' co-routines again? */
	uxCallCounter++;
	if( uxCallCounter >= hookTICK_CALLS_BEFORE_POST )
	{
		uxCallCounter = 0;

		for( xIndex = 0; xIndex < hookNUM_HOOK_CO_ROUTINES; xIndex++ )
		{
			xCoRoutineWoken = pdFALSE;
			if( crQUEUE_RECEIVE_FROM_ISR( xHookRxQueues[ xIndex ], &uxReceivedNumber, &xCoRoutineWoken ) != pdPASS )
			{
				/* There is no reason why we would not expect the queue to
				contain a value. */
				xCoRoutineErrorDetected = pdTRUE;
			}
			else
			{
				/* Each queue used to receive data from the 'hook' co-routines
				should contain the number we last posted to the same co-routine. */
				if( uxReceivedNumber != uxNumberToPost )
				{
					xCoRoutineErrorDetected = pdTRUE;
				}

				/* Nothing should be blocked waiting to post to the queue. */
				if( xCoRoutineWoken != pdFALSE )
				{
					xCoRoutineErrorDetected = pdTRUE;
				}
			}
		}

		/* Start the next cycle by posting the next number onto each Tx queue. */
		uxNumberToPost++;

		for( xIndex = 0; xIndex < hookNUM_HOOK_CO_ROUTINES; xIndex++ )
		{
			if( crQUEUE_SEND_FROM_ISR( xHookTxQueues[ xIndex ], &uxNumberToPost, pdFALSE ) != pdTRUE )
			{
				/* Posting to the queue should have woken the co-routine that
				was blocked on the queue. */
				xCoRoutineErrorDetected = pdTRUE;
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvHookCoRoutine( CoRoutineHandle_t xHandle, UBaseType_t uxIndex )
{
static UBaseType_t uxReceivedValue[ hookNUM_HOOK_CO_ROUTINES ];
BaseType_t xResult;

	/* Each co-routine MUST start with a call to crSTART(); */
	crSTART( xHandle );

	for( ;; )
	{
		/* Wait to receive a value from the tick hook. */
		xResult = pdFAIL;
		crQUEUE_RECEIVE( xHandle, xHookTxQueues[ uxIndex ], &( uxReceivedValue[ uxIndex ] ), portMAX_DELAY, &xResult );

		/* There is no reason why we should not have received something on
		the queue. */
		if( xResult != pdPASS )
		{
			xCoRoutineErrorDetected = pdTRUE;
		}

		/* Send the same number back to the idle hook so it can verify it. */
		xResult = pdFAIL;
		crQUEUE_SEND( xHandle, xHookRxQueues[ uxIndex ], &( uxReceivedValue[ uxIndex ] ), hookNO_BLOCK_TIME, &xResult );
		if( xResult != pdPASS )
		{
			/* There is no reason why we should not have been able to post to
			the queue. */
			xCoRoutineErrorDetected = pdTRUE;
		}
	}

	/* Each co-routine MUST end with a call to crEND(). */
	crEND();
}
/*-----------------------------------------------------------*/

BaseType_t xAreHookCoRoutinesStillRunning( void )
{
	if( xCoRoutineErrorDetected )
	{
		return pdFALSE;
	}
	else
	{
		return pdTRUE;
	}
}



