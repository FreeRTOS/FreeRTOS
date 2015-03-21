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

/**
 * Creates six tasks that operate on three queues as follows:
 *
 * The first two tasks send and receive an incrementing number to/from a queue.  
 * One task acts as a producer and the other as the consumer.  The consumer is a 
 * higher priority than the producer and is set to block on queue reads.  The queue 
 * only has space for one item - as soon as the producer posts a message on the 
 * queue the consumer will unblock, pre-empt the producer, and remove the item.
 * 
 * The second two tasks work the other way around.  Again the queue used only has
 * enough space for one item.  This time the consumer has a lower priority than the 
 * producer.  The producer will try to post on the queue blocking when the queue is 
 * full.  When the consumer wakes it will remove the item from the queue, causing 
 * the producer to unblock, pre-empt the consumer, and immediately re-fill the 
 * queue.
 * 
 * The last two tasks use the same queue producer and consumer functions.  This time the queue has
 * enough space for lots of items and the tasks operate at the same priority.  The 
 * producer will execute, placing items into the queue.  The consumer will start 
 * executing when either the queue becomes full (causing the producer to block) or 
 * a context switch occurs (tasks of the same priority will time slice).
 *
 * \page BlockQC blockQ.c
 * \ingroup DemoFiles
 * <HR>
 */

/*
Changes from V1.00:
	
	+ Reversed the priority and block times of the second two demo tasks so
	  they operate as per the description above.

Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  TickType_t rather than unsigned long.

Changes from V4.0.2

	+ The second set of tasks were created the wrong way around.  This has been
	  corrected.
*/


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo program include files. */
#include "BlockQ.h"
#include "print.h"

#define blckqSTACK_SIZE		( ( unsigned short ) configMINIMAL_STACK_SIZE )
#define blckqNUM_TASK_SETS	( 3 )

/* Structure used to pass parameters to the blocking queue tasks. */
typedef struct BLOCKING_QUEUE_PARAMETERS
{
	QueueHandle_t xQueue;					/*< The queue to be used by the task. */
	TickType_t xBlockTime;			/*< The block time to use on queue reads/writes. */
	volatile short *psCheckVariable;	/*< Incremented on each successful cycle to check the task is still running. */
} xBlockingQueueParameters;

/* Task function that creates an incrementing number and posts it on a queue. */
static void vBlockingQueueProducer( void *pvParameters );

/* Task function that removes the incrementing number from a queue and checks that 
it is the expected number. */
static void vBlockingQueueConsumer( void *pvParameters );

/* Variables which are incremented each time an item is removed from a queue, and 
found to be the expected value. 
These are used to check that the tasks are still running. */
static volatile short sBlockingConsumerCount[ blckqNUM_TASK_SETS ] = { ( short ) 0, ( short ) 0, ( short ) 0 };

/* Variable which are incremented each time an item is posted on a queue.   These 
are used to check that the tasks are still running. */
static volatile short sBlockingProducerCount[ blckqNUM_TASK_SETS ] = { ( short ) 0, ( short ) 0, ( short ) 0 };

/*-----------------------------------------------------------*/

void vStartBlockingQueueTasks( unsigned portBASE_TYPE uxPriority )
{
xBlockingQueueParameters *pxQueueParameters1, *pxQueueParameters2;
xBlockingQueueParameters *pxQueueParameters3, *pxQueueParameters4;
xBlockingQueueParameters *pxQueueParameters5, *pxQueueParameters6;
const unsigned portBASE_TYPE uxQueueSize1 = 1, uxQueueSize5 = 5;
const TickType_t xBlockTime = ( TickType_t ) 1000 / portTICK_PERIOD_MS;
const TickType_t xDontBlock = ( TickType_t ) 0;

	/* Create the first two tasks as described at the top of the file. */ 
	
	/* First create the structure used to pass parameters to the consumer tasks. */
	pxQueueParameters1 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );

	/* Create the queue used by the first two tasks to pass the incrementing number.  
	Pass a pointer to the queue in the parameter structure. */
	pxQueueParameters1->xQueue = xQueueCreate( uxQueueSize1, ( unsigned portBASE_TYPE ) sizeof( unsigned short ) );

	/* The consumer is created first so gets a block time as described above. */
	pxQueueParameters1->xBlockTime = xBlockTime;

	/* Pass in the variable that this task is going to increment so we can check it 
	is still running. */
	pxQueueParameters1->psCheckVariable = &( sBlockingConsumerCount[ 0 ] );
		
	/* Create the structure used to pass parameters to the producer task. */
	pxQueueParameters2 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );

	/* Pass the queue to this task also, using the parameter structure. */
	pxQueueParameters2->xQueue = pxQueueParameters1->xQueue;

	/* The producer is not going to block - as soon as it posts the consumer will 
	wake and remove the item so the producer should always have room to post. */
	pxQueueParameters2->xBlockTime = xDontBlock;

	/* Pass in the variable that this task is going to increment so we can check 
	it is still running. */
	pxQueueParameters2->psCheckVariable = &( sBlockingProducerCount[ 0 ] );


	/* Note the producer has a lower priority than the consumer when the tasks are 
	spawned. */
	xTaskCreate( vBlockingQueueConsumer, "QConsB1", blckqSTACK_SIZE, ( void * ) pxQueueParameters1, uxPriority, NULL );
	xTaskCreate( vBlockingQueueProducer, "QProdB2", blckqSTACK_SIZE, ( void * ) pxQueueParameters2, tskIDLE_PRIORITY, NULL );

	

	/* Create the second two tasks as described at the top of the file.   This uses 
	the same mechanism but reverses the task priorities. */

	pxQueueParameters3 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );
	pxQueueParameters3->xQueue = xQueueCreate( uxQueueSize1, ( unsigned portBASE_TYPE ) sizeof( unsigned short ) );
	pxQueueParameters3->xBlockTime = xDontBlock;
	pxQueueParameters3->psCheckVariable = &( sBlockingProducerCount[ 1 ] );

	pxQueueParameters4 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );
	pxQueueParameters4->xQueue = pxQueueParameters3->xQueue;
	pxQueueParameters4->xBlockTime = xBlockTime;
	pxQueueParameters4->psCheckVariable = &( sBlockingConsumerCount[ 1 ] );

	xTaskCreate( vBlockingQueueProducer, "QProdB3", blckqSTACK_SIZE, ( void * ) pxQueueParameters3, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlockingQueueConsumer, "QConsB4", blckqSTACK_SIZE, ( void * ) pxQueueParameters4, uxPriority, NULL );



	/* Create the last two tasks as described above.  The mechanism is again just 
	the same.  This time both parameter structures are given a block time. */
	pxQueueParameters5 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );
	pxQueueParameters5->xQueue = xQueueCreate( uxQueueSize5, ( unsigned portBASE_TYPE ) sizeof( unsigned short ) );
	pxQueueParameters5->xBlockTime = xBlockTime;
	pxQueueParameters5->psCheckVariable = &( sBlockingProducerCount[ 2 ] );

	pxQueueParameters6 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );
	pxQueueParameters6->xQueue = pxQueueParameters5->xQueue;
	pxQueueParameters6->xBlockTime = xBlockTime;
	pxQueueParameters6->psCheckVariable = &( sBlockingConsumerCount[ 2 ] );	

	xTaskCreate( vBlockingQueueProducer, "QProdB5", blckqSTACK_SIZE, ( void * ) pxQueueParameters5, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlockingQueueConsumer, "QConsB6", blckqSTACK_SIZE, ( void * ) pxQueueParameters6, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

static void vBlockingQueueProducer( void *pvParameters )
{
unsigned short usValue = 0;
xBlockingQueueParameters *pxQueueParameters;
const char * const pcTaskStartMsg = "Blocking queue producer started.\r\n";
const char * const pcTaskErrorMsg = "Could not post on blocking queue\r\n";
short sErrorEverOccurred = pdFALSE;

	pxQueueParameters = ( xBlockingQueueParameters * ) pvParameters;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	for( ;; )
	{		
		if( xQueueSendToBack( pxQueueParameters->xQueue, ( void * ) &usValue, pxQueueParameters->xBlockTime ) != pdPASS )
		{
			vPrintDisplayMessage( &pcTaskErrorMsg );
			sErrorEverOccurred = pdTRUE;
		}
		else
		{
			/* We have successfully posted a message, so increment the variable 
			used to check we are still running. */
			if( sErrorEverOccurred == pdFALSE )
			{
				( *pxQueueParameters->psCheckVariable )++;
			}

			/* Increment the variable we are going to post next time round.  The 
			consumer will expect the numbers to	follow in numerical order. */
			++usValue;
		}
	}
}
/*-----------------------------------------------------------*/

static void vBlockingQueueConsumer( void *pvParameters )
{
unsigned short usData, usExpectedValue = 0;
xBlockingQueueParameters *pxQueueParameters;
const char * const pcTaskStartMsg = "Blocking queue consumer started.\r\n";
const char * const pcTaskErrorMsg = "Incorrect value received on blocking queue.\r\n";
short sErrorEverOccurred = pdFALSE;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	pxQueueParameters = ( xBlockingQueueParameters * ) pvParameters;

	for( ;; )
	{	
		if( xQueueReceive( pxQueueParameters->xQueue, &usData, pxQueueParameters->xBlockTime ) == pdPASS )
		{
			if( usData != usExpectedValue )
			{
				vPrintDisplayMessage( &pcTaskErrorMsg );

				/* Catch-up. */
				usExpectedValue = usData;

				sErrorEverOccurred = pdTRUE;
			}
			else
			{
				/* We have successfully received a message, so increment the 
				variable used to check we are still running. */	
				if( sErrorEverOccurred == pdFALSE )
				{
					( *pxQueueParameters->psCheckVariable )++;
				}
							
				/* Increment the value we expect to remove from the queue next time 
				round. */
				++usExpectedValue;
			}			
		}		
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreBlockingQueuesStillRunning( void )
{
static short sLastBlockingConsumerCount[ blckqNUM_TASK_SETS ] = { ( short ) 0, ( short ) 0, ( short ) 0 };
static short sLastBlockingProducerCount[ blckqNUM_TASK_SETS ] = { ( short ) 0, ( short ) 0, ( short ) 0 };
portBASE_TYPE xReturn = pdPASS, xTasks;

	/* Not too worried about mutual exclusion on these variables as they are 16 
	bits and we are only reading them. We also only care to see if they have 
	changed or not.
	
	Loop through each check variable and return pdFALSE if any are found not 
	to have changed since the last call. */

	for( xTasks = 0; xTasks < blckqNUM_TASK_SETS; xTasks++ )
	{
		if( sBlockingConsumerCount[ xTasks ] == sLastBlockingConsumerCount[ xTasks ]  )
		{
			xReturn = pdFALSE;
		}
		sLastBlockingConsumerCount[ xTasks ] = sBlockingConsumerCount[ xTasks ];


		if( sBlockingProducerCount[ xTasks ] == sLastBlockingProducerCount[ xTasks ]  )
		{
			xReturn = pdFALSE;
		}
		sLastBlockingProducerCount[ xTasks ] = sBlockingProducerCount[ xTasks ];
	}

	return xReturn;
}

