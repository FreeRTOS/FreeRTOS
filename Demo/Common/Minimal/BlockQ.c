/*
	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

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
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/*
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
 */

/* 

Changes from V4.1.1

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

#define blckqSTACK_SIZE		configMINIMAL_STACK_SIZE
#define blckqNUM_TASK_SETS	( 3 )

/* Structure used to pass parameters to the blocking queue tasks. */
typedef struct BLOCKING_QUEUE_PARAMETERS
{
	xQueueHandle xQueue;					/*< The queue to be used by the task. */
	portTickType xBlockTime;				/*< The block time to use on queue reads/writes. */
	volatile portSHORT *psCheckVariable;	/*< Incremented on each successful cycle to check the task is still running. */
} xBlockingQueueParameters;

/* Task function that creates an incrementing number and posts it on a queue. */
static portTASK_FUNCTION_PROTO( vBlockingQueueProducer, pvParameters );

/* Task function that removes the incrementing number from a queue and checks that
it is the expected number. */
static portTASK_FUNCTION_PROTO( vBlockingQueueConsumer, pvParameters );

/* Variables which are incremented each time an item is removed from a queue, and
found to be the expected value.
These are used to check that the tasks are still running. */
static volatile portSHORT sBlockingConsumerCount[ blckqNUM_TASK_SETS ] = { ( unsigned portSHORT ) 0, ( unsigned portSHORT ) 0, ( unsigned portSHORT ) 0 };

/* Variable which are incremented each time an item is posted on a queue.   These
are used to check that the tasks are still running. */
static volatile portSHORT sBlockingProducerCount[ blckqNUM_TASK_SETS ] = { ( unsigned portSHORT ) 0, ( unsigned portSHORT ) 0, ( unsigned portSHORT ) 0 };

/*-----------------------------------------------------------*/

void vStartBlockingQueueTasks( unsigned portBASE_TYPE uxPriority )
{
xBlockingQueueParameters *pxQueueParameters1, *pxQueueParameters2;
xBlockingQueueParameters *pxQueueParameters3, *pxQueueParameters4;
xBlockingQueueParameters *pxQueueParameters5, *pxQueueParameters6;
const unsigned portBASE_TYPE uxQueueSize1 = 1, uxQueueSize5 = 5;
const portTickType xBlockTime = ( portTickType ) 1000 / portTICK_RATE_MS;
const portTickType xDontBlock = ( portTickType ) 0;

	/* Create the first two tasks as described at the top of the file. */
	
	/* First create the structure used to pass parameters to the consumer tasks. */
	pxQueueParameters1 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );

	/* Create the queue used by the first two tasks to pass the incrementing number.
	Pass a pointer to the queue in the parameter structure. */
	pxQueueParameters1->xQueue = xQueueCreate( uxQueueSize1, ( unsigned portBASE_TYPE ) sizeof( unsigned portSHORT ) );

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
	xTaskCreate( vBlockingQueueConsumer, ( signed portCHAR * ) "QConsB1", blckqSTACK_SIZE, ( void * ) pxQueueParameters1, uxPriority, NULL );
	xTaskCreate( vBlockingQueueProducer, ( signed portCHAR * ) "QProdB2", blckqSTACK_SIZE, ( void * ) pxQueueParameters2, tskIDLE_PRIORITY, NULL );

	

	/* Create the second two tasks as described at the top of the file.   This uses
	the same mechanism but reverses the task priorities. */

	pxQueueParameters3 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );
	pxQueueParameters3->xQueue = xQueueCreate( uxQueueSize1, ( unsigned portBASE_TYPE ) sizeof( unsigned portSHORT ) );
	pxQueueParameters3->xBlockTime = xDontBlock;
	pxQueueParameters3->psCheckVariable = &( sBlockingProducerCount[ 1 ] );

	pxQueueParameters4 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );
	pxQueueParameters4->xQueue = pxQueueParameters3->xQueue;
	pxQueueParameters4->xBlockTime = xBlockTime;
	pxQueueParameters4->psCheckVariable = &( sBlockingConsumerCount[ 1 ] );

	xTaskCreate( vBlockingQueueConsumer, ( signed portCHAR * ) "QProdB3", blckqSTACK_SIZE, ( void * ) pxQueueParameters3, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlockingQueueProducer, ( signed portCHAR * ) "QConsB4", blckqSTACK_SIZE, ( void * ) pxQueueParameters4, uxPriority, NULL );



	/* Create the last two tasks as described above.  The mechanism is again just
	the same.  This time both parameter structures are given a block time. */
	pxQueueParameters5 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );
	pxQueueParameters5->xQueue = xQueueCreate( uxQueueSize5, ( unsigned portBASE_TYPE ) sizeof( unsigned portSHORT ) );
	pxQueueParameters5->xBlockTime = xBlockTime;
	pxQueueParameters5->psCheckVariable = &( sBlockingProducerCount[ 2 ] );

	pxQueueParameters6 = ( xBlockingQueueParameters * ) pvPortMalloc( sizeof( xBlockingQueueParameters ) );
	pxQueueParameters6->xQueue = pxQueueParameters5->xQueue;
	pxQueueParameters6->xBlockTime = xBlockTime;
	pxQueueParameters6->psCheckVariable = &( sBlockingConsumerCount[ 2 ] );	

	xTaskCreate( vBlockingQueueProducer, ( signed portCHAR * ) "QProdB5", blckqSTACK_SIZE, ( void * ) pxQueueParameters5, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlockingQueueConsumer, ( signed portCHAR * ) "QConsB6", blckqSTACK_SIZE, ( void * ) pxQueueParameters6, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vBlockingQueueProducer, pvParameters )
{
unsigned portSHORT usValue = 0;
xBlockingQueueParameters *pxQueueParameters;
portSHORT sErrorEverOccurred = pdFALSE;

	pxQueueParameters = ( xBlockingQueueParameters * ) pvParameters;

	for( ;; )
	{		
		if( xQueueSend( pxQueueParameters->xQueue, ( void * ) &usValue, pxQueueParameters->xBlockTime ) != pdPASS )
		{
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

static portTASK_FUNCTION( vBlockingQueueConsumer, pvParameters )
{
unsigned portSHORT usData, usExpectedValue = 0;
xBlockingQueueParameters *pxQueueParameters;
portSHORT sErrorEverOccurred = pdFALSE;

	pxQueueParameters = ( xBlockingQueueParameters * ) pvParameters;

	for( ;; )
	{	
		if( xQueueReceive( pxQueueParameters->xQueue, &usData, pxQueueParameters->xBlockTime ) == pdPASS )
		{
			if( usData != usExpectedValue )
			{
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
static portSHORT sLastBlockingConsumerCount[ blckqNUM_TASK_SETS ] = { ( unsigned portSHORT ) 0, ( unsigned portSHORT ) 0, ( unsigned portSHORT ) 0 };
static portSHORT sLastBlockingProducerCount[ blckqNUM_TASK_SETS ] = { ( unsigned portSHORT ) 0, ( unsigned portSHORT ) 0, ( unsigned portSHORT ) 0 };
portBASE_TYPE xReturn = pdPASS, xTasks;

	/* Not too worried about mutual exclusion on these variables as they are 16
	bits and we are only reading them. We also only care to see if they have
	changed or not.
	
	Loop through each check variable to and return pdFALSE if any are found not
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

