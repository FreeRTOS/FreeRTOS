/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


/**
 * This is a very simple queue test.  See the BlockQ. c documentation for a more 
 * comprehensive version.
 *
 * Creates two tasks that communicate over a single queue.  One task acts as a 
 * producer, the other a consumer.  
 *
 * The producer loops for three iteration, posting an incrementing number onto the 
 * queue each cycle.  It then delays for a fixed period before doing exactly the 
 * same again.
 *
 * The consumer loops emptying the queue.  Each item removed from the queue is 
 * checked to ensure it contains the expected value.  When the queue is empty it 
 * blocks for a fixed period, then does the same again.
 *
 * All queue access is performed without blocking.  The consumer completely empties 
 * the queue each time it runs so the producer should never find the queue full.  
 *
 * An error is flagged if the consumer obtains an unexpected value or the producer 
 * find the queue is full.
 *
 * \page PollQC pollQ.c
 * \ingroup DemoFiles
 * <HR>
 */

/*
Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  TickType_t rather than unsigned long.
*/

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "print.h"

/* Demo program include files. */
#include "PollQ.h"

#define pollqSTACK_SIZE		( ( unsigned short ) configMINIMAL_STACK_SIZE )

/* The task that posts the incrementing number onto the queue. */
static void vPolledQueueProducer( void *pvParameters );

/* The task that empties the queue. */
static void vPolledQueueConsumer( void *pvParameters );

/* Variables that are used to check that the tasks are still running with no errors. */
static volatile short sPollingConsumerCount = 0, sPollingProducerCount = 0;
/*-----------------------------------------------------------*/

void vStartPolledQueueTasks( unsigned portBASE_TYPE uxPriority )
{
static QueueHandle_t xPolledQueue;
const unsigned portBASE_TYPE uxQueueSize = 10;

	/* Create the queue used by the producer and consumer. */
	xPolledQueue = xQueueCreate( uxQueueSize, ( unsigned portBASE_TYPE ) sizeof( unsigned short ) );

	/* Spawn the producer and consumer. */
	xTaskCreate( vPolledQueueConsumer, "QConsNB", pollqSTACK_SIZE, ( void * ) &xPolledQueue, uxPriority, NULL );
	xTaskCreate( vPolledQueueProducer, "QProdNB", pollqSTACK_SIZE, ( void * ) &xPolledQueue, uxPriority, NULL );
}
/*-----------------------------------------------------------*/

static void vPolledQueueProducer( void *pvParameters )
{
unsigned short usValue = 0, usLoop;
QueueHandle_t *pxQueue;
const TickType_t xDelay = ( TickType_t ) 200 / portTICK_PERIOD_MS;
const unsigned short usNumToProduce = 3;
const char * const pcTaskStartMsg = "Polled queue producer started.\r\n";
const char * const pcTaskErrorMsg = "Could not post on polled queue.\r\n";
short sError = pdFALSE;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	/* The queue being used is passed in as the parameter. */
	pxQueue = ( QueueHandle_t * ) pvParameters;

	for( ;; )
	{		
		for( usLoop = 0; usLoop < usNumToProduce; ++usLoop )
		{
			/* Send an incrementing number on the queue without blocking. */
			if( xQueueSendToBack( *pxQueue, ( void * ) &usValue, ( TickType_t ) 0 ) != pdPASS )
			{
				/* We should never find the queue full - this is an error. */
				vPrintDisplayMessage( &pcTaskErrorMsg );
				sError = pdTRUE;
			}
			else
			{
				if( sError == pdFALSE )
				{
					/* If an error has ever been recorded we stop incrementing the 
					check variable. */
					++sPollingProducerCount;
				}

				/* Update the value we are going to post next time around. */
				++usValue;
			}
		}

		/* Wait before we start posting again to ensure the consumer runs and 
		empties the queue. */
		vTaskDelay( xDelay );
	}
}
/*-----------------------------------------------------------*/

static void vPolledQueueConsumer( void *pvParameters )
{
unsigned short usData, usExpectedValue = 0;
QueueHandle_t *pxQueue;
const TickType_t xDelay = ( TickType_t ) 200 / portTICK_PERIOD_MS;
const char * const pcTaskStartMsg = "Polled queue consumer started.\r\n";
const char * const pcTaskErrorMsg = "Incorrect value received on polled queue.\r\n";
short sError = pdFALSE;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	/* The queue being used is passed in as the parameter. */
	pxQueue = ( QueueHandle_t * ) pvParameters;

	for( ;; )
	{		
		/* Loop until the queue is empty. */
		while( uxQueueMessagesWaiting( *pxQueue ) )
		{
			if( xQueueReceive( *pxQueue, &usData, ( TickType_t ) 0 ) == pdPASS )
			{
				if( usData != usExpectedValue )
				{
					/* This is not what we expected to receive so an error has 
					occurred. */
					vPrintDisplayMessage( &pcTaskErrorMsg );
					sError = pdTRUE;
					/* Catch-up to the value we received so our next expected value 
					should again be correct. */
					usExpectedValue = usData;
				}
				else
				{
					if( sError == pdFALSE )
					{
						/* Only increment the check variable if no errors have 
						occurred. */
						++sPollingConsumerCount;
					}
				}
				++usExpectedValue;
			}
		}

		/* Now the queue is empty we block, allowing the producer to place more 
		items in the queue. */
		vTaskDelay( xDelay );
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running with no errors. */
portBASE_TYPE xArePollingQueuesStillRunning( void )
{
static short sLastPollingConsumerCount = 0, sLastPollingProducerCount = 0;
portBASE_TYPE xReturn;

	if( ( sLastPollingConsumerCount == sPollingConsumerCount ) ||
		( sLastPollingProducerCount == sPollingProducerCount ) 
	  )
	{
		xReturn = pdFALSE;
	}
	else
	{
		xReturn = pdTRUE;
	}

	sLastPollingConsumerCount = sPollingConsumerCount;
	sLastPollingProducerCount = sPollingProducerCount;

	return xReturn;
}
